#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

pub use gardswag_core::{ty::Scheme, Substitutable, Ty, TyLit, TyVar};

#[derive(Debug, thiserror::Error)]
pub enum UnifyError {
    #[error("infinite type in {v:?} = {t:?}")]
    Infinite { v: TyVar, t: Ty },
    #[error("subtitution of {v:?} = {t1:?} overridden with {t2:?}")]
    Override { v: TyVar, t1: Ty, t2: Ty },
    #[error("unification of {t1:?} = {t2:?} failed")]
    Mismatch { t1: Ty, t2: Ty },

    #[error("got infinite constraint group while merging $c{c1:?} with $c{c2:?}")]
    InfiniteConstraintGroup {
        c1: TyConstraintGroupId,
        c2: TyConstraintGroupId,
    },

    #[error("partial-record constraint failed while merging container type {container:?} and value type {value:} at key {key:?}")]
    PartialRecord {
        key: String,
        value: Ty,
        container: Ty,
    },

    #[error("one-of constraint conflict between {oo1:?} and {oo2:?} (intersection is empty)")]
    OneOfConflict { oo1: Vec<Ty>, oo2: Vec<Ty> },

    #[error("one-of constraint got {got:?}, but expected {expected:?}")]
    OneOfConstraint { got: Ty, expected: Vec<Ty> },

    #[error("expected record, got {0:?}")]
    NotARecord(Ty),
}

impl Context {
    fn on_apply(&self, i: TyVar) -> Option<Ty> {
        self.m
            .get(&i)
            .and_then(|j| self.g.get(j))
            .and_then(|k| k.ty.clone())
    }

    pub fn unify(&mut self, a: &Ty, b: &Ty) -> Result<(), UnifyError> {
        tracing::trace!("unify a={{{}}}, b={{{}}} ctx={:?}", a, b, self);
        match (a, b) {
            (Ty::Arrow(l1, r1), Ty::Arrow(l2, r2)) => {
                self.unify(l1, l2)?;
                let (mut rx1, mut rx2) = (r1.clone(), r2.clone());
                rx1.apply(&|&i| self.on_apply(i));
                rx2.apply(&|&i| self.on_apply(i));
                self.unify(&rx1, &rx2)?;
                Ok(())
            }
            (Ty::Record(rc1), Ty::Record(rc2)) if rc1.len() == rc2.len() => {
                for (k, v1) in rc1 {
                    let v2 = rc2.get(k).ok_or_else(|| UnifyError::Mismatch {
                        t1: a.clone(),
                        t2: b.clone(),
                    })?;
                    self.unify(v1, v2)?;
                }
                Ok(())
            }
            (Ty::Var(a), t) | (t, Ty::Var(a)) => self.bind(
                *a,
                TyConstraintGroup {
                    ty: Some(t.clone()),
                    ..Default::default()
                },
            ),
            (Ty::Literal(l), Ty::Literal(r)) if l == r => Ok(()),
            (_, _) => Err(UnifyError::Mismatch {
                t1: a.clone(),
                t2: b.clone(),
            }),
        }
    }
}

use core::fmt;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

pub type Tcgs = BTreeMap<TyConstraintGroupId, TyConstraintGroup>;
pub type Tvs = BTreeMap<TyVar, TyConstraintGroupId>;

#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize, Serialize)]
#[serde(transparent)]
#[repr(transparent)]
pub struct TyConstraintGroupId(usize);

impl fmt::Debug for TyConstraintGroupId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "$cg{}", self.0)
    }
}

impl fmt::Display for TyConstraintGroupId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "$cg{}", self.0)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct TyConstraintGroup {
    /// type hint, when this cg was already merged with a type,
    /// might get unified with the next type
    /// when resolved, this is the only field set
    pub ty: Option<Ty>,

    /// set of possible concrete types
    /// must not contain any type variables
    pub oneof: Vec<Ty>,

    /// type should be a record with specific fields
    pub partial_record: BTreeMap<String, Ty>,

    /// when this cg is updated, the specified tyvars get informed
    /// (this is used to forward one-way type information)
    pub listeners: BTreeSet<TyVar>,

    /// the current type is the result of applying (orig // ovrd).
    /// which means that the resulting type is a copy of ovrd,
    /// plus any field present in orig but not in ovrd.
    pub record_update_info: Option<(TyVar, TyVar)>,
}

use TyConstraintGroup as Tcg;

impl Tcg {
    /// checks if the TyCG is resolved, and returns the concrete type if yes
    pub fn resolved(&self) -> Option<&Ty> {
        let ret = self.ty.as_ref()?;
        if self.oneof.is_empty()
            && self.partial_record.is_empty()
            && self.record_update_info.is_none()
        {
            Some(ret)
        } else {
            None
        }
    }
}

pub(crate) fn lowest_tvi_for_cg(m: &Tvs, tv: TyVar) -> TyVar {
    if let Some(&x) = m.get(&tv) {
        // check if any tv with the same *x has a lower id
        // and replace it with that
        return *m.iter().find(|(_, &v)| v == x).unwrap().0;
    }
    tv
}

impl Substitutable for Tcg {
    type In = TyVar;
    type Out = Ty;

    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        if let Some(x) = &self.ty {
            x.fv(accu, do_add);
        }
        self.oneof.fv(accu, do_add);
        self.partial_record.fv(accu, do_add);
        if do_add {
            accu.extend(self.listeners.iter().copied());
        } else {
            accu.retain(|i| !self.listeners.contains(i));
        }
        if let Some((a, b)) = self.record_update_info {
            if do_add {
                accu.insert(a);
                accu.insert(b);
            } else {
                accu.remove(&a);
                accu.remove(&b);
            }
        }
    }

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&TyVar) -> Option<Ty>,
    {
        if let Some(ty) = &mut self.ty {
            ty.apply(f);
        }
        self.oneof.apply(f);
        self.partial_record.apply(f);
        // listeners?
        // record_update_info?
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    pub g: Tcgs,
    pub m: Tvs,

    pub tycg_cnt: core::ops::RangeFrom<usize>,
    pub fresh_tyvars: core::ops::RangeFrom<usize>,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            g: Default::default(),
            m: Default::default(),
            tycg_cnt: 0..,
            fresh_tyvars: 0..,
        }
    }
}

impl Context {
    pub fn fresh_tyvar(&mut self) -> Ty {
        Ty::Var(self.fresh_tyvars.next().unwrap())
    }

    /// resolve the context using itself as far as possible
    pub fn self_resolve(&mut self) {
        loop {
            let mut newg = self.g.clone();
            newg.apply(&|&i| self.on_apply(i));
            if newg == self.g {
                break;
            }
            self.g = newg;
        }
    }

    /// reduce resolved type variable to those listed in the `keep` set
    pub fn retain(&mut self, mut keep: BTreeSet<TyVar>) {
        self.g.fv(&mut keep, true);
        tracing::debug!("Ctx::retain: FV={:?}", keep);

        let orig_tvcnt = self.m.len();
        self.m.retain(|k, _| keep.contains(k));
        tracing::debug!("Ctx::retain: #tv: {} -> {}", orig_tvcnt, self.m.len());

        let keep_gids: BTreeSet<_> = self.m.values().copied().collect();
        tracing::debug!("Ctx::retain: uCG={:?}", keep_gids);

        let orig_cgcnt = self.g.len();
        self.g.retain(|k, _| keep_gids.contains(k));
        tracing::debug!("Ctx::retain: #cg: {} -> {}", orig_cgcnt, self.g.len());
    }

    fn ucg_check4inf(
        &self,
        a: TyConstraintGroupId,
        b: TyConstraintGroupId,
        t: &Ty,
    ) -> Result<(), UnifyError> {
        let mut fvaccu = Default::default();
        t.fv(&mut fvaccu, true);
        for i in fvaccu {
            if let Some(x) = self.m.get(&i) {
                let x = *x;
                if x == a {
                    return Err(UnifyError::InfiniteConstraintGroup { c1: a, c2: b });
                }
                debug_assert_ne!(x, b);
            }
        }
        Ok(())
    }

    fn notify_cgs(&mut self, mut cgs: BTreeSet<TyConstraintGroupId>) -> Result<(), UnifyError> {
        loop {
            let cg = {
                let mut it = core::mem::take(&mut cgs).into_iter();
                let cg = match it.next() {
                    Some(x) => x,
                    None => break,
                };
                cgs = it.collect();
                cg
            };
            tracing::trace!(?cg, "notify-cg");
            let mut g = self.g.remove(&cg).unwrap();
            if g.resolved().is_some() {
                tracing::trace!(?cg, ?g, "already resolved");
                self.g.insert(cg, g);
                // nothing to do
                return Ok(());
            }

            // recheck constraints
            // buffer notifications to prevent unnecessary infinite loops
            let mut modified = false;

            if let Some((orig, ovrd)) = g.record_update_info {
                match (
                    self.g.get(self.m.get(&orig).unwrap()),
                    self.g.get(self.m.get(&ovrd).unwrap()),
                ) {
                    (
                        Some(Tcg {
                            ty: Some(Ty::Record(rcm_orig)),
                            ..
                        }),
                        Some(Tcg {
                            ty: Some(Ty::Record(rcm_ovrd)),
                            ..
                        }),
                    ) => {
                        let mut rcm = rcm_ovrd.clone();
                        for (k, v) in rcm_orig {
                            if rcm.contains_key(k) {
                                continue;
                            }
                            rcm.insert(k.clone(), v.clone());
                        }
                        let rcm_ty = Ty::Record(rcm);
                        if let Some(ty) = &g.ty {
                            self.unify(&rcm_ty, ty)?;
                        }
                        modified = true;
                        g.ty = Some(rcm_ty);
                        g.record_update_info = None;
                    }
                    (
                        Some(Tcg {
                            ty: Some(ty_orig @ Ty::Literal(_) | ty_orig @ Ty::Arrow(_, _)),
                            ..
                        }),
                        _,
                    ) => {
                        return Err(UnifyError::NotARecord(ty_orig.clone()));
                    }
                    (
                        _,
                        Some(Tcg {
                            ty: Some(ty_ovrd @ Ty::Literal(_) | ty_ovrd @ Ty::Arrow(_, _)),
                            ..
                        }),
                    ) => {
                        return Err(UnifyError::NotARecord(ty_ovrd.clone()));
                    }
                    (
                        None
                        | Some(Tcg {
                            ty: None | Some(Ty::Var(_)),
                            ..
                        }),
                        _,
                    )
                    | (
                        _,
                        None
                        | Some(Tcg {
                            ty: None | Some(Ty::Var(_)),
                            ..
                        }),
                    ) => {}
                }
            }

            if let Some(ty) = &mut g.ty {
                ty.apply(&|&i| self.on_apply(i));
                let tfv = {
                    let mut tfv = Default::default();
                    ty.fv(&mut tfv, true);
                    tfv
                };
                if tfv.is_empty() {
                    let mut success = g.oneof.is_empty();
                    for j in &g.oneof {
                        let mut self_bak = self.clone();
                        if self_bak.unify(ty, j).is_ok() {
                            *self = self_bak;
                            success = true;
                            ty.apply(&|&i| self.on_apply(i));
                            break;
                        }
                    }
                    if !success {
                        return Err(UnifyError::OneOfConstraint {
                            expected: core::mem::take(&mut g.oneof),
                            got: ty.clone(),
                        });
                    }
                }

                if !g.partial_record.is_empty() {
                    if let Ty::Record(rcm) = &ty {
                        for (key, value) in core::mem::take(&mut g.partial_record) {
                            if let Some(got_valty) = rcm.get(&key) {
                                self.unify(got_valty, &value)?;
                            } else {
                                return Err(UnifyError::PartialRecord {
                                    key,
                                    value,
                                    container: ty.clone(),
                                });
                            }
                        }
                    } else {
                        return Err(UnifyError::NotARecord(ty.clone()));
                    }
                }
            }

            if modified {
                cgs.extend(g.listeners.iter().flat_map(|i| self.m.get(i)).copied());
            }
            let tmp = self.g.insert(cg, g);
            assert_eq!(tmp, None);
        }
        Ok(())
    }

    fn unify_constraint_groups(
        &mut self,
        a: TyConstraintGroupId,
        b: TyConstraintGroupId,
    ) -> Result<(), UnifyError> {
        if a == b {
            return Ok(());
        }

        tracing::debug!("unify-cgs {} {}", a, b);
        let mut lhs = self.g.remove(&a).unwrap();
        let mut rhs = self.g.remove(&b).unwrap();

        // replace all occurences of $`b` with $`a`
        self.m.values_mut().filter(|i| **i == b).for_each(|i| {
            *i = a;
        });

        if lhs == rhs {
            self.g.insert(a, lhs);
            return Ok(());
        }

        let mut res = match (lhs.resolved(), rhs.resolved()) {
            (Some(t_a), Some(t_b)) => {
                tracing::trace!(?t_a, ?t_b, "unify-cgs");
                self.ucg_check4inf(a, b, t_a)?;
                self.ucg_check4inf(a, b, t_b)?;
                self.unify(t_a, t_b)?;
                lhs.ty.as_mut().unwrap().apply(&|&i| self.on_apply(i));
                debug_assert!({
                    rhs.ty.as_mut().unwrap().apply(&|&i| self.on_apply(i));
                    lhs.ty == rhs.ty
                });
                lhs
            }
            (None, None) => {
                tracing::trace!(?lhs, ?rhs, "unify-cgs (full merge)");
                let mut ty = match (lhs.ty, rhs.ty) {
                    (None, None) => None,
                    (Some(t), None) | (None, Some(t)) => Some(t),
                    (Some(mut t1), Some(t2)) => {
                        self.unify(&t1, &t2)?;
                        t1.apply(&|&i| self.on_apply(i));
                        Some(t1)
                    }
                };
                tracing::trace!(?ty, "unify-cgs type");
                let listeners: BTreeSet<_> = lhs
                    .listeners
                    .into_iter()
                    .chain(rhs.listeners.into_iter())
                    .filter(|i| {
                        if let Some(&j) = self.m.get(i) {
                            j != a && j != b
                        } else {
                            false
                        }
                    })
                    .collect();

                let mut oneof: Vec<_> = lhs
                    .oneof
                    .iter()
                    .flat_map(|i| rhs.oneof.iter().find(|&j| i == j).map(|_| i.clone()))
                    .collect();
                if oneof.is_empty() && (!lhs.oneof.is_empty() || !rhs.oneof.is_empty()) {
                    return Err(UnifyError::OneOfConflict {
                        oo1: lhs.oneof,
                        oo2: rhs.oneof,
                    });
                }
                if oneof.len() == 1 {
                    let ty2 = oneof.remove(0);
                    if let Some(ty) = &mut ty {
                        self.unify(ty, &ty2)?;
                        ty.apply(&|&i| self.on_apply(i));
                    } else {
                        ty = Some(ty2.clone());
                    }
                }
                lhs.oneof.clear();
                rhs.oneof.clear();

                let mut partial_record = lhs.partial_record.clone();

                if partial_record.is_empty() {
                    partial_record = rhs.partial_record.clone();
                } else {
                    for (key, value) in rhs.partial_record {
                        use std::collections::btree_map::Entry;
                        match partial_record.entry(key) {
                            Entry::Occupied(mut occ) => {
                                self.unify(occ.get(), &value)?;
                                occ.get_mut().apply(&|&i| self.on_apply(i));
                            }
                            Entry::Vacant(vac) => {
                                vac.insert(value);
                            }
                        }
                    }
                }

                let record_update_info = match (lhs.record_update_info, rhs.record_update_info) {
                    (None, None) => None,
                    (Some(x), None) | (None, Some(x)) => Some(x),
                    (Some((w, x)), Some((y, z))) => {
                        use Ty::Var;
                        self.unify(&Var(w), &Var(y))?;
                        self.unify(&Var(x), &Var(z))?;
                        Some((lowest_tvi_for_cg(&self.m, w), lowest_tvi_for_cg(&self.m, x)))
                    }
                };

                Tcg {
                    ty,
                    oneof,
                    partial_record,
                    listeners,
                    record_update_info,
                }
            }
            (_, _) => {
                let (t, mut g) = if let Some(t) = lhs.resolved() {
                    (t, rhs)
                } else {
                    (rhs.ty.as_ref().unwrap(), lhs)
                };
                tracing::trace!(?t, ?g, "unify-cg");
                self.ucg_check4inf(a, b, t)?;
                let tfv = {
                    let mut tfv = Default::default();
                    t.fv(&mut tfv, true);
                    tfv
                };
                if !tfv.is_empty() {
                    for i in tfv {
                        self.ucg_check4inf(a, b, &Ty::Var(i))?;
                    }
                } else if !g.oneof.is_empty() {
                    if g.oneof.len() == 1 {
                        let j = core::mem::take(&mut g.oneof).into_iter().next().unwrap();
                        self.ucg_check4inf(a, b, &j)?;
                        self.unify(t, &j)?;
                    } else {
                        let mut success = false;
                        for j in &g.oneof {
                            let mut self_bak = self.clone();
                            if self_bak.unify(t, j).is_ok() {
                                *self = self_bak;
                                success = true;
                                break;
                            }
                        }
                        if !success {
                            return Err(UnifyError::OneOfConstraint {
                                expected: core::mem::take(&mut g.oneof),
                                got: t.clone(),
                            });
                        }
                    }
                }
                if !g.partial_record.is_empty() {
                    if let Ty::Record(rcm) = &t {
                        for (key, value) in core::mem::take(&mut g.partial_record) {
                            if let Some(got_valty) = rcm.get(&key) {
                                self.unify(got_valty, &value)?;
                            } else {
                                return Err(UnifyError::PartialRecord {
                                    key: key.clone(),
                                    value: value.clone(),
                                    container: t.clone(),
                                });
                            }
                        }
                    } else if !matches!(t, Ty::Var(_)) {
                        return Err(UnifyError::NotARecord(t.clone()));
                    }
                }
                if let Some(old) = &g.ty {
                    self.unify(old, t)?;
                } else {
                    g.ty = Some(t.clone());
                }
                g
            }
        };
        res.apply(&|&i| self.on_apply(i));
        let notify_cgs = res
            .listeners
            .iter()
            .flat_map(|i| self.m.get(i))
            .copied()
            .collect();

        let x = self.g.insert(a, res);
        assert_eq!(x, None);
        // propagate inference information
        self.notify_cgs(notify_cgs)?;
        Ok(())
    }

    pub fn bind(&mut self, v: TyVar, tcg: Tcg) -> Result<(), UnifyError> {
        if let Some(t) = tcg.resolved() {
            if let Ty::Var(y) = t {
                let tcgid = match (self.m.get(&v), self.m.get(y)) {
                    (None, None) => {
                        let tcgid = TyConstraintGroupId(self.tycg_cnt.next().unwrap());
                        let tmp = self.g.insert(tcgid, Default::default());
                        assert_eq!(tmp, None);
                        tcgid
                    }
                    (Some(&tcgid), None) | (None, Some(&tcgid)) => tcgid,
                    (Some(&vcg), Some(&ycg)) => return self.unify_constraint_groups(vcg, ycg),
                };
                self.m.insert(v, tcgid);
                self.m.insert(*y, tcgid);
                return Ok(());
            }
            let tfv = {
                let mut tfv = Default::default();
                t.fv(&mut tfv, true);
                tfv
            };
            if tfv.contains(&v) {
                return Err(UnifyError::Infinite { v, t: t.clone() });
            }
        }
        use std::collections::btree_map::Entry;
        match self.m.entry(v) {
            Entry::Occupied(occ) => {
                let lhs_tcgid = *occ.get();
                let rhs_tcgid = TyConstraintGroupId(self.tycg_cnt.next().unwrap());
                self.g.insert(rhs_tcgid, tcg);
                self.unify_constraint_groups(lhs_tcgid, rhs_tcgid)
                /*Err(UnifyError::Override {
                    v: v.clone(),
                    t1: occ.get().clone(),
                    t2: t.clone(),
                })*/
            }
            Entry::Vacant(y) => {
                let tcgid = TyConstraintGroupId(self.tycg_cnt.next().unwrap());
                y.insert(tcgid);
                let z = self.g.insert(tcgid, tcg);
                assert_eq!(z, None);
                Ok(())
            }
        }
    }
}
