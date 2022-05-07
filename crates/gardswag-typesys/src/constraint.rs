use crate::{Substitutable, TyVar, UnifyError};
use core::fmt;
use enum_dispatch::enum_dispatch;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize, Serialize)]
#[serde(transparent)]
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

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[enum_dispatch(Substitutable)]
pub enum TyConstraintGroup {
    /// when not yet resolved, contains the list of constraints
    Constraints(Vec<TyConstraint>),

    /// when resolved, contains the concrete type
    Ty(crate::Ty),
}

impl Default for TyConstraintGroup {
    #[inline]
    fn default() -> Self {
        Self::Constraints(vec![])
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum TyConstraint {
    /// set of concrete types
    /// should most of the time not contain any type variables
    OneOf(Vec<crate::Ty>),

    /// record with specific field
    PartialRecord { key: String, value: crate::Ty },
}

impl Substitutable for TyConstraint {
    fn fv(&self) -> BTreeSet<TyVar> {
        match self {
            Self::OneOf(oo) => oo.fv(),
            Self::PartialRecord { value, .. } => value.fv(),
        }
    }

    fn apply(&mut self, ctx: &Context) {
        match self {
            Self::OneOf(oo) => oo.apply(ctx),
            Self::PartialRecord { value, .. } => value.apply(ctx),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    pub g: HashMap<TyConstraintGroupId, TyConstraintGroup>,
    pub m: BTreeMap<TyVar, TyConstraintGroupId>,

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

impl Substitutable for Context {
    #[inline(always)]
    fn fv(&self) -> BTreeSet<TyVar> {
        self.g.fv()
    }

    #[inline(always)]
    fn apply(&mut self, ctx: &Context) {
        self.g.apply(ctx)
    }
}

impl Context {
    pub fn fresh_tyvar(&mut self) -> crate::Ty {
        crate::Ty::Var(self.fresh_tyvars.next().unwrap())
    }

    pub(crate) fn filter(&self, filt: &BTreeSet<TyVar>) -> Self {
        Context {
            m: self
                .m
                .iter()
                .filter(|(k, _)| !filt.contains(k))
                .map(|(&k, &v)| (k, v))
                .collect(),
            g: self.g.clone(),
            tycg_cnt: self.tycg_cnt.clone(),
            fresh_tyvars: self.fresh_tyvars.clone(),
        }
    }

    /// resolve the context using itself as far as possible
    pub fn self_resolve(&mut self) {
        loop {
            let old = self.clone();
            self.apply(&old);
            if old == *self {
                break;
            }
        }
    }

    /// reduce resolved type variable to those listed in the `keep` set
    pub fn retain(&mut self, mut keep: BTreeSet<TyVar>) {
        keep.extend(self.fv());
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
        t: &crate::Ty,
    ) -> Result<(), UnifyError> {
        for i in t.fv() {
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

    fn unify_constraint_groups(
        &mut self,
        a: TyConstraintGroupId,
        b: TyConstraintGroupId,
    ) -> Result<(), UnifyError> {
        if a == b || *self.g.get(&a).unwrap() == *self.g.get(&b).unwrap() {
            return Ok(());
        }

        let lhs = self.g.remove(&a).unwrap();
        let rhs = self.g.remove(&b).unwrap();

        // replace all occurences of $`b` with $`a`
        self.m.values_mut().filter(|i| **i == b).for_each(|i| {
            *i = a;
        });

        use TyConstraintGroup as Tcg;
        let res = match (lhs, rhs) {
            (Tcg::Ty(mut t_a), Tcg::Ty(mut t_b)) => {
                self.ucg_check4inf(a, b, &t_a)?;
                self.ucg_check4inf(a, b, &t_b)?;
                self.unify(&t_a, &t_b)?;
                t_a.apply(self);
                debug_assert!({
                    t_b.apply(self);
                    t_a == t_b
                });
                Tcg::Ty(t_a)
            }
            (Tcg::Constraints(mut c_a), Tcg::Constraints(c_b)) => {
                c_a.extend(c_b);
                Tcg::Constraints(c_a)
            }
            (Tcg::Constraints(mut c), Tcg::Ty(t)) | (Tcg::Ty(t), Tcg::Constraints(mut c)) => {
                self.ucg_check4inf(a, b, &t)?;
                let tfv = t.fv();
                if !tfv.is_empty() {
                    for i in tfv {
                        self.ucg_check4inf(a, b, &crate::Ty::Var(i))?;
                    }

                    // check for partial record constraints, to improve inference
                    if let crate::Ty::Record(rcm) = &t {
                        for i in &c {
                            if let TyConstraint::PartialRecord { key, value } = i {
                                if let Some(got_valty) = rcm.get(key) {
                                    self.unify(got_valty, value)?;
                                } else {
                                    return Err(UnifyError::Constraint { c: i.clone(), t });
                                }
                            }
                        }
                    }

                    c.push(TyConstraint::OneOf(core::iter::once(t).collect()));
                    Tcg::Constraints(c)
                } else {
                    // check against all constraints
                    for i in c {
                        match i {
                            TyConstraint::OneOf(oo) => {
                                if oo.len() == 1 {
                                    let j = oo.into_iter().next().unwrap();
                                    self.ucg_check4inf(a, b, &j)?;
                                    self.unify(&t, &j)?;
                                } else {
                                    let mut success = false;
                                    for j in &oo {
                                        self.ucg_check4inf(a, b, j)?;
                                        let mut self_bak = self.clone();
                                        if self_bak.unify(&t, j).is_ok() {
                                            *self = self_bak;
                                            success = true;
                                            break;
                                        }
                                    }
                                    if !success {
                                        return Err(UnifyError::Constraint {
                                            c: TyConstraint::OneOf(oo),
                                            t,
                                        });
                                    }
                                }
                            }
                            TyConstraint::PartialRecord { key, value } => {
                                if let crate::Ty::Record(rcm) = &t {
                                    if let Some(got_valty) = rcm.get(&key) {
                                        self.unify(got_valty, &value)?;
                                    } else {
                                        return Err(UnifyError::Constraint {
                                            c: TyConstraint::PartialRecord { key, value },
                                            t,
                                        });
                                    }
                                } else {
                                    return Err(UnifyError::Constraint {
                                        c: TyConstraint::PartialRecord { key, value },
                                        t,
                                    });
                                }
                            }
                        }
                    }
                    Tcg::Ty(t)
                }
            }
        };
        let x = self.g.insert(a, res);
        assert_eq!(x, None);
        Ok(())
    }

    pub fn bind(&mut self, v: TyVar, tcg: TyConstraintGroup) -> Result<(), UnifyError> {
        if let TyConstraintGroup::Ty(t) = &tcg {
            if let crate::Ty::Var(y) = t {
                let tcgid = match (self.m.get(&v), self.m.get(y)) {
                    (None, None) => TyConstraintGroupId(self.tycg_cnt.next().unwrap()),
                    (Some(&tcgid), None) | (None, Some(&tcgid)) => tcgid,
                    (Some(&vcg), Some(&ycg)) => return self.unify_constraint_groups(vcg, ycg),
                };
                self.m.insert(v, tcgid);
                self.m.insert(*y, tcgid);
                return Ok(());
            }
            if t.fv().contains(&v) {
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
