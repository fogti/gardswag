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

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

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
    fresh_tyvars: core::ops::RangeFrom<usize>,
    pub constraints: Vec<(usize, Constraint)>,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            fresh_tyvars: 0..,
            constraints: Default::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    Unify(Ty, Ty),
    Bind(TyVar, Tcg),
}

impl Substitutable for Constraint {
    type In = TyVar;
    type Out = TyVar;

    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        match self {
            Self::Unify(a, b) => {
                a.fv(accu, do_add);
                b.fv(accu, do_add);
            }
            Self::Bind(tv, cg) => {
                if do_add {
                    accu.insert(*tv);
                } else {
                    accu.remove(tv);
                }
                cg.fv(accu, do_add);
            }
        }
    }

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&TyVar) -> Option<TyVar>,
    {
        let f2 = move |i: &TyVar| f(i).map(Ty::Var);
        match self {
            Self::Unify(a, b) => {
                a.apply(&f2);
                b.apply(&f2);
            }
            Self::Bind(tv, cg) => {
                if let Some(x) = f(tv) {
                    *tv = x;
                }
                cg.apply(&f2);
            }
        }
    }
}

impl gardswag_core::ty::Context for Context {
    fn fresh_tyvar(&mut self) -> TyVar {
        self.fresh_tyvars.next().unwrap()
    }

    fn dup_tyvars<I: Iterator<Item = TyVar>>(&mut self, tvs: I) -> BTreeMap<TyVar, TyVar> {
        let ret: BTreeMap<_, _> = tvs
            .map(|i| {
                let j = self.fresh_tyvar();
                (i, j)
            })
            .collect();
        let new_constraints: Vec<_> = self
            .constraints
            .iter()
            .filter(|i| {
                let mut tfv = Default::default();
                i.1.fv(&mut tfv, true);
                tfv.into_iter().any(|j| ret.contains_key(&j))
            })
            .map(|i| {
                let mut i = i.clone();
                let f = |j: &TyVar| ret.get(j).copied();
                i.1.apply(&f);
                i
            })
            .collect();
        self.constraints.extend(new_constraints);
        ret
    }

    fn unify(&mut self, offset: usize, a: Ty, b: Ty) {
        self.constraints.push((offset, Constraint::Unify(a, b)));
    }
}

impl Context {
    pub fn bind(&mut self, offset: usize, v: TyVar, tcg: Tcg) {
        self.constraints.push((offset, Constraint::Bind(v, tcg)));
    }
}
