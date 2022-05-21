use crate::{FreeVars, Substitutable, Ty, TyVar};
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

    /// when this cg is updated, the specified tyvars get informed
    /// (this is used to forward one-way type information)
    pub listeners: BTreeSet<TyVar>,

    pub kind: Option<TyConstraintGroupKind>,
}

use TyConstraintGroup as Tcg;

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum TyConstraintGroupKind {
    /// type should be a record
    Record {
        /// with at least some specific fields
        partial: BTreeMap<String, Ty>,

        /// the current type is the result of applying (orig // ovrd).
        /// which means that the resulting type is a copy of ovrd,
        /// plus any field present in orig but not in ovrd.
        update_info: Option<(TyVar, TyVar)>,
    },

    /// type should be a discriminated/tagged union
    TaggedUnion {
        /// with at least some specific fields
        partial: BTreeMap<String, Ty>,
    },
}

use TyConstraintGroupKind as Tcgk;

impl Tcg {
    /// checks if the TyCG is resolved, and returns the concrete type if yes
    pub fn resolved(&self) -> Option<&Ty> {
        let ret = self.ty.as_ref()?;
        if self.oneof.is_empty() && self.kind.is_none() {
            Some(ret)
        } else {
            None
        }
    }
}

impl FreeVars<TyVar> for Tcg {
    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        if let Some(x) = &self.ty {
            x.fv(accu, do_add);
        }
        self.oneof.fv(accu, do_add);
        if do_add {
            accu.extend(self.listeners.iter().copied());
        } else {
            accu.retain(|i| !self.listeners.contains(i));
        }
        if let Some(x) = &self.kind {
            x.fv(accu, do_add);
        }
    }
}

impl Substitutable<TyVar> for Tcg {
    type Out = Ty;
    fn apply<F: Fn(&TyVar) -> Option<Ty>>(&mut self, f: &F) {
        if let Some(ty) = &mut self.ty {
            ty.apply(f);
        }
        self.oneof.apply(f);
        let f2 = move |i: &TyVar| {
            // this is annoyingly fragile
            if let Some(Ty::Var(x)) = f(i) {
                Some(x)
            } else {
                None
            }
        };
        self.listeners.apply(&f2);
        if let Some(x) = &mut self.kind {
            x.apply(f);
        }
    }
}

impl FreeVars<TyVar> for Tcgk {
    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        match self {
            Tcgk::Record {
                partial,
                update_info,
            } => {
                partial.fv(accu, do_add);
                if let Some((a, b)) = update_info {
                    if do_add {
                        accu.insert(*a);
                        accu.insert(*b);
                    } else {
                        accu.remove(a);
                        accu.remove(b);
                    }
                }
            }
            Tcgk::TaggedUnion { partial } => {
                partial.fv(accu, do_add);
            }
        }
    }
}

impl Substitutable<TyVar> for Tcgk {
    type Out = Ty;
    fn apply<F: Fn(&TyVar) -> Option<Ty>>(&mut self, f: &F) {
        let f2 = move |i: &TyVar| {
            // this is annoyingly fragile
            if let Some(Ty::Var(x)) = f(i) {
                Some(x)
            } else {
                None
            }
        };
        match self {
            Tcgk::Record {
                partial,
                update_info,
            } => {
                partial.apply(f);
                if let Some((a, b)) = update_info {
                    if let Some(x) = f2(a) {
                        *a = x;
                    }
                    if let Some(x) = f2(b) {
                        *b = x;
                    }
                }
            }
            Tcgk::TaggedUnion { partial } => {
                partial.apply(f);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    Unify(Ty, Ty),
    Bind(TyVar, Tcg),
}

impl FreeVars<TyVar> for Constraint {
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
}

impl Substitutable<TyVar> for Constraint {
    type Out = TyVar;
    fn apply<F: Fn(&TyVar) -> Option<TyVar>>(&mut self, f: &F) {
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

/// type constraints collector
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

impl Context {
    pub fn fresh_tyvar(&mut self) -> TyVar {
        self.fresh_tyvars.next().unwrap()
    }

    pub(crate) fn dup_tyvars<I>(&mut self, tvs: I) -> BTreeMap<TyVar, TyVar>
    where
        I: Iterator<Item = TyVar>,
    {
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

    pub fn unify(&mut self, offset: usize, a: Ty, b: Ty) {
        if a != b {
            self.constraints.push((offset, Constraint::Unify(a, b)));
        }
    }

    #[inline]
    pub fn peek_next_tyvar(&self) -> TyVar {
        self.fresh_tyvars.start
    }

    pub fn bind(&mut self, offset: usize, v: TyVar, tcg: Tcg) {
        self.constraints.push((offset, Constraint::Bind(v, tcg)));
    }
}
