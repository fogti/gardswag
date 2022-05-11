#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

use core::{cmp, fmt};
use enum_dispatch::enum_dispatch;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap};

mod constraint;

pub use constraint::*;

pub use gardswag_core::{Ty, TyLit, TyVar};

#[derive(Clone, Debug, Eq, Deserialize, Serialize)]
pub struct Scheme {
    pub forall: BTreeMap<TyVar, TyConstraintGroup>,
    pub t: Ty,
}

impl cmp::PartialEq for Scheme {
    fn eq(&self, oth: &Self) -> bool {
        let slfaie = self.forall.is_empty();
        if slfaie != oth.forall.is_empty() {
            false
        } else if slfaie {
            self.t == oth.t
        } else {
            let mut ctx = Context::default();
            ctx.unify(&self.t, &oth.t).is_ok()
        }
    }
}

impl fmt::Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{:?}>({})", self.forall, self.t)
    }
}

#[enum_dispatch]
pub trait Substitutable {
    // generate list of all free variables
    fn fv(&self) -> BTreeSet<TyVar>;

    // apply substitution
    fn apply(&mut self, g: &Tcgs, m: &Tvs);
}

impl Substitutable for Ty {
    fn fv(&self) -> BTreeSet<TyVar> {
        match self {
            Ty::Literal(_) => Default::default(),
            Ty::Var(tv) => core::iter::once(*tv).collect(),
            Ty::Arrow(arg, ret) => arg.fv().union(&ret.fv()).cloned().collect(),
            Ty::Record(m) => m.values().flat_map(|i| i.fv()).collect(),
        }
    }

    fn apply(&mut self, g: &Tcgs, m: &Tvs) {
        match self {
            Ty::Literal(_) => {}
            Ty::Var(tv) => {
                if let Some(x) = m.get(tv) {
                    *self = if let Some(t) = g.get(x).and_then(|tcg| tcg.resolved()) {
                        t.clone()
                    } else {
                        Ty::Var(constraint::lowest_tvi_for_cg(m, *tv))
                    };
                }
            }
            Ty::Arrow(arg, ret) => {
                arg.apply(g, m);
                ret.apply(g, m);
            }
            Ty::Record(rcm) => {
                rcm.values_mut().for_each(|i| i.apply(g, m));
            }
        }
    }
}

impl Substitutable for Scheme {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.t
            .fv()
            .into_iter()
            .filter(|i| !self.forall.contains_key(i))
            .collect()
    }

    fn apply(&mut self, g: &Tcgs, m: &Tvs) {
        let subm = m
            .iter()
            .filter(|(k, _)| !self.forall.contains_key(k))
            .map(|(&k, &v)| (k, v))
            .collect();
        self.t.apply(g, &subm)
    }
}

impl<V: Substitutable> Substitutable for [V] {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.iter().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, g: &Tcgs, m: &Tvs) {
        self.iter_mut().for_each(|i| i.apply(g, m))
    }
}

impl<V: Substitutable> Substitutable for Vec<V> {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.iter().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, g: &Tcgs, m: &Tvs) {
        self.iter_mut().for_each(|i| i.apply(g, m))
    }
}

impl<V: Substitutable + cmp::Ord> Substitutable for BTreeSet<V> {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.iter().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, g: &Tcgs, m: &Tvs) {
        *self = core::mem::take(self)
            .into_iter()
            .map(|mut i| {
                i.apply(g, m);
                i
            })
            .collect();
    }
}

impl<K: cmp::Eq + cmp::Ord, V: Substitutable> Substitutable for BTreeMap<K, V> {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.values().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, g: &Tcgs, m: &Tvs) {
        self.values_mut().for_each(|i| i.apply(g, m));
    }
}

impl<K: core::hash::Hash + cmp::Eq, V: Substitutable> Substitutable for HashMap<K, V> {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.values().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, g: &Tcgs, m: &Tvs) {
        self.values_mut().for_each(|i| i.apply(g, m));
    }
}

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
    pub fn unify(&mut self, a: &Ty, b: &Ty) -> Result<(), UnifyError> {
        tracing::trace!("unify a={{{}}}, b={{{}}} ctx={:?}", a, b, self);
        match (a, b) {
            (Ty::Arrow(l1, r1), Ty::Arrow(l2, r2)) => {
                self.unify(l1, l2)?;
                let (mut rx1, mut rx2) = (r1.clone(), r2.clone());
                rx1.apply(&self.g, &self.m);
                rx2.apply(&self.g, &self.m);
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

impl Scheme {
    pub fn instantiate(&self, outerctx: &mut Context) -> Ty {
        let mut t2 = self.t.clone();
        let mut m = BTreeMap::default();
        let cdfl = Default::default();
        for (k, c) in &self.forall {
            tracing::trace!("instantiate (forall item) {:?}=>{:?}", k, c);
            let new_tid = outerctx.fresh_tyvars.next().unwrap();
            if c != &cdfl {
                outerctx.bind(new_tid, c.clone()).unwrap();
            }
            m.insert(*k, new_tid);
        }
        tracing::trace!("instantiate (input): {:?}", t2);
        tracing::trace!("instantiate (ctx): {:?}", outerctx);
        t2.replace_tyvars(&m);
        tracing::trace!("instantiate (output): {:?}", t2);
        t2
    }
}

pub fn generalize<S: Substitutable + fmt::Debug>(ty: Ty, env: &S, outerctx: &Context) -> Scheme {
    let ret = Scheme {
        forall: ty
            .fv()
            .difference(&env.fv())
            .inspect(|var| tracing::trace!(?var, "generalize:tyvar"))
            .cloned()
            .map(|var| {
                // TODO: make sure this works correctly
                (
                    var,
                    outerctx
                        .m
                        .get(&var)
                        .map(|gid| outerctx.g.get(gid).unwrap())
                        .cloned()
                        .unwrap_or_default(),
                )
            })
            .collect(),
        t: ty,
    };
    tracing::trace!(?env, ?outerctx, ?ret, "generalize");
    ret
}

#[cfg(test)]
mod tests {}
