use core::{cmp, fmt};
use enum_dispatch::enum_dispatch;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap};

mod constraint;

pub use constraint::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize, Serialize)]
pub enum TyLit {
    Unit,
    Bool,
    Int,
    String,
}

impl fmt::Display for TyLit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Unit => "()",
            Self::Bool => "bool",
            Self::Int => "int",
            Self::String => "str",
        })
    }
}

pub type TyVar = usize;

#[derive(Clone, PartialEq, Eq, Deserialize, Serialize)]
pub enum Ty {
    Literal(TyLit),

    Var(TyVar),

    Arrow(Box<Ty>, Box<Ty>),

    Record(HashMap<String, Ty>),
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Literal(lit) => write!(f, "{}", lit),
            Ty::Var(v) => write!(f, "${:?}", v),
            Ty::Arrow(a, b) => {
                if matches!(**a, Ty::Arrow(..)) {
                    write!(f, "({})", a)
                } else {
                    write!(f, "{}", a)
                }?;
                write!(f, " -> {}", b)
            },
            Ty::Record(m) => write!(f, "{:?}", m),
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ty{{{}}}", self)
    }
}

#[derive(Clone, Debug, Eq)]
pub struct Scheme {
    pub forall: HashMap<TyVar, TyConstraintGroup>,
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
    fn apply(&mut self, ctx: &Context);
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

    fn apply(&mut self, ctx: &Context) {
        match self {
            Ty::Literal(_) => {}
            Ty::Var(tv) => {
                if let Some(x) = ctx.m.get(tv) {
                    if let Some(TyConstraintGroup::Ty(t)) = ctx.g.get(x) {
                        *self = t.clone();
                    } else {
                        // check if any tv with the same *x has a lower id
                        // and replace it with that
                        for (k, v) in &ctx.m {
                            if *k >= *tv {
                                break;
                            }
                            if *v == *x {
                                *self = Ty::Var(*k);
                                break;
                            }
                        }
                    }
                }
            }
            Ty::Arrow(arg, ret) => {
                arg.apply(ctx);
                ret.apply(ctx);
            }
            Ty::Record(m) => {
                m.values_mut().for_each(|i| i.apply(ctx));
            }
        }
    }
}

impl Ty {
    pub fn replace_tyvars(&mut self, tym: &BTreeMap<TyVar, TyVar>) {
        match self {
            Ty::Literal(_) => {}
            Ty::Var(ref mut tv) => {
                if let Some(x) = tym.get(tv) {
                    *tv = *x;
                }
            }
            Ty::Arrow(arg, ret) => {
                arg.replace_tyvars(tym);
                ret.replace_tyvars(tym);
            }
            Ty::Record(m) => {
                m.values_mut().for_each(|i| i.replace_tyvars(tym));
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

    fn apply(&mut self, ctx: &Context) {
        self.t
            .apply(&ctx.filter(&self.forall.keys().copied().collect()))
    }
}

impl<V: Substitutable> Substitutable for [V] {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.iter().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, ctx: &Context) {
        self.iter_mut().for_each(|i| i.apply(ctx))
    }
}

impl<V: Substitutable> Substitutable for Vec<V> {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.iter().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, ctx: &Context) {
        self.iter_mut().for_each(|i| i.apply(ctx))
    }
}

impl<V: Substitutable + cmp::Ord> Substitutable for BTreeSet<V> {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.iter().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, ctx: &Context) {
        *self = core::mem::take(self)
            .into_iter()
            .map(|mut i| {
                i.apply(ctx);
                i
            })
            .collect();
    }
}

impl<K: core::hash::Hash + cmp::Eq, V: Substitutable> Substitutable for HashMap<K, V> {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.values().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, ctx: &Context) {
        self.values_mut().for_each(|i| i.apply(ctx));
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
    #[error("constraint {c:?} isn't compatible with type {t:?}")]
    Constraint { c: TyConstraint, t: Ty },
}

impl constraint::Context {
    pub fn unify(&mut self, a: &Ty, b: &Ty) -> Result<(), UnifyError> {
        tracing::trace!("unify a={{{}}}, b={{{}}} ctx={:?}", a, b, self);
        match (a, b) {
            (Ty::Arrow(l1, r1), Ty::Arrow(l2, r2)) => {
                self.unify(l1, l2)?;
                let (mut rx1, mut rx2) = (r1.clone(), r2.clone());
                rx1.apply(self);
                rx2.apply(self);
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
            (Ty::Var(a), t) => self.bind(*a, TyConstraintGroup::from(t.clone())),
            (t, Ty::Var(a)) => self.bind(*a, TyConstraintGroup::from(t.clone())),
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
            let new_tid = outerctx.fresh_tyvars.next().unwrap();
            if c != &cdfl {
                outerctx.bind(new_tid, c.clone()).unwrap();
            }
            m.insert(*k, new_tid);
        }
        t2.replace_tyvars(&m);
        t2
    }
}

impl Ty {
    pub fn generalize<S: Substitutable>(self, env: &S, outerctx: &Context) -> Scheme {
        Scheme {
            forall: self
                .fv()
                .difference(&env.fv())
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
            t: self,
        }
    }
}

#[cfg(test)]
mod tests {}
