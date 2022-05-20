use crate::{FreeVars, Substitutable};
use core::fmt;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// atomic base types
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
            Self::Bool => "Bool",
            Self::Int => "Int",
            Self::String => "Str",
        })
    }
}

pub type TyVar = usize;

#[derive(Clone, PartialEq, Eq, Deserialize, Serialize)]
pub enum Ty {
    Literal(TyLit),

    Var(TyVar),

    Arrow(Box<Ty>, Box<Ty>),

    ChanSend(Box<Ty>),

    ChanRecv(Box<Ty>),

    Record(BTreeMap<String, Ty>),

    TaggedUnion(BTreeMap<String, Ty>),
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Literal(lit) => write!(f, "{}", lit),
            Ty::Var(v) => write!(f, "${}", v),
            Ty::Arrow(a, b) => {
                if matches!(**a, Ty::Arrow(..)) {
                    write!(f, "({})", a)
                } else {
                    write!(f, "{}", a)
                }?;
                write!(f, " -> {}", b)
            }
            Ty::ChanSend(x) => {
                write!(f, "Chan:send(")?;
                <Ty as fmt::Display>::fmt(x, f)?;
                write!(f, ")")
            }
            Ty::ChanRecv(x) => {
                write!(f, "Chan:recv(")?;
                <Ty as fmt::Display>::fmt(x, f)?;
                write!(f, ")")
            }
            Ty::Record(m) => f.debug_map().entries(m.iter()).finish(),
            Ty::TaggedUnion(m) => {
                write!(f, "any(")?;
                f.debug_map().entries(m.iter()).finish()?;
                write!(f, ")")
            }
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ty{{")?;
        <Ty as fmt::Display>::fmt(self, f)?;
        write!(f, "}}")
    }
}

impl FreeVars for Ty {
    type In = TyVar;

    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        match self {
            Ty::Literal(_) => {}
            Ty::Var(tv) => {
                tv.fv(accu, do_add);
            }
            Ty::Arrow(arg, ret) => {
                arg.fv(accu, do_add);
                ret.fv(accu, do_add);
            }
            Ty::ChanSend(x) => x.fv(accu, do_add),
            Ty::ChanRecv(x) => x.fv(accu, do_add),
            Ty::Record(rcm) => {
                rcm.values().for_each(|i| i.fv(accu, do_add));
            }
            Ty::TaggedUnion(rcm) => {
                rcm.values().for_each(|i| i.fv(accu, do_add));
            }
        }
    }
}

impl Substitutable for Ty {
    type Out = Self;

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&TyVar) -> Option<Self>,
    {
        match self {
            Ty::Literal(_) => {}
            Ty::Var(ref mut tv) => {
                if let Some(x) = f(tv) {
                    *self = x;
                }
            }
            Ty::Arrow(arg, ret) => {
                arg.apply(f);
                ret.apply(f);
            }
            Ty::ChanSend(x) => x.apply(f),
            Ty::ChanRecv(x) => x.apply(f),
            Ty::Record(rcm) => {
                rcm.values_mut().for_each(|i| i.apply(f));
            }
            Ty::TaggedUnion(rcm) => {
                rcm.values_mut().for_each(|i| i.apply(f));
            }
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Scheme {
    pub forall: BTreeSet<TyVar>,
    pub ty: Ty,
}

impl fmt::Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{:?}>({})", self.forall, self.ty)
    }
}

impl Ty {
    /// compute the type scheme
    /// by recording all inner type variables
    pub fn generalize<E>(self, depenv: &E, rng: core::ops::Range<TyVar>) -> Scheme
    where
        E: FreeVars<In = TyVar>,
    {
        let mut forall = rng.collect();
        //self.fv(&mut forall, true);
        depenv.fv(&mut forall, false);
        let ret = Scheme { forall, ty: self };
        tracing::trace!("generalize res {:?}", ret);
        ret
    }
}

impl Scheme {
    pub fn instantiate(&self, outerctx: &mut crate::CollectContext) -> Ty {
        let mut t2 = self.ty.clone();
        let m = outerctx.dup_tyvars(self.forall.iter().copied());
        t2.apply(&|i| m.get(i).map(|&j| Ty::Var(j)));
        tracing::trace!("instantiate res {:?}", t2);
        t2
    }
}

impl FreeVars for Scheme {
    type In = TyVar;

    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        if do_add {
            let x: Vec<usize> = self.forall.difference(accu).copied().collect();
            if !x.is_empty() {
                panic!("Scheme::fv: accu contains elements of forall: {:?}", x);
            }
            self.ty.fv(accu, true);
            for i in &self.forall {
                accu.remove(i);
            }
        } else {
            self.ty.fv(accu, false);
        }
    }
}

impl Substitutable for Scheme {
    type Out = Ty;

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&Self::In) -> Option<Self::Out>,
    {
        self.ty.apply(&|i| {
            if self.forall.contains(i) {
                if let Some(x) = f(i) {
                    tracing::warn!(
                        "Scheme::apply: tried to apply ${} <- {:?}, but ${} is an forall element",
                        i,
                        x,
                        i
                    );
                }
                None
            } else {
                f(i)
            }
        });
    }
}
