use crate::Substitutable;
use core::fmt;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

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

pub trait Context {
    /// duplicates a type variable, including it's constraints
    fn dup_tyvars<I: Iterator<Item = TyVar>>(&mut self, tv: I) -> BTreeMap<TyVar, TyVar>;
}

#[derive(Clone, PartialEq, Eq, Deserialize, Serialize)]
pub enum Ty {
    Literal(TyLit),

    Var(TyVar),

    Arrow(Box<Ty>, Box<Ty>),

    Record(BTreeMap<String, Ty>),
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
            }
            Ty::Record(m) => write!(f, "{:?}", m),
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ty{{{}}}", self)
    }
}

impl Substitutable for Ty {
    type In = TyVar;
    type Out = Self;

    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        match self {
            Ty::Literal(_) => {}
            Ty::Var(tv) => {
                if do_add {
                    accu.insert(*tv);
                } else {
                    accu.remove(tv);
                }
            }
            Ty::Arrow(arg, ret) => {
                arg.fv(accu, do_add);
                ret.fv(accu, do_add);
            }
            Ty::Record(rcm) => {
                rcm.values().for_each(|i| i.fv(accu, do_add));
            }
        }
    }

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&Self::In) -> Option<Self::Out>,
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
            Ty::Record(rcm) => {
                rcm.values_mut().for_each(|i| i.apply(f));
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Scheme {
    pub forall: BTreeSet<TyVar>,
    pub ty: Ty,
}

impl Ty {
    /// compute the type scheme
    /// by recording all inner type variables
    pub fn generalize<E>(self, depenv: &E) -> Scheme
    where
        E: Substitutable<In = TyVar>,
    {
        let mut forall = Default::default();
        self.fv(&mut forall, true);
        depenv.fv(&mut forall, false);
        Scheme {
            forall,
            ty: self,
        }
    }
}

impl Scheme {
    pub fn instantiate<C>(&self, outerctx: &mut C) -> Ty
    where
        C: Context,
    {
        let mut t2 = self.ty.clone();
        let m = outerctx.dup_tyvars(self.forall.iter().copied());
        t2.apply(& |i| m.get(i).map(|&j| Ty::Var(j)));
        t2
    }
}
