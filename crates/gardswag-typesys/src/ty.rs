use crate::{FreeVars, Substitutable, Symbol};
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

// de Bruijn index as type variable
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize, Serialize)]
pub struct DistanceTyVar(pub usize);

impl gardswag_subst::AutoImpl for DistanceTyVar {}

impl fmt::Display for DistanceTyVar {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "^{}", self.0)
    }
}

#[derive(Clone, PartialEq, Eq, Deserialize, Serialize)]
pub enum Ty {
    Literal(TyLit),

    Var(TyVar),
    DistanceVar(DistanceTyVar),

    Arrow {
        arg_multi: FinalArgMultiplicity,
        arg: Box<Ty>,
        ret: Box<Ty>,
    },

    /// recursive type fixpoint operator
    Fix(Box<Ty>),

    /// sender end of channels
    ChanSend(Box<Ty>),

    /// receiver end of channels
    ChanRecv(Box<Ty>),

    Record(BTreeMap<Symbol, Ty>),

    TaggedUnion(BTreeMap<Symbol, Ty>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum FinalArgMultiplicity {
    /// argument is discarded / erased
    Erased,
    /// argument is used exactly once
    Linear,
    /// unrestricted usage of argument
    Unrestricted,
}

impl fmt::Display for FinalArgMultiplicity {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Erased => '0',
                Self::Linear => '1',
                Self::Unrestricted => '*',
            }
        )
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Literal(lit) => write!(f, "{}", lit),
            Ty::Var(v) => write!(f, "${}", v),
            Ty::DistanceVar(v) => write!(f, "{}", v),
            Ty::Arrow {
                arg_multi,
                arg,
                ret,
            } => {
                write!(f, "{}", arg_multi)?;
                if matches!(&**arg, Ty::Arrow { .. }) {
                    write!(f, "({})", arg)
                } else {
                    write!(f, "{}", arg)
                }?;
                write!(f, " -> {}", ret)
            }
            Ty::Fix(x) => {
                write!(f, "μ(")?;
                <Ty as fmt::Display>::fmt(x, f)?;
                write!(f, ")")
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

impl FreeVars<TyVar> for Ty {
    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        let mut xs = vec![self];
        while let Some(x) = xs.pop() {
            match x {
                Ty::Literal(_) | Ty::DistanceVar(_) => {}
                Ty::Var(tv) => {
                    tv.fv(accu, do_add);
                }
                Ty::Arrow { arg, ret, .. } => {
                    xs.push(&*arg);
                    xs.push(&*ret);
                }
                Ty::Fix(x) => {
                    xs.push(&*x);
                }
                Ty::ChanSend(x) | Ty::ChanRecv(x) => xs.push(&*x),
                Ty::Record(rcm) => {
                    xs.extend(rcm.values());
                }
                Ty::TaggedUnion(rcm) => {
                    xs.extend(rcm.values());
                }
            }
        }
    }
}

impl FreeVars<DistanceTyVar> for Ty {
    fn fv(&self, accu: &mut BTreeSet<DistanceTyVar>, do_add: bool) {
        let mut xs = vec![self];
        while let Some(x) = xs.pop() {
            match x {
                Ty::Literal(_) | Ty::Var(_) => {}
                Ty::DistanceVar(tv) => {
                    tv.fv(accu, do_add);
                }
                Ty::Arrow { arg, ret, .. } => {
                    xs.push(&*arg);
                    xs.push(&*ret);
                }
                Ty::Fix(x) => {
                    xs.push(&*x);
                }
                Ty::ChanSend(x) | Ty::ChanRecv(x) => xs.push(&*x),
                Ty::Record(rcm) => {
                    xs.extend(rcm.values());
                }
                Ty::TaggedUnion(rcm) => {
                    xs.extend(rcm.values());
                }
            }
        }
    }
}

impl Substitutable<TyVar> for Ty {
    type Out = Ty;
    fn apply<F: FnMut(&TyVar) -> Option<Ty>>(&mut self, f: &mut F) {
        match self {
            Ty::Literal(_) | Ty::DistanceVar(_) => {}
            Ty::Var(ref tv) => {
                if let Some(x) = f(tv) {
                    *self = x;
                }
            }
            Ty::Arrow { arg, ret, .. } => {
                arg.apply(f);
                ret.apply(f);
            }
            Ty::Fix(x) => {
                x.apply(f);
            }
            Ty::ChanSend(x) | Ty::ChanRecv(x) => x.apply(f),
            Ty::Record(rcm) => {
                for i in rcm.values_mut() {
                    i.apply(f);
                }
            }
            Ty::TaggedUnion(rcm) => {
                for i in rcm.values_mut() {
                    i.apply(f);
                }
            }
        }
    }
}

impl Ty {
    fn apply_fixpoint(&mut self, shiftval: usize, trg: &Ty) {
        match self {
            Ty::Literal(_) | Ty::Var(_) => {}
            Ty::DistanceVar(DistanceTyVar(tv)) => {
                use core::cmp::Ordering as Ordr;
                let tv: usize = *tv;
                match tv.cmp(&shiftval) {
                    Ordr::Less => {}
                    Ordr::Equal => *self = Ty::Fix(Box::new(trg.clone())),
                    Ordr::Greater => panic!(
                        "unexpanded type-level fixpoint variable encountered: {}",
                        DistanceTyVar(tv)
                    ),
                }
            }
            Ty::Arrow { arg, ret, .. } => {
                arg.apply_fixpoint(shiftval, trg);
                ret.apply_fixpoint(shiftval, trg);
            }
            Ty::Fix(x) => {
                x.apply_fixpoint(shiftval + 1, trg);
            }
            Ty::ChanSend(x) | Ty::ChanRecv(x) => x.apply_fixpoint(shiftval, trg),
            Ty::Record(rcm) => {
                for i in rcm.values_mut() {
                    i.apply_fixpoint(shiftval, trg);
                }
            }
            Ty::TaggedUnion(rcm) => {
                for i in rcm.values_mut() {
                    i.apply_fixpoint(shiftval, trg);
                }
            }
        }
    }

    /// this function expects the inner content of `Ty::Fix(inner)` as its `self` argument.
    pub fn unfold_fixpoint(&self) -> Ty {
        let mut s2 = self.clone();
        s2.apply_fixpoint(0, self);
        s2
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
        E: FreeVars<TyVar>,
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
        t2.apply(&mut |i| m.get(i).map(|&j| Ty::Var(j)));
        tracing::trace!("instantiate res {:?}", t2);
        t2
    }
}

impl FreeVars<TyVar> for Scheme {
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

impl Substitutable<TyVar> for Scheme {
    type Out = Ty;
    fn apply<F: FnMut(&TyVar) -> Option<Ty>>(&mut self, f: &mut F) {
        self.ty.apply(&mut |i| {
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
