use crate::{FinalArgMultiplicity as Fam, FreeVars, Substitutable, Ty, TyVar};
use core::fmt;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize, Serialize)]
#[serde(transparent)]
#[repr(transparent)]
pub struct ArgMultiplicityId(pub(crate) usize);

impl fmt::Debug for ArgMultiplicityId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "$am{}", self.0)
    }
}

impl fmt::Display for ArgMultiplicityId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "$am{}", self.0)
    }
}

use ArgMultiplicityId as ArgMultId;

impl gardswag_subst::AutoImpl for ArgMultId {}

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
    /// type should be an arrow
    Arrow {
        /// multiplicity variable
        multi: ArgMultId,

        /// argument type
        ty_arg: Ty,

        /// return type
        ty_ret: Ty,
    },

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
    fn apply<F: FnMut(&TyVar) -> Option<Ty>>(&mut self, f: &mut F) {
        if let Some(ty) = &mut self.ty {
            ty.apply(f);
        }
        self.oneof.apply(f);
        if let Some(x) = &mut self.kind {
            x.apply(f);
        }
        let mut f2 = move |i: &TyVar| {
            // this is annoyingly fragile
            if let Some(Ty::Var(x)) = f(i) {
                Some(x)
            } else {
                None
            }
        };
        self.listeners.apply(&mut f2);
    }
}

impl FreeVars<ArgMultId> for Tcg {
    fn fv(&self, accu: &mut BTreeSet<ArgMultId>, do_add: bool) {
        if let Some(Tcgk::Arrow { multi, .. }) = &self.kind {
            multi.fv(accu, do_add);
        }
    }
}

impl Substitutable<ArgMultId> for Tcg {
    type Out = ArgMultId;
    fn apply<F: FnMut(&ArgMultId) -> Option<ArgMultId>>(&mut self, f: &mut F) {
        if let Some(Tcgk::Arrow { multi, .. }) = &mut self.kind {
            multi.apply(f);
        }
    }
}

impl FreeVars<TyVar> for Tcgk {
    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        match self {
            Tcgk::Arrow {
                multi: _,
                ty_arg,
                ty_ret,
            } => {
                ty_arg.fv(accu, do_add);
                ty_ret.fv(accu, do_add);
            }
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
    fn apply<F: FnMut(&TyVar) -> Option<Ty>>(&mut self, f: &mut F) {
        match self {
            Tcgk::Arrow {
                multi: _,
                ty_arg,
                ty_ret,
            } => {
                ty_arg.apply(f);
                ty_ret.apply(f);
            }
            Tcgk::Record {
                partial,
                update_info,
            } => {
                partial.apply(f);
                if let Some((a, b)) = update_info {
                    let mut f2 = move |i: &TyVar| {
                        // this is annoyingly fragile
                        if let Some(Ty::Var(x)) = f(i) {
                            Some(x)
                        } else {
                            None
                        }
                    };
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

/// multiplicity of the argument of an arrow.
/// used for inferring multiplicity from usage.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
pub enum ArgMultiplicity {
    Var(ArgMultId),

    // `Erased` / 0 is omiited, because it can be represented using `Sum([])`
    // and is otherwise unnecessary, because `Ty::Arrow0` can be used instead.
    Linear,
    Unrestricted,

    /// used for classic multiple usages with unknown multiplicity
    Sum(Vec<ArgMultiplicity>),

    /// used for pattern matching, if stmts etc.
    Max(Vec<ArgMultiplicity>),

    /// used for lambda invocations
    Prod(Vec<ArgMultiplicity>),
}

impl Default for ArgMultiplicity {
    #[inline]
    fn default() -> Self {
        Self::Sum(Vec::new())
    }
}

impl ArgMultiplicity {
    #[inline]
    pub fn null() -> Self {
        Self::Sum(Vec::new())
    }

    pub fn as_fam(&self) -> Option<Fam> {
        match self {
            Self::Linear => Some(Fam::Linear),
            Self::Unrestricted => Some(Fam::Unrestricted),
            Self::Sum(xs) if xs.is_empty() => Some(Fam::Erased),
            _ => None,
        }
    }

    pub fn resolved(&self, a: Ty, b: Ty) -> Result<Ty, (Ty, Ty)> {
        match self.as_fam() {
            Some(x) => Ok(x.resolved(a, b)),
            None => Err((a, b)),
        }
    }
}

impl From<Fam> for ArgMultiplicity {
    fn from(x: Fam) -> Self {
        match x {
            Fam::Erased => Self::null(),
            Fam::Linear => Self::Linear,
            Fam::Unrestricted => Self::Unrestricted,
        }
    }
}

impl FreeVars<ArgMultId> for ArgMultiplicity {
    fn fv(&self, accu: &mut BTreeSet<ArgMultId>, do_add: bool) {
        match self {
            Self::Var(x) => x.fv(accu, do_add),
            Self::Linear | Self::Unrestricted => {}
            Self::Sum(xs) | Self::Max(xs) | Self::Prod(xs) => xs.fv(accu, do_add),
        }
    }
}

impl Substitutable<ArgMultId> for ArgMultiplicity {
    type Out = ArgMultId;
    fn apply<F: FnMut(&ArgMultId) -> Option<ArgMultId>>(&mut self, f: &mut F) {
        match self {
            Self::Var(x) => x.apply(f),
            Self::Linear | Self::Unrestricted => {}
            Self::Sum(xs) | Self::Max(xs) | Self::Prod(xs) => xs.apply(f),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    Unify(Ty, Ty),
    Bind(TyVar, Tcg),
    BindArgMulti(ArgMultId, ArgMultiplicity),
}

impl FreeVars<TyVar> for Constraint {
    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        match self {
            Self::Unify(a, b) => {
                a.fv(accu, do_add);
                b.fv(accu, do_add);
            }
            Self::Bind(tv, cg) => {
                tv.fv(accu, do_add);
                cg.fv(accu, do_add);
            }
            Self::BindArgMulti(_, _) => {}
        }
    }
}

impl Substitutable<TyVar> for Constraint {
    type Out = TyVar;
    fn apply<F: FnMut(&TyVar) -> Option<TyVar>>(&mut self, f: &mut F) {
        match self {
            Self::Unify(a, b) => {
                let mut f2 = move |i: &TyVar| f(i).map(Ty::Var);
                a.apply(&mut f2);
                b.apply(&mut f2);
            }
            Self::Bind(tv, cg) => {
                if let Some(x) = f(tv) {
                    *tv = x;
                }
                let mut f2 = move |i: &TyVar| f(i).map(Ty::Var);
                cg.apply(&mut f2);
            }
            Self::BindArgMulti(_, _) => {}
        }
    }
}

impl FreeVars<ArgMultId> for Constraint {
    fn fv(&self, accu: &mut BTreeSet<ArgMultId>, do_add: bool) {
        match self {
            Self::Unify(_, _) => {}
            Self::Bind(_, cg) => {
                cg.fv(accu, do_add);
            }
            Self::BindArgMulti(amid, amdat) => {
                amid.fv(accu, do_add);
                amdat.fv(accu, do_add);
            }
        }
    }
}

impl Substitutable<ArgMultId> for Constraint {
    type Out = ArgMultId;
    fn apply<F: FnMut(&ArgMultId) -> Option<ArgMultId>>(&mut self, f: &mut F) {
        match self {
            Self::Unify(_, _) => {}
            Self::Bind(_, cg) => {
                cg.apply(f);
            }
            Self::BindArgMulti(amid, amdat) => {
                amid.apply(f);
                amdat.apply(f);
            }
        }
    }
}

/// type constraints collector
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    fresh_tyvars: core::ops::RangeFrom<usize>,
    fresh_argmulti: core::ops::RangeFrom<usize>,
    pub constraints: Vec<(usize, Constraint)>,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            fresh_tyvars: 0..,
            fresh_argmulti: 0..,
            constraints: Default::default(),
        }
    }
}

impl Context {
    pub fn fresh_tyvar(&mut self) -> TyVar {
        self.fresh_tyvars.next().unwrap()
    }

    pub fn fresh_argmulti(&mut self) -> ArgMultId {
        ArgMultId(self.fresh_argmulti.next().unwrap())
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
        let mut amm = BTreeMap::<ArgMultId, ArgMultId>::new();

        // constraints for tyvars
        let new_constraints: Vec<_> = self
            .constraints
            .iter()
            .filter(|i| {
                let mut tfv = BTreeSet::<TyVar>::new();
                i.1.fv(&mut tfv, true);
                tfv.into_iter().any(|j| ret.contains_key(&j))
            })
            .map(|i| {
                let mut i = i.clone();
                i.1.apply(&mut |j| ret.get(j).copied());
                i.1.apply(&mut |j| {
                    Some(
                        *amm.entry(*j)
                            .or_insert_with(|| ArgMultId(self.fresh_argmulti.next().unwrap())),
                    )
                });
                i
            })
            .collect();

        // constraints for argmultis
        let new_constraints_ams: Vec<_> = self
            .constraints
            .iter()
            .filter(|i| {
                if let Constraint::BindArgMulti(_, _) = &i.1 {
                    let mut afv = BTreeSet::<ArgMultId>::new();
                    i.1.fv(&mut afv, true);
                    afv.into_iter().any(|j| amm.contains_key(&j))
                } else {
                    false
                }
            })
            .map(|i| {
                let mut i = i.clone();
                i.1.apply(&mut |j| amm.get(j).copied());
                i
            })
            .collect();

        // argmultis constraints must come before tyvar constraints
        self.constraints.extend(new_constraints_ams);
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

    pub fn create_argmulti(&mut self, offset: usize, am: ArgMultiplicity) -> ArgMultId {
        let ret = self.fresh_argmulti();
        self.constraints
            .push((offset, Constraint::BindArgMulti(ret, am)));
        ret
    }
}
