use core::{cmp, fmt};
use std::collections::{BTreeSet, HashMap};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Literal(TyLit),

    Var(TyVar),

    Arrow(Box<Ty>, Box<Ty>),

    Record {
        m: HashMap<String, Ty>,
        partial: bool,
    },
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Literal(lit) => write!(f, "{}", lit),
            Ty::Var(v) => write!(f, "${:?}", v),
            Ty::Arrow(a, b) => write!(f, "({}) -> {}", a, b),
            Ty::Record { m, partial } => {
                write!(f, "{:?}", m)?;
                if *partial {
                    write!(f, "..")?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Context {
    pub m: HashMap<TyVar, Ty>,
}

#[derive(Clone, Debug, Eq)]
pub struct Scheme {
    pub forall: BTreeSet<TyVar>,
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
            Ty::Record { m, .. } => m.values().flat_map(|i| i.fv()).collect(),
        }
    }

    fn apply(&mut self, ctx: &Context) {
        match self {
            Ty::Literal(_) => {}
            Ty::Var(tv) => {
                if let Some(x) = ctx.m.get(tv) {
                    *self = x.clone();
                }
            }
            Ty::Arrow(arg, ret) => {
                arg.apply(ctx);
                ret.apply(ctx);
            }
            Ty::Record { m, .. } => {
                m.values_mut().for_each(|i| i.apply(ctx));
            }
        }
    }
}

impl Substitutable for Context {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.m.values().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, ctx: &Context) {
        self.m.values_mut().for_each(|i| i.apply(ctx))
    }
}

impl Context {
    fn filter(&self, filt: &BTreeSet<TyVar>) -> Self {
        Context {
            m: self
                .m
                .iter()
                .filter(|(k, _)| !filt.contains(k))
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
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

    pub fn retain(&mut self, keep: &BTreeSet<TyVar>) {
        let orig_tvcnt = self.m.len();
        self.m.retain(|k, _| keep.contains(k));
        tracing::debug!("Ctx::retain: #tv: {} -> {}", orig_tvcnt, self.m.len());
    }
}

impl Substitutable for Scheme {
    fn fv(&self) -> BTreeSet<TyVar> {
        let fvt = self.t.fv();
        fvt.difference(&self.forall).cloned().collect()
    }

    fn apply(&mut self, ctx: &Context) {
        self.t.apply(&ctx.filter(&self.forall));
    }
}

impl<V: Substitutable> Substitutable for HashMap<String, V> {
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
}

impl Context {
    fn bind(&mut self, v: TyVar, t: &Ty) -> Result<(), UnifyError> {
        if let Ty::Var(y) = t {
            if &v == y {
                return Ok(());
            }
        }
        if t.fv().contains(&v) {
            return Err(UnifyError::Infinite { v, t: t.clone() });
        }
        use std::collections::hash_map::Entry;
        match self.m.entry(v) {
            Entry::Occupied(occ) => {
                if occ.get() == t {
                    Ok(())
                } else {
                    let present = occ.get().clone();
                    self.unify(&present, t)?;
                    /*Err(UnifyError::Override {
                        v: v.clone(),
                        t1: occ.get().clone(),
                        t2: t.clone(),
                    })*/
                    Ok(())
                }
            }
            Entry::Vacant(y) => {
                y.insert(t.clone());
                Ok(())
            }
        }
    }

    pub fn unify(&mut self, a: &Ty, b: &Ty) -> Result<(), UnifyError> {
        tracing::debug!("unify a={:?}, b={:?} ctx={:?}", a, b, self);
        match (a, b) {
            (Ty::Arrow(l1, r1), Ty::Arrow(l2, r2)) => {
                self.unify(l1, l2)?;
                let (mut rx1, mut rx2) = (r1.clone(), r2.clone());
                rx1.apply(self);
                rx2.apply(self);
                self.unify(&rx1, &rx2)?;
                Ok(())
            }
            (
                Ty::Record {
                    m: rc1,
                    partial: false,
                },
                Ty::Record {
                    m: rc2,
                    partial: false,
                },
            ) if rc1.len() == rc2.len() => {
                for (k, v1) in rc1 {
                    let v2 = rc2.get(k).ok_or_else(|| UnifyError::Mismatch {
                        t1: a.clone(),
                        t2: b.clone(),
                    })?;
                    self.unify(v1, v2)?;
                }
                Ok(())
            }
            (
                Ty::Record {
                    m: rc1,
                    partial: rc1p,
                },
                Ty::Record {
                    m: rc2,
                    partial: rc2p,
                },
            ) if *rc1p || *rc2p => {
                // partial record, only unify intersection
                for (k, v1) in rc1 {
                    if let Some(v2) = rc2.get(k) {
                        self.unify(v1, v2)?;
                    }
                }
                Ok(())
            }
            (Ty::Var(a), t) => self.bind(*a, t),
            (t, Ty::Var(a)) => self.bind(*a, t),
            (Ty::Literal(l), Ty::Literal(r)) if l == r => Ok(()),
            (_, _) => Err(UnifyError::Mismatch {
                t1: a.clone(),
                t2: b.clone(),
            }),
        }
    }
}

impl Scheme {
    pub fn instantiate<I: Iterator<Item = TyVar>>(&self, fresh_vars: &mut I) -> Ty {
        let forall2 = Context {
            m: self
                .forall
                .iter()
                .map(|i| (*i, Ty::Var(fresh_vars.next().unwrap())))
                .collect(),
        };
        let mut t2 = self.t.clone();
        t2.apply(&forall2);
        t2
    }
}

impl Ty {
    pub fn generalize<S: Substitutable>(self, env: &S) -> Scheme {
        Scheme {
            forall: self.fv().difference(&env.fv()).cloned().collect(),
            t: self,
        }
    }
}

#[cfg(test)]
mod tests {}
