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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty<Var> {
    Literal(TyLit),

    Var(Var),

    Arrow(Box<Ty<Var>>, Box<Ty<Var>>),

    Record {
        m: HashMap<String, Ty<Var>>,
        partial: bool,
    },
}

impl<Var: fmt::Debug> fmt::Display for Ty<Var> {
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scheme<Var> {
    pub forall: BTreeSet<Var>,
    pub t: Ty<Var>,
}

pub trait VarBase:
    Clone + core::fmt::Debug + cmp::PartialEq + cmp::Eq + cmp::PartialOrd + cmp::Ord + core::hash::Hash
{
}
impl<
        T: Clone
            + core::fmt::Debug
            + cmp::PartialEq
            + cmp::Eq
            + cmp::PartialOrd
            + cmp::Ord
            + core::hash::Hash,
    > VarBase for T
{
}

pub trait Substitutable {
    type Var: VarBase;

    // generate list of all free variables
    fn fv(&self) -> BTreeSet<Self::Var>;

    // apply substitution
    fn apply(&mut self, ctx: &HashMap<Self::Var, Ty<Self::Var>>);
}

impl<Var: VarBase> Substitutable for Ty<Var> {
    type Var = Var;

    fn fv(&self) -> BTreeSet<Var> {
        match self {
            Ty::Literal(_) => Default::default(),
            Ty::Var(tv) => core::iter::once(tv.clone()).collect(),
            Ty::Arrow(arg, ret) => arg.fv().union(&ret.fv()).cloned().collect(),
            Ty::Record { m, .. } => m.values().flat_map(|i| i.fv()).collect(),
        }
    }

    fn apply(&mut self, ctx: &HashMap<Var, Ty<Var>>) {
        match self {
            Ty::Literal(_) => {}
            Ty::Var(tv) => {
                if let Some(x) = ctx.get(tv) {
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

impl<Var: VarBase> Substitutable for Scheme<Var> {
    type Var = Var;

    fn fv(&self) -> BTreeSet<Var> {
        let fvt = self.t.fv();
        fvt.difference(&self.forall).cloned().collect()
    }

    fn apply(&mut self, ctx: &HashMap<Var, Ty<Var>>) {
        let filtctx = ctx
            .iter()
            .filter(|(k, _)| !self.forall.contains(k))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        self.t.apply(&filtctx);
    }
}

impl<V: Substitutable> Substitutable for HashMap<String, V> {
    type Var = V::Var;

    fn fv(&self) -> BTreeSet<V::Var> {
        self.values().flat_map(|i| i.fv()).collect()
    }

    fn apply(&mut self, ctx: &HashMap<V::Var, Ty<V::Var>>) {
        self.values_mut().for_each(|i| i.apply(ctx));
    }
}

#[derive(Debug, thiserror::Error)]
pub enum UnifyError<Var> {
    #[error("infinite type in {v:?} = {t:?}")]
    Infinite { v: Var, t: Ty<Var> },
    #[error("subtitution of {v:?} = {t1:?} overridden with {t2:?}")]
    Override { v: Var, t1: Ty<Var>, t2: Ty<Var> },
    #[error("unification of {t1:?} = {t2:?} failed")]
    Mismatch { t1: Ty<Var>, t2: Ty<Var> },
}

fn bind<Var: VarBase>(
    ctx: &mut HashMap<Var, Ty<Var>>,
    v: &Var,
    t: &Ty<Var>,
) -> Result<(), UnifyError<Var>> {
    if let Ty::Var(y) = t {
        if v == y {
            return Ok(());
        }
    }
    if t.fv().contains(v) {
        return Err(UnifyError::Infinite {
            v: v.clone(),
            t: t.clone(),
        });
    }
    use std::collections::hash_map::Entry;
    match ctx.entry(v.clone()) {
        Entry::Occupied(occ) => {
            if occ.get() == t {
                Ok(())
            } else {
                let present = occ.get().clone();
                unify(ctx, &present, t)?;
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

pub fn unify<Var: VarBase>(
    ctx: &mut HashMap<Var, Ty<Var>>,
    a: &Ty<Var>,
    b: &Ty<Var>,
) -> Result<(), UnifyError<Var>> {
    tracing::debug!("unify a={:?}, b={:?} ctx={:?}", a, b, ctx);
    match (a, b) {
        (Ty::Arrow(l1, r1), Ty::Arrow(l2, r2)) => {
            unify(ctx, l1, l2)?;
            let (mut rx1, mut rx2) = (r1.clone(), r2.clone());
            rx1.apply(ctx);
            rx2.apply(ctx);
            unify(ctx, &rx1, &rx2)?;
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
                unify(ctx, v1, v2)?;
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
                    unify(ctx, v1, v2)?;
                }
            }
            Ok(())
        }
        (Ty::Var(a), t) => bind(ctx, a, t),
        (t, Ty::Var(a)) => bind(ctx, a, t),
        (Ty::Literal(l), Ty::Literal(r)) if l == r => Ok(()),
        (_, _) => Err(UnifyError::Mismatch {
            t1: a.clone(),
            t2: b.clone(),
        }),
    }
}

impl<Var: VarBase> Scheme<Var> {
    pub fn instantiate<I: Iterator<Item = Var>>(&self, fresh_vars: &mut I) -> Ty<Var> {
        let forall2 = self
            .forall
            .iter()
            .map(|i| (i.clone(), Ty::Var(fresh_vars.next().unwrap())))
            .collect();
        let mut t2 = self.t.clone();
        t2.apply(&forall2);
        t2
    }
}

impl<Var: VarBase> Ty<Var> {
    pub fn generalize<S: Substitutable<Var = Var>>(self, env: &S) -> Scheme<Var> {
        Scheme {
            forall: self.fv().difference(&env.fv()).cloned().collect(),
            t: self,
        }
    }
}

#[cfg(test)]
mod tests {}
