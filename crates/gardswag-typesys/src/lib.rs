use std::cmp;
use std::collections::{BTreeSet, HashMap};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyLit {
    Unit,
    Int,
    String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ty<Var> {
    Literal(TyLit),

    Var(Var),

    Arrow(Box<Ty<Var>>, Box<Ty<Var>>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Scheme<Var> {
    pub forall: BTreeSet<Var>,
    pub t: Ty<Var>,
}

pub trait VarBase:
    Clone + cmp::PartialEq + cmp::Eq + cmp::PartialOrd + cmp::Ord + core::hash::Hash
{
}
impl<T: Clone + cmp::PartialEq + cmp::Eq + cmp::PartialOrd + cmp::Ord + core::hash::Hash> VarBase
    for T
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
        }
    }

    fn apply(&mut self, ctx: &HashMap<Var, Ty<Var>>) {
        match self {
            Ty::Var(tv) => {
                if let Some(x) = ctx.get(tv) {
                    *self = x.clone();
                }
            }
            Ty::Arrow(ref mut arg, ref mut ret) => {
                arg.apply(ctx);
                ret.apply(ctx);
            }
            _ => {}
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

#[derive(Debug)]
pub enum UnifyError<Var> {
    Infinite { v: Var, t: Ty<Var> },
    Override { v: Var, t1: Ty<Var>, t2: Ty<Var> },
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
        return Err(UnifyError::Infinite { v: v.clone(), t: t.clone() });
    }
    use std::collections::hash_map::Entry;
    match ctx.entry(v.clone()) {
        Entry::Occupied(occ) => {
            if occ.get() == t {
                Ok(())
            } else {
                Err(UnifyError::Override {
                    v: v.clone(),
                    t1: occ.get().clone(),
                    t2: t.clone(),
                })
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
    match (a, b) {
        (Ty::Arrow(l1, r1), Ty::Arrow(l2, r2)) => {
            unify(ctx, l1, l2)?;
            let (mut rx1, mut rx2) = (r1.clone(), r2.clone());
            rx1.apply(ctx);
            rx2.apply(ctx);
            unify(ctx, &rx1, &rx2)?;
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

impl<Var: VarBase + From<usize>> Scheme<Var> {
    pub fn instantiate(&self, mut offset: usize) -> Ty<Var> {
        let forall2 = self
            .forall
            .iter()
            .map(|i| {
                let newi = offset;
                offset += 1;
                (i.clone(), Ty::Var(newi.into()))
            })
            .collect();
        let mut t2 = self.t.clone();
        t2.apply(&forall2);
        t2
    }
}

#[cfg(test)]
mod tests {}
