use gardswag_syntax as synt;
use gardswag_typesys as tysy;
use std::collections::{BTreeSet, HashMap};

use tysy::{Substitutable as _, Ty, TyLit, TyVar};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("undefind variable used: {0}")]
    UndefVar(synt::Identifier),

    #[error("unification error: {0}")]
    Unify(#[from] tysy::UnifyError),
}

pub struct Tracker {
    pub fresh_tyvars: core::ops::RangeFrom<TyVar>,
    pub subst: tysy::Context,
}

impl Tracker {
    pub fn fresh_tyvar(&mut self) -> Ty {
        Ty::Var(self.fresh_tyvars.next().unwrap())
    }
}

#[derive(Clone)]
pub struct Env {
    pub vars: HashMap<String, tysy::Scheme>,
}

impl Env {
    /// this function should only be called when this is the only env existing
    pub fn gc<I: Iterator<Item = Ty>>(&self, tracker: &mut Tracker, extra_tys: I) {
        // reduce necessary type vars to minimum
        tracker.subst.self_resolve();

        //self.vars.apply(&tracker.subst);

        // remove all unnecessary type vars
        let mut xfv = self.vars.fv();
        tracker.subst.retain(xfv.clone());

        // reset fresh tyvars counter
        xfv.extend(
            self.vars
                .values()
                .flat_map(|i| &i.forall)
                .map(|(i, _)| *i)
                .chain(extra_tys.flat_map(|i| i.fv())),
        );
        let orig_freetvc = core::mem::replace(
            &mut tracker.fresh_tyvars,
            xfv.iter().last().map(|&i| i + 1).unwrap_or(0)..,
        );
        tracing::debug!(
            "gc: fresh#tv: {:?} -> {:?}",
            orig_freetvc,
            tracker.fresh_tyvars
        );
    }
}

impl tysy::Substitutable for Env {
    fn fv(&self) -> BTreeSet<TyVar> {
        self.vars.fv()
    }

    fn apply(&mut self, ctx: &tysy::Context) {
        self.vars.apply(ctx);
    }
}

impl Env {
    fn update(&mut self, tracker: &Tracker) {
        self.vars.apply(&tracker.subst);
    }
}

pub fn infer_block(env: &Env, tracker: &mut Tracker, blk: &synt::Block) -> Result<Ty, Error> {
    let mut ret = Ty::Literal(TyLit::Unit);
    for i in &blk.stmts {
        let _ = infer(env, tracker, i)?;
    }
    if let Some(x) = &blk.term {
        ret = infer(env, tracker, x)?;
    }
    tracker.subst.self_resolve();
    ret.apply(&tracker.subst);
    Ok(ret)
}

fn infer_inner(env: &Env, tracker: &mut Tracker, expr: &synt::Expr) -> Result<Ty, Error> {
    use synt::ExprKind as Ek;
    match &expr.inner {
        Ek::Let { lhs, rhs, rest } => {
            let t1 = infer(env, tracker, rhs)?;
            let mut env2 = env.clone();
            env2.update(tracker);
            let t2 = t1.generalize(&env2, &tracker.subst);
            env2.vars.insert(lhs.inner.clone(), t2);
            infer_block(&env2, tracker, rest)
        }
        Ek::Assign { lhs, rhs } => {
            let x = infer(env, tracker, rhs)?;
            let prev_ty = env
                .vars
                .get(&lhs.inner)
                .ok_or_else(|| Error::UndefVar(lhs.clone()))?;

            // make it possible to assign another polymorphic function
            let mut env2 = env.clone();
            env2.update(tracker);
            let next_ty = x.generalize(&env2, &tracker.subst);

            // TODO: does this work as expected?
            if *prev_ty != next_ty {
                let prev_ty = prev_ty.instantiate(&mut tracker.subst, &mut tracker.fresh_tyvars);
                let next_ty = next_ty.instantiate(&mut tracker.subst, &mut tracker.fresh_tyvars);
                tracker.subst.unify(&prev_ty, &next_ty)?;
            }
            Ok(Ty::Literal(TyLit::Unit))
        }
        Ek::Block(blk) => infer_block(env, tracker, blk),

        Ek::If {
            cond,
            then,
            or_else,
        } => {
            let x_cond = infer(env, tracker, cond)?;
            let mut x_then = infer_block(env, tracker, then)?;
            let x_else = infer_block(env, tracker, or_else)?;
            tracker.subst.unify(&x_cond, &Ty::Literal(TyLit::Bool))?;
            tracker.subst.unify(&x_then, &x_else)?;
            x_then.apply(&tracker.subst);
            Ok(x_then)
        }

        Ek::Lambda { arg, body } => {
            let mut env2 = env.clone();
            let mut tv = tracker.fresh_tyvar();
            if !arg.inner.is_empty() {
                env2.vars.insert(
                    arg.inner.clone(),
                    tysy::Scheme {
                        forall: Default::default(),
                        t: tv.clone(),
                    },
                );
            }
            let x = infer(&env2, tracker, body)?;
            tv.apply(&tracker.subst);
            Ok(Ty::Arrow(Box::new(tv), Box::new(x)))
        }

        Ek::Call { prim, args } => {
            let mut t_prim = infer(env, tracker, prim)?;
            let mut env2 = env.clone();
            env2.update(tracker);
            for arg in args {
                let tv = tracker.fresh_tyvar();
                let t_arg = infer(&env2, tracker, arg)?;
                t_prim.apply(&tracker.subst);
                env2.update(tracker);
                tracker
                    .subst
                    .unify(&t_prim, &Ty::Arrow(Box::new(t_arg), Box::new(tv.clone())))?;
                t_prim = tv;
                t_prim.apply(&tracker.subst);
            }
            Ok(t_prim)
        }

        Ek::Dot { prim, key } => {
            let t = infer(env, tracker, prim)?;
            let mut tv = tracker.fresh_tyvar();
            tracker.subst.unify(
                &t,
                &Ty::Record {
                    m: core::iter::once((key.inner.to_string(), tv.clone())).collect(),
                    partial: true,
                },
            )?;
            tv.apply(&tracker.subst);
            Ok(tv)
        }

        Ek::Fix(body) => {
            let t = infer(env, tracker, body)?;
            let mut tv = tracker.fresh_tyvar();
            tracker
                .subst
                .unify(&t, &Ty::Arrow(Box::new(tv.clone()), Box::new(tv.clone())))?;
            tv.apply(&tracker.subst);
            Ok(tv)
        }

        Ek::FormatString(fsexs) => {
            let mut env = env.clone();
            for i in fsexs {
                env.update(tracker);
                let _ = infer(&env, tracker, i)?;
            }
            Ok(Ty::Literal(TyLit::String))
        }

        Ek::Record(rcd) => {
            let mut m = HashMap::default();
            let mut env = env.clone();
            for (k, v) in rcd {
                env.update(tracker);
                let t = infer(&env, tracker, v)?;
                m.insert(k.clone(), t);
            }
            Ok(Ty::Record { m, partial: false })
        }

        Ek::Identifier(id) => {
            if let Some(x) = env.vars.get(&id.inner) {
                Ok(x.instantiate(&mut tracker.subst, &mut tracker.fresh_tyvars))
            } else {
                Err(Error::UndefVar(id.clone()))
            }
        }
        Ek::Integer(_) => Ok(Ty::Literal(TyLit::Int)),
        Ek::PureString(_) => Ok(Ty::Literal(TyLit::String)),
    }
}

pub fn infer(env: &Env, tracker: &mut Tracker, expr: &synt::Expr) -> Result<Ty, Error> {
    tracing::debug!("infer {:?}", expr);
    let res = infer_inner(env, tracker, expr);
    tracing::debug!("infer {:?} -> {:?}", expr, res);
    res
}
