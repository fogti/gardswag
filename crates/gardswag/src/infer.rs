use gardswag_syntax as synt;
use gardswag_typesys as tysy;
use std::collections::{BTreeSet, HashMap};

use tysy::{Context, Substitutable as _, Ty, TyLit, TyVar};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("undefind variable used: {0}")]
    UndefVar(synt::Identifier),

    #[error("unification error: {0}")]
    Unify(#[from] tysy::UnifyError),
}

#[derive(Clone)]
pub struct Env {
    pub vars: HashMap<String, tysy::Scheme>,
}

impl Env {
    /// this function should only be called when this is the only env existing
    pub fn gc<I: Iterator<Item = Ty>>(&self, ctx: &mut Context, extra_tys: I) {
        // reduce necessary type vars to minimum
        ctx.self_resolve();

        //self.vars.apply(ctx);

        // remove all unnecessary type vars
        let mut xfv = self.vars.fv();

        // reset fresh tyvars counter
        xfv.extend(
            self.vars
                .values()
                .flat_map(|i| &i.forall)
                .map(|(i, _)| *i)
                .chain(extra_tys.flat_map(|i| i.fv())),
        );

        ctx.retain(xfv.clone());

        let orig_freetvc = core::mem::replace(
            &mut ctx.fresh_tyvars,
            xfv.iter().last().map(|&i| i + 1).unwrap_or(0)..,
        );
        tracing::debug!("gc: fresh#tv: {:?} -> {:?}", orig_freetvc, ctx.fresh_tyvars);
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
    fn update(&mut self, ctx: &Context) {
        self.vars.apply(ctx);
    }
}

pub fn infer_block(env: &Env, ctx: &mut Context, blk: &synt::Block) -> Result<Ty, Error> {
    let mut ret = Ty::Literal(TyLit::Unit);
    for i in &blk.stmts {
        let _ = infer(env, ctx, i)?;
    }
    if let Some(x) = &blk.term {
        ret = infer(env, ctx, x)?;
    }
    ctx.self_resolve();
    ret.apply(ctx);
    Ok(ret)
}

fn infer_inner(env: &Env, ctx: &mut Context, expr: &synt::Expr) -> Result<Ty, Error> {
    use synt::ExprKind as Ek;
    match &expr.inner {
        Ek::Let { lhs, rhs, rest } => {
            let t1 = infer(env, ctx, rhs)?;
            let mut env2 = env.clone();
            env2.update(ctx);
            let t2 = t1.generalize(&env2, ctx);
            env2.vars.insert(lhs.inner.clone(), t2);
            infer_block(&env2, ctx, rest)
        }
        Ek::Assign { lhs, rhs } => {
            let x = infer(env, ctx, rhs)?;
            let prev_ty = env
                .vars
                .get(&lhs.inner)
                .ok_or_else(|| Error::UndefVar(lhs.clone()))?;

            // make it possible to assign another polymorphic function
            let mut env2 = env.clone();
            env2.update(ctx);
            let next_ty = x.generalize(&env2, ctx);

            // TODO: does this work as expected?
            if *prev_ty != next_ty {
                let prev_ty = prev_ty.instantiate(ctx);
                let next_ty = next_ty.instantiate(ctx);
                ctx.unify(&prev_ty, &next_ty)?;
            }
            Ok(Ty::Literal(TyLit::Unit))
        }
        Ek::Block(blk) => infer_block(env, ctx, blk),

        Ek::If {
            cond,
            then,
            or_else,
        } => {
            let x_cond = infer(env, ctx, cond)?;
            let mut x_then = infer_block(env, ctx, then)?;
            let x_else = infer_block(env, ctx, or_else)?;
            ctx.unify(&x_cond, &Ty::Literal(TyLit::Bool))?;
            ctx.unify(&x_then, &x_else)?;
            x_then.apply(ctx);
            Ok(x_then)
        }

        Ek::Lambda { arg, body } => {
            let mut env2 = env.clone();
            let mut tv = ctx.fresh_tyvar();
            if !arg.inner.is_empty() {
                env2.vars.insert(
                    arg.inner.clone(),
                    tysy::Scheme {
                        forall: Default::default(),
                        t: tv.clone(),
                    },
                );
            }
            let x = infer(&env2, ctx, body)?;
            tv.apply(ctx);
            Ok(Ty::Arrow(Box::new(tv), Box::new(x)))
        }

        Ek::Call { prim, args } => {
            let mut t_prim = infer(env, ctx, prim)?;
            let mut env2 = env.clone();
            env2.update(ctx);
            for arg in args {
                let tv = ctx.fresh_tyvar();
                let t_arg = infer(&env2, ctx, arg)?;
                t_prim.apply(ctx);
                env2.update(ctx);
                ctx.unify(&t_prim, &Ty::Arrow(Box::new(t_arg), Box::new(tv.clone())))?;
                t_prim = tv;
                t_prim.apply(ctx);
            }
            Ok(t_prim)
        }

        Ek::Dot { prim, key } => {
            let t = infer(env, ctx, prim)?;
            let tvinp = ctx.fresh_tyvars.next().unwrap();
            let mut tvout = ctx.fresh_tyvar();
            ctx.bind(
                tvinp,
                tysy::TyConstraintGroup::Constraints(vec![tysy::TyConstraint::PartialRecord {
                    key: key.inner.to_string(),
                    value: tvout.clone(),
                }]),
            )?;
            let tvinp = Ty::Var(tvinp);
            ctx.unify(&t, &tvinp)?;
            tvout.apply(ctx);
            Ok(tvout)
        }

        Ek::Fix(body) => {
            let t = infer(env, ctx, body)?;
            let mut tv = ctx.fresh_tyvar();
            ctx.unify(&t, &Ty::Arrow(Box::new(tv.clone()), Box::new(tv.clone())))?;
            tv.apply(ctx);
            Ok(tv)
        }

        Ek::FormatString(fsexs) => {
            let mut env = env.clone();
            for i in fsexs {
                env.update(ctx);
                let t = infer(&env, ctx, i)?;
                let tv = ctx.fresh_tyvars.next().unwrap();
                ctx.bind(
                    tv,
                    tysy::TyConstraintGroup::Constraints(vec![tysy::TyConstraint::OneOf(
                        [TyLit::Unit, TyLit::Bool, TyLit::Int, TyLit::String]
                            .into_iter()
                            .map(Ty::Literal)
                            .collect(),
                    )]),
                )
                .unwrap();
                ctx.unify(&t, &Ty::Var(tv))?;
            }
            Ok(Ty::Literal(TyLit::String))
        }

        Ek::Record(rcd) => {
            let mut m = HashMap::default();
            let mut env = env.clone();
            for (k, v) in rcd {
                env.update(ctx);
                let t = infer(&env, ctx, v)?;
                m.insert(k.clone(), t);
            }
            Ok(Ty::Record(m))
        }

        Ek::Identifier(id) => {
            if let Some(x) = env.vars.get(&id.inner) {
                Ok(x.instantiate(ctx))
            } else {
                Err(Error::UndefVar(id.clone()))
            }
        }
        Ek::Boolean(_) => Ok(Ty::Literal(TyLit::Bool)),
        Ek::Integer(_) => Ok(Ty::Literal(TyLit::Int)),
        Ek::PureString(_) => Ok(Ty::Literal(TyLit::String)),
    }
}

pub fn infer(env: &Env, ctx: &mut Context, expr: &synt::Expr) -> Result<Ty, Error> {
    tracing::trace!("infer {:?}", expr);
    let res = infer_inner(env, ctx, expr);
    tracing::debug!("infer {:?} -> {:?}", expr, res);
    res
}
