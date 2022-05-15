use gardswag_syntax as synt;
use gardswag_typesys as tysy;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use gardswag_core::{ty::Context as _, Substitutable, Ty, TyLit, TyVar};
use gardswag_tysy_collect::Context;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("undefind variable used: {0}")]
    UndefVar(synt::Identifier),
}

#[derive(Clone, Debug)]
pub struct Env {
    pub vars: HashMap<String, tysy::Scheme>,
}

impl Substitutable for Env {
    type In = TyVar;
    type Out = Ty;

    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        self.vars.fv(accu, do_add);
    }

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&TyVar) -> Option<Ty>,
    {
        self.vars.apply(f);
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
    Ok(ret)
}

fn infer(env: &Env, ctx: &mut Context, expr: &synt::Expr) -> Result<Ty, Error> {
    use synt::ExprKind as Ek;
    match &expr.inner {
        Ek::Let { lhs, rhs, rest } => {
            let t1 = infer(env, ctx, rhs)?;
            let mut env2 = env.clone();
            let t2 = t1.generalize(&env2);
            env2.vars.insert(lhs.inner.clone(), t2);
            infer_block(&env2, ctx, rest)
        }
        Ek::Block(blk) => infer_block(env, ctx, blk),

        Ek::If {
            cond,
            then,
            or_else,
        } => {
            let x_cond = infer(env, ctx, cond)?;
            let x_then = infer_block(env, ctx, then)?;
            let x_else = infer_block(env, ctx, or_else)?;
            ctx.unify(expr.offset, x_cond, Ty::Literal(TyLit::Bool));
            ctx.unify(expr.offset, x_then.clone(), x_else);
            Ok(x_then)
        }

        Ek::Lambda { arg, body } => {
            let mut env2 = env.clone();
            let tv = Ty::Var(ctx.fresh_tyvar());
            if !arg.inner.is_empty() {
                env2.vars.insert(
                    arg.inner.clone(),
                    tysy::Scheme {
                        forall: Default::default(),
                        ty: tv.clone(),
                    },
                );
            }
            let x = infer(&env2, ctx, body)?;
            Ok(Ty::Arrow(Box::new(tv), Box::new(x)))
        }

        Ek::Fix { arg, body } => {
            let mut env2 = env.clone();
            let tv = Ty::Var(ctx.fresh_tyvar());
            if !arg.inner.is_empty() {
                env2.vars.insert(
                    arg.inner.clone(),
                    tysy::Scheme {
                        forall: Default::default(),
                        ty: tv.clone(),
                    },
                );
            }
            let x = infer(&env2, ctx, body)?;
            // unify {$tv -> x} & {$tv -> $tv}, inlined
            ctx.unify(expr.offset, x, tv.clone());
            Ok(tv)
        }

        Ek::Call { prim, arg } => {
            let t_prim = infer(env, ctx, prim)?;
            let env2 = env.clone();
            let tv = Ty::Var(ctx.fresh_tyvar());
            let t_arg = infer(&env2, ctx, arg)?;
            ctx.unify(
                expr.offset,
                t_prim,
                Ty::Arrow(Box::new(t_arg), Box::new(tv.clone())),
            );
            Ok(tv)
        }

        Ek::Dot { prim, key } => {
            let t = infer(env, ctx, prim)?;
            let tvinp = ctx.fresh_tyvar();
            let tvout = Ty::Var(ctx.fresh_tyvar());
            ctx.bind(
                expr.offset,
                tvinp,
                tysy::TyConstraintGroup {
                    partial_record: [(key.inner.to_string(), tvout.clone())]
                        .into_iter()
                        .collect(),
                    ..Default::default()
                },
            );
            let tvinp = Ty::Var(tvinp);
            ctx.unify(expr.offset, t, tvinp);
            Ok(tvout)
        }

        Ek::Update { orig, ovrd } => {
            let t_orig = infer(env, ctx, orig)?;
            let t_ovrd = infer(env, ctx, ovrd)?;
            let tvout = ctx.fresh_tyvars.next().unwrap();
            let tvorig = ctx.fresh_tyvars.next().unwrap();
            let tcg_listen = tysy::TyConstraintGroup {
                listeners: [tvout].into_iter().collect(),
                ..Default::default()
            };
            ctx.bind(expr.offset, tvorig, tcg_listen.clone());
            let tvovrd = ctx.fresh_tyvars.next().unwrap();
            ctx.bind(expr.offset, tvovrd, tcg_listen);
            ctx.bind(
                expr.offset,
                tvout,
                tysy::TyConstraintGroup {
                    record_update_info: Some((tvorig, tvovrd)),
                    ..Default::default()
                },
            );
            ctx.unify(expr.offset, t_orig, Ty::Var(tvorig));
            ctx.unify(expr.offset, t_ovrd, Ty::Var(tvovrd));
            let tvout = Ty::Var(tvout);
            Ok(tvout)
        }

        Ek::FormatString(fsexs) => {
            let env = env.clone();
            for i in fsexs {
                let t = infer(&env, ctx, i)?;
                let tv = ctx.fresh_tyvars.next().unwrap();
                ctx.bind(
                    i.offset,
                    tv,
                    tysy::TyConstraintGroup {
                        oneof: [TyLit::Unit, TyLit::Bool, TyLit::Int, TyLit::String]
                            .into_iter()
                            .map(Ty::Literal)
                            .collect(),
                        ..Default::default()
                    },
                );
                ctx.unify(i.offset, t, Ty::Var(tv));
            }
            Ok(Ty::Literal(TyLit::String))
        }

        Ek::Record(rcd) => {
            let mut m = BTreeMap::default();
            let env = env.clone();
            for (k, v) in rcd {
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
