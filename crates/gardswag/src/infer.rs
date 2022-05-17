use gardswag_syntax as synt;
use gardswag_typesys as tysy;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use gardswag_core::{ty::Context as _, Substitutable, Ty, TyLit, TyVar};
use gardswag_tysy_collect::{Context, TyConstraintGroup as Tcg, TyConstraintGroupKind as Tcgk};

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

fn maybe_new_tyvar(offset: usize, t: Ty, ctx: &mut Context) -> TyVar {
    match t {
        Ty::Var(x) => x,
        _ => {
            let tv = ctx.fresh_tyvar();
            ctx.unify(offset, t, Ty::Var(tv));
            tv
        }
    }
}

fn infer(env: &Env, ctx: &mut Context, expr: &synt::Expr) -> Result<Ty, Error> {
    use synt::ExprKind as Ek;
    match &expr.inner {
        Ek::Let { lhs, rhs, rest } => {
            let lev = ctx.peek_next_tyvar();
            let t1 = infer(env, ctx, rhs)?;
            let lev2 = ctx.peek_next_tyvar();
            let mut env2 = env.clone();
            let t2 = t1.generalize(&env2, lev..lev2);
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
            let tvinp = maybe_new_tyvar(expr.offset, t, ctx);
            let tvout = Ty::Var(ctx.fresh_tyvar());
            ctx.bind(
                expr.offset,
                tvinp,
                Tcg {
                    kind: Some(Tcgk::Record {
                        partial: [(key.inner.to_string(), tvout.clone())]
                            .into_iter()
                            .collect(),
                        update_info: None,
                    }),
                    ..Default::default()
                },
            );
            Ok(tvout)
        }

        Ek::Update { orig, ovrd } => {
            let t_orig = infer(env, ctx, orig)?;
            let t_ovrd = infer(env, ctx, ovrd)?;
            let tvout = ctx.fresh_tyvar();
            let tvorig = maybe_new_tyvar(expr.offset, t_orig, ctx);
            let tvovrd = maybe_new_tyvar(expr.offset, t_ovrd, ctx);
            let tcg_listen = Tcg {
                listeners: [tvout].into_iter().collect(),
                kind: Some(Tcgk::Record {
                    partial: Default::default(),
                    update_info: None,
                }),
                ..Default::default()
            };
            ctx.bind(expr.offset, tvorig, tcg_listen.clone());
            ctx.bind(expr.offset, tvovrd, tcg_listen);
            ctx.bind(
                expr.offset,
                tvout,
                Tcg {
                    kind: Some(Tcgk::Record {
                        partial: Default::default(),
                        update_info: Some((tvorig, tvovrd)),
                    }),
                    ..Default::default()
                },
            );
            Ok(Ty::Var(tvout))
        }

        Ek::FormatString(fsexs) => {
            let env = env.clone();
            for i in fsexs {
                let t = infer(&env, ctx, i)?;
                let tv = maybe_new_tyvar(i.offset, t, ctx);
                ctx.bind(
                    i.offset,
                    tv,
                    Tcg {
                        oneof: [TyLit::Unit, TyLit::Bool, TyLit::Int, TyLit::String]
                            .into_iter()
                            .map(Ty::Literal)
                            .collect(),
                        ..Default::default()
                    },
                );
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
