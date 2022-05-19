use gardswag_syntax as synt;
use gardswag_typesys::constraint::{TyGroup as Tcg, TyGroupKind as Tcgk};
use gardswag_typesys::{self as tysy, Substitutable, Ty, TyLit, TyVar};
use std::collections::{BTreeMap, BTreeSet, HashMap};

mod pattern;
use self::pattern::{infer_match, PatternError};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("undefind variable used: {0}")]
    UndefVar(synt::Identifier),

    #[error("case {0:?}")]
    Pattern(synt::Offsetted<PatternError>),
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

pub fn infer_block(
    env: &Env,
    ctx: &mut tysy::CollectContext,
    super_offset: usize,
    blk: &synt::Block,
    res_ty: Option<Ty>,
) -> Result<Ty, Error> {
    for i in &blk.stmts {
        let _ = infer(env, ctx, i, None)?;
    }
    if let Some(x) = &blk.term {
        infer(env, ctx, x, res_ty)
    } else {
        if let Some(x) = res_ty {
            ctx.unify(super_offset, x, Ty::Literal(TyLit::Unit));
        }
        Ok(Ty::Literal(TyLit::Unit))
    }
}

fn maybe_new_tyvar(offset: usize, t: Ty, ctx: &mut tysy::CollectContext) -> TyVar {
    match t {
        Ty::Var(x) => x,
        _ => {
            let tv = ctx.fresh_tyvar();
            ctx.unify(offset, t, Ty::Var(tv));
            tv
        }
    }
}

fn maybe_new_tyvar_opt(offset: usize, t: Option<Ty>, ctx: &mut tysy::CollectContext) -> TyVar {
    match t {
        Some(t) => maybe_new_tyvar(offset, t, ctx),
        None => ctx.fresh_tyvar(),
    }
}

fn infer(
    env: &Env,
    ctx: &mut tysy::CollectContext,
    expr: &synt::Expr,
    mut res_ty: Option<Ty>,
) -> Result<Ty, Error> {
    use synt::ExprKind as Ek;
    let ret = match &expr.inner {
        Ek::Let { lhs, rhs, rest } => {
            let lev = ctx.peek_next_tyvar();
            let t1 = infer(env, ctx, rhs, None)?;
            let lev2 = ctx.peek_next_tyvar();
            let mut env2 = env.clone();
            let t2 = t1.generalize(&env2, lev..lev2);
            env2.vars.insert(lhs.inner.clone(), t2);
            infer_block(&env2, ctx, expr.offset, rest, None)
        }
        Ek::Block(blk) => infer_block(env, ctx, expr.offset, blk, None),

        Ek::If {
            cond,
            then,
            or_else,
        } => {
            let _ = infer(env, ctx, cond, Some(Ty::Literal(TyLit::Bool)))?;
            let x_then = infer_block(env, ctx, expr.offset, then, res_ty.take())?;
            let _ = infer_block(env, ctx, expr.offset, or_else, Some(x_then.clone()))?;
            Ok(x_then)
        }

        Ek::Lambda { arg, body } => {
            let mut env2 = env.clone();
            let tv = Ty::Var(ctx.fresh_tyvar());
            if !arg.is_empty() {
                env2.vars.insert(
                    arg.clone(),
                    tysy::Scheme {
                        forall: Default::default(),
                        ty: tv.clone(),
                    },
                );
            }
            let x = infer(&env2, ctx, body, None)?;
            Ok(Ty::Arrow(Box::new(tv), Box::new(x)))
        }

        Ek::Fix { arg, body } => {
            let mut env2 = env.clone();
            let tv = Ty::Var(maybe_new_tyvar_opt(expr.offset, res_ty.take(), ctx));
            if !arg.is_empty() {
                env2.vars.insert(
                    arg.clone(),
                    tysy::Scheme {
                        forall: Default::default(),
                        ty: tv.clone(),
                    },
                );
            }
            // unify {$tv -> x} & {$tv -> $tv}, inlined
            let _ = infer(&env2, ctx, body, Some(tv.clone()))?;
            Ok(tv)
        }

        Ek::Call { prim, arg } => {
            // special-casing here is done in order to avoid some unnecessary
            // tyvar allocations which otherwise clutter up cg listings
            Ok(if let Ek::Tagger { key } = &prim.inner {
                // optimized by 2x unfolding
                let t_arg = infer(env, ctx, arg, None)?;
                let tvout = maybe_new_tyvar_opt(prim.offset, res_ty.take(), ctx);
                ctx.bind(
                    prim.offset,
                    tvout,
                    Tcg {
                        kind: Some(Tcgk::TaggedUnion {
                            partial: [(key.to_string(), t_arg)].into_iter().collect(),
                        }),
                        ..Default::default()
                    },
                );
                Ty::Var(tvout)
            } else {
                let t_prim = infer(env, ctx, prim, None)?;
                let t_arg = infer(env, ctx, arg, None)?;
                if let Ty::Arrow(tp_arg, tp_ret) = t_prim {
                    // optimized by 1x unfolding
                    ctx.unify(expr.offset, *tp_arg, t_arg);
                    *tp_ret
                } else {
                    let tvout = maybe_new_tyvar_opt(expr.offset, res_ty.take(), ctx);
                    ctx.unify(
                        expr.offset,
                        t_prim,
                        Ty::Arrow(Box::new(t_arg), Box::new(Ty::Var(tvout))),
                    );
                    Ty::Var(tvout)
                }
            })
        }

        Ek::Record(rcd) => {
            let mut m = BTreeMap::default();
            for (k, v) in rcd {
                let t = infer(env, ctx, v, None)?;
                m.insert(k.clone(), t);
            }
            Ok(Ty::Record(m))
        }

        Ek::Dot { prim, key } => {
            let t = infer(env, ctx, prim, None)?;
            let tvinp = maybe_new_tyvar(expr.offset, t, ctx);
            let tvout = Ty::Var(maybe_new_tyvar_opt(expr.offset, res_ty.take(), ctx));
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
            let t_orig = infer(env, ctx, orig, None)?;
            let t_ovrd = infer(env, ctx, ovrd, None)?;
            let tvout = maybe_new_tyvar_opt(expr.offset, res_ty.take(), ctx);
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

        Ek::Tagger { key } => {
            // .<tag> :: 't -> any.partial{<tag>: 't}
            let tvinp = ctx.fresh_tyvar();
            let tvout = ctx.fresh_tyvar();
            ctx.bind(
                expr.offset,
                tvout,
                Tcg {
                    kind: Some(Tcgk::TaggedUnion {
                        partial: [(key.to_string(), Ty::Var(tvinp))].into_iter().collect(),
                    }),
                    ..Default::default()
                },
            );
            Ok(Ty::Arrow(
                Box::new(Ty::Var(tvinp)),
                Box::new(Ty::Var(tvout)),
            ))
        }
        Ek::Match { inp, cases } => infer_match(env, ctx, &*inp, &cases[..]),

        Ek::FormatString(fsexs) => {
            let env = env.clone();
            for i in fsexs {
                let t = infer(&env, ctx, i, None)?;
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

        Ek::Identifier(id) => {
            if let Some(x) = env.vars.get(id) {
                Ok(x.instantiate(ctx))
            } else {
                Err(Error::UndefVar(synt::Offsetted {
                    offset: expr.offset,
                    inner: id.clone(),
                }))
            }
        }
        Ek::Unit => Ok(Ty::Literal(TyLit::Unit)),
        Ek::Boolean(_) => Ok(Ty::Literal(TyLit::Bool)),
        Ek::Integer(_) => Ok(Ty::Literal(TyLit::Int)),
        Ek::PureString(_) => Ok(Ty::Literal(TyLit::String)),
    };
    let ret = ret?;
    tracing::trace!("infer @{}:{} -> {}", expr.offset, expr.inner.typ(), ret);
    if let Some(x) = res_ty {
        ctx.unify(expr.offset, ret.clone(), x);
    }
    Ok(ret)
}