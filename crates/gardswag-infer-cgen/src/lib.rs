#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

use core::cell::RefCell;
use gardswag_syntax::{self as synt, Annot, Symbol};
use gardswag_typesys::constraint::{TyGroup as Tcg, TyGroupKind as Tcgk};
use gardswag_typesys::{
    self as tysy, ArgMultiplicity as ArgMult, FreeVars, Substitutable, Ty, TyLit, TyVar,
};
use gardswag_varstack::VarStack;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

mod pattern;
use self::pattern::{infer_match, PatternError};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("undefind variable used: {0:?}")]
    UndefVar(synt::Identifier<()>),

    #[error("case {0:?}")]
    Pattern(synt::Annot<PatternError>),
}

type IdentMeta = Rc<RefCell<(Vec<ArgMult>, usize)>>;
pub type Env<'s> = &'s VarStack<'s, Symbol, (tysy::Scheme, IdentMeta)>;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct InferExtra {
    pub ty: Ty,
    pub ident_multi: usize,
}

impl FreeVars<TyVar> for InferExtra {
    #[inline]
    fn fv(&self, accu: &mut BTreeSet<TyVar>, do_add: bool) {
        self.ty.fv(accu, do_add);
    }
}

impl Substitutable<TyVar> for InferExtra {
    type Out = Ty;
    #[inline]
    fn apply<F: FnMut(&TyVar) -> Option<Ty>>(&mut self, f: &mut F) {
        self.ty.apply(f);
    }
}

pub fn infer_block(
    env: Env<'_>,
    ctx: &mut tysy::CollectContext,
    super_offset: usize,
    blk: &synt::Block<()>,
    res_ty: Option<Ty>,
) -> Result<synt::Block<InferExtra>, Error> {
    let stmts: Vec<_> = blk
        .stmts
        .iter()
        .map(|i| infer(env, ctx, i, None))
        .collect::<Result<_, _>>()?;
    let term = if let Some(x) = &blk.term {
        Some(Box::new(infer(env, ctx, x, res_ty)?))
    } else {
        if let Some(x) = res_ty {
            ctx.unify(super_offset, x, Ty::Literal(TyLit::Unit));
        }
        None
    };
    Ok(synt::Block { stmts, term })
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

fn maybe_new_argmulti(
    offset: usize,
    a: ArgMult,
    ctx: &mut tysy::CollectContext,
) -> gardswag_typesys::ArgMultiplicityId {
    match a {
        ArgMult::Var(x) => x,
        _ => ctx.create_argmulti(offset, a),
    }
}

fn infer(
    env: Env<'_>,
    ctx: &mut tysy::CollectContext,
    expr: &synt::Expr<()>,
    mut res_ty: Option<Ty>,
) -> Result<synt::Expr<InferExtra>, Error> {
    use synt::ExprKind as Ek;
    let ret = match &expr.inner {
        Ek::Let { lhs, rhs, rest } => {
            let lev = ctx.peek_next_tyvar();
            let rhs = infer(env, ctx, rhs, None)?;
            let lev2 = ctx.peek_next_tyvar();
            let t2 = rhs.extra.ty.clone().generalize(env, lev..lev2);
            let vs = VarStack {
                parent: Some(env),
                name: lhs.inner,
                value: (t2, Rc::new(RefCell::new((vec![ArgMult::null()], 0)))),
            };
            let rest = infer_block(&vs, ctx, expr.offset, rest, None)?;
            let extra = InferExtra {
                ty: rest
                    .term
                    .as_ref()
                    .map(|i| i.extra.ty.clone())
                    .unwrap_or(Ty::Literal(TyLit::Unit)),
                ident_multi: vs.value.1.take().1,
            };
            Ok(Annot {
                offset: expr.offset,
                extra,
                inner: Ek::Let {
                    lhs: lhs.clone(),
                    rhs: Box::new(rhs),
                    rest,
                },
            })
        }
        Ek::Block(blk) => {
            let blk = infer_block(env, ctx, expr.offset, blk, None)?;
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra {
                    ty: blk
                        .term
                        .as_ref()
                        .map(|i| i.extra.ty.clone())
                        .unwrap_or(Ty::Literal(TyLit::Unit)),
                    ident_multi: 0,
                },
                inner: Ek::Block(blk),
            })
        }

        Ek::If {
            cond,
            then,
            or_else,
        } => {
            let cond = infer(env, ctx, cond, Some(Ty::Literal(TyLit::Bool)))?;
            for (_, i) in env.iter() {
                let mut im = i.1.borrow_mut();
                let l = im.0.last().unwrap().clone();
                im.0.push(l);
            }
            let then = infer_block(env, ctx, expr.offset, then, res_ty.take())?;
            let t_then = then
                .term
                .as_ref()
                .map(|i| i.extra.ty.clone())
                .unwrap_or(Ty::Literal(TyLit::Unit));
            for (_, i) in env.iter() {
                let mut im = i.1.borrow_mut();
                let l = im.0[im.0.len() - 2].clone();
                im.0.push(l);
            }
            let or_else = infer_block(env, ctx, expr.offset, or_else, Some(t_then.clone()))?;
            for (_, i) in env.iter() {
                let mut im = i.1.borrow_mut();
                let l = im.0.pop().unwrap();
                let l2 = im.0.pop().unwrap();
                *im.0.last_mut().unwrap() = if l != l2 {
                    ArgMult::Max(vec![l, l2])
                } else {
                    l
                };
            }
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra {
                    ty: t_then,
                    ident_multi: 0,
                },
                inner: Ek::If {
                    cond: Box::new(cond),
                    then,
                    or_else,
                },
            })
        }

        Ek::Lambda { arg, body } => {
            let tv = Ty::Var(ctx.fresh_tyvar());
            let env2 = VarStack {
                parent: Some(env),
                name: arg.inner,
                value: (
                    tysy::Scheme {
                        forall: Default::default(),
                        ty: tv.clone(),
                    },
                    Rc::new(RefCell::new((vec![ArgMult::null()], 0))),
                ),
            };
            let body: synt::Expr<InferExtra> = infer(
                if arg.inner.is_empty() { env } else { &env2 },
                ctx,
                body,
                None,
            )?;
            let (mut ident_argm, ident_multi) = env2.value.1.take();
            let ident_argm = ident_argm.pop().unwrap();
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra {
                    ty: match ident_argm.as_fam() {
                        Some(arg_multi) => Ty::Arrow {
                            arg_multi,
                            arg: Box::new(tv),
                            ret: Box::new(body.extra.ty.clone()),
                        },
                        None => {
                            let tv2 = maybe_new_tyvar_opt(expr.offset, res_ty.take(), ctx);
                            let argm = maybe_new_argmulti(expr.offset, ident_argm, ctx);
                            ctx.bind(
                                expr.offset,
                                tv2,
                                Tcg {
                                    kind: Some(Tcgk::Arrow {
                                        ty_arg: tv,
                                        ty_ret: body.extra.ty.clone(),
                                        multi: argm,
                                    }),
                                    ..Default::default()
                                },
                            );
                            Ty::Var(tv2)
                        }
                    },
                    ident_multi,
                },
                inner: Ek::<InferExtra>::Lambda {
                    arg: arg.clone(),
                    body: Box::new(body),
                },
            })
        }

        Ek::Fix { arg, body } => {
            let tv = Ty::Var(maybe_new_tyvar_opt(expr.offset, res_ty.take(), ctx));
            let env2 = VarStack {
                parent: Some(env),
                name: arg.inner,
                value: (
                    tysy::Scheme {
                        forall: Default::default(),
                        ty: tv.clone(),
                    },
                    Rc::new(RefCell::new((vec![ArgMult::null()], 0))),
                ),
            };
            // unify {$tv -> x} & {$tv -> $tv}, inlined
            let body = infer(
                if arg.inner.is_empty() { env } else { &env2 },
                ctx,
                body,
                Some(tv.clone()),
            )?;
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra {
                    ty: tv,
                    ident_multi: env2.value.1.take().1,
                },
                inner: Ek::Fix {
                    arg: arg.clone(),
                    body: Box::new(body),
                },
            })
        }

        Ek::Call { prim, arg } => {
            // special-casing here is done in order to avoid some unnecessary
            // tyvar allocations which otherwise clutter up cg listings
            let (ty, inner) = {
                let prim = infer(env, ctx, prim, None)?;
                for (_, i) in env.iter() {
                    let mut im = i.1.borrow_mut();
                    let l = im.0.last().unwrap().clone();
                    im.0.push(l);
                }
                let arg = infer(env, ctx, arg, None)?;
                let (argmult, ty) = if let Ty::Arrow {
                    arg_multi,
                    arg: tp_arg,
                    ret: tp_ret,
                } = &prim.extra.ty
                {
                    // optimized by 1x unfolding
                    ctx.unify(expr.offset, (**tp_arg).clone(), arg.extra.ty.clone());
                    ((*arg_multi).into(), (**tp_ret).clone())
                } else {
                    let tvout = maybe_new_tyvar_opt(expr.offset, res_ty.take(), ctx);
                    let tva = maybe_new_tyvar(expr.offset, prim.extra.ty.clone(), ctx);
                    let argm = ctx.fresh_argmulti();
                    ctx.bind(
                        expr.offset,
                        tva,
                        Tcg {
                            kind: Some(Tcgk::Arrow {
                                multi: argm,
                                ty_arg: arg.extra.ty.clone(),
                                ty_ret: Ty::Var(tvout),
                            }),
                            ..Default::default()
                        },
                    );
                    (ArgMult::Var(argm), Ty::Var(tvout))
                };
                for (_, i) in env.iter() {
                    let mut im = i.1.borrow_mut();
                    let l = im.0.pop().unwrap();
                    let lm = im.0.last_mut().unwrap();
                    if l != *lm {
                        // variable was accessed
                        *lm = ArgMult::Prod(vec![l, argmult.clone()]);
                        lm.normalize();
                    }
                }
                (
                    ty,
                    Ek::Call {
                        prim: Box::new(prim),
                        arg: Box::new(arg),
                    },
                )
            };
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra { ty, ident_multi: 0 },
                inner,
            })
        }

        Ek::Record(rcd) => {
            let rcd2 = rcd
                .iter()
                .map(|(k, v)| infer(env, ctx, v, None).map(|v| (*k, v)))
                .collect::<Result<BTreeMap<_, _>, _>>()?;
            let ty = Ty::Record(rcd2.iter().map(|(k, v)| (*k, v.extra.ty.clone())).collect());
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra { ty, ident_multi: 0 },
                inner: Ek::Record(rcd2),
            })
        }

        Ek::Dot { prim, key } => {
            let prim = infer(env, ctx, prim, None)?;
            let tvinp = maybe_new_tyvar(expr.offset, prim.extra.ty.clone(), ctx);
            let tvout = Ty::Var(maybe_new_tyvar_opt(expr.offset, res_ty.take(), ctx));
            ctx.bind(
                expr.offset,
                tvinp,
                Tcg {
                    kind: Some(Tcgk::Record {
                        partial: [(key.inner, tvout.clone())].into_iter().collect(),
                        update_info: None,
                    }),
                    ..Default::default()
                },
            );
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra {
                    ty: tvout,
                    ident_multi: 0,
                },
                inner: Ek::Dot {
                    prim: Box::new(prim),
                    key: key.clone(),
                },
            })
        }

        Ek::Update { orig, ovrd } => {
            let orig = infer(env, ctx, orig, None)?;
            let ovrd = infer(env, ctx, ovrd, None)?;
            let tvout = maybe_new_tyvar_opt(expr.offset, res_ty.take(), ctx);
            let tvorig = maybe_new_tyvar(expr.offset, orig.extra.ty.clone(), ctx);
            let tvovrd = maybe_new_tyvar(expr.offset, ovrd.extra.ty.clone(), ctx);
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
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra {
                    ty: Ty::Var(tvout),
                    ident_multi: 0,
                },
                inner: Ek::Update {
                    orig: Box::new(orig),
                    ovrd: Box::new(ovrd),
                },
            })
        }

        Ek::Tagger(key) => {
            // .<tag> :: 't -> any.partial{<tag>: 't}
            let tvinp = ctx.fresh_tyvar();
            let tvout = ctx.fresh_tyvar();
            let key = *key;
            ctx.bind(
                expr.offset,
                tvout,
                Tcg {
                    kind: Some(Tcgk::TaggedUnion {
                        partial: [(key, Ty::Var(tvinp))].into_iter().collect(),
                    }),
                    ..Default::default()
                },
            );
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra {
                    ty: Ty::Arrow {
                        arg_multi: tysy::FinalArgMultiplicity::Linear,
                        arg: Box::new(Ty::Var(tvinp)),
                        ret: Box::new(Ty::Var(tvout)),
                    },
                    ident_multi: 0,
                },
                inner: Ek::Tagger(key),
            })
        }
        Ek::Match { inp, cases } => infer_match(env, ctx, expr.offset, inp, &cases[..]),

        Ek::FormatString(fsexs) => {
            let mut fsexs2 = Vec::with_capacity(fsexs.len());
            for i in fsexs {
                let j = infer(env, ctx, i, None)?;
                let tv = maybe_new_tyvar(j.offset, j.extra.ty.clone(), ctx);
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
                fsexs2.push(j);
            }
            Ok(Annot {
                offset: expr.offset,
                extra: InferExtra {
                    ty: Ty::Literal(TyLit::String),
                    ident_multi: 0,
                },
                inner: Ek::FormatString(fsexs2),
            })
        }

        Ek::Identifier(id) => {
            if let Some((x, cnt)) = env.find(id) {
                let mut cntm = cnt.borrow_mut();
                cntm.1 += 1;
                let cntm0lm = cntm.0.last_mut().unwrap();
                *cntm0lm = match core::mem::replace(cntm0lm, ArgMult::Unrestricted) {
                    // 0 + 1 = 1
                    ArgMult::Sum(xs) if xs.is_empty() => ArgMult::Linear,
                    // 1 + (1 | ω) = ω
                    ArgMult::Linear | ArgMult::Unrestricted => ArgMult::Unrestricted,
                    y => {
                        let mut tmp = ArgMult::Sum(vec![y, ArgMult::Linear]);
                        tmp.normalize();
                        tmp
                    }
                };
                Ok(Annot {
                    offset: expr.offset,
                    extra: InferExtra {
                        ty: x.instantiate(ctx),
                        ident_multi: 0,
                    },
                    inner: Ek::Identifier(*id),
                })
            } else {
                Err(Error::UndefVar(synt::Annot {
                    offset: expr.offset,
                    inner: *id,
                    extra: (),
                }))
            }
        }
        Ek::Unit => Ok(Annot {
            offset: expr.offset,
            extra: InferExtra {
                ty: Ty::Literal(TyLit::Unit),
                ident_multi: 0,
            },
            inner: Ek::Unit,
        }),
        Ek::Boolean(b) => Ok(Annot {
            offset: expr.offset,
            extra: InferExtra {
                ty: Ty::Literal(TyLit::Bool),
                ident_multi: 0,
            },
            inner: Ek::Boolean(*b),
        }),
        Ek::Integer(x) => Ok(Annot {
            offset: expr.offset,
            extra: InferExtra {
                ty: Ty::Literal(TyLit::Int),
                ident_multi: 0,
            },
            inner: Ek::Integer(*x),
        }),
        Ek::PureString(x) => Ok(Annot {
            offset: expr.offset,
            extra: InferExtra {
                ty: Ty::Literal(TyLit::String),
                ident_multi: 0,
            },
            inner: Ek::PureString(x.clone()),
        }),
    };
    let ret = ret?;
    tracing::trace!("@{}:{} -> {:?}", expr.offset, expr.inner.typ(), ret);
    if let Some(x) = res_ty {
        ctx.unify(expr.offset, ret.extra.ty.clone(), x);
    }
    Ok(ret)
}
