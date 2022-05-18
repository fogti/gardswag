use gardswag_syntax as synt;
use gardswag_typesys::constraint::{TyGroup as Tcg, TyGroupKind as Tcgk};
use gardswag_typesys::{self as tysy, Substitutable, Ty, TyLit, TyVar};
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("undefind variable used: {0}")]
    UndefVar(synt::Identifier),

    #[error("case {0:?}")]
    Pattern(synt::Offsetted<PatternError>),
}

#[derive(Debug, thiserror::Error)]
pub enum PatternError {
    #[error("unreachable pattern: {0:?}")]
    Unreachable(synt::Pattern),

    #[error("unreachable pattern: {0}")]
    Unreachable2(String),

    #[error("pattern kind mismatch: expected {expected}, got {got:?}")]
    KindMismatchSingle {
        expected: String,
        got: synt::Pattern,
    },

    #[error("pattern kind mismatch: lhs {lhs}, rhs {rhs}")]
    KindMismatchMerge { lhs: String, rhs: String },

    #[error("pattern record {record} has invalid/mismatching key '{key}'")]
    RecordInvalidKey { record: String, key: String },

    #[error("pattern contains identifier '{ident}' multiple times: @{offset1}, @{offset2}")]
    IdentAmbiguous {
        ident: String,
        offset1: usize,
        offset2: usize,
    },
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
    blk: &synt::Block,
) -> Result<Ty, Error> {
    let mut ret = Ty::Literal(TyLit::Unit);
    for i in &blk.stmts {
        let _ = infer(env, ctx, i)?;
    }
    if let Some(x) = &blk.term {
        ret = infer(env, ctx, x)?;
    }
    Ok(ret)
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

#[derive(Clone, Debug)]
struct PatNode<'a> {
    offset: usize,
    kind: Option<PatNodeKind<'a>>,
    wildcard_witn: bool,
}

#[derive(Clone, Debug)]
enum PatNodeKind<'a> {
    TaggedUnion(BTreeMap<&'a str, PatNode<'a>>),
    Record(BTreeMap<&'a str, PatNode<'a>>),
}

impl<'a> PatNode<'a> {
    fn push(&mut self, oth: Self) -> Result<(), PatternError> {
        if self.wildcard_witn {
            return Err(PatternError::Unreachable2(format!("{:?}", oth)));
        }
        self.wildcard_witn = oth.wildcard_witn;
        match (self.kind.as_mut(), oth.kind) {
            (Some(lhs), Some(rhs)) => lhs.push(rhs)?,
            (_, None) => {}
            (None, _) => unreachable!(),
        }
        Ok(())
    }
}

impl<'a> PatNodeKind<'a> {
    fn push(&mut self, oth: Self) -> Result<(), PatternError> {
        use std::collections::btree_map::Entry;
        match (self, oth) {
            (PatNodeKind::TaggedUnion(tu1), PatNodeKind::TaggedUnion(tu2)) => {
                for (key, value) in tu2 {
                    match tu1.entry(key) {
                        Entry::Occupied(occ) => {
                            occ.into_mut().push(value)?;
                        }
                        Entry::Vacant(vac) => {
                            vac.insert(value);
                        }
                    }
                }
            }
            (PatNodeKind::Record(rc1), PatNodeKind::Record(rc2)) if rc1.len() == rc2.len() => {
                for (key, value) in rc2 {
                    match rc1.entry(key) {
                        Entry::Occupied(occ) => {
                            occ.into_mut().push(value)?;
                        }
                        Entry::Vacant(_) => {
                            return Err(PatternError::RecordInvalidKey {
                                record: format!("{:?}", rc1),
                                key: key.to_string(),
                            });
                        }
                    }
                }
            }
            (a, b) => {
                return Err(PatternError::KindMismatchMerge {
                    lhs: format!("{:?}", a),
                    rhs: format!("{:?}", b),
                })
            }
        }
        Ok(())
    }
}

fn patterns2nodetree<'a, I: Iterator<Item = (usize, &'a synt::Pattern)>>(
    mut pats: I,
) -> Result<PatNode<'a>, Error> {
    use core::iter::once;
    use synt::{Offsetted, Pattern as Pat};
    use PatNodeKind as Pnk;

    // build case tree, first detect type
    let (main_offset, mut ret) = match pats.next().unwrap() {
        (offset, Pat::Identifier(_)) => {
            if let Some((offset, i)) = pats.next() {
                return Err(Error::Pattern(Offsetted {
                    offset,
                    inner: PatternError::Unreachable(i.clone()),
                }));
            }
            return Ok(PatNode {
                offset,
                kind: None,
                wildcard_witn: true,
            });
        }
        (offset, Pat::Tagged { key, value }) => (
            offset,
            PatNodeKind::TaggedUnion(
                once((&*key.inner, patterns2nodetree(once((offset, &**value)))?)).collect(),
            ),
        ),
        (offset, Pat::Record(rcd)) => (
            offset,
            PatNodeKind::Record({
                let mut rcpat = BTreeMap::default();
                for (key, value) in &rcd.inner {
                    rcpat.insert(&**key, patterns2nodetree(once((offset, &*value)))?);
                }
                rcpat
            }),
        ),
    };

    let mut wildcard_witn = false;
    for (offset, i) in &mut pats {
        use std::collections::btree_map::Entry;
        match (i, &mut ret) {
            (Pat::Identifier(_), _) => {
                wildcard_witn = true;
                break;
            }
            (Pat::Tagged { key, value }, Pnk::TaggedUnion(tupat)) => {
                let subpnt = patterns2nodetree(once((offset, &**value)))?;
                match tupat.entry(&key.inner) {
                    Entry::Vacant(vac) => {
                        vac.insert(subpnt);
                    }
                    Entry::Occupied(occ) => {
                        occ.into_mut()
                            .push(subpnt)
                            .map_err(|inner| Error::Pattern(Offsetted { offset, inner }))?;
                    }
                }
            }
            (Pat::Record(rcinp), Pnk::Record(rcpat)) if rcinp.inner.len() == rcpat.len() => {
                let rcinpk = patterns2nodetree(once((offset, i)))?.kind;
                ret.push(rcinpk.unwrap())
                    .map_err(|inner| Error::Pattern(Offsetted { offset, inner }))?;
            }
            (got, expected) => {
                return Err(Error::Pattern(Offsetted {
                    offset,
                    inner: PatternError::KindMismatchSingle {
                        expected: format!("{:?}", expected),
                        got: got.clone(),
                    },
                }));
            }
        }
    }
    if let Some((offset, i)) = pats.next() {
        Err(Error::Pattern(Offsetted {
            offset,
            inner: PatternError::Unreachable(i.clone()),
        }))
    } else {
        Ok(PatNode {
            offset: main_offset,
            kind: Some(ret),
            wildcard_witn,
        })
    }
}

fn infer_pat(
    env: &Env,
    ctx: &mut tysy::CollectContext,
    inp: Ty,
    PatNode {
        offset,
        kind,
        wildcard_witn,
    }: PatNode<'_>,
) -> Result<Ty, Error> {
    Ok(if let Some(kind) = kind {
        #[derive(Clone)]
        enum MaybeWldc {
            Wildcard(TyVar),
            Normal(Ty),
        }
        let inptv = if wildcard_witn {
            MaybeWldc::Wildcard(maybe_new_tyvar(offset, inp, ctx))
        } else {
            MaybeWldc::Normal(inp)
        };
        use PatNodeKind as Pnk;
        match kind {
            Pnk::TaggedUnion(tud) => {
                let pre = tud
                    .into_iter()
                    .map(|(key, i)| {
                        let ttv = Ty::Var(ctx.fresh_tyvar());
                        Ok((key.to_string(), infer_pat(env, ctx, ttv, i)?))
                    })
                    .collect::<Result<_, _>>()?;
                match inptv.clone() {
                    MaybeWldc::Wildcard(inptv) => ctx.bind(
                        offset,
                        inptv,
                        Tcg {
                            kind: Some(Tcgk::TaggedUnion { partial: pre }),
                            ..Tcg::default()
                        },
                    ),
                    MaybeWldc::Normal(inp) => ctx.unify(offset, inp, Ty::TaggedUnion(pre)),
                }
            }
            Pnk::Record(rcd) => {
                let pre = rcd
                    .into_iter()
                    .map(|(key, i)| {
                        let ttv = Ty::Var(ctx.fresh_tyvar());
                        Ok((key.to_string(), infer_pat(env, ctx, ttv, i)?))
                    })
                    .collect::<Result<_, _>>()?;
                match inptv.clone() {
                    MaybeWldc::Wildcard(inptv) => ctx.bind(
                        offset,
                        inptv,
                        Tcg {
                            kind: Some(Tcgk::Record {
                                partial: pre,
                                update_info: None,
                            }),
                            ..Tcg::default()
                        },
                    ),
                    MaybeWldc::Normal(inp) => ctx.unify(offset, inp, Ty::Record(pre)),
                }
            }
        }
        match inptv {
            MaybeWldc::Normal(inp) => inp,
            MaybeWldc::Wildcard(inptv) => Ty::Var(inptv),
        }
    } else {
        // wildcard
        inp
    })
}

fn infer_case_pat(
    env: &mut BTreeMap<String, (usize, Ty)>,
    ctx: &mut tysy::CollectContext,
    pat: &synt::Pattern,
) -> Result<Ty, PatternError> {
    use synt::Pattern;
    let ttv = ctx.fresh_tyvar();
    match pat {
        Pattern::Identifier(x) => {
            use std::collections::btree_map::Entry;
            match env.entry(x.inner.to_string()) {
                Entry::Vacant(vac) => {
                    vac.insert((x.offset, Ty::Var(ttv)));
                }
                Entry::Occupied(occ) => {
                    return Err(PatternError::IdentAmbiguous {
                        ident: x.inner.to_string(),
                        offset1: occ.get().0,
                        offset2: x.offset,
                    });
                }
            }
        }
        Pattern::Tagged { key, value } => {
            let t_value = infer_case_pat(env, ctx, &*value)?;
            ctx.bind(
                key.offset,
                ttv,
                Tcg {
                    kind: Some(Tcgk::TaggedUnion {
                        partial: core::iter::once((key.inner.to_string(), t_value)).collect(),
                    }),
                    ..Tcg::default()
                },
            );
        }
        Pattern::Record(rcd) => {
            let mut rcm = BTreeMap::default();
            for (key, value) in &rcd.inner {
                let t_value = infer_case_pat(env, ctx, value)?;
                rcm.insert(key.to_string(), t_value);
            }
            ctx.bind(
                rcd.offset,
                ttv,
                Tcg {
                    kind: Some(Tcgk::Record {
                        partial: rcm,
                        update_info: None,
                    }),
                    ..Tcg::default()
                },
            );
        }
    }
    Ok(Ty::Var(ttv))
}

fn infer_match(
    env: &Env,
    ctx: &mut tysy::CollectContext,
    inp: &synt::Expr,
    cases: &[synt::Case],
) -> Result<Ty, Error> {
    let inp_t = infer(env, ctx, inp)?;

    // build case tree, and detect type
    let patnode = patterns2nodetree(cases.iter().map(|i| (i.body.offset, &i.pat)))?;

    // inspect normalized pattern tree
    let inp_t = infer_pat(env, ctx, inp_t, patnode)?;

    // inspect bodies
    let resty = ctx.fresh_tyvar();
    for synt::Case { pat, body } in cases {
        let mut env2 = env.clone();
        let mut tmpenv = Default::default();
        let inp_t2 = infer_case_pat(&mut tmpenv, ctx, pat).map_err(|inner| {
            Error::Pattern(synt::Offsetted {
                offset: body.offset,
                inner,
            })
        })?;
        ctx.unify(body.offset, inp_t.clone(), inp_t2);
        for (key, (_, ty)) in tmpenv {
            env2.vars.insert(
                key,
                tysy::Scheme {
                    forall: Default::default(),
                    ty,
                },
            );
        }
        let tmpty = infer(&env2, ctx, body)?;
        ctx.unify(body.offset, Ty::Var(resty), tmpty);
    }
    Ok(Ty::Var(resty))
}

fn infer(env: &Env, ctx: &mut tysy::CollectContext, expr: &synt::Expr) -> Result<Ty, Error> {
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
            if !arg.is_empty() {
                env2.vars.insert(
                    arg.clone(),
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
            if !arg.is_empty() {
                env2.vars.insert(
                    arg.clone(),
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

        Ek::Record(rcd) => {
            let mut m = BTreeMap::default();
            let env = env.clone();
            for (k, v) in rcd {
                let t = infer(&env, ctx, v)?;
                m.insert(k.clone(), t);
            }
            Ok(Ty::Record(m))
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

        Ek::Tagged { key, value } => {
            let tinp = infer(env, ctx, value)?;
            let tvout = ctx.fresh_tyvar();
            ctx.bind(
                expr.offset,
                tvout,
                Tcg {
                    kind: Some(Tcgk::TaggedUnion {
                        partial: [(key.to_string(), tinp)].into_iter().collect(),
                    }),
                    ..Default::default()
                },
            );
            Ok(Ty::Var(tvout))
        }
        Ek::Match { inp, cases } => infer_match(env, ctx, &*inp, &cases[..]),

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
        Ek::Boolean(_) => Ok(Ty::Literal(TyLit::Bool)),
        Ek::Integer(_) => Ok(Ty::Literal(TyLit::Int)),
        Ek::PureString(_) => Ok(Ty::Literal(TyLit::String)),
    }
}
