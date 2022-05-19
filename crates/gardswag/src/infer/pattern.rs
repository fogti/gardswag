use core::iter::once;
use gardswag_syntax::{self as synt, Case, Expr, Offsetted, Pattern as Pat};
use gardswag_typesys::constraint::{TyGroup as Tcg, TyGroupKind as Tcgk};
use gardswag_typesys::{self as tysy, CollectContext, Ty, TyLit, TyVar};
use std::{cell::RefCell, collections::BTreeMap, rc::Rc};

use super::{infer, maybe_new_tyvar_opt, Env, Error};

#[derive(Debug, thiserror::Error)]
pub enum PatternError {
    #[error("unreachable pattern: {0:?}")]
    Unreachable(Pat),

    #[error("unreachable pattern: {0}")]
    Unreachable2(String),

    #[error("pattern kind mismatch: expected {expected}, got {got:?}")]
    KindMismatchSingle { expected: String, got: Pat },

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

type ICaseVars<'a> = BTreeMap<&'a str, (usize, Rc<RefCell<Option<Ty>>>)>;

#[derive(Clone, Debug)]
struct ICase<'a> {
    vars: ICaseVars<'a>,
    pat: &'a Pat,
    body: &'a Expr,
}

#[derive(Clone, Debug)]
struct PatNode<'a> {
    offset: usize,
    kind: Option<PatNodeKind<'a>>,
    wildcard_witn: Option<Rc<RefCell<Option<Ty>>>>,
}

#[derive(Clone, Debug)]
enum PatNodeKind<'a> {
    TaggedUnion(BTreeMap<&'a str, PatNode<'a>>),
    Record(BTreeMap<&'a str, PatNode<'a>>),
    Unit,
}

use PatNodeKind as Pnk;

impl<'a> PatNode<'a> {
    fn push(&mut self, oth: Self) -> Result<(), PatternError> {
        if self.wildcard_witn.is_some() {
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
            (PatNodeKind::Unit, PatNodeKind::Unit) => {}
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

fn pattern2node<'a>(
    vars: &mut ICaseVars<'a>,
    offset: usize,
    pat: &'a Pat,
) -> Result<PatNode<'a>, Error> {
    let kind = match pat {
        Pat::Identifier(x) => {
            use std::collections::btree_map::Entry;
            return match vars.entry(&*x.inner) {
                Entry::Vacant(vac) => {
                    let t_x = Rc::new(RefCell::new(None));
                    vac.insert((x.offset, Rc::clone(&t_x)));
                    Ok(PatNode {
                        offset,
                        kind: None,
                        wildcard_witn: Some(t_x),
                    })
                }
                Entry::Occupied(occ) => Err(Error::Pattern(Offsetted {
                    offset,
                    inner: PatternError::IdentAmbiguous {
                        ident: x.inner.to_string(),
                        offset1: occ.get().0,
                        offset2: x.offset,
                    },
                })),
            };
        }
        Pat::Tagged { key, value } => PatNodeKind::TaggedUnion(
            once((&*key.inner, pattern2node(vars, offset, &**value)?)).collect(),
        ),
        Pat::Record(rcd) => PatNodeKind::Record({
            let mut rcpat = BTreeMap::default();
            for (key, value) in &rcd.inner {
                rcpat.insert(&**key, pattern2node(vars, offset, &*value)?);
            }
            rcpat
        }),
        Pat::Unit => PatNodeKind::Unit,
    };
    Ok(PatNode {
        offset,
        kind: Some(kind),
        wildcard_witn: None,
    })
}

fn cases2nodetree<'a>(cases: &mut [ICase<'a>]) -> Result<PatNode<'a>, Error> {
    let mut cases = cases.iter_mut();

    // build case tree, first detect type
    let (main_offset, mut ret) = {
        let icase = cases.next().unwrap();
        let tmp = pattern2node(&mut icase.vars, icase.body.offset, icase.pat)?;
        if let Some(kind) = tmp.kind {
            assert!(tmp.wildcard_witn.is_none());
            (tmp.offset, kind)
        } else {
            return if let Some(ICase { body, pat, .. }) = cases.next() {
                Err(Error::Pattern(Offsetted {
                    offset: body.offset,
                    inner: PatternError::Unreachable(pat.clone()),
                }))
            } else {
                Ok(tmp)
            };
        }
    };

    let mut wildcard_witn = None;
    for ICase { vars, body, pat } in &mut cases {
        use std::collections::btree_map::Entry;
        let offset = body.offset;
        let pat = &**pat;
        match (pat, &mut ret) {
            (_, Pnk::Unit) => {
                return Err(Error::Pattern(Offsetted {
                    offset,
                    inner: PatternError::Unreachable(pat.clone()),
                }));
            }
            (Pat::Identifier(x), _) => match vars.entry(&x.inner) {
                Entry::Vacant(vac) => {
                    let t_x = Rc::new(RefCell::new(None));
                    vac.insert((x.offset, Rc::clone(&t_x)));
                    wildcard_witn = Some(t_x);
                    break;
                }
                Entry::Occupied(occ) => {
                    return Err(Error::Pattern(Offsetted {
                        offset,
                        inner: PatternError::IdentAmbiguous {
                            ident: x.inner.to_string(),
                            offset1: occ.get().0,
                            offset2: x.offset,
                        },
                    }));
                }
            },
            (Pat::Tagged { key, value }, Pnk::TaggedUnion(tupat)) => {
                let subpnt = pattern2node(vars, offset, &**value)?;
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
                let rcinpk = pattern2node(vars, offset, pat)?.kind;
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
    if let Some(ICase { body, pat, .. }) = cases.next() {
        Err(Error::Pattern(Offsetted {
            offset: body.offset,
            inner: PatternError::Unreachable(pat.clone()),
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
    ctx: &mut CollectContext,
    inp: Option<Ty>,
    PatNode {
        offset,
        kind,
        wildcard_witn,
    }: PatNode<'_>,
) -> Result<Ty, Error> {
    let ret = if let Some(kind) = kind {
        #[derive(Clone)]
        enum MaybeWldc {
            Wildcard(TyVar),
            Normal(Ty),
        }
        let already_known_ty = matches!(kind, Pnk::Unit);
        let inptv = if already_known_ty {
            inp.map(MaybeWldc::Normal)
        } else if wildcard_witn.is_some() {
            Some(MaybeWldc::Wildcard(maybe_new_tyvar_opt(offset, inp, ctx)))
        } else {
            Some(MaybeWldc::Normal(
                inp.unwrap_or_else(|| Ty::Var(ctx.fresh_tyvar())),
            ))
        };
        match kind {
            Pnk::TaggedUnion(tud) => {
                let pre = tud
                    .into_iter()
                    .map(|(key, i)| Ok((key.to_string(), infer_pat(env, ctx, None, i)?)))
                    .collect::<Result<_, _>>()?;
                match inptv.unwrap() {
                    MaybeWldc::Wildcard(inptv) => {
                        ctx.bind(
                            offset,
                            inptv,
                            Tcg {
                                kind: Some(Tcgk::TaggedUnion { partial: pre }),
                                ..Tcg::default()
                            },
                        );
                        Ty::Var(inptv)
                    }
                    MaybeWldc::Normal(inp) => {
                        ctx.unify(offset, inp.clone(), Ty::TaggedUnion(pre));
                        inp
                    }
                }
            }
            Pnk::Record(rcd) => {
                let pre = rcd
                    .into_iter()
                    .map(|(key, i)| Ok((key.to_string(), infer_pat(env, ctx, None, i)?)))
                    .collect::<Result<_, _>>()?;
                match inptv.unwrap() {
                    MaybeWldc::Wildcard(inptv) => {
                        ctx.bind(
                            offset,
                            inptv,
                            Tcg {
                                kind: Some(Tcgk::Record {
                                    partial: pre,
                                    update_info: None,
                                }),
                                ..Tcg::default()
                            },
                        );
                        Ty::Var(inptv)
                    }
                    MaybeWldc::Normal(inp) => {
                        ctx.unify(offset, inp.clone(), Ty::Record(pre));
                        inp
                    }
                }
            }
            Pnk::Unit => {
                if let Some(inptv) = inptv {
                    ctx.unify(
                        offset,
                        match inptv {
                            MaybeWldc::Wildcard(inptv) => Ty::Var(inptv),
                            MaybeWldc::Normal(inp) => inp,
                        },
                        Ty::Literal(TyLit::Unit),
                    );
                }
                Ty::Literal(TyLit::Unit)
            }
        }
    } else {
        // wildcard
        inp.unwrap_or_else(|| Ty::Var(ctx.fresh_tyvar()))
    };
    if let Some(x) = wildcard_witn {
        let mut xm = x.borrow_mut();
        assert_eq!(*xm, None);
        *xm = Some(ret.clone());
    }
    Ok(ret)
}

pub fn infer_match(
    env: &Env,
    ctx: &mut CollectContext,
    inp: &synt::Expr,
    cases: &[Case],
) -> Result<Ty, Error> {
    let inp_t = infer(env, ctx, inp)?;

    // build annotatable case list
    let mut cases: Vec<_> = cases
        .iter()
        .map(|i| ICase {
            vars: Default::default(),
            pat: &i.pat,
            body: &i.body,
        })
        .collect();

    // build case tree
    let patnode = cases2nodetree(&mut cases[..])?;

    // inspect normalized pattern tree
    let _ = infer_pat(env, ctx, Some(inp_t), patnode)?;

    // inspect bodies
    let resty = ctx.fresh_tyvar();
    for ICase { vars, body, pat: _ } in cases {
        let mut env2 = env.clone();
        for (key, (_, mut ty)) in vars {
            let ty: &mut Option<Ty> = RefCell::get_mut(Rc::get_mut(&mut ty).unwrap());
            env2.vars.insert(
                key.to_string(),
                tysy::Scheme {
                    forall: Default::default(),
                    ty: ty.take().unwrap(),
                },
            );
        }
        let tmpty = infer(&env2, ctx, body)?;
        ctx.unify(body.offset, Ty::Var(resty), tmpty);
    }
    Ok(Ty::Var(resty))
}
