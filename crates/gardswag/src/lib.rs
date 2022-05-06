use gardswag_syntax as synt;
use gardswag_typesys as tysy;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use tysy::Substitutable as _;

pub type TyVar = usize;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("undefind variable used: {0}")]
    UndefVar(synt::Identifier),

    #[error("unification error: {0}")]
    Unify(#[from] tysy::UnifyError<TyVar>),
}

#[derive(Debug)]
pub struct InferData {
    pub subst: HashMap<TyVar, tysy::Ty<TyVar>>,
    pub t: tysy::Ty<TyVar>,
}

#[derive(Clone)]
pub struct Env {
    pub vars: HashMap<String, tysy::Scheme<TyVar>>,
    pub fresh_tyvars: Rc<RefCell<core::ops::RangeFrom<TyVar>>>,
}

impl tysy::Substitutable for Env {
    type Var = TyVar;

    fn fv(&self) -> BTreeSet<TyVar> {
        self.vars.fv()
    }

    fn apply(&mut self, ctx: &HashMap<TyVar, tysy::Ty<TyVar>>) {
        self.vars.apply(ctx);
    }
}

impl Default for Env {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

impl Env {
    pub fn new() -> Self {
        Self {
            vars: Default::default(),
            fresh_tyvars: Rc::new(RefCell::new(0..)),
        }
    }

    fn fresh_tyvar(&self) -> tysy::Ty<TyVar> {
        tysy::Ty::Var(self.fresh_tyvars.borrow_mut().next().unwrap())
    }

    pub fn infer_block(&self, blk: &synt::Block) -> Result<InferData, Error> {
        let mut env = self.clone();
        let mut ret = InferData {
            subst: Default::default(),
            t: tysy::Ty::Literal(tysy::TyLit::Unit),
        };
        for i in &blk.stmts {
            let InferData { subst, .. } = env.infer(i)?;
            env.apply(&subst);
            ret.subst.extend(subst);
        }
        if let Some(x) = &blk.term {
            let InferData { subst, t } = env.infer(x)?;
            ret.t = t;
            ret.subst.extend(subst);
        }
        Ok(ret)
    }

    pub fn infer(&self, expr: &synt::Expr) -> Result<InferData, Error> {
        use synt::ExprKind as Ek;
        match &expr.inner {
            Ek::Let { lhs, rhs, rest } => {
                let x1 = self.infer(rhs)?;
                let mut env2 = self.clone();
                env2.apply(&x1.subst);
                let t2 = x1.t.generalize(&env2);
                env2.vars.insert(lhs.inner.clone(), t2);
                let x3 = env2.infer_block(rest)?;
                let mut env3 = x1.subst;
                env3.extend(x3.subst);
                Ok(InferData {
                    subst: env3,
                    t: x3.t,
                })
            }
            Ek::Assign { lhs, rhs } => {
                let mut x = self.infer(rhs)?;
                let prev_ty = self
                    .vars
                    .get(&lhs.inner)
                    .ok_or_else(|| Error::UndefVar(lhs.clone()))?;

                // make it possible to assign another polymorphic function
                let mut env2 = self.clone();
                env2.apply(&x.subst);
                let next_ty = x.t.generalize(&env2);

                // TODO: does this work as expected?
                if *prev_ty != next_ty {
                    let mut fresh_tyvars = self.fresh_tyvars.borrow_mut();
                    let prev_ty = prev_ty.instantiate(&mut *fresh_tyvars);
                    let next_ty = next_ty.instantiate(&mut *fresh_tyvars);
                    tysy::unify(&mut x.subst, &prev_ty, &next_ty)?;
                }
                x.t = tysy::Ty::Literal(tysy::TyLit::Unit);
                Ok(x)
            }
            Ek::Block(blk) => self.infer_block(blk),

            Ek::If {
                cond,
                then,
                or_else,
            } => {
                let x_cond = self.infer(cond)?;
                let mut x_then = self.infer_block(then)?;
                let x_else = self.infer_block(or_else)?;
                let mut subst = x_cond.subst;
                subst.extend(x_then.subst);
                subst.extend(x_else.subst);
                tysy::unify(&mut subst, &x_cond.t, &tysy::Ty::Literal(tysy::TyLit::Bool))?;
                tysy::unify(&mut subst, &x_then.t, &x_else.t)?;
                x_then.t.apply(&subst);
                Ok(InferData { subst, t: x_then.t })
            }

            Ek::Lambda { arg, body } => {
                let mut env2 = self.clone();
                let mut tv = self.fresh_tyvar();
                if !arg.inner.is_empty() {
                    env2.vars.insert(
                        arg.inner.clone(),
                        tysy::Scheme {
                            forall: Default::default(),
                            t: tv.clone(),
                        },
                    );
                }
                let x = env2.infer(body)?;
                tv.apply(&x.subst);
                Ok(InferData {
                    subst: x.subst,
                    t: tysy::Ty::Arrow(Box::new(tv), Box::new(x.t)),
                })
            }

            Ek::Call { prim, args } => {
                let mut x_prim = self.infer(prim)?;
                let mut env2 = self.clone();
                env2.apply(&x_prim.subst);
                for arg in args {
                    let tv = self.fresh_tyvar();
                    let InferData {
                        subst: subst_arg,
                        t: t_arg,
                    } = env2.infer(arg)?;
                    env2.apply(&subst_arg);
                    x_prim.t.apply(&subst_arg);
                    x_prim.subst.extend(subst_arg);
                    tysy::unify(
                        &mut x_prim.subst,
                        &x_prim.t,
                        &tysy::Ty::Arrow(Box::new(t_arg), Box::new(tv)),
                    )?;
                }
                Ok(x_prim)
            }

            Ek::Dot { prim, key } => {
                let mut tv = self.fresh_tyvar();
                let mut x = self.infer(prim)?;
                tysy::unify(
                    &mut x.subst,
                    &x.t,
                    &tysy::Ty::Record {
                        m: core::iter::once((key.inner.to_string(), tv.clone())).collect(),
                        partial: true,
                    },
                )?;
                tv.apply(&x.subst);
                x.t = tv;
                Ok(x)
            }

            Ek::Fix(body) => {
                let mut x = self.infer(body)?;
                let mut tv = self.fresh_tyvar();
                tysy::unify(
                    &mut x.subst,
                    &x.t,
                    &tysy::Ty::Arrow(Box::new(tv.clone()), Box::new(tv.clone())),
                )?;
                tv.apply(&x.subst);
                x.t = tv;
                Ok(x)
            }

            Ek::FormatString(fsexs) => {
                let mut env = self.clone();
                let mut ret = InferData {
                    subst: Default::default(),
                    t: tysy::Ty::Literal(tysy::TyLit::String),
                };
                for i in fsexs {
                    let x = self.infer(i)?;
                    env.apply(&x.subst);
                    ret.subst.extend(x.subst);
                }
                Ok(ret)
            }

            Ek::Identifier(id) => {
                if let Some(x) = self.vars.get(&id.inner) {
                    Ok(InferData {
                        subst: Default::default(),
                        t: x.instantiate(&mut *self.fresh_tyvars.borrow_mut()),
                    })
                } else {
                    Err(Error::UndefVar(id.clone()))
                }
            }
            Ek::Integer(_) => Ok(InferData {
                subst: Default::default(),
                t: tysy::Ty::Literal(tysy::TyLit::Int),
            }),
            Ek::PureString(_) => Ok(InferData {
                subst: Default::default(),
                t: tysy::Ty::Literal(tysy::TyLit::String),
            }),
        }
    }
}
