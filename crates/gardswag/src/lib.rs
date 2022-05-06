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

pub type InferData = tysy::Ty<TyVar>;

pub struct Tracker {
    pub fresh_tyvars: core::ops::RangeFrom<TyVar>,
    pub subst: HashMap<TyVar, tysy::Ty<TyVar>>,
}

impl Tracker {
    pub fn self_resolve(&mut self) {
        // resolve the subst map as far as possible
        loop {
            let old_subst = self.subst.clone();
            for v in self.subst.values_mut() {
                v.apply(&old_subst);
            }
            if old_subst == self.subst {
                break;
            }
        }
    }
}

#[derive(Clone)]
pub struct Env {
    pub vars: HashMap<String, tysy::Scheme<TyVar>>,
    pub tracker: Rc<RefCell<Tracker>>,
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

impl Env {
    fn fresh_tyvar(&self) -> tysy::Ty<TyVar> {
        tysy::Ty::Var(self.tracker.borrow_mut().fresh_tyvars.next().unwrap())
    }

    fn mkupdate(&self) -> Self {
        let mut x = self.clone();
        x.update();
        x
    }

    fn update(&mut self) {
        let tracker = self.tracker.borrow();
        self.vars.apply(&tracker.subst);
    }

    pub fn infer_block(&self, blk: &synt::Block) -> Result<InferData, Error> {
        let mut ret = tysy::Ty::Literal(tysy::TyLit::Unit);
        for i in &blk.stmts {
            let _ = self.infer(i)?;
        }
        if let Some(x) = &blk.term {
            ret = self.infer(x)?;
        }
        self.tracker.borrow_mut().self_resolve();
        ret.apply(&self.tracker.borrow().subst);
        Ok(ret)
    }

    fn infer_inner(&self, expr: &synt::Expr) -> Result<InferData, Error> {
        use synt::ExprKind as Ek;
        match &expr.inner {
            Ek::Let { lhs, rhs, rest } => {
                let t1 = self.infer(rhs)?;
                let mut env2 = self.mkupdate();
                let t2 = t1.generalize(&env2);
                env2.vars.insert(lhs.inner.clone(), t2);
                env2.infer_block(rest)
            }
            Ek::Assign { lhs, rhs } => {
                let x = self.infer(rhs)?;
                let prev_ty = self
                    .vars
                    .get(&lhs.inner)
                    .ok_or_else(|| Error::UndefVar(lhs.clone()))?;

                // make it possible to assign another polymorphic function
                let env2 = self.mkupdate();
                let next_ty = x.generalize(&env2);

                // TODO: does this work as expected?
                if *prev_ty != next_ty {
                    let mut tracker = self.tracker.borrow_mut();
                    let prev_ty = prev_ty.instantiate(&mut tracker.fresh_tyvars);
                    let next_ty = next_ty.instantiate(&mut tracker.fresh_tyvars);
                    tysy::unify(&mut tracker.subst, &prev_ty, &next_ty)?;
                }
                Ok(tysy::Ty::Literal(tysy::TyLit::Unit))
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
                let mut tracker = self.tracker.borrow_mut();
                tysy::unify(&mut tracker.subst, &x_cond, &tysy::Ty::Literal(tysy::TyLit::Bool))?;
                tysy::unify(&mut tracker.subst, &x_then, &x_else)?;
                x_then.apply(&tracker.subst);
                Ok(x_then)
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
                tv.apply(&self.tracker.borrow().subst);
                Ok(tysy::Ty::Arrow(Box::new(tv), Box::new(x)))
            }

            Ek::Call { prim, args } => {
                let mut t_prim = self.infer(prim)?;
                let mut env2 = self.mkupdate();
                for arg in args {
                    let tv = self.fresh_tyvar();
                    let t_arg = env2.infer(arg)?;
                    t_prim.apply(&self.tracker.borrow().subst);
                    env2.update();
                    tysy::unify(
                        &mut self.tracker.borrow_mut().subst,
                        &t_prim,
                        &tysy::Ty::Arrow(Box::new(t_arg), Box::new(tv.clone())),
                    )?;
                    t_prim = tv;
                    t_prim.apply(&self.tracker.borrow().subst);
                }
                Ok(t_prim)
            }

            Ek::Dot { prim, key } => {
                let t = self.infer(prim)?;
                let mut tv = self.fresh_tyvar();
                tysy::unify(
                    &mut self.tracker.borrow_mut().subst,
                    &t,
                    &tysy::Ty::Record {
                        m: core::iter::once((key.inner.to_string(), tv.clone())).collect(),
                        partial: true,
                    },
                )?;
                tv.apply(&self.tracker.borrow().subst);
                Ok(tv)
            }

            Ek::Fix(body) => {
                let t = self.infer(body)?;
                let mut tv = self.fresh_tyvar();
                tysy::unify(
                    &mut self.tracker.borrow_mut().subst,
                    &t,
                    &tysy::Ty::Arrow(Box::new(tv.clone()), Box::new(tv.clone())),
                )?;
                tv.apply(&self.tracker.borrow().subst);
                Ok(tv)
            }

            Ek::FormatString(fsexs) => {
                let mut env = self.clone();
                for i in fsexs {
                    env.apply(&self.tracker.borrow().subst);
                    let _ = env.infer(i)?;
                }
                Ok(tysy::Ty::Literal(tysy::TyLit::String))
            }

            Ek::Identifier(id) => {
                if let Some(x) = self.vars.get(&id.inner) {
                    Ok(x.instantiate(&mut self.tracker.borrow_mut().fresh_tyvars))
                } else {
                    Err(Error::UndefVar(id.clone()))
                }
            }
            Ek::Integer(_) => Ok(
                tysy::Ty::Literal(tysy::TyLit::Int),
            ),
            Ek::PureString(_) => Ok(
                tysy::Ty::Literal(tysy::TyLit::String),
            ),
        }
    }

    pub fn infer(&self, expr: &synt::Expr) -> Result<InferData, Error> {
        tracing::debug!("infer {:?}", expr);
        let res = self.infer_inner(expr);
        tracing::debug!("infer {:?} -> {:?}", expr, res);
        res
    }
}
