use std::collections::{BTreeSet, HashMap};
use gardswag_typesys as tysy;
use gardswag_syntax as synt;

pub type TyVar = usize;

#[derive(Debug, thiserror::Error)]
pub struct Error {
    #[error("undefind variable used: {0}")]
    UndefVar(synt::Identifier),

    #[error("unification error: {0}")]
    Unify(#[from] tysy::UnifyError<TyVar>),
}

pub struct InferData {
    pub subst: tysy::HashMap<TyVar, tysy::Ty<TyVar>>,
    pub t: tysy::Ty<TyVar>,
}

pub struct Env {
    pub vars: HashMap<String, tysy::Scheme<TyVar>>,
}

impl tysy::Substitutable for Env {
    type Var = TyVar;

    fn highest_used(&self) -> Option<TyVar> {
        self.vars.highest_used()
    }

    fn fv(&self) -> BTreeSet<TyVar> {
        self.vars.fv()
    }

    fn apply(&mut self, ctx: &HashMap<TyVar, tysy::Ty<TyVar>>) {
        self.vars.apply(ctx);
    }
}

impl Env {
fn infer_block(&self, blk: &synt::Block) -> Result<InferData, Error> {
}

pub fn infer(&self, expr: &synt::Expr) -> Result<InferData, Error> {
    use synt::ExprKind as Ek;
    match expr.kind {
        Ek::Let {
            lhs,
            rhs,
            rest
        } => {
            let x1 = self.infer(rhs)?;
            let mut env2 = self.clone();
            env2.apply(&x1.subst);
            let t2 = x1.t.generalize(&env2);
            env2.insert(lhs, t2);
            let x3 = env2.infer(rest)?;
            let mut env3 = x1.subst;
            env3.extend(x3.subst);
            Ok(InferData { subst: env3, t: x3.t })
        },
        Ek::Assign { lhs, rhs } => {
            let mut x = self.infer(rhs)?;
            let prev_ty = self.vars.get().ok_or_else(|| Error::UndefVar(lhs.clone()))?;
            tysy::unify(&mut x.subst, prev_ty, &x.t)?;
            x.t = tysy::Ty::Literal(tysy::TyLit::Unit);
            Ok(x)
        },
        Ek::Block(blk) => {
            let (x, ) = self.infer_block(blk);
        },
    }
}
}
