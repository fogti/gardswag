use gardswag_infer_cgen::InferExtra;
use gardswag_syntax::{Expr, Interner, Symbol};
use gardswag_varstack::VarStack;

#[cxx::bridge]
mod ffi {
    unsafe extern "C++" {
        include!("gdsllvm.hpp");
        type Type;
        type Value;

        type GdsIfCtx;
        fn selectThen(&mut self);
        fn selectElse(&mut self);
        fn finish(&mut self, thenV: *const Value, elseV: *const Value) -> *const Value;

        type GdsLLVMCtx;
        fn gdsllvm_new_ctx() -> UniquePtr<GdsLLVMCtx>;

        fn getUnit(&mut self) -> *const Value;
        fn getFalse(&mut self) -> *const Value;
        fn getTrue(&mut self) -> *const Value;
        fn getInt(&mut self, i: i32) -> *const Value;
        fn getString(&mut self, len: usize, dat: *const u8) -> *const Value;

        fn createIfContext(&mut self, condV: *const Value) -> UniquePtr<GdsIfCtx>;

        fn emitFixpoint(
            &mut self,
            innerV: *const Value,
            namelen: usize,
            namedat: *const u8,
        ) -> *const Value;
    }
}

pub struct Context {
    inner: UniquePtr<GdsLLVMCtx>,
}

pub fn codegen(itn: &Interner, tlexpr: &Expr<InferExtra>) -> Context {
    let mut ctx = ffi::gdsllvm_new_ctx();

    // TODO: generate code for exprs... etc...

    Context { inner: ctx }
}

fn codegen_expr(
    ctx: &mut Context,
    itn: &Interner,
    vs: &VarStack<'_, Symbol, *const ffi::Value>,
    expr: &Expr<InferExtra>,
) -> *const ffi::Value {
    use gardswag_syntax::ExprKind as Ek;
    match expr {
        // literals and references
        Ek::Unit => ctx.getUnit(),
        Ek::Boolean(false) => ctx.getFalse(),
        Ek::Boolean(true) => ctx.getTrue(),
        Ek::Integer(i) => ctx.getInt(i),
        Ek::Identifier(i) => *vs
            .find(i)
            .expect("unknown identifier encountered during codegen"),
        Ek::PureString(s) => ctx.getString(s.len(), s.bytes()),

        // code structure
        Ek::Let { lhs, rhs, rest } => {
            let v_rhs = codegen_expr(ctx, itn, vs, rhs);
            codegen_block(
                ctx,
                itn,
                VarStack {
                    psrent: vs,
                    name: lhs,
                    value: v_rhs,
                },
                rest,
            )
        }

        Ek::Block(blk) => codegen_block(ctx, itn, vs, blk),

        Ek::If {
            cond,
            then,
            or_else,
        } => {
            let v_cond = codegen_expr(ctx, itn, vs, cond);
            let subctx = ctx.createIfContext(v_cond);
            subctx.selectThen();
            let v_then = codegen_expr(ctx, itn, vs, then);
            subctx.selectElse();
            let v_else = codegen_expr(ctx, itn, vs, or_else);
            subctx.finish()
        }

        // lambdas (these require lifting, etc.)
        Ek::Lambda { arg, body } => todo!(),

        Ek::Call { prim, arg } => todo!(),

        Ek::Fix { arg, body } => {
            let v_body = codegen_expr(ctx, itn, vs);
        }
    }
}

fn codegen_block(
    ctx: &mut Context,
    itn: &Interner,
    vs: &VarStack<'_, Symbol, *const ffi::Value>,
    blk: &Block<InferExtra>,
) -> *const ffi::Value {
    for i in &blk.stmts {
        codegen_expr(ctx, itn, vs, i);
    }

    if let Some(x) = &blk.term {
        codegen_expr(ctx, itn, vs, x)
    } else {
        ctx.getUnit()
    }
}
