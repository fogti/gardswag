use core::marker::Pin;
use gardswag_infer_cgen::InferExtra;
use gardswag_syntax::{Expr, Interner, Symbol};
use gardswag_varstack::VarStack;

#[cxx::bridge]
mod ffi {
    extern "C++" {
        include!("gdsllvm.hpp");
        type Type;
        type Value;

        type GdsFixpCtx;

        type GdsIfCtx;
        unsafe fn selectThen(self: &mut GdsIfCtx);
        unsafe fn selectElse(self: &mut GdsIfCtx);
        unsafe fn finish(
            self: &mut GdsIfCtx,
            thenV: *const Value,
            elseV: *const Value,
        ) -> *const Value;

        type GdsLLVMCtx;
        unsafe fn gdsllvm_new_ctx() -> UniquePtr<GdsLLVMCtx>;

        unsafe fn getUnit(self: Pin<&mut GdsLLVMCtx>) -> *const Value;
        unsafe fn getFalse(self: Pin<&mut GdsLLVMCtx>) -> *const Value;
        unsafe fn getTrue(self: Pin<&mut GdsLLVMCtx>) -> *const Value;
        unsafe fn getInt(self: Pin<&mut GdsLLVMCtx>, i: i32) -> *const Value;
        unsafe fn getString(self: Pin<&mut GdsLLVMCtx>, len: usize, dat: *const u8)
            -> *const Value;

        unsafe fn createIfContext(self: Pin<&mut GdsLLVMCtx>, condV: *const Value) -> GdsIfCtx;

        unsafe fn emitFixpoint(
            self: Pin<&mut GdsLLVMCtx>,
            innerV: *const Value,
            namelen: usize,
            namedat: *const u8,
        ) -> UniquePtr<GdsFixpCtx>;
    }
}

unsafe impl cxx::ExternType for ffi::GdsIfCtx {
    type Id = cxx::type_id!("GdsIfCtx");
    type Kind = cxx::kind::Trivial;
}

unsafe impl cxx::ExternType for ffi::GdsLLVMCtx {
    type Id = cxx::type_id!("GdsLLVMCtx");
    type Kind = cxx::kind::Opaque;
}

pub struct Context {
    inner: UniquePtr<GdsLLVMCtx>,
}

pub fn codegen(itn: &Interner, tlexpr: &Expr<InferExtra>) -> Context {
    let mut ctx = unsafe { ffi::gdsllvm_new_ctx() };
    {
        let mut ctx = unsafe { Pin::new_unchecked(&mut *ctx) };

        // TODO: generate code for exprs... etc...
        unsafe {
            codegen_expr(
                &mut ctx,
                itn,
                VarStack {
                    parent: None,
                    name: "std",
                    value: core::ptr::null(),
                },
            )
        };
    }

    Context { inner: ctx }
}

unsafe fn codegen_expr(
    ctx: Pin<&mut ffi::GdsLLVMCtx>,
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

unsafe fn codegen_block(
    ctx: Pin<&mut GdsLLVMCtx>,
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
