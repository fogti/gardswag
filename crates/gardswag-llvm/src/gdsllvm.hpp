#pragma once
#include <stddef.h>
#include <inttypes.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>
#include <string_view>

struct GdsLLVMCtx {
    llvm::LLVMContext TheContext;
    llvm::IRBuilder<> Builder;
    llvm::Module TheModule;

    GdsLLVMCtx();

    llvm::Type * getUnitType();
    llvm::Value * getUnit();

    llvm::Type * getBoolType();
    llvm::Value * getFalse();
    llvm::Value * getTrue();

    llvm::Type * getIntType();
    llvm::Value * getInt(int32_t);

    llvm::Value * getString(size_t, const char *);

    GdsIfCtx createIfContext(llvm::Value * condV);

    std::unique_ptr<GdsFixpCtx> emitFixpoint(size_t, const char *);
};

struct GdsIfCtx {
    GdsLLVMCtx * parent;
    llvm::Function * TheFunction;
    llvm::BasicBlock * ThenBB;
    llvm::BasicBlock * ElseBB;
    llvm::BasicBlock * MergeBB;

    void selectThen();
    void selectElse();
    llvm::Value * finish(llvm::Value * thenV, llvm::Value * elseV);
};

struct GdsFixpCtx {
    GdsLLVMCtx * parent;
    std::string_view name;

    llvm::PHINode * PhN;
};

std::unique_ptr<GdsLLVMCtx> gdsllvm_new_ctx();

using llvm::Type;
using llvm::Value;
