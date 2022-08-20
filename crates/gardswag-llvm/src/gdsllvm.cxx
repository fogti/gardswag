#include <gardswag-llvm/src/lib.rs.h>
#include "gdsllvm.hpp"

#include <string_view>

GdsLLVMCtx::GdsLLVMCtx():
    Builder(TheContext),
    TheModule("gardswag runner", TheContext)
    {}

std::unique_ptr<GdsLLVMCtx> gdsllvm_new_ctx() {
    auto ret = std::make_unique<GdsLLVMCtx>();

    // insert preamble (TODO: put this into separate library)...

    return ret;
}

llvm::Type * GdsLLVMCtx::getUnitType() {
    return llvm::IntegerType::get(TheContext, 0);
}

llvm::Value * GdsLLVMCtx::getUnit() {
    return llvm::ConstantInt::get(getUnitType(), llvm::APInt(0, 0, false), false);
}

llvm::Type * GdsLLVMCtx::getBoolType() {
    return llvm::IntegerType::get(TheContext, 1);
}

llvm::Value * GdsLLVMCtx::getFalse() {
    return llvm::ConstantInt::get(getBoolType());
}

llvm::Value * GdsLLVMCtx::getTrue() {
    return llvm::ConstantInt::get(getBoolType());
}

llvm::Type * GdsLLVMCtx::getIntType() {
    return llvm::IntegerType::get(TheContext, 32);
}

llvm::Value * GdsLLVMCtx::getInt(int32_t i) {
    return llvm::ConstantInt::get(
        reinterpret_cast<llvm::IntegerType *>(getIntType()),
        llvm::APInt::getSigned());
}

llvm::Value * GdsLLVMCtx::getString(size_t len, const char * dat) {
    return llvm::ConstantDataArray::getString(TheContext, std::string_view(dat, len), true);
}

GdsIfCtx GdsLLVMCtx::createIfContext(llvm::Value * condV) {
    llvm::Function *TheFunction = Builder.GetInsertBlock()->getParent();

    GdsIfCtx ret;
    ret.parent = this;
    ret.TheFunction = TheFunction;
    ret.ThenBB = BasicBlock::Create(TheContext, "then", TheFunction);
    ret.ElseBB = BasicBlock::Create(TheContext, "else");
    ret.MergeBB = BasicBlock::Create(TheContext, "ifcont");

    Builder.CreateCondBr(condV, ret.ThenBB, ret.ElseBB);

    return ret;
}

void GdsIfCtx::selectThen() {
    parent->Builder.SetInsertPoint(ThenBB);
}

void GdsIfCtx::selectElse() {
    parent->Builder.CreateBr(MergeBB);
    ThenBB = parent->Builder.GetInsertPoint();
    TheFunction->getBasicBlockList().push_back(ElseBB);
    parent->Builder.SetInsertPoint(ElseBB);
}

llvm::Value * GdsIfCtx::finish(llvm::Value *thenV, llvm::Value *elseV) {
    parent->Builder.CreateBr(MergeBB);
    ElseBB = parent->Builder.GetInsertPoint();
    TheFunction->getBasicBlockList().push_back(MergeBB);
    parent->Builder.SetInsertPoint(MergeBB);

    llvm::PHINode * PhN = parent->Builder.CreatePHI(thenV->getType(), 2, "iftmp");
    PhN->addIncoming(thenV, ThenBB);
    PhN->addIncoming(elseV, ElseBB);

    return PhN;
}

std::unique_ptr<GdsFixpCtx> GdsLLVMCtx::emitFixpoint(size_t len, const char * dat) {
    GdsFixpCtx ret;
    ret.parent = this;
    ret.name = std::string_view(dat, len);

    ret.PhN = Builder.CreatePHI();

    return std::make_unique<GdsFixpCtx>(ret);
}

