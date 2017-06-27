#include "compiling.hh"

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

using namespace goat;
using namespace node;
using namespace compiling;
using namespace inference;

static llvm::AllocaInst *CreateAlloca(llvm::Function *function,
                                      llvm::LLVMContext &context,
                                      const std::string &VarName) {
  llvm::IRBuilder<> TmpB(&function->getEntryBlock(),
                   function->getEntryBlock().begin());
  return TmpB.CreateAlloca(llvm::Type::getDoubleTy(context), nullptr,
                           VarName.c_str());
}

void CompilingVisitor::visit(const Number &number) {
  current_ = llvm::ConstantFP::get(context_, llvm::APFloat(number.value()));
}

void CompilingVisitor::visit(const Identifier &identifier) {
  llvm::Value *v = scope_[identifier.value()];
  if(!v) {
    current_ = nullptr;
    return;
  }
  current_ = builder_.CreateLoad(v, identifier.value());
}

void CompilingVisitor::visit(const String &string) {

}

void CompilingVisitor::visit(const Program &program) {

}

void CompilingVisitor::visit(const Argument &argument) {

}
// http://stackoverflow.com/questions/24429378/function-pointer-as-argument-to-call
void CompilingVisitor::visit(const Function &function) {

}

void CompilingVisitor::visit(const Application &application) {

}

void CompilingVisitor::visit(const Conditional &conditional) {

}

void CompilingVisitor::visit(const Operation &operation) {

}

void CompilingVisitor::visit(const Declaration &declaration) {
  declaration.expression()->accept(*this);
  llvm::Value *exp = current_;
  if(!exp) {
    current_ = nullptr;
    return;
  }
  scope_.erase(declaration.identifier()->value());

  declaration.identifier()->accept(*this);
  llvm::Value *var = current_;
  if(!exp) {
    current_ = nullptr;
    perror("Compiler bug, couldn't allocate a variable.");
    return;
  }

  llvm::Function *fn = builder_.GetInsertBlock()->getParent();
  llvm::AllocaInst *alloca = CreateAlloca(fn, context_, declaration.identifier()->value());

  builder_.CreateStore(exp, alloca);
  scope_[declaration.identifier()->value()] = var;
  current_ = exp;
}
