#include "compiling.hh"

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

using namespace goat;
using namespace node;
using namespace compiling;
using namespace inference;

void CompilingVisitor::visit(const Number &number) {
  current_ = llvm::ConstantFP::get(context_, llvm::APFloat(number.value()));
}

void CompilingVisitor::visit(const Identifier &identifier) {

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

}
