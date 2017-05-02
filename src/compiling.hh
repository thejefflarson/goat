#ifndef SRC_COMPILING_
#define SRC_COMPILING_

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

#include "inference.hh"
#include "node.hh"
#include "visitor.hh"

namespace goat {
namespace compiling {

// The actual compiler!
class CompilingVisitor : public node::Visitor {
public:
  CompilingVisitor(std::set<inference::Substitution> substitutions) :
    substitutions_(substitutions),
    context_(),
    builder_(context_),
    module_(std::move(llvm::make_unique<llvm::Module>("Goat Compiler", context_))),
    scope_() {}
  VisitorMethods
private:
  std::set<inference::Substitution> substitutions_;
  llvm::LLVMContext context_;
  llvm::IRBuilder<> builder_;
  std::unique_ptr<llvm::Module> module_;
  std::map<std::string, llvm::Value *> scope_;
};

}
}

#endif
