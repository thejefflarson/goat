#ifndef SRC_COMPILER_
#define SRC_COMPILER_

#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

#include "inferer.hh"
#include "node.hh"
#include "visitor.hh"

namespace goat {
namespace compiling {

// The actual compiler!
class Compiler : public node::Visitor {
public:
  Compiler(std::set<inference::Substitution> substitutions) :
    substitutions_(substitutions),
    context_(),
    builder_(context_),
    module_(llvm::make_unique<llvm::Module>("Goat", context_)),
    scope_(),
    current_() {}
  VisitorMethods
private:
  std::set<inference::Substitution> substitutions_;
  llvm::LLVMContext context_;
  llvm::IRBuilder<> builder_;
  std::unique_ptr<llvm::Module> module_;
  std::map<std::string, llvm::Value *> scope_;
  llvm::Value *current_;
};

}
}

#endif
