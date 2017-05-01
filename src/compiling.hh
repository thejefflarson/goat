#ifndef SRC_COMPILING_
#define SRC_COMPILING_

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
    scope_() {}
  VisitorMethods
private:
  std::set<inference::Substitution> substitutions_;
  std::set<node::Identifier> scope_;
  LLVMContext context_;
};

}
}

#endif
