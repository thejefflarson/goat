#ifndef GOAT_CONSTRAINTS_HH_
#define GOAT_CONSTRAINTS_HH_

#include <set>

#include "visitor.hh"

namespace goat {
namespace inference {

class TypingVisitor : public node::Visitor {
public:
  TypingVisitor() : monomorphic_(), constraints_() {};
  void visit(const node::Number &number);
  void visit(const node::Identifier &identifier);
  void visit(const node::String &string);
  void visit(const node::Program &program);
  void visit(const node::Argument &argument);
  void visit(const node::Function &function);
  void visit(const node::Application &application);
  void visit(const node::Conditional &conditional);
  void visit(const node::Operation &operation);
  void visit(const node::Declaration &declaration);
private:
  std::set<Type> monomorphic_;
  ConstraintSet constraints_;
};

} // inference
} // goat

#endif
