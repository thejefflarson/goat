#ifndef SRC_INFERENCE_HH_
#define SRC_INFERENCE_HH_

#include <set>
#include <memory>
#include <string>
#include <typeinfo>
#include <unordered_map>
#include <vector>
#include "util.hh"
#include "visitor.hh"

namespace goat {
namespace inference {

// Note: this is just a language; create an AST and parse it...
// generate a set of constraints and then use union-find to infer
class Type {
 public:
  Type(std::string id) :
    id_(id) {}
  bool operator==(const Type &b) const {
    return id_ == b.id_;
  }
  bool operator!=(const Type &b) const {
    return !(*this == b);
  }
  bool operator<(const Type &b) const {
    return *this != b;
  }
private:
  std::string id_;
};

class TypeFactory {
 public:
  TypeFactory() : last_(1) {}
  Type next();
 private:
  uint32_t last_;
};

enum ConstraintRelation {
  Equality,
  ExplicitInstance,
  ImplicitInstance
};

class Constraint {
 public:
  Constraint(ConstraintRelation relation,
             std::vector<Type> variables) :
    relation_(relation),
    variables_(variables) {}
    bool operator==(const Constraint &b) const {
      return relation_ == b.relation_ &&
        util::compare_vector_pointers(&variables_, &b.variables_);
    }
    bool operator!=(const Constraint&b) const {
      return !(*this == b);
    }
 private:
  ConstraintRelation relation_;
  std::vector<Type> variables_;
};


class TypingVisitor : public node::Visitor {
public:
  TypingVisitor() :
    monomorphic_(),
    constraints_(),
    assumptions_(),
    typer_() {};
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
  std::set<Constraint> constraints_;
  std::unordered_map<node::Identifier &, Type> assumptions_;
  TypeFactory typer_;
};


}  // namespace inference
}  // namespace goat

#endif  // SRC_INFERENCE_HH_
