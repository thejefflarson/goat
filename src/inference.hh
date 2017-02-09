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
  virtual ~Type() = default;
  bool operator==(const Type &b) const {
    if(typeid(*this) != typeid(b)) return false;
    return equals(b);
  }
  bool operator!=(const Type &b) const {
    return !(*this == b);
  }
  bool operator<(const Type &b) const {
    return *this != b;
  }
private:
  virtual bool equals(const Node &) const = 0;
  std::string id_;
};

class TypeVariable : Type {
  Type(std::string id) :
    id_(id) {}
private:
  std::string id_;
};

class NumberType : Type {

};

class StringType : Type {

};

class BoolType : Type {

};

class FunctionType : Type {

};

class TypeFactory {
 public:
  TypeFactory() : last_(1) {}
  TypeVar next();
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
             std::pair<Type, Type> variables) :
    relation_(relation),
    variables_(variables) {}
    bool operator==(const Constraint &b) const {
      return relation_ == b.relation_ &&
        variables_ == b.variables_;
    }
    bool operator!=(const Constraint&b) const {
      return !(*this == b);
    }
 private:
  ConstraintRelation relation_;
  std::pair<Type, Type> variables_;
};


class TypingVisitor : public node::Visitor {
public:
  TypingVisitor() :
    monomorphic_(),
    constraints_(),
    assumptions_() {};
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
  std::unordered_map<std::string, Type> assumptions_;
};


}  // namespace inference
}  // namespace goat

#endif  // SRC_INFERENCE_HH_
