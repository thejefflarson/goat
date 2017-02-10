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
class AbstractType {
 public:
  virtual ~AbstractType() = default;
  bool operator==(const AbstractType &b) const {
    if(typeid(*this) != typeid(b)) return false;
    return equals(b);
  }
  bool operator!=(const AbstractType &b) const {
    return !(*this == b);
  }
  bool operator<(const AbstractType &b) const {
    return *this != b;
  }
private:
  bool equals(const AbstractType &) const { return true; };
};

class TypeVariable : public AbstractType {
public:
  TypeVariable(std::string id) :
    id_(id) {}
private:
  bool equals(const TypeVariable &b) const { return id_ == b.id_; }
  std::string id_;
};

class NumberType : public AbstractType {};
class StringType : public AbstractType {};
class BoolType : public AbstractType {};
class NoType : public AbstractType {};

class FunctionType;
using Type = util::Variant<TypeVariable,
                           NumberType,
                           StringType,
                           BoolType,
                           NoType,
                           FunctionType>;

class FunctionType : public AbstractType {
public:
  FunctionType(std::vector<Type> types, TypeVariable ret) :
    types_(types),
    ret_(ret) {}
private:
  std::vector<Type> types_;
  TypeVariable ret_;
};

class TypeFactory {
 public:
  TypeFactory() : last_(1) {}
  TypeVariable next();
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
