#ifndef SRC_INFERENCE_HH_
#define SRC_INFERENCE_HH_

#include <cassert>
#include <memory>
#include <set>
#include <string>
#include <iostream>
#include <typeinfo>
#include <unordered_map>
#include <utility>
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
    if(typeid(*this) != typeid(b)) return true;
    return less(b);
  }
 private:
  virtual bool equals(const AbstractType &b) const { return true; }
  virtual bool less(const AbstractType &b) const { return false; }
};

class TypeVariable : public AbstractType {
 public:
  TypeVariable(std::string id) :
    id_(id) {}
  const std::string& id() const { return id_; }
 private:
  bool equals(const AbstractType &b) const {
    auto c = *static_cast<const TypeVariable *>(&b);
    return id_ == c.id_;
  }
  bool less(const AbstractType &b) const {
    auto c = *static_cast<const TypeVariable *>(&b);
    return id_ < c.id_;
  }
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

using ConcreteType = util::Variant<NoType,
                                   NumberType,
                                   StringType,
                                   BoolType>;

class FunctionType : public AbstractType {
 public:
  FunctionType(std::vector<Type> types, TypeVariable ret) :
    types_(types),
    ret_(ret) {}
  const std::vector<Type>& types() const { return types_; };
  const TypeVariable ret() const { return ret_; }
 private:
  bool equals(const AbstractType &b) const {
    auto c = *static_cast<const FunctionType *>(&b);
    return types_ == c.types_ && ret_ == c.ret_;
  }
  bool less(const AbstractType &b) const {
    auto c = *static_cast<const FunctionType *>(&b);
    return types_ < c.types_ || ret_ < c.ret_;
  }
  std::vector<Type> types_;
  TypeVariable ret_;
};

class TypeFactory {
 public:
  TypeFactory() : last_(0) {}
  TypeVariable next();
 private:
  uint32_t last_;
};

enum class Relation {
  Equality,
  Explicit,
  Implicit
};

class Constraint {
 public:
  Constraint(Relation relation,
             std::pair<Type, Type> variables) :
    relation_(relation),
    variables_(variables) {}
  Constraint(Relation relation,
             std::pair<Type, Type> variables,
             std::set<Type> monomorphic) :
    relation_(relation),
    variables_(variables),
    monomorphic_(monomorphic) { assert(relation == Relation::Implicit); }
  bool operator==(const Constraint &b) const {
    return relation_ == b.relation_ &&
      variables_ == b.variables_;
  }

  bool operator!=(const Constraint &b) const {
    return !(*this == b);
  }

  bool operator<(const Constraint &b) const {
    return variables_ < b.variables_;
  }

  Relation relation() { return relation_; }
  std::pair<Type, Type> variables() { return variables_; }
 private:
  Relation relation_;
  std::pair<Type, Type> variables_;
  std::set<Type> monomorphic_;
};

class Substitution {
public:
  Substitution(TypeVariable s, ConcreteType t) :
    error_(false),
    s_(s),
    t_(t) {}
  Substitution(TypeVariable s) :
    error_(true),
    s_(s),
    t_() {}
  bool is_error() { return error_; }
  bool operator==(const Substitution &b) const {
    return s_ == b.s_ && t_ == b.t_;
  }

  bool operator!=(const Substitution &b) const {
    return !(*this == b);
  }

  bool operator<(const Substitution &b) const {
    return s_ < b.s_ || t_ < b.t_;
  }
private:
  bool error_;
  TypeVariable s_;
  ConcreteType t_;
};

class TypingVisitor : public node::Visitor {
 public:
  TypingVisitor() :
    monomorphic_(),
    constraints_(),
    assumptions_(),
    typer_() {}
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
  const std::set<Constraint>& constraints() const { return constraints_; }
  std::set<Substitution> solve();
 private:
  std::set<Type> monomorphic_;
  std::set<Constraint> constraints_;
  std::unordered_map<std::string, Type> assumptions_;
  TypeFactory typer_;
};


}  // namespace inference
}  // namespace goat

#endif  // SRC_INFERENCE_HH_
