#ifndef SRC_INFERER_
#define SRC_INFERER_

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
    if(typeid(*this) != typeid(b)) return this < &b;
    return less(b);
  }
 private:
  virtual bool equals(const AbstractType &b) const { return true; }
  virtual bool less(const AbstractType &b) const { return false; }
};

class NumberType : public AbstractType {};
class StringType : public AbstractType {};
class BoolType : public AbstractType {};
class NoType : public AbstractType {};
class FunctionType;
class TypeVariable;
using Type = util::Variant<NoType,
                           TypeVariable,
                           NumberType,
                           StringType,
                           BoolType,
                           FunctionType>;

class TypeVariable : public AbstractType {
 public:
  TypeVariable(std::string id) :
    id_(id) {}
  const std::string& id() const { return id_; }
  bool occurs(Type in) const;
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

class FunctionType : public AbstractType {
 public:
  FunctionType(std::vector<Type> types) :
    types_(types) {}
  const std::vector<Type>& types() const { return types_; };
  const Type ret() const { return types_.back(); }
 private:
  bool equals(const AbstractType &b) const {
    auto c = *static_cast<const FunctionType *>(&b);
    return types_ == c.types_;
  }
  bool less(const AbstractType &b) const {
    auto c = *static_cast<const FunctionType *>(&b);
    return types_ < c.types_;
  }
  std::vector<Type> types_;
};

class Substitution {
public:
  Substitution(Type s, Type t) :
    error_(false),
    s_(s),
    t_(t) {}
  static Substitution error() { return Substitution(TypeVariable("error")); }
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

  Type operator()(Type in) const;
  Type left() const { return s_; }
  Type right() const { return t_; }
private:
  Substitution(Type s) :
    error_(true),
    s_(s),
    t_(TypeVariable("error")) {}
  bool error_;
  Type s_;
  Type t_;
};

class Constraint {
 public:
  Constraint(std::pair<Type, Type> variables) :
    variables_(variables) {}
  bool operator==(const Constraint &b) const {
    return variables_ == b.variables_;
  }

  bool operator!=(const Constraint &b) const {
    return !(*this == b);
  }

  bool operator<(const Constraint &b) const {
    return variables_ < b.variables_;
  }

  std::pair<Type, Type> variables() const { return variables_; }
  std::set<TypeVariable> activevars() const;
  Constraint apply(Substitution s) const;
  std::set<Substitution> unify() const;
 private:
  std::pair<Type, Type> variables_;
};

class Inferer : public node::TreeCloner {
 public:
  Inferer() :
    constraints_(),
    namer_() {}
  void visit(const node::Program &program);
  void visit(const node::Identifier &identifier);
  void visit(const node::Argument &argument);
  void visit(const node::Function &function);
  void visit(const node::Application &application);
  void visit(const node::Conditional &conditional);
  void visit(const node::Declaration &declaration);
  void visit(const node::Operation &operation);
  const std::set<Constraint>& constraints() const { return constraints_; }
  std::set<Substitution> solve();
 private:
  std::set<Constraint> constraints_;
  util::Namer namer_;
  std::unordered_map<std::string, Type> scope_;
};

}  // namespace inference
}  // namespace goat

#endif  // SRC_INFERER_HH_
