#ifndef SRC_CONSTRAINTS_HH_
#define SRC_CONSTRAINTS_HH_

#include <set>
#include <memory>
#include <string>
#include <vector>

#include "node.hh"
#include "visitor.hh"

namespace goat {
namespace inference {

// Note: this is just a language; create an AST and parse it...
// generate a set of constraints and then use union-find to infer
class TypeNode {
 public:
  virtual ~TypeNode() = default;
  bool operator==(const TypeNode &b) const {
    if (typeid(*this) != typeid(b)) return false;
    return equals(b);
  }
  bool operator!=(const TypeNode &b) const {
    return !(*this == b);
  }
  virtual bool equals(const TypeNode &b) const = 0;
};

class TypeVariable : public TypeNode {
  TypeVariable(std::string id,
               std::shared_ptr<node::Identifier> ident) :
    id_(id),
    ident_(ident) {}
  bool equals(const TypeNode &b) const;
 private:
  std::string id_;
  std::shared_ptr<node::Identifier> ident_;
};

class FunctionType : public TypeNode {
  FunctionType(std::vector<std::unique_ptr<TypeVariable>> in,
               TypeVariable ret,
               std::shared_ptr<node::Identifier> ident) :
    in_(std::move(in)),
    ret_(ret),
    ident_(ident) {}
  bool equals(const TypeNode &b) const;
 private:
  std::vector<std::unique_ptr<TypeVariable>> in_;
  TypeVariable ret_;
  std::shared_ptr<node::Identifier> ident_;
};

class TypeVariableFactory {
  TypeVariableFactory() : last_("a") {}
  TypeVariable create(std::string id);
  TypeVariable next();
 private:
  std::string last_;
  std::set<std::string> used_;
};

enum ConstraintRelation {
  Equality,
  ExplicitInstance,
  ImplicitInstance
};

class Constraint {
  Constraint(ConstraintRelation relation,
             std::vector<std::unique_ptr<TypeNode>> variables) :
    relation_(relation),
    variables_(std::move(variables)) {}
    bool operator==(const Constraint &b) const {
      return relation_ == b.relation_ && variables_ == b.variables_;
    }
    bool operator!=(const Constraint&b) const {
      return !(*this == b);
    }
 private:
  ConstraintRelation relation_;
  std::vector<std::unique_ptr<TypeNode>> variables_;
};

class ConstraintSet {
  ConstraintSet() : constraints_() {}
  void add(std::unique_ptr<Constraint> constraint) {
    constraints_.insert(std::move(constraint));
  }
 private:
  std::set<std::unique_ptr<Constraint>> constraints_;
};

class Constrainer : public node::Visitor {

 private:
  ConstraintSet constraints_;
  TypeVariableFactory type_factory_;
};

}  // namespace inference
}  // namespace goat

#endif  // SRC_CONSTRAINTS_HH_
