#ifndef GOAT_CONSTRAINTS_HH
#define GOAT_CONSTRAINTS_HH

#include "visitor.hh"
#include <set>
#include <memory>

namespace goat {
namespace inference {

class TypeVariable {
  TypeVariable(std::string id) : id_(id) {}
private:
  std::string id_;
};

class TypeVariableFactory {
  TypeVariableFactory() : last_("a") {}
  std::shared_ptr<TypeVariable> create(std::string id);
  std::shared_ptr<TypeVariable> next();
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
             std::vector<std::shared_ptr<TypeVariable>> variables) :
    relation_(relation),
    variables_(variables) {}
private:
  ConstraintRelation relation_;
  std::vector<std::shared_ptr<TypeVariable>> variables_;
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

}
}

#endif
