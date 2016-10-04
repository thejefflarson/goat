#ifndef GOAT_CONSTRAINTS_HH
#define GOAT_CONSTRAINTS_HH

#include <set>
#include <memory>
#include <string>
#include <vector>

#include "visitor.hh"

namespace goat {
namespace inference {

class TypeNode {
public:
  virtual ~TypeNode() = default;
};

class TypeVariable : public TypeNode {
  TypeVariable(std::string id) : id_(id) {}
private:
  std::string id_;
};

class FunctionType : public TypeNode {
  FunctionType(std::vector<TypeVariable> in, TypeVariable ret) :
    in_(in),
    ret_(ret) {}
private:
  std::vector<TypeVariable> in_;
  TypeVariable ret_;
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
             std::vector<TypeNode> variables) :
    relation_(relation),
    variables_(variables) {}
private:
  ConstraintRelation relation_;
  std::vector<TypeNode> variables_;
};

class ConstraintSet {
  ConstraintSet() : constraints_() {}
  void add(Constraint constraint) {
    constraints_.insert(constraint);
  }

private:
  std::set<Constraint> constraints_;
};

class Constrainer : public node::Visitor {

private:
  ConstraintSet constraints_;
  TypeVariableFactory type_factory_;
};

}
}

#endif
