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
  std::unique_ptr<TypeVariable> create(std::string id);
  std::unique_ptr<TypeVariable> next();
private:
  std::string last_;
  std::set<std::string> used_;
};

class Constraint {

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
