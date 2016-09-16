#ifndef GOAT_CONSTRAINTS_HH
#define GOAT_CONSTRAINTS_HH

#include "visitor.hh"
#include <set>
#include <memory>

namespace goat {
namespace inference {

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

};

}
}

#endif
