#ifndef SRC_FREEVARS_
#define SRC_FREEVARS_

#include "visitor.hh"
#include <set>

namespace goat {
namespace lifter {
class FreeVars : public node::Visitor {
public:
  FreeVars(std::set<std::string> scope) : scope_(scope) {}
  VisitorMethods
private:
  std::set<std::string> scope_;
};
}
}

#endif
