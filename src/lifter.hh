#ifndef SRC_LIFTER_
#define SRC_LIFTER_

#include "visitor.hh"
#include "node.hh"

namespace goat {
namespace lifter {
// Lifts closures to the global scope
class Lifter : public node::TreeCloner {
public:
  Lifter() :
    names_(),
    root_() {};
  VisitorMethods
  std::shared_ptr<node::Program> lift(std::shared_ptr<node::Program> program);
private:
  std::unordered_map<std::string, std::string> names_;
  std::shared_ptr<node::Program> root_;
};
}
}

#endif
