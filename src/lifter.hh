#ifndef SRC_LIFTER_
#define SRC_LIFTER_

#include <visitor.hh>

namespace goat {
namespace lifter {
// Lifts closures to the global scope
class Lifter : public node::Visitor {
  Lifter();
};
}
}
#endif
