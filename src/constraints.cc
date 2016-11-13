#include "constraints.hh"
#include "util.hh"
#include <memory>

namespace goat {
namespace inference {

bool Type::equals(const TypeNode &b) const {
  const Type *c = static_cast<const Type *>(&b);
  return id_ == c->id_;
}

bool FunctionType::equals(const TypeNode &b) const {
  const FunctionType *c = static_cast<const FunctionType *>(&b);
  return ret_ == c->ret_ &&
    util::compare_vector_pointers(&in_, &c->in_);
}

}
}
