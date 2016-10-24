#include "constraints.hh"
#include "util.hh"

namespace goat {
namespace inference {

bool TypeVariable::equals(const TypeNode &b) const {
  const TypeVariable *c = static_cast<const TypeVariable *>(&b);
  return id_ == c->id_;
}

bool FunctionType::equals(const TypeNode &b) const {
  const FunctionType *c = static_cast<const FunctionType *>(&b);

  return ret_ == c->ret_ &&
    util::compare_vector_pointers(in_, c->in_);
}

}
}
