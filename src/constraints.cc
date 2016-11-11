#include "constraints.hh"
#include "util.hh"
#include <memory>

namespace goat {
namespace inference {

<<<<<<< HEAD
bool Type::equals(const TypeNode &b) const {
  const Type *c = static_cast<const Type *>(&b);
=======
bool TypeVariable::equals(const TypeNode &b) const {
  const TypeVariable *c = static_cast<const TypeVariable *>(&b);
>>>>>>> 39946fe0b12c3d7a4ea5c365c1974dc8790e01e8
  return id_ == c->id_;
}

bool FunctionType::equals(const TypeNode &b) const {
  const FunctionType *c = static_cast<const FunctionType *>(&b);
  return ret_ == c->ret_ &&
    util::compare_vector_pointers(&in_, &c->in_);
}

}
}
