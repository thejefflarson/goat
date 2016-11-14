#include "constraints.hh"
#include "util.hh"
#include <memory>
#include <sstream>

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

Type TypeFactory::next() {
  last_++;
  std::stringstream stream;
  stream << last_ << std::hex;
  return Type(stream.str());
}

}
}
