#include "constraints.hh"
#include "util.hh"
#include <memory>
#include <string>

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

const char *alpha = "abcdefghijklmnopqrstuvwxyz";
const uint8_t len = 26;
Type TypeFactory::next() {
  last_++;
  uint32_t current = last_;
  std::string accum;
  while(current > 0) {
    uint8_t index = current % len;
    accum.push_back(alpha[index]);
    current /= len;
  }
  return Type(accum);
}

}
}
