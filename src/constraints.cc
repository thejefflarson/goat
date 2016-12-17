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

std::string alpha = "abcdefghijklmnopqrstuvwxyz";
Type TypeFactory::next() {
  last_++;
  uint32_t current = last_;
  std::string accum;
  while(current > 0) {
    uint8_t index = current % alpha.length();
    accum.push_back(alpha[index]);
    current /= alpha.length();
  }
  return Type(accum);
}

}
}
