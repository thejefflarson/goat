#ifndef SRC_UTIL_H_
#define SRC_UTIL_H_

#include <algorithm>
#include <memory>
#include <new>
#include <tuple>
#include <typeindex>
#include <type_traits>
#include <vector>

namespace goat {

namespace node {
class Visitor;
}

namespace util {
template <typename T>
bool compare_vector_pointers(const T &a, const T &b) {
  if (a->size() != b->size())
    return false;

  auto eq = [](const auto &a, const auto &b) {
    return *a == *b;
  };

  return std::equal(a->begin(), a->end(), b->begin(), eq);
}

class Namer {
 public:
  Namer() : last_(0) {}
  std::string next();
 private:
  uint32_t last_;
};
}
}
#endif
