#ifndef SRC_UTIL_H_
#define SRC_UTIL_H_

#include <memory>
#include <vector>

namespace goat {

namespace node {
class Visitor;
}

namespace util {
template<typename T>
bool compare_vector_pointers(const T &a, const T &b) {
  if (a->size() != b->size())
    return false;

  auto eq = [](const auto &a, const auto &b) {
    return *a == *b;
  };

  return std::equal(a->begin(), a->end(), b->begin(), eq);
}

template<typename T>
void list_accept(const T list, node::Visitor &v) {
  for(auto i : *list) {
    i->accept(v);
  }
}

}
}
#endif
