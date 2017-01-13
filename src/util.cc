#include "node.hh"

using namespace goat::node;

template<typename T>
inline void list_accept(const T list, Visitor &v) {
  for(auto i : *list) {
    i->accept(v);
  }
}
