#ifndef SRC_RENAMER_
#define SRC_RENAMER_

#include <string>
#include <map>

#include "visitor.hh"

namespace goat {
namespace inference {

class Renamer : public node::Visitor {
 public:
  Renamer() :
    names_(),
    namer_() {}
 private:
  std::map<std::string, std::string> names_;
  Namer namer_;
};

} // namespace inference
} // namespace goat

#endif
