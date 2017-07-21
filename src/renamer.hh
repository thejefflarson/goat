#ifndef SRC_RENAMER_
#define SRC_RENAMER_

#include <string>
#include <map>

#include "node.hh"
#include "visitor.hh"
#include "util.hh"

namespace goat {
namespace renaming {

class Renamer : public node::Visitor {
 public:
  Renamer(node::Program root) :
    names_(),
    namer_(),
    root_(root),
    child_(nullptr) {}
 VisitorMethods
 private:
  std::map<std::string, std::string> names_;
  std::map<std::string, std::string> scope_;
  util::Namer namer_;
  node::Program root_;
  std::shared_ptr<node::Node> child_;
};

} // namespace inference
} // namespace goat

#endif
