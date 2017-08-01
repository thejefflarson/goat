#ifndef SRC_RENAMER_
#define SRC_RENAMER_

#include <string>
#include <map>

#include "node.hh"
#include "visitor.hh"
#include "util.hh"

namespace goat {
namespace renaming {

class Renamer : public node::TreeCloner {
 public:
  Renamer() :
    TreeCloner(),
    names_(),
    namer_() {}
  void visit(const node::Declaration &declaration);
  void visit(const node::Function &function);
  void visit(const node::Identifier &identifier);
  std::shared_ptr<node::Program> rename(std::shared_ptr<node::Program> program);
 private:
  std::map<std::string, std::string> names_;
  util::Namer namer_;
};

} // namespace inference
} // namespace goat

#endif
