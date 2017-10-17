#include <gsl/gsl>

#include "node.hh"
#include "renamer.hh"

using namespace goat;
using namespace renaming;

std::shared_ptr<node::Program> Renamer::rename(std::shared_ptr<node::Program> program) {
  return clone(program);
}

void Renamer::visit(const node::Identifier &identifier) {
  Expects(names_.find(identifier.value()) != names_.end());
  child_ = std::make_shared<node::Identifier>(identifier.value(),
                                              names_[identifier.value()]);
}

void Renamer::visit(const node::Function &function) {
  auto names = names_;
  for(auto a : *function.arguments()) {
    std::cout << a->identifier()->value() << std::endl;
    names_[a->identifier()->value()] = namer_.next();
    std::cout << names_[a->identifier()->value()] << std::endl;
  }
  TreeCloner::visit(function);
  names_ = names;
}

void Renamer::visit(const node::Declaration &declaration) {
  names_[declaration.identifier()->value()] = namer_.next();
  TreeCloner::visit(declaration);
}
