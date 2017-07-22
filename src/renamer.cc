#include "node.hh"
#include "renamer.hh"

using namespace goat;
using namespace renaming;

void Renamer::visit(const node::Identifier &identifier) {
  assert(names_[identifier.value() != map::end]);
  child_ = std::make_shared<node::Identifier>(identifier.value(), names_[identifier.value()]);
}

void Renamer::visit(const node::Function &function) {
  auto names = names_;
  for(auto a : *function.arguments()) {
    names_[a->identifier()->value()] = namer_.next();
  }
  TreeCloner::visit(function);
  names_ = names;
}

void Renamer::visit(const node::Declaration &declaration) {
  names_[declaration.identifier()->value()] = namer_.next();
  TreeCloner::visit(declaration);
}
