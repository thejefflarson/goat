#include "node.hh"
#include "renamer.hh"

using namespace goat;
using namespace renaming;

void Renamer::visit(const node::Number &number) {
  child_ = std::make_shared<node::Number>(number);
}

void Renamer::visit(const node::Identifier &identifier) {
  assert(names_[identifier.value() == map::end]);
  auto internal = namer_.next();
  names_[identifier.value()] = internal;
  child_ = std::make_shared<node::Identifier>(identifier.value(), internal);
}

void Renamer::visit(const node::String &string) {
  child_ = std::make_shared<node::String>(string);
}

void Renamer::visit(const node::Program &program) {
  program.accept(*this);
  child_ = std::make_shared<node::Program>(program);
}

void Renamer::visit(const node::Argument &argument) {

}

void Renamer::visit(const node::Function &function) {}
void Renamer::visit(const node::Application &application) {}
void Renamer::visit(const node::Conditional &conditional) {}
void Renamer::visit(const node::Operation &operation) {}
void Renamer::visit(const node::Declaration &declaration) {}
