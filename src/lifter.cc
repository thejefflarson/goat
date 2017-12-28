#include "lifter.hh"

using namespace goat::node;
using namespace goat::lifter;

std::shared_ptr<Program> Lifter::lift(std::shared_ptr<node::Program> program) {
  root_ = program;
  visit(*program);
}

void Lifter::visit(const node::Program &program) {
  program.expression()->accept(*this);
  child_ = std::make_shared<node::Program>(child_);
}

void Lifter::visit(const node::Function &function) {
  auto args = std::make_shared<ArgumentList>();
  for(auto a : *function.arguments()) {
    a->accept(*this);
    args->push_back(std::static_pointer_cast<Argument>(child_));
  }
  function.program()->accept(*this);
  child_ = std::make_shared<Function>(
    args,
    std::static_pointer_cast<Program>(child_)
  );
}

void Lifter::visit(const node::Application &application) {
  auto args = std::make_shared<Labels>();
  application.identifier()->accept(*this);
  auto ident = child_;
  for(auto l : *application.labels()) {
    l.second->accept(*this);
    auto label = std::static_pointer_cast<Label>(child_);
    args->insert({label->name(), label});
  }
  child_ = std::make_shared<Application>(
    std::static_pointer_cast<Identifier>(ident),
    args
  );
}
