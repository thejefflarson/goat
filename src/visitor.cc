#include <memory>

#include "node.hh"
#include "visitor.hh"

using namespace goat::node;

std::shared_ptr<Program> TreeCloner::clone(std::shared_ptr<node::Program> program) {
  program->accept(*this);
  return std::static_pointer_cast<Program>(child_);
}

void TreeCloner::visit(const node::EmptyExpression &empty) {
  child_ = std::make_shared<node::EmptyExpression>();
}

void TreeCloner::visit(const node::Number &number) {
  child_ = std::make_shared<node::Number>(number);
}

void TreeCloner::visit(const node::Identifier &identifier) {
  child_ = std::make_shared<node::Identifier>(identifier);
}

void TreeCloner::visit(const node::String &string) {
  child_ = std::make_shared<node::String>(string);
}

void TreeCloner::visit(const node::Program &program) {
  program.expression()->accept(*this);
  child_ = std::make_shared<node::Program>(child_);
}

void TreeCloner::visit(const node::Argument &argument) {
  argument.identifier()->accept(*this);
  auto ident = std::static_pointer_cast<Identifier>(child_);
  if(argument.expression() != nullptr) {
    argument.expression()->accept(*this);
    child_ = std::make_shared<Argument>(ident, child_);
  } else {
    child_ = std::make_shared<Argument>(ident);
  }
}

void TreeCloner::visit(const node::Function &function) {
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

void TreeCloner::visit(const node::Label &label) {
  label.expression()->accept(*this);
  auto expression = std::static_pointer_cast<Node>(child_);
  child_ = std::make_shared<node::Label>(label.name(), expression);
}

void TreeCloner::visit(const node::Application &application) {
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

void TreeCloner::visit(const node::Conditional &conditional) {
  conditional.expression()->accept(*this);
  auto expression = child_;
  conditional.true_block()->accept(*this);
  auto true_block = std::static_pointer_cast<Program>(child_);
  conditional.false_block()->accept(*this);
  auto false_block = std::static_pointer_cast<Program>(child_);
  child_ = std::make_shared<Conditional>(expression, true_block, false_block);
}

void TreeCloner::visit(const node::Operation &operation) {
  operation.left()->accept(*this);
  auto left = child_;
  operation.right()->accept(*this);
  auto right = child_;
  child_ = std::make_shared<Operation>(left, right, operation.operation());
}

void TreeCloner::visit(const node::Declaration &declaration) {
  declaration.identifier()->accept(*this);
  auto ident = std::static_pointer_cast<Identifier>(child_);
  declaration.value()->accept(*this);
  auto value = child_;
  declaration.expression()->accept(*this);
  auto expr = child_;
  child_ = std::make_shared<Declaration>(ident, value, expr);
}
