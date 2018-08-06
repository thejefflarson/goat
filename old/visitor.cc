#include <memory>

#include "node.hh"
#include "visitor.hh"

using namespace goat::node;

void Visitor::visit(const EmptyExpression &empty) {

}

void Visitor::visit(const Number &number) {

}

void Visitor::visit(const Identifier &identifier) {

}

void Visitor::visit(const String &string) {

}

void Visitor::visit(const Program &program) {
  program.expression()->accept(*this);
}

void Visitor::visit(const Argument &argument) {
  argument.identifier()->accept(*this);
  if(argument.expression() != nullptr) {
    argument.expression()->accept(*this);
  }
}

void Visitor::visit(const Function &function) {
  for(auto a : *function.arguments()) {
    a->accept(*this);
  }
  function.program()->accept(*this);
}

void Visitor::visit(const Label &label) {
  label.expression()->accept(*this);
}

void Visitor::visit(const Application &application) {
  application.identifier()->accept(*this);

  for(auto l : *application.labels()) {
    l.second->accept(*this);
  }
}

void Visitor::visit(const Conditional &conditional) {
  conditional.expression()->accept(*this);
  conditional.true_block()->accept(*this);
  conditional.false_block()->accept(*this);
}

void Visitor::visit(const Operation &operation) {
  operation.left()->accept(*this);
  operation.right()->accept(*this);
}

void Visitor::visit(const Declaration &declaration) {
  declaration.identifier()->accept(*this);
  declaration.value()->accept(*this);
  declaration.expression()->accept(*this);
}



std::shared_ptr<Program> TreeCloner::clone(std::shared_ptr<Program> program) {
  program->accept(*this);
  return std::static_pointer_cast<Program>(child_);
}

void TreeCloner::visit(const EmptyExpression &empty) {
  child_ = std::make_shared<EmptyExpression>();
}

void TreeCloner::visit(const Number &number) {
  child_ = std::make_shared<Number>(number);
}

void TreeCloner::visit(const Identifier &identifier) {
  child_ = std::make_shared<Identifier>(identifier);
}

void TreeCloner::visit(const String &string) {
  child_ = std::make_shared<String>(string);
}

void TreeCloner::visit(const Program &program) {
  program.expression()->accept(*this);
  child_ = std::make_shared<Program>(child_);
}

void TreeCloner::visit(const Argument &argument) {
  argument.identifier()->accept(*this);
  auto ident = std::static_pointer_cast<Identifier>(child_);
  if(argument.expression() != nullptr) {
    argument.expression()->accept(*this);
    child_ = std::make_shared<Argument>(ident, child_);
  } else {
    child_ = std::make_shared<Argument>(ident);
  }
}

void TreeCloner::visit(const Function &function) {
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

void TreeCloner::visit(const Label &label) {
  label.expression()->accept(*this);
  auto expression = std::static_pointer_cast<Node>(child_);
  child_ = std::make_shared<Label>(label.name(), expression);
}

void TreeCloner::visit(const Application &application) {
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

void TreeCloner::visit(const Conditional &conditional) {
  conditional.expression()->accept(*this);
  auto expression = child_;
  conditional.true_block()->accept(*this);
  auto true_block = std::static_pointer_cast<Program>(child_);
  conditional.false_block()->accept(*this);
  auto false_block = std::static_pointer_cast<Program>(child_);
  child_ = std::make_shared<Conditional>(expression, true_block, false_block);
}

void TreeCloner::visit(const Operation &operation) {
  operation.left()->accept(*this);
  auto left = child_;
  operation.right()->accept(*this);
  auto right = child_;
  child_ = std::make_shared<Operation>(left, right, operation.operation());
}

void TreeCloner::visit(const Declaration &declaration) {
  declaration.identifier()->accept(*this);
  auto ident = std::static_pointer_cast<Identifier>(child_);
  declaration.value()->accept(*this);
  auto value = child_;
  declaration.expression()->accept(*this);
  auto expr = child_;
  child_ = std::make_shared<Declaration>(ident, value, expr);
}
