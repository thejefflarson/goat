#include "freevars.hh"
#include "node.hh"

using namespace goat::node;
using namespace goat::lifter;

void FreeVars::visit(const node::EmptyExpression &empty) {

}

void FreeVars::visit(const node::Number &number) {

}

void FreeVars::visit(const node::Identifier &identifier) {

}

void FreeVars::visit(const node::String &string) {

}

void FreeVars::visit(const node::Program &program) {
  program.expression()->accept(*this);
}

void FreeVars::visit(const node::Argument &argument) {
  argument.identifier()->accept(*this);
  if(argument.expression() != nullptr) {
    argument.expression()->accept(*this);
  }
}

void FreeVars::visit(const node::Function &function) {
  for(auto a : *function.arguments()) {
    a->accept(*this);
  }
  function.program()->accept(*this);
}

void FreeVars::visit(const node::Label &label) {
  label.expression()->accept(*this);
}

void FreeVars::visit(const node::Application &application) {
  application.identifier()->accept(*this);

  for(auto l : *application.labels()) {
    l.second->accept(*this);
  }
}

void FreeVars::visit(const node::Conditional &conditional) {
  conditional.expression()->accept(*this);
  conditional.true_block()->accept(*this);
  conditional.false_block()->accept(*this);
}

void FreeVars::visit(const node::Operation &operation) {
  operation.left()->accept(*this);
  operation.right()->accept(*this);
}

void FreeVars::visit(const node::Declaration &declaration) {
  declaration.identifier()->accept(*this);
  declaration.value()->accept(*this);
  declaration.expression()->accept(*this);
}
