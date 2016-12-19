#include "typing_visitor.hh"

using namespace goat;
using namespace goat::node;
using namespace goat::inference;

void TypingVisitor::visit(const Number &number) {

}

void TypingVisitor::visit(const Identifier &identifier) {

}

void TypingVisitor::visit(const String &string) {

}

void TypingVisitor::visit(const Program &program) {

}

void TypingVisitor::visit(const Argument &argument) {
  monomorphic_.insert(argument.type());
}

void TypingVisitor::visit(const Function &function) {
  auto before = monomorphic_;
  list_accept(function.arguments(), *this);
  function.program()->accept(*this);
  monomorphic_ = before;
}

void TypingVisitor::visit(const Application &application) {

}

void TypingVisitor::visit(const Conditional &conditional) {

}

void TypingVisitor::visit(const Operation &operation) {

}

void TypingVisitor::visit(const Declaration &declaration) {

}
