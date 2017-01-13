#include "typing_visitor.hh"
using namespace goat;
using namespace goat::inference;

void TypingVisitor::visit(const node::Number &number) {

}

void TypingVisitor::visit(const node::Identifier &identifier) {

}

void TypingVisitor::visit(const node::String &string) {

}

void TypingVisitor::visit(const node::Program &program) {

}

void TypingVisitor::visit(const node::Argument &argument) {
  monomorphic_.insert(argument.type());
}

void TypingVisitor::visit(const node::Function &function) {
  auto before = monomorphic_;

  monomorphic_ = before;
}

void TypingVisitor::visit(const node::Application &application) {

}

void TypingVisitor::visit(const node::Conditional &conditional) {

}

void TypingVisitor::visit(const node::Operation &operation) {

}

void TypingVisitor::visit(const node::Declaration &declaration) {

}
