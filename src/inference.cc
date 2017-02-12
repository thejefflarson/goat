#include <cassert>
#include <cstdint>
#include <memory>
#include <string>

#include "inference.hh"
#include "node.hh"
#include "util.hh"

using namespace goat;
using namespace goat::inference;
using namespace goat::node;

std::string alpha = "abcdefghijklmnopqrstuvwxyz";
TypeVariable TypeFactory::next() {
  last_++;
  uint32_t current = last_;
  std::string accum;
  while(current > 0) {
    uint8_t index = current % alpha.length();
    accum.push_back(alpha[index]);
    current /= alpha.length();
  }
  return TypeVariable(accum);
}

void TypingVisitor::visit(const Number &number) {

}

void TypingVisitor::visit(const Identifier &identifier) {
  assumptions_.insert({identifier.value(), identifier.type()});
}

void TypingVisitor::visit(const String &string) {

}

void TypingVisitor::visit(const Program &program) {

}

void TypingVisitor::visit(const Argument &argument) {
  assert(argument.type().is<inference::TypeVariable>());
  monomorphic_.insert(argument.type());
}

void TypingVisitor::visit(const Function &function) {
  auto before = monomorphic_;
  util::list_accept(function.arguments(), *this);
  function.program()->accept(*this);
  monomorphic_ = before;
}

void TypingVisitor::visit(const Application &application) {
  for(auto i : *application.arguments()) {
    i->accept(*this);
  }
  constraints_.insert(Constraint(Equality,
                                 { application.identifier()->type(),
                                     application.type() }));
}

void TypingVisitor::visit(const Conditional &conditional) {

}


void TypingVisitor::visit(const Operation &operation) {

}

void TypingVisitor::visit(const Declaration &declaration) {

}
