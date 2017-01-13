#include "inference.hh"
#include "util.hh"
#include <memory>
#include <string>

using namespace goat;
using namespace goat::inference;
using namespace goat::node;

bool Type::equals(const TypeNode &b) const {
  const Type *c = static_cast<const Type *>(&b);
  return id_ == c->id_;
}

bool FunctionType::equals(const TypeNode &b) const {
  const FunctionType *c = static_cast<const FunctionType *>(&b);
  return ret_ == c->ret_ &&
    util::compare_vector_pointers(&in_, &c->in_);
}

std::string alpha = "abcdefghijklmnopqrstuvwxyz";
Type TypeFactory::next() {
  last_++;
  uint32_t current = last_;
  std::string accum;
  while(current > 0) {
    uint8_t index = current % alpha.length();
    accum.push_back(alpha[index]);
    current /= alpha.length();
  }
  return Type(accum);
}

void TypingVisitor::visit(const Number &number) {

}

void TypingVisitor::visit(const Identifier &identifier) {
  assumptions_.insert(identifier);
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
  constraints_.insert(Constraint(Equality,
                                 { std::make_unique<Type>(application.ident()->type()),
                                   std::make_unique<Type>(application.type()) }));
}

void TypingVisitor::visit(const Conditional &conditional) {

}


void TypingVisitor::visit(const Operation &operation) {

}

void TypingVisitor::visit(const Declaration &declaration) {

}
