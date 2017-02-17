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
  if(last_ == 0){ last_++; return TypeVariable("a"); }
  uint32_t current = last_;
  std::string accum;
  while(current > 0) {
    uint8_t index = current % alpha.length();
    accum.push_back(alpha[index]);
    current /= alpha.length();
  }
  last_++;
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
  util::list_accept(program.nodes(), *this);
}

void TypingVisitor::visit(const Argument &argument) {
  monomorphic_.insert(argument.type());
  argument.identifier()->accept(*this);
  argument.expression()->accept(*this);
}

void TypingVisitor::visit(const Function &function) {
  auto before = monomorphic_;
  util::list_accept(function.arguments(), *this);
  function.program()->accept(*this);
  monomorphic_ = before;

  for(auto i : *function.arguments()) {
    std::shared_ptr<Identifier> ident = i->identifier();
    if(assumptions_.find(ident->value()) == assumptions_.end()) std::cout << "uhoh" << std::endl;
    Type var = assumptions_.find(ident->value())->second;
    constraints_.insert(Constraint(Relation::Equality, { ident->type(), var }));
    assumptions_.erase(ident->value());
  }
}

void TypingVisitor::visit(const Application &application) {
  // invariant: this needs to be a function type.
  assert(application.type().is<inference::FunctionType>());
  inference::FunctionType type = application.type().get<inference::FunctionType>();
  // invariant: these need to be the same size.
  assert(application.arguments()->size() == type.types().size());

  size_t j = 0;
  for(auto i : *application.arguments()) {
    constraints_.insert(Constraint(Relation::Equality,
                                   { type.types().at(j),
                                       i->type() }));
    j++;
  }
  auto t = constraints_.insert(Constraint(Relation::Equality,
                                 { application.identifier()->type(),
                                     application.type() }));
  std::cout << t.second << std::endl;
  std::cout << constraints_.size() << std::endl;
  util::list_accept(application.arguments(), *this);
}

void TypingVisitor::visit(const Conditional &conditional) {
  constraints_.insert(Constraint(Relation::Equality,
                                 { conditional.true_type(),
                                     conditional.false_type()}));
  conditional.expression()->accept(*this);
  conditional.true_block()->accept(*this);
  conditional.false_block()->accept(*this);
}


void TypingVisitor::visit(const Operation &operation) {
  operation.left()->accept(*this);
  operation.right()->accept(*this);
}

void TypingVisitor::visit(const Declaration &declaration) {
  constraints_.insert(Constraint(Relation::Implicit,
                                  { declaration.identifier()->type(),
                                      declaration.expression()->type() },
                                  monomorphic_));

  declaration.identifier()->accept(*this);
  if(declaration.expression()) declaration.expression()->accept(*this);
}
