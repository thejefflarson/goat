#include <cassert>
#include <cstdint>
#include <memory>
#include <string>
#include <type_traits>

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

bool occurs(TypeVariable t, Type in) {
  if(in.is<TypeVariable>()) {
    return t == in.get<TypeVariable>();
  } else if(in.is<NumberType>()
            || in.is<StringType>()
            || in.is<BoolType>()
            || in.is<NoType>()) {
    return false;
  } else if(in.is<FunctionType>()) {
    auto f = in.get<FunctionType>();
    bool accum = true;
    for(auto v : f.types()) {
      accum = accum && occurs(t, v);
    }
    return accum;
  } else {
    return false; // TODO: report compiler error
  }
}

std::set<Substitution> unify(Constraint& relation) {
  auto vars = relation.variables();
  Type s = vars.first;
  Type t = vars.second;
  auto err = Substitution(TypeVariable("error"));

  if(s == t)
    return std::set<Substitution>();

  if(s.is<TypeVariable>() && !t.is<TypeVariable>()) {
    auto c = Constraint(Relation::Equality, {t, s});
    return unify(c);
  }

  if(s.is<FunctionType>() && t.is<FunctionType>()) {
    std::set<Substitution> ret;
    const FunctionType &st = s.get<FunctionType>();
    const FunctionType &tt = t.get<FunctionType>();
    if(st.types().size() != tt.types().size()) {
      ret.insert(err);
      return ret;
    }
    auto ttiter = tt.types().begin();
    for(auto sitter = st.types().begin(); sitter != st.types().end(); sitter++) {
      auto constraint = Constraint(Relation::Equality, {*sitter, *ttiter});
      auto result = unify(constraint);
      ret.insert(result.begin(), result.end());
      ttiter++;
    }
    return ret;
  }

  // occurs check / eliminate rule
  return {err};
}

std::set<Substitution> TypingVisitor::solve() {
  std::set<Substitution> ret;
  auto working_set = constraints_;
  for(auto it : working_set) {
    switch(it.relation()) {
    case Relation::Equality: {
      auto unified = unify(it);
      ret.insert(unified.begin(), unified.end());
      break;
    }
    case Relation::Explicit:
      break;
    case Relation::Implicit:
      break;
    }
  }
  auto error = Substitution(TypeVariable("error"));
  if(ret.find(error) != ret.end()) {
    auto err = std::set<Substitution>();
    err.insert(error);
    return err;
  }
  return ret;
}
