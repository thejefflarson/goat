#include <algorithm>
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
  assert(argument.type().is<TypeVariable>());
  monomorphic_.insert(argument.type().get<TypeVariable>());
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

  constraints_.insert(Constraint(Relation::Equality, {
    function.type().get<FunctionType>().ret(),
    function.program()->type()
   }));
}

void TypingVisitor::visit(const Application &application) {
  auto maybe_type = assumptions_.find(application.identifier()->value());
  assert(maybe_type != assumptions_.end());

  constraints_.insert(Constraint(Relation::Equality,
                                 { application.type(),
                                     maybe_type->second }));
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
  auto expr = declaration.expression().get();
  auto type = expr->type();
  if(typeid(*expr) == typeid(Identifier)) {
    auto it = dynamic_cast<Identifier *>(expr);
    if(assumptions_.find(it->value()) != assumptions_.end())
      type = assumptions_.find(it->value())->second;
  }

  constraints_.insert(Constraint(Relation::Implicit,
                                  { declaration.identifier()->type(),
                                      type },
                                  monomorphic_));

  declaration.identifier()->accept(*this);
  declaration.expression()->accept(*this);
}

Constraint Constraint::apply(Substitution s) const {
  auto left = s(variables_.first);
  auto right = s(variables_.second);
  if (monomorphic_.empty()) {
    return Constraint(relation_, {left, right});
  } else {
    auto tmp = std::set<TypeVariable>();
    for(auto m : monomorphic_) {
      tmp.insert(s(TypeVariable(m)).get<TypeVariable>());
    }
    return Constraint(relation_, {left, right}, tmp);
  }
}

bool TypeVariable::occurs(Type in) const {
  if(in.is<TypeVariable>()) {
    return *this == in.get<TypeVariable>();
  } else if(in.is<NumberType>()
            || in.is<StringType>()
            || in.is<BoolType>()
            || in.is<NoType>()) {
    return false;
  } else if(in.is<FunctionType>()) {
    auto f = in.get<FunctionType>();
    bool accum = true;
    for(auto v : f.types()) {
      accum = accum && this->occurs(v);
    }
    return accum;
  } else {
    return false; // TODO: report compiler error
  }
}

Type Substitution::operator()(Type in) const {
  if(s_ == in) {
    return t_;
  } else if(in.is<FunctionType>()) {
    std::vector<Type> args;
    auto fn = in.get<FunctionType>();
    for(auto v : fn.types()) {
      if(Type(s_) != v) {
        args.push_back(v);
      } else {
        args.push_back(Substitution(s_, t_)(v));
      }
    }

    return FunctionType(args);
  } else {
    return in;
  }
}

std::set<Substitution> Constraint::unify() const {
  auto vars = variables_;
  Type s = vars.first;
  Type t = vars.second;

  // Delete rule
  if(s == t)
    return {};

  // Orient rule
  if(!s.is<TypeVariable>() && t.is<TypeVariable>()) {
    return Constraint(Relation::Equality, {t, s}).unify();
  }

  // Decompose rule
  if(s.is<FunctionType>() && t.is<FunctionType>()) {
    std::set<Substitution> ret;
    const FunctionType &st = s.get<FunctionType>();
    const FunctionType &tt = t.get<FunctionType>();
    if(st.types().size() != tt.types().size()) {
      ret.insert(Substitution::error());
      return ret;
    }
    auto ttiter = tt.types().begin();
    for(auto sitter = st.types().begin(); sitter != st.types().end(); sitter++) {
      auto constraint = Constraint(Relation::Equality, {*sitter, *ttiter});
      auto result = constraint.unify();
      ret.insert(result.begin(), result.end());
      ttiter++;
    }
    return ret;
  }

  // Eliminate rule
  if(s.is<TypeVariable>()) {
    auto var = s.get<TypeVariable>();
    if(!var.occurs(t)) {
      return {Substitution(s, t)};
    }
  }
  std::cout << "Error!" << std::endl;
  return {Substitution::error()};
}

std::set<TypeVariable> freevars(Type in) {
  if(in.is<TypeVariable>()) {
    return {in.get<TypeVariable>()};
  } else if(in.is<FunctionType>()){
    std::set<TypeVariable> ret;
    for(auto t : in.get<FunctionType>().types()) {
      auto vars = freevars(in);
      ret.insert(vars.begin(), vars.end());
    }
    return ret;
  } else {
    return {};
  }
}

std::set<TypeVariable> Constraint::activevars() const {
  auto left = freevars(variables_.first);
  auto right = freevars(variables_.second);
  if(relation_ == Relation::Explicit) {
    right.erase(monomorphic_.begin(), monomorphic_.end());
  }
  std::set<TypeVariable> ret;
  ret.insert(left.begin(), left.end());
  ret.insert(right.begin(), right.end());
  return ret;
}

std::set<Substitution> TypingVisitor::solve() {
  std::set<Substitution> ret;
  auto working_set = constraints_;
  while(!working_set.empty()) {
    auto it = *working_set.begin();
    working_set.erase(it);

    switch(it.relation()) {
    case Relation::Equality: {
      auto unified = it.unify();
      if(unified.size() > 0) {
        std::set<Constraint> tmp;
        for(auto c : working_set) {
          for(auto s : unified) {
            tmp.insert(c.apply(s));
          }
        }
        working_set = tmp;
        for(auto s : unified)
          ret.insert(s);
      }
      break;
    }
    case Relation::Explicit: {
      std::set<TypeVariable> fvars = freevars(it.variables().second);
      std::set<TypeVariable> mono = it.monomorphic();
      fvars.erase(mono.begin(), mono.end());
      std::set<TypeVariable> all;
      for(auto c : working_set) {
        std::set<TypeVariable> v = c.activevars();
        all.insert(v.begin(), v.end());
      }
      std::set<TypeVariable> intxs;
      std::set_intersection(fvars.begin(), fvars.end(),
                            all.begin(), all.end(),
                            std::inserter(intxs, intxs.end()));
      if(intxs.size() == 0) {
        auto cons = Constraint(Relation::Implicit, it.variables());
        working_set.insert(cons);
      } else {
        fvars = freevars(it.variables().second);
        mono.erase(fvars.begin(), fvars.end());
        working_set.insert(Constraint(Relation::Explicit, it.variables(), mono));
      }
      break;
    }
    case Relation::Implicit:
      working_set.insert(Constraint(Relation::Equality, it.variables()));
      break;
    }
  }
  auto error = Substitution::error();
  if(ret.find(error) != ret.end()) {
    return {error};
  }
  return ret;
}
