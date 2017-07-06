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
// this should be more like:
// http://www.cs.cornell.edu/courses/cs3110/2016fa/l/17-inference/notes.html
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
  if(!assumptions_.insert({identifier.value(), identifier.type()}).second) {
    constraints_.insert(Constraint(Relation::Implicit, {
      identifier.type(),
      assumptions_.find(identifier.value())->second
    }, monomorphic_));
  };
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
  if(argument.expression() == nullptr) return;
  argument.expression()->accept(*this);
  constraints_.insert(Constraint(Relation::Equality, {
    argument.identifier()->type(),
    argument.expression()->type()
  }));
}

void TypingVisitor::visit(const Function &function) {
  auto assumptions = assumptions_;
  auto monomorphic = monomorphic_;
  for(auto a : *function.arguments())
    assumptions_.erase(a->identifier()->value());
  util::list_accept(function.arguments(), *this);
  function.program()->accept(*this);
  constraints_.insert(Constraint(Relation::Equality, {
    function.type().get<FunctionType>().ret(),
    function.program()->type()
  }));
  monomorphic_ = monomorphic;
  assumptions_ = assumptions;
}

void TypingVisitor::visit(const Application &application) {
  application.identifier()->accept(*this);
  util::list_accept(application.arguments(), *this);
}

void TypingVisitor::visit(const Conditional &conditional) {
  constraints_.insert(Constraint(Relation::Equality, {
    conditional.true_type(),
    conditional.false_type()
  }));
  constraints_.insert(Constraint(Relation::Equality, {
    conditional.expression()->type(),
    BoolType()
  }));
  conditional.expression()->accept(*this);
  conditional.true_block()->accept(*this);
  conditional.false_block()->accept(*this);
}

void TypingVisitor::visit(const Operation &operation) {
  constraints_.insert(Constraint(Relation::Equality, {
    operation.left()->type(),
    NumberType()
  }));
  constraints_.insert(Constraint(Relation::Equality, {
    operation.right()->type(),
    NumberType()
  }));
  operation.left()->accept(*this);
  operation.right()->accept(*this);
}

void TypingVisitor::visit(const Declaration &declaration) {
  assumptions_.erase(declaration.identifier()->value());
  constraints_.insert(Constraint(Relation::Implicit, {
    declaration.identifier()->type(),
    declaration.expression()->type()
  }, monomorphic_));
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
    for(TypeVariable m : monomorphic_) {
      Type n = TypeVariable(m.id());
      Type v = s(n);
      if(v.is<TypeVariable>()) {
        tmp.insert(v.get<TypeVariable>());
      } else {
        tmp.insert(m);
      }
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
    working_set.erase(working_set.begin());
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
      auto fvars = freevars(it.variables().second);
      auto mono = it.monomorphic();
      fvars.erase(mono.begin(), mono.end());
      std::set<TypeVariable> all;
      for(auto c : working_set) {
        auto v = c.activevars();
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
        working_set.insert(it);
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
