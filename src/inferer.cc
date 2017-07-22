#include <algorithm>
#include <cassert>
#include <cstdint>
#include <memory>
#include <string>
#include <type_traits>

#include "inferer.hh"
#include "node.hh"
#include "util.hh"

using namespace goat;
using namespace goat::inference;
using namespace goat::node;
// this should be more like:
// http://www.cs.cornell.edu/courses/cs3110/2016fa/l/17-inference/notes.html

void Inferer::visit(const Number &number) {

}

void Inferer::visit(const Identifier &identifier) {
// TODO: think hard about scoping rules.
//  constraints_.insert(Constraint({
//    identifier.type(),
//    scope_.find(identifier.value())->second
//  }));
}

void Inferer::visit(const String &string) {

}

void Inferer::visit(const Program &program) {
  node::list_accept(program.nodes(), *this);
}

void Inferer::visit(const Argument &argument) {
  assert(argument.type().is<TypeVariable>());
  argument.identifier()->accept(*this);
  if(argument.expression() == nullptr) return;
  argument.expression()->accept(*this);
  constraints_.insert(Constraint({
    argument.identifier()->type(),
    argument.expression()->type()
  }));
}

void Inferer::visit(const Function &function) {
  node::list_accept(function.arguments(), *this);
  function.program()->accept(*this);
  constraints_.insert(Constraint({
    function.type().get<FunctionType>().ret(),
    function.program()->type()
  }));
}

void Inferer::visit(const Application &application) {
  application.identifier()->accept(*this);
  node::list_accept(application.arguments(), *this);
}

void Inferer::visit(const Conditional &conditional) {
  constraints_.insert(Constraint({
    conditional.true_type(),
    conditional.false_type()
  }));
  constraints_.insert(Constraint({
    conditional.expression()->type(),
    BoolType()
  }));
  conditional.expression()->accept(*this);
  conditional.true_block()->accept(*this);
  conditional.false_block()->accept(*this);
}

void Inferer::visit(const Operation &operation) {
  constraints_.insert(Constraint({
    operation.left()->type(),
    NumberType()
  }));
  constraints_.insert(Constraint({
    operation.right()->type(),
    NumberType()
  }));
  operation.left()->accept(*this);
  operation.right()->accept(*this);
}

void Inferer::visit(const Declaration &declaration) {
  constraints_.insert(Constraint({
    declaration.identifier()->type(),
    declaration.expression()->type()
  }));
  declaration.identifier()->accept(*this);
  declaration.expression()->accept(*this);
}

Constraint Constraint::apply(Substitution s) const {
  auto left = s(variables_.first);
  auto right = s(variables_.second);
  return Constraint({left, right});
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
    return Constraint({t, s}).unify();
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
      auto constraint = Constraint({*sitter, *ttiter});
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
  std::set<TypeVariable> ret;
  ret.insert(left.begin(), left.end());
  ret.insert(right.begin(), right.end());
  return ret;
}

std::set<Substitution> Inferer::solve() {
  std::set<Substitution> ret;
  auto working_set = constraints_;
  while(!working_set.empty()) {
    auto it = *working_set.begin();
    working_set.erase(working_set.begin());
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
  }
  auto error = Substitution::error();
  if(ret.find(error) != ret.end()) {
    return {error};
  }
  return ret;
}
