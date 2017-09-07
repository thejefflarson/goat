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

std::shared_ptr<node::Program> Inferer::infer(std::shared_ptr<node::Program> program) {
  return clone(program);
}

void Inferer::visit(const Identifier &identifier) {
  assert(scope_.fi-nd(identifier.internal_value()) != scope_.end());
  auto type = scope_.find(identifier.internal_value())->second;
  assert(type.is<TypeVariable>());
  child_ = std::make_shared<node::Identifier>(
    identifier.value(),
    identifier.internal_value(),
    type
  );
}

void Inferer::visit(const Argument &argument) {
  argument.identifier()->accept(*this);
  auto ident = std::static_pointer_cast<Identifier>(child_);
  if(*argument.expression() == EmptyExpression()) {
    child_ = std::make_shared<Argument>(ident);
    return;
  }
  argument.expression()->accept(*this);
  auto expression = child_;
  constraints_.insert(Constraint({
    argument.identifier()->type(),
    argument.expression()->type()
  }));
  child_ = std::make_shared<Argument>(ident, expression);
}

void Inferer::visit(const Function &function) {
  auto args = std::make_shared<ArgumentList>();
  auto types = std::vector<Type>();
  for(auto argument : *function.arguments()) {
    auto var = argument->identifier()->internal_value();
    scope_[var] = TypeVariable(namer_.next());
    types.push_back(scope_[var]);
    argument->accept(*this);
    args->push_back(std::static_pointer_cast<Argument>(child_));
  }

  function.program()->accept(*this);
  auto program = std::static_pointer_cast<Program>(child_);
  Type ret = TypeVariable(namer_.next());
  types.push_back(ret);
  constraints_.insert(Constraint({
    ret,
    program->type()
  }));

  child_ = std::make_shared<Function>(args, program, FunctionType(types));
}

void Inferer::visit(const Application &application) {
  auto args = std::make_shared<ArgumentList>();
  application.identifier()->accept(*this);
  auto ident = std::static_pointer_cast<Identifier>(child_);
  auto types = std::vector<Type>();
  for(auto argument : *application.arguments()) {
    argument->accept(*this);
    auto arg = std::static_pointer_cast<Argument>(child_);
    auto type = arg->type();
    types.push_back(type);
    args->push_back(arg);
  }

  types.push_back(TypeVariable(namer_.next()));
  Type type = FunctionType(types);
  constraints_.insert(Constraint({
    ident->type(),
    type
  }));

  child_ = std::make_shared<Application>(ident, args, type);
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
  auto expr = child_;
  conditional.true_block()->accept(*this);
  auto true_block = child_;
  conditional.false_block()->accept(*this);
  auto false_block = child_;

  child_ = std::make_shared<Conditional>(
    expr,
    std::static_pointer_cast<Program>(true_block),
    std::static_pointer_cast<Program>(false_block)
  );
}

void Inferer::visit(const Operation &operation) {
  operation.left()->accept(*this);
  auto left = child_;
  constraints_.insert(Constraint({
    left->type(),
    NumberType()
  }));

  operation.right()->accept(*this);
  auto right = child_;
  constraints_.insert(Constraint({
    right->type(),
    NumberType()
  }));

  child_ = std::make_shared<Operation>(left, right, operation.operation());
}

void Inferer::visit(const Declaration &declaration) {
  scope_[declaration.identifier()->internal_value()] = TypeVariable(namer_.next());
  declaration.identifier()->accept(*this);
  auto ident = child_;
  declaration.expression()->accept(*this);
  auto expr = child_;

  constraints_.insert(Constraint({
    ident->type(),
    expr->type()
  }));

  child_ = std::make_shared<Declaration>(
    std::static_pointer_cast<Identifier>(ident),
    expr
  );
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

std::set<Substitution> Constraint::unify(std::set<Constraint> constraints) {
  auto c = constraints.begin();
  if(c == constraints.end())
    return {};
  auto constraint = *c;
  constraints.erase(c);
  auto vars = constraint.variables_;
  Type t = vars.first;
  Type tq = vars.second;

  if(t == tq)
    return unify(constraints);

  if(t.is<TypeVariable>()) {
    if(!t.get<TypeVariable>().occurs(tq)) {
      auto subs = Substitution(t, tq);
      std::set<Constraint> consts;
      for (auto c : constraints) {
        consts.insert(Constraint({
          subs(c.variables_.first),
          subs(c.variables_.second)
        }));
      }
      std::set<Substitution> substitutions = unify(consts);
      substitutions.insert(subs);
      return substitutions;
    }
  }

  if(tq.is<TypeVariable>()) {
    constraints.insert(Constraint({tq, t}));
    return unify(constraints);
  }

  if(t.is<FunctionType>() && tq.is<FunctionType>()) {
    auto tf = t.get<FunctionType>();
    auto tqf = tq.get<FunctionType>();
    if(tf.types().size() != tqf.types().size()) {
      return {Substitution::error()};
    }
    auto tqfiter = tqf.types().begin();
    for(auto tfiter = tf.types().begin();
        tfiter != tf.types().end();
        tfiter++, tqfiter++) {
      constraints.insert(Constraint({*tfiter, *tqfiter}));
    }
    return unify(constraints);
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
  return Constraint::unify(constraints_);
}
