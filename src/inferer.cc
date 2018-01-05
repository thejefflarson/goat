#include <algorithm>
#include <cstdint>
#include <memory>
#include <string>
#include <type_traits>
#include <variant>

#include <gsl/gsl>

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
  Expects(scope_.find(identifier.internal_value()) != scope_.end());
  auto type = scope_.find(identifier.internal_value())->second;
  Expects(std::holds_alternative<TypeVariable>(type));
  child_ = std::make_shared<node::Identifier>(
    identifier.value(),
    identifier.internal_value(),
    type
  );
}

void Inferer::visit(const Argument &argument) {
  argument.identifier()->accept(*this);
  auto identifier = std::static_pointer_cast<Identifier>(child_);
  if(*argument.expression() == EmptyExpression()) {
    child_ = std::make_shared<Argument>(identifier);
    return;
  }
  argument.expression()->accept(*this);
  auto expression = child_;

  constraints_.insert(Constraint({
    identifier->type(),
    expression->type()
  }));
  child_ = std::make_shared<Argument>(identifier, expression);
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
  auto args = std::make_shared<Labels>();
  application.identifier()->accept(*this);
  auto ident = std::static_pointer_cast<Identifier>(child_);
  auto types = std::vector<Type>();
  for(auto l : *application.labels()) {
    l.second->accept(*this);
    auto arg = std::static_pointer_cast<Label>(child_);
    auto type = arg->type();
    types.push_back(type);
    args->insert({arg->name(), arg});
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
  declaration.value()->accept(*this);
  auto value = child_;

  constraints_.insert(Constraint({
    ident->type(),
    value->type()
  }));

  declaration.expression()->accept(*this);
  auto expr = child_;

  child_ = std::make_shared<Declaration>(
    std::static_pointer_cast<Identifier>(ident),
    value,
    expr
  );
}

Constraint Constraint::apply(Substitution s) const {
  auto left = s(variables_.first);
  auto right = s(variables_.second);
  return Constraint({left, right});
}

bool TypeVariable::occurs(Type in) const {
  return std::visit([this](auto&& arg) {
      using T = std::decay_t<decltype(arg)>;
      if constexpr (std::is_same_v<T, TypeVariable>) {
        return *this = arg;
      } else if constexpr (
        std::is_same_v<T, NumberType>
        || std::is_same_v<T, StringType>
        || std::is_same_v<T, BoolType>
        || std::is_same_v<T, NoType>
      ) {
        return false;
      } else if constexpr (std::is_same_v<T, FunctionType>) {
        bool accum = false;
          for(auto v : arg.types()) {
            accum = accum || this->occurs(v);
          }
          return accum;
      } else {
        return false;
      }
    }, in);
}

Type Substitution::operator()(Type in) const {
  if(s_ == in) {
    return t_;
  } else if(std::holds_alternative<FunctionType>(in)) {
    std::vector<Type> args;
    auto fn = std::get<FunctionType>(in);
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

  if(std::holds_altertive<TypeVariable>(tq)) {
    constraints.insert(Constraint({tq, t}));
    return unify(constraints);
  }

  if(std::hold_alternative<TypeVariable>(t)) {
    if(!t.get<TypeVariable>().occurs(tq)) {
      auto subs = Substitution(t, tq);
      std::set<Constraint> consts;
      for (auto c : constraints) {
        consts.insert(c.apply(subs));
      }
      std::set<Substitution> substitutions = unify(consts);
      substitutions.insert(subs);
      return substitutions;
    }
  }

  if(std::holds_alternative<FunctionType>(t) && std::holds_alternative<FunctionType>(tq)) {
    auto tf = std::get<FunctionType>(t);
    auto tqf = std::get<FunctionType>(tq);
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
  if(std::holds_alternative<TypeVariable>(in)) {
    return {std::get<TypeVariable>(in)};
  } else if(std::holds_alternative<FunctionType>(in)){
    std::set<TypeVariable> ret;
    for(auto t : std::get<FunctionType>(in).types()) {
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
