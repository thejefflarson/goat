#include <algorithm>
#include <vector>
#include "node.hh"
#include "util.hh"
#include "visitor.hh"
#include "util.hh"

namespace goat {
namespace node {

#define accept(kls)                    \
  void kls::accept(Visitor &v) const { \
    v.visit(*this);                    \
  }

accept(EmptyExpression)
accept(Number)
accept(Identifier)
accept(String)
accept(Program)
accept(Function)
accept(Label)
accept(Application)
accept(Conditional)
accept(Operation)
accept(Declaration)
accept(Argument)

template<typename T>
inline bool string_equals(const T *a, const Node &b) {
  const T *c = static_cast<const T *>(&b);
  return a->value().compare(c->value()) == 0;
}

bool String::equals(const Node &b) const {
  return string_equals(this, b);
}

bool Identifier::equals(const Node &b) const {
  const Identifier *c = static_cast<const Identifier *>(&b);
  return string_equals(this, b) &&
    internal_value_ == c->internal_value_;
}

bool Number::equals(const Node &b) const {
  const Number *c = static_cast<const Number *>(&b);
  return value_ == c->value_;
}

bool Program::equals(const Node &b) const {
  const Program *c = static_cast<const Program *>(&b);
  return *expression_ == *c->expression_;
}

bool Argument::equals(const Node &b) const {
  const Argument *c = static_cast<const Argument *>(&b);
  return *identifier_ == *c->identifier_ &&
    *expression_ == *c->expression_;
}

bool Function::equals(const Node &b) const {
  const Function *c = static_cast<const Function *>(&b);
  return util::compare_vector_pointers(arguments_, c->arguments_) &&
    *program_ == *c->program_;
}

bool Label::equals(const Node &b) const {
  const Label *c = static_cast<const Label *>(&b);
  return name_ == c->name_ &&
    *expression_ == *c->expression_;
}

bool Application::equals(const Node &b) const {
  const Application *c = static_cast<const Application *>(&b);
  if(labels_->size() != c->labels_->size())
    return false;

  auto eq = [](const auto &a, const auto &b) {
    return a.first == b.first && *a.second == *b.second;
  };

  return *identifier_ == *c->identifier() &&
    std::equal(labels_->begin(), labels_->end(), c->labels_->begin(), eq);
}

bool Conditional::equals(const Node &b) const {
  const Conditional *c = static_cast<const Conditional *>(&b);
  return *expression_ == *c->expression_ &&
    *true_block_ == *c->true_block_ &&
    *false_block_ == *c->false_block_;
}

bool Operation::equals(const Node &b) const {
  const Operation *c = static_cast<const Operation *>(&b);
  return *lhs_ == *c->lhs_ && *rhs_ == *c->rhs_ && op_ == c->op_;
}

bool Declaration::equals(const Node &b) const {
  const Declaration *c = static_cast<const Declaration *>(&b);
  return *identifier_ == *c->identifier_ &&
    *expression_ == *c->expression_ &&
    *value_ == *c->value_;
}

}  // namespace node
}  // namespace goat
