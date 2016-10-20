#include <vector>
#include "node.hh"
#include "visitor.hh"

namespace goat {
namespace node {

#define accept(kls)                             \
  void kls::accept(Visitor &v) {                \
    v.visit(*this);                             \
  }

accept(Number)
accept(Identifier)
accept(String)
accept(Program)
accept(Function)
accept(Application)
accept(Conditional)
accept(Operation)
accept(Declaration)

template<typename T>
inline bool string_equals(const T *a, const Node &b) {
  const T *c = static_cast<const T *>(&b);
  return a->value().compare(c->value()) == 0;
}

bool String::equals(const Node &b) const {
  return string_equals(this, b);
}

bool Identifier::equals(const Node &b) const {
  return string_equals(this, b);
}

bool Number::equals(const Node &b) const {
  const Number *c = static_cast<const Number *>(&b);
  return value_ == c->value_;
}

template<typename T>
bool compare_vectors(const T &a, const T &b) {
  if (a->size() != b->size())
    return false;

  auto eq = [](const std::shared_ptr<Node> &a, const std::shared_ptr<Node> &b) {
    return *a == *b;
  };

  return std::equal(a->begin(), a->end(), b->begin(), eq);
}

bool Program::equals(const Node &b) const {
  const Program *c = static_cast<const Program *>(&b);
  return compare_vectors(this->nodes_, c->nodes_);
}

bool Function::equals(const Node &b) const {
  const Function *c = static_cast<const Function *>(&b);
  return compare_vectors(arguments_, c->arguments_) &&
    *program_ == *c->program_;
}

bool Application::equals(const Node &b) const {
  const Application *c = static_cast<const Application *>(&b);
  return *ident_ == *c->ident() &&
    compare_vectors(arguments_, c->arguments_);
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
    expression_ == c->expression_ &&
    *expression_ == *c->expression_;
}

}  // namespace node
}  // namespace goat
