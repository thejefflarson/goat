#ifndef SRC_CONSTRAINTS_HH_
#define SRC_CONSTRAINTS_HH_

#include <set>
#include <memory>
#include <string>
#include <typeinfo>
#include <vector>
#include "util.hh"
#include "visitor.hh"

namespace goat {
namespace inference {

// Note: this is just a language; create an AST and parse it...
// generate a set of constraints and then use union-find to infer
class TypeNode {
 public:
  virtual ~TypeNode() = default;
  bool operator==(const TypeNode &b) const {
    if (typeid(*this) != typeid(b)) return false;
    return equals(b);
  }
  bool operator!=(const TypeNode &b) const {
    return !(*this == b);
  }
  bool operator<(const TypeNode &b) const {
    return *this != b;
  }
  virtual bool equals(const TypeNode &b) const = 0;
};

class Type : public TypeNode {
 public:
  Type(std::string id) :
    id_(id) {}
  bool equals(const TypeNode &b) const;
  std::string id() const { return id_; };
 private:
  std::string id_;
};

class FunctionType : public TypeNode {
 public:
  FunctionType(std::vector<Type> in,
               Type ret) :
    in_(in),
    ret_(ret) {}
  bool equals(const TypeNode &b) const;
 private:
  std::vector<Type> in_;
  Type ret_;
};

class TypeFactory {
 public:
  TypeFactory() : last_(1) {}
  Type next();
 private:
  uint32_t last_;
};

enum ConstraintRelation {
  Equality,
  ExplicitInstance,
  ImplicitInstance
};

class Constraint {
 public:
  Constraint(ConstraintRelation relation,
             std::vector<std::unique_ptr<TypeNode>> variables) :
    relation_(relation),
    variables_(std::move(variables)) {}
    bool operator==(const Constraint &b) const {
      return relation_ == b.relation_ &&
        util::compare_vector_pointers(&variables_, &b.variables_);
    }
    bool operator!=(const Constraint&b) const {
      return !(*this == b);
    }
 private:
  ConstraintRelation relation_;
  std::vector<std::unique_ptr<TypeNode>> variables_;
};


class TypingVisitor : public node::Visitor {
public:
  TypingVisitor() : monomorphic_(), constraints_(), assumptions_() {};
  void visit(const node::Number &number);
  void visit(const node::Identifier &identifier);
  void visit(const node::String &string);
  void visit(const node::Program &program);
  void visit(const node::Argument &argument);
  void visit(const node::Function &function);
  void visit(const node::Application &application);
  void visit(const node::Conditional &conditional);
  void visit(const node::Operation &operation);
  void visit(const node::Declaration &declaration);
private:
  std::set<Type> monomorphic_;
  std::set<Constraint> constraints_;
  std::set<node::Identifier> assumptions_;
};


}  // namespace inference
}  // namespace goat

#endif  // SRC_CONSTRAINTS_HH_
