#ifndef SRC_CONSTRAINTS_HH_
#define SRC_CONSTRAINTS_HH_

#include <set>
#include <memory>
#include <string>
#include <vector>

namespace goat {
namespace inference {

// Note: this is just a language; create an AST and parse it...
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
  virtual bool equals(const TypeNode &b) const = 0;
};

class Type : public TypeNode {
 public:
  Type(std::string id) :
    id_(id) {}
  bool equals(const TypeNode &b) const;
 private:
  std::string id_;
};

class FunctionType : public TypeNode {
 public:
  FunctionType(std::vector<std::unique_ptr<Type>> in,
               Type ret) :
    in_(std::move(in)),
    ret_(ret) {}
  bool equals(const TypeNode &b) const;
 private:
  std::vector<std::unique_ptr<Type>> in_;
  Type ret_;
};

class TypeFactory {
 public:
  TypeFactory() : last_("a") {}
  Type next();
 private:
  std::string last_;
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
      return relation_ == b.relation_ && variables_ == b.variables_;
    }
    bool operator!=(const Constraint&b) const {
      return !(*this == b);
    }
 private:
  ConstraintRelation relation_;
  std::vector<std::unique_ptr<TypeNode>> variables_;
};

class ConstraintSet {
 public:
  ConstraintSet() : constraints_() {}
  void add(std::unique_ptr<Constraint> constraint) {
    constraints_.insert(std::move(constraint));
  }
 private:
  std::set<std::unique_ptr<Constraint>> constraints_;
};

}  // namespace inference
}  // namespace goat

#endif  // SRC_CONSTRAINTS_HH_
