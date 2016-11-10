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
<<<<<<< HEAD
 public:
  FunctionType(std::vector<std::unique_ptr<Type>> in,
               Type ret) :
    in_(std::move(in)),
    ret_(ret) {}
  bool equals(const TypeNode &b) const;
 private:
  std::vector<std::unique_ptr<Type>> in_;
  Type ret_;
=======
  FunctionType(std::vector<std::unique_ptr<TypeVariable>> in,
               TypeVariable ret,
               std::shared_ptr<node::Identifier> ident) :
    in_(std::move(in)),
    ret_(ret),
    ident_(ident) {}
  bool equals(const TypeNode &b) const;
 private:
  std::vector<std::unique_ptr<TypeVariable>> in_;
  TypeVariable ret_;
  std::shared_ptr<node::Identifier> ident_;
>>>>>>> 39946fe0b12c3d7a4ea5c365c1974dc8790e01e8
};

class TypeVariableFactory {
  TypeVariableFactory() : last_("a") {}
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
<<<<<<< HEAD
=======
};

class Constrainer : public node::Visitor {

 private:
  ConstraintSet constraints_;
  TypeVariableFactory type_factory_;
>>>>>>> 39946fe0b12c3d7a4ea5c365c1974dc8790e01e8
};

}  // namespace inference
}  // namespace goat

#endif  // SRC_CONSTRAINTS_HH_
