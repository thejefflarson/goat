#ifndef GOAT_NODE_HH
#define GOAT_NODE_HH

#include <stdint.h>
#include <string>
#include <vector>
#include <memory>
#include <iostream>

namespace goat {
namespace node {

class Node;
typedef std::vector<std::shared_ptr<Node>> NodeList;
class Type;
typedef std::vector<std::shared_ptr<Type>> TypeList;

class Node {
public:
  virtual ~Node() = default;
  virtual void accept(class Visitor &v) = 0;
  bool operator==(const Node &) const {
    return false;
  };
  bool operator!=(const Node &b) const {
    return !(*this == b);
  }
};

class Number : public Node {
public:
  Number(const double value) : value_(value) {}
  void accept(Visitor &v);
  double value() const { return value_; }
  bool operator==(const Number &b) const {
    return value_ == b.value_;
  }
private:
  const double value_;
};

class Identifier : public Node {
public:
  Identifier(const std::string value) : value_(value) {}
  void accept(Visitor &v);
  const std::string & value() const { return value_; }
  bool operator==(Identifier &b) const {
    return value_ == b.value_;
  }
private:
  const std::string value_;
};

class String : public Node {
public:
  String(const std::string value) : value_(value) {}
  void accept(Visitor &v);
  const std::string & value() const { return value_; }
  bool operator==(const String &b) const {
    return value_ == b.value_;
  }
private:
  const std::string value_;
};

class Program : public Node {
public:
  Program() : nodes_(std::make_shared<NodeList>()) {}
  void push_back(std::shared_ptr<NodeList> it) {
    nodes_->insert(nodes_->end(), it->begin(), it->end());
  }
  void accept(Visitor &v);
  const std::shared_ptr<NodeList> nodes() const { return nodes_; }
  bool operator==(const Program &b) const {
    return *nodes_ == *b.nodes_;
  }
private:
  std::shared_ptr<NodeList> nodes_;
};

class Function : public Node {
public:
  Function(const std::shared_ptr<TypeList> arguments,
           const std::shared_ptr<Program> program) :
    arguments_(arguments),
    program_(program) {}
  void accept(Visitor &v);
  const std::shared_ptr<TypeList> arguments() const { return arguments_; }
  const std::shared_ptr<Program> program() const { return program_; }
  bool operator==(const Function &b) const {
    return (*arguments_ == *b.arguments_) && (*program_ == *b.program_);
  }
private:
  const std::shared_ptr<TypeList> arguments_;
  const std::shared_ptr<Program> program_;
};

class Application : public Node {
public:
  Application(std::shared_ptr<Identifier> ident,
              std::shared_ptr<NodeList> arguments) :
    ident_(ident),
    arguments_(arguments) {}
  void accept(Visitor &v);
  const std::shared_ptr<Identifier> ident() const { return ident_; }
  const std::shared_ptr<NodeList> arguments() const { return arguments_; }
  bool operator==(const Application &b) const {
    return (*ident_ == *b.ident_) && (*arguments_ == *b.arguments_);
  }
private:
  const std::shared_ptr<Identifier> ident_;
  const std::shared_ptr<NodeList> arguments_;
};

class Conditional : public Node {
public:
  Conditional(std::shared_ptr<Node> expression,
              std::shared_ptr<Program> true_block,
              std::shared_ptr<Program> false_block) :
    expression_(expression),
    true_block_(true_block),
    false_block_(false_block) {}
  Conditional(std::shared_ptr<Node> expression,
              std::shared_ptr<Program> true_block) :
    expression_(expression),
    true_block_(true_block),
    false_block_(std::make_shared<Program>()) {}
  void accept(Visitor &v);
  const std::shared_ptr<Node> expression() const { return expression_; }
  const std::shared_ptr<Program> true_block() const { return true_block_; }
  const std::shared_ptr<Program> false_block() const { return false_block_; }
  bool operator==(const Conditional &b) const {
    return (*expression_ == *b.expression_) &&
      (*true_block_ == *b.true_block_) &&
      (*false_block_ == *b.false_block_);
  }
private:
  const std::shared_ptr<Node> expression_;
  const std::shared_ptr<Program> true_block_;
  const std::shared_ptr<Program> false_block_;
};

enum Ops {
  Addition = 0,
  Subtraction,
  Division,
  Multiplication
};

class Operation : public Node {
public:
  Operation(std::shared_ptr<Node> lhs,
            std::shared_ptr<Node> rhs,
            Ops op) :
    lhs_(lhs),
    rhs_(rhs),
    op_(op) {}
  void accept(Visitor &v);
  const std::shared_ptr<Node> left() const { return lhs_; }
  const std::shared_ptr<Node> right() const { return rhs_; }
  Ops operation() const { return op_; }
  bool operator==(const Operation &b) const {
    return (*lhs_ == *b.lhs_) && (*rhs_ == *b.rhs_) && (op_ == b.op_);
  }
private:
  const std::shared_ptr<Node> lhs_;
  const std::shared_ptr<Node> rhs_;
  const Ops op_;
};

// TODO: think about splitting this into different classes based on different
// kinds of types.
class Type : public Node {
public:
  Type(std::shared_ptr<Identifier> ident) :
    ident_(ident) {};
  Type(std::shared_ptr<TypeList> arguments,
       std::shared_ptr<Identifier> ident) :
    ident_(ident),
    args_(arguments) {}
  void accept(Visitor &v);
  const std::shared_ptr<Identifier> ident() const { return ident_; }
  const std::shared_ptr<TypeList> arguments() const { return args_; }
  bool operator==(const Type &b) const {
    return (*ident_ == *b.ident_) && (*args_ == *b.args_);
  }
private:
  const std::shared_ptr<Identifier> ident_;
  const std::shared_ptr<TypeList> args_;
};

class Declaration : public Node {
public:
  Declaration(std::shared_ptr<Identifier> ident,
              std::shared_ptr<Type> type) :
    ident_(ident),
    type_(type) {}
  Declaration(std::shared_ptr<Identifier> ident,
              std::shared_ptr<Node> expr) :
    ident_(ident),
    expr_(expr) {}
  Declaration(std::shared_ptr<Identifier> ident,
              std::shared_ptr<Type> type,
              std::shared_ptr<Node> expr) :
    ident_(ident),
    type_(type),
    expr_(expr) {}
  void accept(Visitor &v);
  const std::shared_ptr<Identifier> ident() const { return ident_; }
  const std::shared_ptr<Type> type() const { return type_; }
  const std::shared_ptr<Node> expression() const { return expr_; }
  bool operator==(const Declaration &b) const {
    return (*ident_ == *b.ident_) &&
      (*type_ == *b.type_) &&
      (*expr_ == *b.expr_);
  }
private:
  const std::shared_ptr<Identifier> ident_;
  const std::shared_ptr<Type> type_;
  const std::shared_ptr<Node> expr_;
};

}
}
#endif
