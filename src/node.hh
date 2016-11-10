#ifndef GOAT_NODE_HH_
#define GOAT_NODE_HH_

#include <stdint.h>
#include <string>
#include <vector>
#include <memory>
#include <iostream>
#include "constraints.hh"


namespace goat {
namespace node {

class Node;
typedef std::vector<std::shared_ptr<Node>> NodeList;
class Argument;
typedef std::vector<std::shared_ptr<Argument>> ArgumentList;

class Node {
 public:
  virtual ~Node() = default;
  virtual void accept(class Visitor &v) = 0;
  bool operator==(const Node &b) const {
    if(typeid(*this) != typeid(b)) return false;
    return equals(b);
  }
  bool operator!=(const Node &b) const {
    return !(*this == b);
  }
  virtual inference::Type type();
 private:
  virtual bool equals(const Node &) const = 0;
};

class Typed {
 public:
  Typed(inference::Type type) : type_(type) {}
  inference::Type type() { return type_; }
 private:
  const inference::Type type_;
};

class Number : public Typed, public Node {
 public:
  Number(const double value) :
    Typed(inference::Type("Number")),
    value_(value) {}
  void accept(Visitor &v);
  double value() const { return value_; }
 private:
  bool equals(const Node &b) const;
  const double value_;
};

  class Identifier : public Typed, public Node {
 public:
  Identifier(const std::string value,
             inference::Type type) :
    Typed(type),
    value_(value) {}
  void accept(Visitor &v);
  const std::string & value() const { return value_; }
 private:
  bool equals(const Node &b) const;
  const std::string value_;
};

  class String : public Typed, public Node {
 public:
  String(const std::string value) :
    Typed(inference::Type("String")),
    value_(value) {}
  void accept(Visitor &v);
  const std::string & value() const { return value_; }
 private:
  bool equals(const Node &b) const;
  const std::string value_;
};

// a block the type is the same as the last node on the list
class Program : public Node {
 public:
  Program() :
    nodes_(std::make_shared<NodeList>()) {}
  void push_back(std::shared_ptr<NodeList> it) {
    nodes_->insert(nodes_->end(), it->begin(), it->end());
  }
  void accept(Visitor &v);
  const std::shared_ptr<NodeList> nodes() const { return nodes_; }
 private:
  bool equals(const Node &b) const;
  std::shared_ptr<NodeList> nodes_;
};

class Argument : public Typed, public Node {
 public:
  Argument(const std::shared_ptr<Identifier> ident,
           const std::shared_ptr<Node> expression,
           inference::Type type) :
    Typed(type),
    identifier_(ident),
    expression_(expression) {}
  void accept(Visitor &v);
  const std::shared_ptr<Identifier> identifier() const { return identifier_; }
  const std::shared_ptr<Node> expression() const { return expression_; }
 private:
  bool equals(const Node &b) const;
  const std::shared_ptr<Identifier> identifier_;
  const std::shared_ptr<Node> expression_;
};

class Function : public Typed, public Node {
 public:
  Function(const std::shared_ptr<ArgumentList> arguments,
           const std::shared_ptr<Program> program,
           inference::Type type) :
    Typed(type),
    arguments_(arguments),
    program_(program) {}
  void accept(Visitor &v);
  const std::shared_ptr<ArgumentList> arguments() const { return arguments_; }
  const std::shared_ptr<Program> program() const { return program_; }
 private:
  bool equals(const Node &b) const;
  const std::shared_ptr<ArgumentList> arguments_;
  const std::shared_ptr<Program> program_;
};

class Application : public Typed, public Node {
 public:
  Application(std::shared_ptr<Identifier> ident,
              std::shared_ptr<ArgumentList> arguments,
              inference::Type type) :
    Typed(type),
    ident_(ident),
    arguments_(arguments) {}
  void accept(Visitor &v);
  const std::shared_ptr<Identifier> ident() const { return ident_; }
  const std::shared_ptr<ArgumentList> arguments() const { return arguments_; }
 private:
  bool equals(const Node &b) const;
  const std::shared_ptr<Identifier> ident_;
  const std::shared_ptr<ArgumentList> arguments_;
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
 private:
  bool equals(const Node &b) const;
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
 private:
  bool equals(const Node &b) const;
  const std::shared_ptr<Node> lhs_;
  const std::shared_ptr<Node> rhs_;
  const Ops op_;
};

class Declaration : public Node {
 public:
  Declaration(std::shared_ptr<Identifier> ident,
              std::shared_ptr<Node> expression) :
    identifier_(ident),
    expression_(expression) {}
  void accept(Visitor &v);
  const std::shared_ptr<Identifier> identifier() const { return identifier_; }
  const std::shared_ptr<Node> expression() const { return expression_; }
 private:
  bool equals(const Node &b) const;
  const std::shared_ptr<Identifier> identifier_;
  const std::shared_ptr<Node> expression_;
};

}
}
#endif // GOAT_NODE_HH_
