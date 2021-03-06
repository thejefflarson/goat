#ifndef GOAT_NODE_HH_
#define GOAT_NODE_HH_

#include <cassert>
#include <iostream>
#include <map>
#include <memory>
#include <stdint.h>
#include <string>
#include <vector>

#include "inferer.hh"

namespace goat {
namespace node {

class Node {
 public:
  virtual ~Node() = default;
  virtual void accept(class Visitor &v) const = 0;
  virtual const inference::Type type() const = 0;
  bool operator==(const Node &b) const {
    if(typeid(*this) != typeid(b)) return false;
    return equals(b);
  }
  bool operator!=(const Node &b) const {
    return !(*this == b);
  }
 private:
  virtual bool equals(const Node &) const = 0;
};
using NodeList = std::vector<std::shared_ptr<Node>>;

// Empty node that we use in place of a null pointer to help out things like
// comparisons.
class EmptyExpression : public Node {
 public:
  EmptyExpression() {}
  void accept(Visitor &v) const;
  const inference::Type type() const { return inference::NoType(); };
private:
  bool equals(const Node &b) const { return true; }
};

class Number : public Node {
 public:
  Number(const double value) :
    value_(value),
    type_(inference::NumberType()) {}
  void accept(Visitor& v) const;
  double value() const { return value_; }
  const inference::Type type() const {  return type_; }
 private:
  bool equals(const Node &b) const;
  const double value_;
  const inference::Type type_;
};

class Identifier : public Node {
 public:
  Identifier(const std::string name) :
    value_(name),
    internal_value_(),
    type_(inference::NoType()) {}
  Identifier(const std::string name,
             const std::string internal_name) :
    value_(name),
    internal_value_(internal_name),
    type_(inference::NoType()) {}
  Identifier(const std::string name,
             const std::string internal_name,
             inference::Type type) :
    value_(name),
    internal_value_(internal_name),
    type_(type) {}
  void accept(Visitor& v) const;
  const std::string value() const { return value_; }
  const std::string internal_value() const { return internal_value_; }
  const inference::Type type() const { return type_; };
 private:
  bool equals(const Node& b) const;
  const std::string value_;
  const std::string internal_value_;
  const inference::Type type_;
};

class String : public Node {
 public:
  String(const std::string value) :
    value_(value),
    type_(inference::StringType()) {}
  void accept(Visitor& v) const;
  const std::string value() const { return value_; }
  const inference::Type type() const { return type_; };
 private:
  bool equals(const Node& b) const;
  const std::string value_;
  const inference::Type type_;
};

// For a block the type is the same as the last node on the list.
class Program : public Node {
 public:
  Program() : expression_(std::make_shared<EmptyExpression>()) {}
  Program(std::shared_ptr<Node> expression) :
    expression_(expression) {}
  void accept(Visitor& v) const;
  const std::shared_ptr<Node> expression() const { return expression_; }
  const inference::Type type() const { return expression_->type(); }
 private:
  bool equals(const Node& b) const;
  std::shared_ptr<Node> expression_;
};

class Argument : public Node {
 public:
  Argument(const std::shared_ptr<Identifier> ident,
           const std::shared_ptr<Node> expression) :
    identifier_(ident),
    expression_(expression) {}
  Argument(const std::shared_ptr<Identifier> ident) :
    identifier_(ident),
    expression_(std::make_shared<EmptyExpression>()) {}
  void accept(Visitor& v) const;
  const std::shared_ptr<Identifier> identifier() const { return identifier_; }
  const std::shared_ptr<Node> expression() const { return expression_; }
  const inference::Type type() const { return identifier_->type(); }
 private:
  bool equals(const Node& b) const;
  const std::shared_ptr<Identifier> identifier_;
  const std::shared_ptr<Node> expression_;
};
using ArgumentList = std::vector<std::shared_ptr<Argument>>;

class Function : public Node {
 public:
  Function(const std::shared_ptr<ArgumentList> arguments,
           const std::shared_ptr<Program> program) :
    arguments_(arguments),
    program_(program),
    type_(inference::NoType()) {}
  Function(const std::shared_ptr<ArgumentList> arguments,
           const std::shared_ptr<Program> program,
           inference::Type type) :
    arguments_(arguments),
    program_(program),
    type_(type) {}
  void accept(Visitor& v) const;
  const std::shared_ptr<ArgumentList> arguments() const { return arguments_; }
  const std::shared_ptr<Program> program() const { return program_; }
  const std::string id() const;
  const inference::Type type() const { return type_; }
 private:
  bool equals(const Node &b) const;
  const std::shared_ptr<ArgumentList> arguments_;
  const std::shared_ptr<Program> program_;
  inference::Type type_;
};

class Label : public Node {
 public:
  Label(std::string name,
        std::shared_ptr<Node> expression) :
    name_(name),
    expression_(expression) {}
  void accept(Visitor& v) const;
  const std::string name() const { return name_; }
  const std::shared_ptr<Node> expression() const { return expression_; }
  const inference::Type type() const { return expression_->type(); }
 private:
  bool equals(const Node &b) const;
  std::string name_;
  std::shared_ptr<Node> expression_;
};

using Labels = std::map<std::string, std::shared_ptr<Label>>;
class Application : public Node {
 public:
  Application(std::shared_ptr<Identifier> ident,
              std::shared_ptr<Labels> labels) :
    identifier_(ident),
    labels_(labels),
    type_(inference::NoType()) {}
  Application(std::shared_ptr<Identifier> ident,
              std::shared_ptr<Labels> labels,
              inference::Type type) :
    identifier_(ident),
    labels_(labels),
    type_(type) {}
  void accept(Visitor& v) const;
  const std::shared_ptr<Identifier> identifier() const { return identifier_; }
  const std::shared_ptr<Labels> labels() const { return labels_; }
  const inference::Type type() const { return type_; }
 private:
  bool equals(const Node& b) const;
  const std::shared_ptr<Identifier> identifier_;
  const std::shared_ptr<Labels> labels_;
  inference::Type type_;
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
  void accept(Visitor& v) const;
  const std::shared_ptr<Node> expression() const { return expression_; }
  const std::shared_ptr<Program> true_block() const { return true_block_; }
  const std::shared_ptr<Program> false_block() const { return false_block_; }
  const inference::Type type() const { return true_type(); }
  const inference::Type true_type() const { return true_block_->type(); }
  const inference::Type false_type() const { return true_block_->type(); }
 private:
  bool equals(const Node& b) const;
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
  void accept(Visitor& v) const;
  const std::shared_ptr<Node> left() const { return lhs_; }
  const std::shared_ptr<Node> right() const { return rhs_; }
  Ops operation() const { return op_; }
  const inference::Type type() const {
    return inference::Type(inference::NumberType());
  }
 private:
  bool equals(const Node& b) const;
  const std::shared_ptr<Node> lhs_;
  const std::shared_ptr<Node> rhs_;
  const Ops op_;
};

class Declaration : public Node {
 public:
  Declaration(std::shared_ptr<Identifier> ident,
              std::shared_ptr<Node> value,
              std::shared_ptr<Node> expression) :
    identifier_(ident),
    value_(value),
    expression_(expression) {}
  void accept(Visitor& v) const;
  const std::shared_ptr<Identifier> identifier() const { return identifier_; }
  const std::shared_ptr<Node> expression() const { return expression_; }
  const std::shared_ptr<Node> value() const { return value_; }
  const inference::Type type() const { return identifier_->type(); }
 private:
  bool equals(const Node& b) const;
  const std::shared_ptr<Identifier> identifier_;
  const std::shared_ptr<Node> value_;
  const std::shared_ptr<Node> expression_;
};

}
}
#endif // GOAT_NODE_HH_
