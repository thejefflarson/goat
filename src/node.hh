#ifndef GOAT_NODE_HH
#define GOAT_NODE_HH

#include <stdint.h>
#include <string>
#include <vector>
#include <memory>

namespace goat {
namespace node {

class Node;
typedef std::shared_ptr<std::vector<std::shared_ptr<Node>>> NodeList;
class Type;
typedef std::shared_ptr<std::vector<std::shared_ptr<Type>>> TypeList;

class Node {
public:
  virtual ~Node() {};
  virtual void accept(class Visitor &v) = 0;
};

class Number : public Node {
public:
  Number(const double value) : value_(value) {}
  void accept(Visitor &v);
  double value() const { return value_; }
private:
  const double value_;
};

class Identifier : public Node {
public:
  Identifier(const std::string value) : value_(value) {}
  void accept(Visitor &v);
  const std::string & value() const { return value_; }
private:
  const std::string value_;
};

class String : public Node {
public:
  String(const std::string value) : value_(value) {}
  void accept(Visitor &v);
  const std::string & value() const { return value_; }
private:
  const std::string value_;
};

class Program : public Node {
public:
  Program() : nodes_(std::make_shared<std::vector<std::shared_ptr<Node>>>()) {}
  void push_back(std::shared_ptr<Node> it) { nodes_->push_back(it); }
  void accept(Visitor &v);
  const NodeList nodes() const { return nodes_; }
private:
  NodeList nodes_;
};

class Function : public Node {
public:
  Function(const TypeList arguments,
           const std::shared_ptr<Program> program) :
    arguments_(arguments),
    program_(program) {}
  void accept(Visitor &v);
  const TypeList arguments() const { return arguments_; }
  const std::shared_ptr<Program> program() const { return program_; }
private:
  const TypeList arguments_;
  const std::shared_ptr<Program> program_;
};

class Application : public Node {
public:
  Application(std::shared_ptr<Identifier> ident,
              NodeList arguments) :
    ident_(ident),
    arguments_(arguments) {}
  void accept(Visitor &v);
  const std::shared_ptr<Identifier> ident() const { return ident_; }
  const NodeList arguments() const { return arguments_; }
private:
  const std::shared_ptr<Identifier> ident_;
  const NodeList arguments_;
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
    false_block_(std::shared_ptr<Program>(new Program())) {}
  void accept(Visitor &v);
  const std::shared_ptr<Node> expression() const { return expression_; }
  const std::shared_ptr<Program> true_block() const { return true_block_; }
  const std::shared_ptr<Program> false_block() const { return false_block_; }
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
    lhs_(std::move(lhs)),
    rhs_(std::move(rhs)),
    op_(op) {}
  void accept(Visitor &v);
  const std::shared_ptr<Node> left() const { return lhs_; }
  const std::shared_ptr<Node> right() const { return rhs_; }
  Ops operation() const { return op_; }
private:
  const std::shared_ptr<Node> lhs_;
  const std::shared_ptr<Node> rhs_;
  const Ops op_;
};

class Type : public Node {
public:
  Type(std::shared_ptr<Identifier> ident) :
    ident_(std::move(ident)) {};
  Type(TypeList arguments,
       std::shared_ptr<Identifier> ident) :
    ident_(std::move(ident)),
    args_(std::move(arguments)) {}
  void accept(Visitor &v);
  const std::shared_ptr<Identifier> ident() const { return ident_; }
  const TypeList arguments() const { return args_; }
private:
  const std::shared_ptr<Identifier> ident_;
  const TypeList args_;
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
private:
  const std::shared_ptr<Identifier> ident_;
  const std::shared_ptr<Type> type_;
  const std::shared_ptr<Node> expr_;
};

}
}
#endif
