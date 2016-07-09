#include <stdint.h>
#include <string>
#include <vector>
#include <memory>

using namespace std;

namespace goat {
namespace node {

class Node;
typedef shared_ptr<vector<shared_ptr<Node>>> NodeList;
class Type;
typedef shared_ptr<vector<shared_ptr<Type>>> TypeList;

class Visitor {
public:
  virtual ~Visitor() = default;
  virtual void visit(Node *node) = 0;
};

class Node {
public:
  virtual ~Node() = default;
  virtual void accept(Visitor &v) = 0;
};

class Number : public Node {
public:
  Number(const double value) : value_(value) {}
  void accept(Visitor &v) { v.visit(this); }
  double value() const { return value_; }
private:
  const double value_;
};

class Identifier : public Node {
public:
  Identifier(const string value) : value_(value) {}
  void accept(Visitor &v) { v.visit(this); }
  const string & value() const { return value_; }
private:
  const string value_;
};

class String : public Node {
public:
  String(const string value) : value_(value) {}
  void accept(Visitor &v) { v.visit(this); }
  const string & value() const { return value_; }
private:
  const string value_;
};

class Program : public Node {
public:
  Program() : nodes_() {}
  void push_back(shared_ptr<Node> it) { nodes_->push_back(move(it)); }
  void accept(Visitor &v) { v.visit(this); }
  const NodeList nodes() const { return nodes_; }
private:
  NodeList nodes_;
};

class Function : public Node {
public:
  Function(const NodeList arguments,
           const shared_ptr<Program> program) :
    arguments_(move(arguments)),
    program_(move(program)) {}
  void accept(Visitor &v) { v.visit(this); }
  const NodeList arguments() const { return arguments_; }
  const shared_ptr<Program> program() const { return program_; }
private:
  const NodeList arguments_;
  const shared_ptr<Program> program_;
};

class Application : public Node {
public:
  Application(NodeList arguments) :
    arguments_(move(arguments)) {}
  void accept(Visitor &v) { v.visit(this); }
  const NodeList arguments() const { return arguments_; }
private:
  const NodeList arguments_;
};

class Conditional : public Node {
public:
  Conditional(shared_ptr<Node> expression,
              shared_ptr<Program> true_block,
              shared_ptr<Program> false_block) :
    expression_(move(expression)),
    true_block_(move(true_block)),
    false_block_(move(false_block)) {}
  Conditional(shared_ptr<Node> expression,
              shared_ptr<Program> true_block) :
    expression_(move(expression)),
    true_block_(move(true_block)),
    false_block_(shared_ptr<Program>(new Program())) {}
  void accept(Visitor &v) { v.visit(this); }
  const shared_ptr<Node> expression() const { return expression_; }
  const shared_ptr<Program> true_block() const { return true_block_; }
  const shared_ptr<Program> false_block() const { return false_block_; }
private:
  const shared_ptr<Node> expression_;
  const shared_ptr<Program> true_block_;
  const shared_ptr<Program> false_block_;
};

enum Ops {
  Addition = 0,
  Subtraction,
  Division,
  Multiplication
};

class Operation : public Node {
public:
  Operation(shared_ptr<Node> lhs,
            shared_ptr<Node> rhs,
            Ops op) :
    lhs_(move(lhs)),
    rhs_(move(rhs)),
    op_(op) {}
  void accept(Visitor &v) { v.visit(this); }
  const shared_ptr<Node> left() const { return lhs_; }
  const shared_ptr<Node> right() const { return rhs_; }
  Ops operation() const { return op_; }
private:
  const shared_ptr<Node> lhs_;
  const shared_ptr<Node> rhs_;
  const Ops op_;
};

class Type : public Node {
public:
  Type(shared_ptr<Identifier> ident) :
    ident_(move(ident)) {};
  Type(shared_ptr<Identifier> ident,
       shared_ptr<vector<shared_ptr<Type>>> arguments) :
    ident_(move(ident)),
    args_(move(arguments)) {}
  void accept(Visitor &v) { v.visit(this); }
  const shared_ptr<Identifier> ident() const { return ident_; }
  const TypeList arguments() const { return args_; }
private:
  shared_ptr<Identifier> ident_;
  TypeList args_;
};

class Declaration : public Node {
public:
  Declaration(shared_ptr<Identifier> ident,
              shared_ptr<Type> type) :
    ident_(move(ident)),
    type_(type) {}
  Declaration(shared_ptr<Identifier> ident,
              shared_ptr<Node> expr) :
    ident_(move(ident)),
    expr_(move(expr)) {}
  Declaration(shared_ptr<Identifier> ident,
              shared_ptr<Type> type,
              shared_ptr<Node> expr) :
    ident_(move(ident)),
    type_(move(type)),
    expr_(move(expr)) {}
  void accept(Visitor &v) { v.visit(this); }
  const shared_ptr<Identifier> ident() const { return ident_; }
  const shared_ptr<Type> type() const { return type_; }
  const shared_ptr<Node> expression() { return expr_; }
  void set_type(shared_ptr<Type> type) { type_ = type; }
private:
  const shared_ptr<Identifier> ident_;
  shared_ptr<Type> type_;
  const shared_ptr<Node> expr_;
};

}
}
