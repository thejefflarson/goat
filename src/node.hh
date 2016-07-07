#include <stdint.h>
#include <string>
#include <vector>
#include <memory>

using namespace std;

namespace goat {
namespace node {

class Node;
typedef vector<shared_ptr<Node>> NodeList;


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
  Number(double value) : value_(value) {}
  void accept(Visitor &v) { v.visit(this); }
private:
  double value_;
};

class Identifier : public Node {
public:
  Identifier(string value) : value_(value) {}
  void accept(Visitor &v) { v.visit(this); }
private:
  string value_;
};

class String : public Node {
public:
  String(string value) : value_(value) {}
  void accept(Visitor &v) { v.visit(this); }
private:
  string value_;
};

class Program : public Node {
public:
  Program() : nodes_() {}
  void push_back(shared_ptr<Node> it) { nodes_.push_back(it); }
  void accept(Visitor &v) { v.visit(this); }
private:
  NodeList nodes_;
};

class Function : public Node {
public:
  Function(NodeList arguments,
           unique_ptr<Program> program) :
    arguments_(move(arguments)),
    program_(move(program)) {}
  void accept(Visitor &v) { v.visit(this); }
private:
  NodeList arguments_;
  unique_ptr<Program> program_;
};

class Application : public Node {
public:
  Application(NodeList arguments) :
    arguments_(move(arguments)) {}
  void accept(Visitor &v) { v.visit(this); }
private:
  NodeList arguments_;
};

class Conditional : public Node {
public:
  Conditional(unique_ptr<Node> expression,
              unique_ptr<Program> true_block,
              unique_ptr<Program> false_block) :
    expression_(move(expression)),
    true_block_(move(true_block)),
    false_block_(move(false_block)) {}
  Conditional(unique_ptr<Node> expression,
              unique_ptr<Program> true_block) :
    expression_(move(expression)),
    true_block_(move(true_block)),
    false_block_(unique_ptr<Program>(new Program())) {}
  void accept(Visitor &v) { v.visit(this); }
private:
  unique_ptr<Node> expression_;
  unique_ptr<Program> true_block_;
  unique_ptr<Program> false_block_;
};

enum Ops {
  Addition = 0,
  Subtraction,
  Division,
  Multiplication
};

class Operation : public Node {
public:
  Operation(unique_ptr<Node> lhs,
            unique_ptr<Node> rhs,
            Ops op) :
    lhs_(move(lhs)),
    rhs_(move(rhs)),
    op_(op) {}
  void accept(Visitor &v) { v.visit(this); }
private:
  unique_ptr<Node> lhs_;
  unique_ptr<Node> rhs_;
  Ops op_;
};

class Type : public Node {
public:
  Type(unique_ptr<Identifier> ident) :
    ident_(move(ident)) {};
  Type(unique_ptr<Identifier> ident,
       vector<unique_ptr<Identifier>> arguments) :
    ident_(move(ident)),
    args_(move(arguments)) {}
  void accept(Visitor &v) { v.visit(this); }
private:
  unique_ptr<Identifier> ident_;
  vector<unique_ptr<Identifier>> args_;
};

class Declaration : public Node {
public:
  Declaration(unique_ptr<Identifier> ident,
              unique_ptr<Type> type) :
    ident_(move(ident)),
    type_(move(type)) {}
  Declaration(unique_ptr<Identifier> ident,
              unique_ptr<Node> expr) :
    ident_(move(ident)),
    expr_(move(expr)) {}
  Declaration(unique_ptr<Identifier> ident,
              unique_ptr<Type> type,
              unique_ptr<Node> expr) :
    ident_(move(ident)),
    type_(move(type)),
    expr_(move(expr)) {}
  void accept(Visitor &v) { v.visit(this); }
private:
  unique_ptr<Identifier> ident_;
  unique_ptr<Type> type_;
  unique_ptr<Node> expr_;
};

}
}
