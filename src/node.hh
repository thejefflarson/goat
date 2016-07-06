#include <stdint.h>
#include <string>
#include <vector>
#include <memory>

using namespace std;

namespace goat {
namespace node {

class Node;
typedef vector<unique_ptr<Node>> NodeList;

class Node {
public:
  virtual void Compile() = 0;
};

class Number : Node {
public:
  Number(double value) : value_(value) {}
  void Compile();
private:
  double value_;
};

class Identifier : Node {
public:
  Identifier(string value) : value_(value) {}
  void Compile();
private:
  string value_;
};

class String : Node {
public:
  String(string value) : value_(value) {}
  void Compile();
private:
  string value_;
};

class Program : Node {
public:
  Program() : nodes_() {};
  void push_back(unique_ptr<Node> it) { nodes_.push_back(move(it)); }
  void Compile();
private:
  NodeList nodes_;
};

class Function : Node {
public:
  Function(NodeList arguments,
           unique_ptr<Program> program) :
    arguments_(move(arguments)),
    program_(move(program)) {};
  void Compile();
private:
  NodeList arguments_;
  unique_ptr<Program> program_;
};

class Application : Node {
public:
  Application(NodeList arguments) :
    arguments_(move(arguments)) {};
  void Compile();
private:
  NodeList arguments_;
};

class Conditional : Node {
public:
  Conditional(unique_ptr<Node> expression,
              unique_ptr<Program> true_block,
              unique_ptr<Program> false_block) :
    expression_(move(expression)),
    true_block_(move(true_block)),
    false_block_(move(false_block)) {};
  Conditional(unique_ptr<Node> expression,
              unique_ptr<Program> true_block) :
    expression_(move(expression)),
    true_block_(move(true_block)),
    false_block_(unique_ptr<Program>(new Program())){};
  void Compile();
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

class Operation : Node {
public:
  Operation(unique_ptr<Node> lhs,
            unique_ptr<Node> rhs,
            Ops op) :
    lhs_(move(lhs)),
    rhs_(move(rhs)),
    op_(op) {};

  void Compile();
private:
  unique_ptr<Node> lhs_;
  unique_ptr<Node> rhs_;
  Ops op_;
};

class Type : Node {
public:
  Type(unique_ptr<Identifier> ident) :
    ident_(move(ident)) {};
  Type(unique_ptr<Identifier> ident,
       vector<unique_ptr<Identifier>> arguments) :
    ident_(move(ident)),
    args_(move(arguments)) {};
private:
  unique_ptr<Identifier> ident_;
  vector<unique_ptr<Identifier>> args_;
};

class Declaration : Node {
public:
  Declaration(unique_ptr<Identifier> ident,
              unique_ptr<Type> type) :
    ident_(move(ident)),
    type_(move(type)) {};
  Declaration(unique_ptr<Identifier> ident,
              unique_ptr<Node> expr) :
    ident_(move(ident)),
    expr_(move(expr)) {};
  Declaration(unique_ptr<Identifier> ident,
              unique_ptr<Type> type,
              unique_ptr<Node> expr) :
    ident_(move(ident)),
    type_(move(type)),
    expr_(move(expr)){};
private:
  unique_ptr<Identifier> ident_;
  unique_ptr<Type> type_;
  unique_ptr<Node> expr_;
};

}
}
