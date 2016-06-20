#include <stdint.h>
#include <string>
#include <vector>
#include <memory>

using namespace std;

namespace goat {
namespace node {

class Node {
public:
  virtual void Compile() = 0;
};

class SimpleNode : Node {
public:
  SimpleNode(char *str, size_t length) :
    value_(str, length) {};
private:
  string value_;
};

class Number : SimpleNode {
public:
  void Compile();
};

class Identifier : SimpleNode {
public:
  void Compile();
};

class String : SimpleNode {
public:
  void Compile();
};

class Program : Node {
public:
  Program(vector<unique_ptr<Node>> nodes) :
    nodes_(move(nodes)) {};
  Program() : nodes_() {};
  void Compile();
private:
  vector<unique_ptr<Node>> nodes_;
};

class Function : Node {
public:
  Function(vector<unique_ptr<Node>> arguments,
           unique_ptr<Program> program) :
    arguments_(move(arguments)),
    program_(move(program)) {};
  void Compile();
private:
  vector<unique_ptr<Node>> arguments_;
  unique_ptr<Program> program_;
};

class Application : Node {
public:
  Application(vector<unique_ptr<Node>> arguments) :
    arguments_(move(arguments)) {};
  void Compile();
private:
  vector<unique_ptr<Node>> arguments_;
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

}
}
