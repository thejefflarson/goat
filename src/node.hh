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

class Number : SimpleNode {};
class Identifier : SimpleNode {};
class String : SimpleNode {};

class Program : Node {
public:
  Program(vector<unique_ptr<Node>> nodes) :
    nodes_(move(nodes)) {};
  Program() : nodes_() {};
private:
  vector<unique_ptr<Node>> nodes_;
};

class Function : Node {
public:
  Function(vector<unique_ptr<Node>> arguments,
           unique_ptr<Program> program) :
    arguments_(move(arguments)),
    program_(move(program)) {};
private:
  vector<unique_ptr<Node>> arguments_;
  unique_ptr<Program> program_;
};

class Application : Node {
public:
  Application(vector<unique_ptr<Node>> arguments) :
    arguments_(move(arguments)) {};
private:
  vector<unique_ptr<Node>> arguments_;
};

}
}
