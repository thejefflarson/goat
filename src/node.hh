#include <stdint.h>
#include <string>
#include <vector>

namespace goat {
namespace node {

class Node {
public:
  virtual void Compile() = 0;
};

class SimpleNode : Node {
public:
  SimpleNode(char *str, size_t length) : value_(str, length) {};
private:
  std::string value_;
};

class Integer : SimpleNode {};
class Identifier : SimpleNode {};
class String : SimpleNode {};

}
}
