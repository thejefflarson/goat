#include <stdint.h>
#include <string>
#include <vector>

namespace goat {
namespace nodes {

class Node {
  virtual void Compile() = 0;
};

class Integer : Node {
  Integer(char *str, size_t length) : value_(str, length) {};
  void Compile();
private:
  std::string value_;
};

class Identifier : Node {
  Identifier(char *str, size_t length) : value_(str, length) {};
  void Compile();
private:
  std::string value_;
};

class String : Node {
  String(char *str, size_t length) : value_(str, length) {};
  void Compile();
private:
  std::string value_;
};

}
}
