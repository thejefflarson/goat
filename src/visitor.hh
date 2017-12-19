#ifndef GOAT_VISITOR_HH
#define GOAT_VISITOR_HH

#include <memory>

namespace goat {
namespace node {

class Node;
class EmptyExpression;
class Number;
class Identifier;
class String;
class Program;
class Argument;
class Function;
class Label;
class Application;
class Conditional;
class Operation;
class Declaration;

#define VisitorMethods \
  void visit(const node::EmptyExpression &empty); \
  void visit(const node::Number &number); \
  void visit(const node::Identifier &identifier); \
  void visit(const node::String &string); \
  void visit(const node::Program &program); \
  void visit(const node::Argument &argument); \
  void visit(const node::Function &function); \
  void visit(const node::Label &label); \
  void visit(const node::Application &application); \
  void visit(const node::Conditional &conditional); \
  void visit(const node::Operation &operation); \
  void visit(const node::Declaration &declaration);

class Visitor {
public:
  virtual ~Visitor() {}
  virtual void visit(const node::EmptyExpression &empty) = 0;
  virtual void visit(const node::Number &number) = 0;
  virtual void visit(const node::Identifier &identifier) = 0;
  virtual void visit(const node::String &string) = 0;
  virtual void visit(const node::Program &program) = 0;
  virtual void visit(const node::Argument &argument) = 0;
  virtual void visit(const node::Function &function) = 0;
  virtual void visit(const node::Label &label) = 0;
  virtual void visit(const node::Application &application) = 0;
  virtual void visit(const node::Conditional &conditional) = 0;
  virtual void visit(const node::Operation &operation) = 0;
  virtual void visit(const node::Declaration &declaration) = 0;
};

template <typename T>
void list_accept(const T list, node::Visitor &v) {
  for(auto i : *list) {
    i->accept(v);
  }
}

class TreeCloner : public Visitor {
public:
  TreeCloner() : child_(nullptr) {}
  VisitorMethods
  std::shared_ptr<node::Program> clone(std::shared_ptr<node::Program> program);
protected:
  std::shared_ptr<node::Node> child_;
};

}
}

#endif
