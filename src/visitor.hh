#ifndef GOAT_VISITOR_HH
#define GOAT_VISITOR_HH

#include "node.hh"
namespace goat {
namespace node {

class Visitor {
public:
  virtual ~Visitor() {};
  // TODO: maybe these should be const?
  virtual void visit(Node &node) = 0;
  virtual void visit(Number &number) = 0;
  virtual void visit(Identifier &identifier) = 0;
  virtual void visit(String &string) = 0;
  virtual void visit(Program &program) = 0;
  virtual void visit(Function &function) = 0;
  virtual void visit(Application &application) = 0;
  virtual void visit(Conditional &conditional) = 0;
  virtual void visit(Operation &operation) = 0;
  virtual void visit(Type &type) = 0;
  virtual void visit(Declaration &declaration) = 0;
};

}
}

#endif
