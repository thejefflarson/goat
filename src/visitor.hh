#ifndef GOAT_VISITOR_HH
#define GOAT_VISITOR_HH

#include "node.hh"
namespace goat {
namespace node {

class Visitor {
public:
  virtual ~Visitor() {};
  virtual void visit(const Number &number) = 0;
  virtual void visit(const Identifier &identifier) = 0;
  virtual void visit(const String &string) = 0;
  virtual void visit(const Program &program) = 0;
  virtual void visit(const Function &function) = 0;
  virtual void visit(const Application &application) = 0;
  virtual void visit(const Conditional &conditional) = 0;
  virtual void visit(const Operation &operation) = 0;
  virtual void visit(const Declaration &declaration) = 0;
};

}
}

#endif
