#ifndef GOAT_VISITOR_HH
#define GOAT_VISITOR_HH

namespace goat {
namespace node {

class Number;
class Identifier;
class String;
class Program;
class Argument;
class Function;
class Application;
class Conditional;
class Operation;
class Declaration;

#define VisitorMethods \
  void visit(const node::Number &number); \
  void visit(const node::Identifier &identifier); \
  void visit(const node::String &string); \
  void visit(const node::Program &program); \
  void visit(const node::Argument &argument); \
  void visit(const node::Function &function); \
  void visit(const node::Application &application); \
  void visit(const node::Conditional &conditional); \
  void visit(const node::Operation &operation); \
  void visit(const node::Declaration &declaration);


class Visitor {
 public:
  virtual ~Visitor() {}
  VisitorMethods
};

}
}

#endif
