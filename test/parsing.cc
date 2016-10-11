#include <sstream>
#include "node.hh"
#include "visitor.hh"
#include "driver.hh"
#include "tap.h"

using namespace std;
using namespace goat::node;

template<typename T>
inline void list_accept(const T list, Visitor &v) {
  for(auto i : *list) {
    i->accept(v);
  }
}

class PrintingVisitor : public Visitor {
public:
  PrintingVisitor() {}
  void visit(const Number &number) {
    std::cout << "Number " << number.value() << std::endl;
  }

  void visit(const Identifier &identifier) {
    std::cout << "Identifier " << identifier.value() << std::endl;
  }

  void visit(const String &string) {
    std::cout << "String " << string.value() << std::endl;
  }

  void visit(const Program &program) {
    std::cout << "Program" << std::endl;
    list_accept(program.nodes(), *this);
  }

  void visit(const Function &function) {
    std::cout << "Function" << std::endl;
    list_accept(function.arguments(), *this);
    function.program()->accept(*this);
  }

  void visit(const Application &application) {
    std::cout << "Application" << std::endl;
    application.ident()->accept(*this);
    list_accept(application.arguments(), *this);
  }

  void visit(const Conditional &conditional) {
    std::cout << "Conditional" << std::endl;
    conditional.expression()->accept(*this);
    conditional.true_block()->accept(*this);
    conditional.false_block()->accept(*this);
  }

  void visit(const Operation &operation) {
    std::cout << "Operation" << std::endl;
    operation.left()->accept(*this);
    operation.right()->accept(*this);
  }

  void visit(const Type &type) {
    std::cout << "Type" << std::endl;
    type.ident()->accept(*this);
    if(type.arguments()) list_accept(type.arguments(), *this);
  }

  void visit(const Declaration &declaration) {
    std::cout << "Declaration" << std::endl;
    declaration.ident()->accept(*this);
    if(declaration.type()) declaration.type()->accept(*this);
    if(declaration.expression()) declaration.expression()->accept(*this);
  }
};


bool test(const std::string program, const Program &result) {
  std::shared_ptr<Program> p;
  auto s = make_shared<std::stringstream>(program);
  int r = goat::driver::parse(s, p);
  bool equal = result == *p;

  if(!equal) {
    PrintingVisitor print;
    print.visit(result);
    print.visit(*p);
  }

  return r == 0 && equal;
}

void test_empty() {
  Program p;
  ok(test("", p), "Parses an empty string");
}

void test_literals() {
  Program p;
  auto args = make_shared<NodeList>();
  args->push_back(make_shared<Number>(1));
  p.push_back(args);
  ok(test("1", p), "Parses a number");
  args->clear();
  args->push_back(make_shared<String>("Why hello!"));
  ok(test("\"Why hello!\"", p), "Parses a string");
}

int main() {
  start_test;
  test_empty();
  test_literals();
}
