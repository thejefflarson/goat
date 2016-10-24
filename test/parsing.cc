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

  void visit(const Declaration &declaration) {
    std::cout << "Declaration" << std::endl;
    declaration.identifier()->accept(*this);
    if(declaration.expression()) declaration.expression()->accept(*this);
  }
};

bool test(const std::string program, const Program &result) {
  std::shared_ptr<Program> p;
  auto s = make_shared<std::stringstream>(program);
  int r = goat::driver::parse(s, p);
  if(r != 0) return false;
  bool equal = result == *p;

  if(!equal) {
    PrintingVisitor print;
    std::cout << "Result:" << std::endl;
    print.visit(result);
    std::cout << "Should be:" << std::endl;
    print.visit(*p);
  }

  return equal;
}

void test_empty() {
  Program p;
  ok(test("", p), "Parses an empty string");
}

bool program(std::string program, std::shared_ptr<Node> a) {
  Program p;
  auto args = make_shared<NodeList>();
  args->push_back(a);
  p.push_back(args);
  return test(program, p);
}

void test_literals() {
  ok(program("1", make_shared<Number>(1)), "Parses a number");
  ok(program("a", make_shared<Identifier>("a")), "Parses an identifier");
  ok(program("\"Why hello!\"", make_shared<String>("\"Why hello!\"")),
     "Parses a string");
}

void test_math() {
  auto math =
    make_shared<Operation>(
      make_shared<Operation>(
        make_shared<Number>(1),
        make_shared<Number>(1),
        Subtraction),
      make_shared<Operation>(
        make_shared<Number>(2),
        make_shared<Operation>(
          make_shared<Number>(3),
          make_shared<Number>(4),
          Multiplication),
        Division),
      Addition);
  ok(program("1 - 1 + 2 / (3 * 4)", math), "Parses math");
}

void test_function() {
  auto exprs = make_shared<NodeList>();
  exprs->push_back(make_shared<Identifier>("b"));
  exprs->push_back(make_shared<Operation>(make_shared<Number>(1),
                                          make_shared<Number>(2),
                                          Addition));
  auto application = make_shared<Application>(make_shared<Identifier>("a"),
                                              exprs);
  ok(program("a(b, 1 + 2)", application), "Parses a function application");

  auto args = make_shared<IdentifierList>();
  args->push_back(make_shared<Identifier>("a"));
  args->push_back(make_shared<Identifier>("b"));
  auto fn = make_shared<Function>(args, make_shared<Program>());
  ok(program("program(a, b) do done", fn), "Parses a function declaration");
}

void test_conditional() {
  auto true_block = make_shared<Program>();
  auto true_nodes = make_shared<NodeList>();
  true_nodes->push_back(make_shared<Identifier>("b"));
  true_block->push_back(true_nodes);

  auto false_block = make_shared<Program>();
  auto false_nodes = make_shared<NodeList>();
  false_nodes->push_back(make_shared<Identifier>("c"));
  false_block->push_back(false_nodes);

  ok(program("if a then b else c done", make_shared<Conditional>(
               make_shared<Identifier>("a"),
               true_block,
               false_block)), "Parses a conditional");
  ok(program("if a then b done", make_shared<Conditional>(
               make_shared<Identifier>("a"),
               true_block)), "Parses a true branch conditional");
}

int main() {
  start_test;
  test_empty();
  test_literals();
  test_math();
  test_function();
  test_conditional();
}
