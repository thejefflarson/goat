#include <sstream>
#include <typeinfo>
#include "driver.hh"
#include "inference.hh"
#include "node.hh"
#include "util.hh"
#include "visitor.hh"
#include "tap.h"

using namespace std;
using namespace goat::node;
using namespace goat::inference;
using namespace goat::util;

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

  void visit(const Argument &argument) {
    std::cout << "Argument" << std::endl;
    argument.identifier()->accept(*this);
    argument.expression()->accept(*this);
  }

  void visit(const Function &function) {
    std::cout << "Function" << std::endl;
    list_accept(function.arguments(), *this);
    function.program()->accept(*this);
  }

  void visit(const Application &application) {
    std::cout << "Application" << std::endl;
    application.identifier()->accept(*this);
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
  auto s = std::stringstream(program);
  int r = goat::driver::parse(&s, p);

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
  TypeFactory typer;
  Identifier ident = Identifier("a", typer.next());
  ok(ident.type().is<TypeVariable>(), "Returns the right type.");
  ok(program("1", make_shared<Number>(1)), "Parses a number");
  ok(program("a", make_shared<Identifier>("a", typer.next())),
     "Parses an identifier");
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
  TypeFactory typer;
  auto args = make_shared<ArgumentList>();
  args->push_back(make_shared<Argument>(make_shared<Identifier>("c",
                                                                typer.next()),
                                        make_shared<Identifier>("b",
                                                                typer.next())));
  args->push_back(make_shared<Argument>(make_shared<Identifier>("d",
                                                                typer.next()),
                                         make_shared<Operation>(
                                           make_shared<Number>(1),
                                           make_shared<Number>(2),
                                           Addition)));
  auto application = make_shared<Application>(
    make_shared<Identifier>("a", typer.next()),
    args, typer.next());
  ok(program("a(c: b, d: 1+2)", application), "Parses a function application");

  args = make_shared<ArgumentList>();
  args->push_back(make_shared<Argument>(make_shared<Identifier>("a",
                                                                typer.next()),
                                        make_shared<Number>(10)));
  args->push_back(make_shared<Argument>(make_shared<Identifier>("b",
                                                                typer.next()),
                                        make_shared<Number>(20)));
  auto fn = make_shared<Function>(args, make_shared<Program>(),
                                  FunctionType({typer.next(), typer.next()}));
  ok(program("program(a: 10, b: 20) do done", fn),
     "Parses a function declaration");
}

void test_conditional() {
  TypeFactory typer;
  auto true_block = make_shared<Program>();
  auto true_nodes = make_shared<NodeList>();
  true_nodes->push_back(make_shared<Identifier>("b", typer.next()));
  true_block->push_back(true_nodes);

  auto false_block = make_shared<Program>();
  auto false_nodes = make_shared<NodeList>();
  false_nodes->push_back(make_shared<Identifier>("c", typer.next()));
  false_block->push_back(false_nodes);

  ok(program("if a then b else c done", make_shared<Conditional>(
               make_shared<Identifier>("a", typer.next()),
               true_block,
               false_block)), "Parses a conditional");
  ok(program("if a then b done", make_shared<Conditional>(
               make_shared<Identifier>("a", typer.next()),
               true_block)), "Parses a true branch conditional");
}

std::shared_ptr<Program> parse_program(std::string program) {
  std::shared_ptr<Program> p;
  auto s = std::stringstream(program);
  int r = goat::driver::parse(&s, p);
  ok(r == 0, "Parses program");
  return p;
}

void print_type(Type t) {
  if(t.is<TypeVariable>()) {
    std::cout << t.get<TypeVariable>().id();
  } else if(t.is<NumberType>()) {
    std::cout << "Number";
  } else if(t.is<StringType>()){
    std::cout << "String";
  } else if(t.is<BoolType>()){
    std::cout << "Bool";
  } else if(t.is<NoType>()){
    std::cout << "nil";
  } else if(t.is<FunctionType>()) {
    auto f = t.get<FunctionType>();
    std::cout << "(";
    for(auto a : f.types()) {
      print_type(a);
      std::cout << ", ";
    }
    std::cout << ")";
  } else {
    std::cout << "wauh";
  }
}

void test_inference() {
  // auto p = parse_program("a = 1");
  // auto visitor = TypingVisitor();
  // visitor.visit(*p);
  // auto constraints = visitor.constraints();
  // ok(constraints.size() == 1, "Generates constraints");
  // auto substitutions = visitor.solve();
  // ok(p->type().is<TypeVariable>(), "The type is a variable");
  // ok(substitutions.size() == 1, "Has a substitution");
  // auto subst = *substitutions.begin();
  // ok(subst.left() == p->type(), "Assigns the right variable");
  // ok(subst.right().is<NumberType>(), "Is a number");
  auto p = parse_program("a = 1 b = a");
  auto visitor = TypingVisitor();
  visitor.visit(*p);
  auto substitutions = visitor.solve();
  p = parse_program("b = 3 a = program(b: 1) do b + 2 done x = a(b: b)");
  visitor = TypingVisitor();
  visitor.visit(*p);
  substitutions = visitor.solve();
  //std::cout << substitutions.size() << std::endl;
  //std::cout << visitor.constraints().size() << std::endl;
  //  ok(substitutions.size() == 2, "Generates function substitution");


  for(auto s : visitor.constraints()) {
    print_type(s.variables().first);
    switch(s.relation()) {
    case Relation::Implicit:
      std::cout << " <= ";
      break;
    case Relation::Equality:
      std::cout << " = ";
      break;
    case Relation::Explicit:
      std::cout << " < ";
    }
    print_type(s.variables().second);
    std::cout << std::endl;
  }
  std::cout << "subs" << std::endl;

  for(auto s : substitutions) {
    print_type(s.left());
    std::cout << " = ";
    print_type(s.right());
    std::cout << std::endl;
    if(s.is_error())
      std::cout << "Error!";
  }
  //auto it = substitutions.begin();
  //ok((*it).right().is<FunctionType>(), "Function definition is a function type");
  //ok((*it).right().get<FunctionType>().types()[0].is<NumberType>(), "Function return is a number");
  // it++;
  //ok((*it).right().is<NumberType>(), "Function application is a number");
  //it++;
  //ok((*it).right().is<NumberType>(), "Function application is a number");
}

void test_constraints() {
  auto constraints = std::set<Constraint>();
  auto typer = TypeFactory();
  auto did = constraints.insert(Constraint(Relation::Equality, {typer.next(), typer.next()}));
  ok(did.second, "Inserted a constraint");
  did = constraints.insert(Constraint(Relation::Equality, {typer.next(), typer.next()}));
  ok(did.second, "Inserted another constraint");
  constraints = std::set<Constraint>();
  constraints.insert(Constraint(Relation::Implicit, {NumberType(), NumberType()}));
  ok(constraints.size() == 1, "Inserted a number type constraint");
  auto it = *constraints.begin();
  constraints.erase(it);
  ok(constraints.size() == 0, "Deleted a number type constraint");
}

int main() {
  start_test;
  //test_empty();
  //test_literals();
  //test_math();
  //test_function();
  //test_conditional();
  // eventually these should be in their own file
  test_inference();
  test_constraints();
}
