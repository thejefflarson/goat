#include <sstream>
#include <typeinfo>
#include "driver.hh"
#include "inferer.hh"
#include "node.hh"
#include "renamer.hh"
#include "tap.h"
#include "util.hh"
#include "visitor.hh"

using namespace std;
using namespace goat::node;
using namespace goat::inference;
using namespace goat::renaming;
using namespace goat::util;

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
    std::cout << "NoType";
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

class Printer : public Visitor {
public:
  Printer() {}
  void visit(const EmptyExpression &empty) {
    std::cout << "Empty" << std::endl;
  }

  void visit(const Number &number) {
    std::cout << "Number " << number.value() << std::endl;
  }

  void visit(const Identifier &identifier) {
    std::cout <<
      "Identifier " << identifier.value() <<
      " Internal " << identifier.internal_value() <<
      " Type ";
    print_type(identifier.type());
    std::cout << std::endl;
  }

  void visit(const String &string) {
    std::cout << "String " << string.value() << std::endl;
  }

  void visit(const Program &program) {
    std::cout << "Program" << std::endl;
    program.expression()->accept(*this);
  }

  void visit(const Argument &argument) {
    std::cout << "Argument" << std::endl;
    argument.identifier()->accept(*this);
    if(argument.expression()) argument.expression()->accept(*this);
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
    declaration.expression()->accept(*this);
  }
};

bool test(const std::string program, const Program &result) {
  std::shared_ptr<Program> p;
  auto s = std::stringstream(program);
  int r = goat::driver::parse(&s, p);

  if(r != 0) return false;
  bool equal = result == *p;

  if(!equal) {
    Printer print;
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
  Program p(a);
  return test(program, p);
}

void test_literals() {
  Identifier ident = Identifier("a");
  //ok(ident.type().is<TypeVariable>(), "Returns the right type.");
  ok(program("1", make_shared<Number>(1)), "Parses a number");
  ok(program("a", make_shared<Identifier>("a")),
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
  auto args = make_shared<ArgumentList>();
  args->push_back(make_shared<Argument>(make_shared<Identifier>("c"),
                                        make_shared<Identifier>("b")));
  args->push_back(make_shared<Argument>(make_shared<Identifier>("d"),
                                         make_shared<Operation>(
                                           make_shared<Number>(1),
                                           make_shared<Number>(2),
                                           Addition)));
  auto application = make_shared<Application>(make_shared<Identifier>("a"),
                                              args);
  ok(program("a(c: b, d: 1+2)", application), "Parses a function application");

  args = make_shared<ArgumentList>();
  args->push_back(make_shared<Argument>(make_shared<Identifier>("a"),
                                        make_shared<Number>(10)));
  args->push_back(make_shared<Argument>(make_shared<Identifier>("b"),
                                        make_shared<Number>(20)));
  auto fn = make_shared<Function>(args, make_shared<Program>());
  ok(program("program (a: 10, b: 20) do done", fn),
     "Parses a function declaration");
}

void test_conditional() {
  auto true_block = make_shared<Program>(make_shared<Identifier>("b"));
  auto false_block = make_shared<Program>(make_shared<Identifier>("c"));
  ok(program("if a then b else c done", make_shared<Conditional>(
               make_shared<Identifier>("a"),
               true_block,
               false_block)), "Parses a conditional");
  ok(program("if a then b done", make_shared<Conditional>(
               make_shared<Identifier>("a"),
               true_block)), "Parses a true branch conditional");
}

std::shared_ptr<Program> parse_program(std::string program) {
  std::shared_ptr<Program> p;
  auto s = std::stringstream(program);
  int r = goat::driver::parse(&s, p);
  ok(r == 0, "Parses program");
  return p;
}

void test_cloner() {
  auto program = parse_program("a = 1; b = a; c = program(a: 1) do a done; d = a(a: b)");
  auto cloned = TreeCloner().clone(program);

  ok(*program == *cloned, "Tree cloner can clone a node");
}

void test_renamer() {
  auto program = parse_program("a");
  auto renamed = Renamer().rename(program);
  auto program2 = std::make_shared<Program>(std::make_shared<Identifier>("a"));
  auto renamed2 = Renamer().rename(program2);
  Printer().visit(*renamed2);
  ok(*renamed == *renamed2, "Renamer renames nodes.");
}

void test_inference() {
  auto p = parse_program("a = 1; b = a; c = program(a: a) do a + b done; d = c(a: 1)");
  p = Renamer().rename(p);
  Printer().visit(*p);
  auto inferer = Inferer();
  auto i = inferer.infer(p);

  auto constraints = inferer.constraints();
  std::cout << constraints.size() << std::endl;
  //ok(constraints.size() == 2, "Generates constraints");
  auto substitutions = inferer.solve();
  //ok(p->type().is<TypeVariable>(), "The type is a variable");
  //ok(substitutions.size() == 1, "Has a substitution");
  //auto subst = *substitutions.begin();
  //ok(subst.left() == p->type(), "Assigns the right variable");
  //ok(subst.right().is<NumberType>(), "Is a number");

  //p = parse_program("a = 'Hello'");
  //visitor = Inferer();
  //visitor.visit(&p);
  //constraints = visitor.constraints();
  //substitutions = visitor.solve();
  //subst = *substitutions.begin();
  //ok(subst.right().is<StringType>(), "Infers a string type");

  //p = parse_program("a = 1 b = 'a' c = b c = a");
  //visitor = Inferer();
  //visitor.visit(*p);
  //substitutions = visitor.solve();
  // for(auto a : substitutions) {
  //   ok(a.left().is<TypeVariable>(), "Substitution is assignment");
  //   ok(a.right().is<NumberType>(), "Substitution is a number");
  // }

//  p = parse_program("program c() do 'a' done a = c()");
//  visitor = TypingVisitor();
//  visitor.visit(*p);
//  substitutions = visitor.solve();
  std::cout << substitutions.size() << std::endl;
  std::cout << inferer.constraints().size() << std::endl;


  for(auto s : inferer.constraints()) {
    std::cout << "# ";
    print_type(s.variables().first);
    std::cout << " = ";
    print_type(s.variables().second);
    std::cout << std::endl;
  }
  std::cout << "subs" << std::endl;

  for(auto s : substitutions) {
    std::cout << "# ";
    print_type(s.left());
    std::cout << " = ";
    print_type(s.right());
    std::cout << std::endl;
    if(s.is_error())
      std::cout << "Error!";
  }
}

void test_constraints() {
  auto constraints = std::set<Constraint>();
  auto namer = Namer();
  auto did = constraints.insert(Constraint({
    TypeVariable(namer.next()),
    TypeVariable(namer.next())
  }));
  ok(did.second, "Inserted a constraint");
  did = constraints.insert(Constraint({
    TypeVariable(namer.next()),
    TypeVariable(namer.next())
  }));
  ok(did.second, "Inserted another constraint");
  did = constraints.insert(Constraint({
    TypeVariable(namer.next()),
    TypeVariable(namer.next())
  }));
  ok(did.second, "Inserted a different constraint");
  Type t = TypeVariable(namer.next());
  auto a = Constraint({t, NumberType()});
  auto b = Constraint({t, NumberType()});
  ok(a == b, "Two constraints are equal");
  constraints.insert(Constraint({t, FunctionType({
    TypeVariable(namer.next()),
    TypeVariable(namer.next())
  })}));
  ok(constraints.size() == 4, "Inserted a FunctionType type constraint");
  auto it = constraints.begin();
  constraints.erase(it);
  ok(constraints.size() == 3, "Deleted a FunctionType constraint");
}

int main() {
  start_test;
  test_empty();
  test_literals();
  test_math();
  test_cloner();
  test_renamer();
  test_function();
  test_conditional();
// eventually these should be in their own file
  test_inference();
  test_constraints();
}
