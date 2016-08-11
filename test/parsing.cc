#include <sstream>
#include "node.hh"
#include "visitor.hh"
#include "driver.hh"

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
    list_accept(type.arguments(), *this);
  }

  void visit(const Declaration &declaration) {
    std::cout << "Declaration" << std::endl;
    declaration.ident()->accept(*this);
    declaration.type()->accept(*this);
    declaration.expression()->accept(*this);
  }
};

int main() {
  std::shared_ptr<Program> p;
  std::string program = "a = 1 program hello(a) do a = 1 done";
  auto s =  make_shared<std::stringstream>(program);
  goat::driver::parse(s, p);
}