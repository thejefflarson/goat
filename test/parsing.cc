#include "node.hh"
#include "visitor.hh"
#include "driver.hh"

#include <iostream>

using namespace goat::node;


template<typename T>
inline void list_accept(T list, Visitor &v) {
  for(auto i : *list) {
    i->accept(v);
  }
}

class PrintingVisitor : public Visitor {
public:
  void visit(Number &number) {
    std::cout << "Number " << number.value() << std::endl;
  }

  void visit(Identifier &identifier) {
    std::cout << "Identifier " << identifier.value() << std::endl;
  }

  void visit(String &string) {
    std::cout << "String " << string.value() << std::endl;
  }

  void visit(Program &program) {
    std::cout << "Program" << std::endl;
    list_accept(program.nodes(), *this);
  }

  void visit(Function &function) {
    std::cout << "Function" << std::endl;
    list_accept(function.arguments(), *this);
    function.program()->accept(*this);
  }

  void visit(Application &application) {
    std::cout << "Application" << std::endl;
    application.ident()->accept(*this);
  }

  void visit(Conditional &conditional) {
    std::cout << "Conditional" << std::endl;
    conditional.expression()->accept(*this);
    conditional.true_block()->accept(*this);
    conditional.false_block()->accept(*this);
  }

  void visit(Operation &operation) {
    std::cout << "Operation" << std::endl;
    operation.left()->accept(*this);
    operation.right()->accept(*this);
  }

  void visit(Type &type) {
    std::cout << "Type" << std::endl;
    type.ident()->accept(*this);
    list_accept(type.arguments(), *this);
  }

  void visit(Declaration &declaration) {
    std::cout << "Declaration" << std::endl;
    declaration.ident()->accept(*this);
    declaration.type()->accept(*this);
    declaration.expression()->accept(*this);
  }
};

int main() {

}
