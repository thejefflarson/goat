#include "compiling.hh"

using namespace goat;
using namespace node;
using namespace inference;

void CompilingVisitor::visit(const Number &number) {

}

void CompilingVisitor::visit(const Identifier &identifier) {

}

void CompilingVisitor::visit(const String &string) {}
void CompilingVisitor::visit(const Program &program) {}
void CompilingVisitor::visit(const Argument &argument) {}
void CompilingVisitor::visit(const Function &function) {}
void CompilingVisitor::visit(const Application &application) {}
void CompilingVisitor::visit(const Conditional &conditional) {}
void CompilingVisitor::visit(const Operation &operation) {}
void CompilingVisitor::visit(const Declaration &declaration) {}
