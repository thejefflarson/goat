#include "node.hh"
#include "visitor.hh"

using namespace goat::node;

#define accept(kls) \
void kls::accept(Visitor &v) { \
  v.visit(*this); \
}

accept(Number)
accept(Identifier)
accept(String)
accept(Program)
accept(Function)
accept(Application)
accept(Conditional)
accept(Operation)
accept(Type)
accept(Declaration)
