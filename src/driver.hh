#ifndef GOAT_DRIVER_HH
#define GOAT_DRIVER_HH

#include <istream>
#include <memory>

#include "node.hh"
#include "parser.tab.hh"

using namespace std;

// this is a silly place to put this, bison
#define YY_DECL goat::parser::symbol_type yylex()
YY_DECL;

namespace goat {
namespace driver {

void parse(unique_ptr<istream> const &parse);

}
}

#endif
