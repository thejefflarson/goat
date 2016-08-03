#ifndef GOAT_DRIVER_HH
#define GOAT_DRIVER_HH

#include <istream>
#include <memory>

#include "node.hh"
#include "parser.tab.hh"

// this is a silly place to put this, bison
#define YY_DECL goat::parser::symbol_type yylex(goat::location loc)
YY_DECL;

namespace goat {
namespace driver {

void parse(std::unique_ptr<std::istream> const &src);

}
}

#endif
