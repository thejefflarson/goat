#ifndef GOAT_DRIVER_HH_
#define GOAT_DRIVER_HH_

#include <istream>
#include <memory>

#include "node.hh"
#include "parser.tab.hh"

// this is a silly place to put this, bison
#define YY_DECL goat::parser::symbol_type yylex(void *yyscanner, \
                                                goat::location &loc)
YY_DECL;

namespace goat {
namespace driver {

int parse(std::istream *src,
          std::shared_ptr<goat::node::Program> &result);

}  // namespace goat
}  // namespace driver

#endif  // GOAT_DRIVER_HH_
