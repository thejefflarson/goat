%{
#include "parser.tab.hh"
using namespace goat;
%}

%option bison-bridge
%option bison-locations

%%

program {
  return parser::make_PROGRAM();
}

if {
  return parser::make_IF();
}

do {
  return parser::make_DO();
}

done {
  return parser::make_DONE();
}

start at {
  return parser::make_START_AT();
}

repeat {
  return parser::make_REPEAT();
}

times {
  return parser::make_TIMES();
}

box {
  return parser::make_BOX();
}

is {
  return parser::make_IS();
}

-> {
  return parser::make_RETURNS();
}

return {
  return parser::make_RETURN();
}

-?[[:digit:]]+"."[[:digit:]]* {
  return parser::make_NUMBER(strtod(yytext));
}

[[:alnum:]]+ {
  return parser::make_IDENT(yytext);
}

"="|"("|")"|"*"|"/"|"+"|"-"|":" {
  return yytext[0];
}

[ \t]+

%%
