%{
#include "driver.hh"
#include "parser.tab.hh"
using namespace goat;
%}

%option noyywrap debug reentrant

%{
  # define YY_USER_ACTION loc.columns(yyleng);
%}

%%

%{
  loc.step();
%}
<<EOF>>       return parser::make_END(loc);
program       return parser::make_PROGRAM(loc);
if            return parser::make_IF(loc);
do            return parser::make_DO(loc);
done          return parser::make_DONE(loc);
"start at"    return parser::make_START_AT(loc);
repeat        return parser::make_REPEAT(loc);
times         return parser::make_TIMES(loc);
box           return parser::make_BOX(loc);
is            return parser::make_IS(loc);
->            return parser::make_RETURNS(loc);
return        return parser::make_RETURN(loc);
[[:alnum:]]+  return parser::make_IDENT(yytext, loc);
"="           return parser::make_EQUALS(loc);
"("           return parser::make_LPAREN(loc);
")"           return parser::make_RPAREN(loc);
"*"           return parser::make_STAR(loc);
"/"           return parser::make_SLASH(loc);
"+"           return parser::make_PLUS(loc);
"-"           return parser::make_MINUS(loc);
":"           return parser::make_COLON(loc);
[\n]+         loc.lines(yyleng); loc.step();
[ \t]+        loc.step();

-?[[:digit:]]+"."[[:digit:]]* {
  // todo check for overflow
  return parser::make_NUMBER(strtod(yytext, NULL), loc);
}

%%

void goat::driver::parse(std::unique_ptr<std::istream> &str) {

}
