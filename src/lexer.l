%{
#include "driver.hh"
#include "parser.tab.hh"
using namespace goat;
static location loc;
%}

%option noyywrap debug

%{
  # define YY_USER_ACTION  loc.columns(yyleng);
%}

%%

%{
  loc.step();
%}

program                          return parser::make_PROGRAM(loc);
if                               return parser::make_IF(loc);
do                               return parser::make_DO(loc);
done                             return parser::make_DONE(loc);
"start at"                       return parser::make_START_AT(loc);
repeat                           return parser::make_REPEAT(loc);
times                            return parser::make_TIMES(loc);
box                              return parser::make_BOX(loc);
is                               return parser::make_IS(loc);
->                               return parser::make_RETURNS(loc);
return                           return parser::make_RETURN(loc);
-?[[:digit:]]+"."[[:digit:]]*    return parser::make_NUMBER(strtod(yytext), loc);
[[:alnum:]]+                     return parser::make_IDENT(yytext, loc);
"="|"("|")"|"*"|"/"|"+"|"-"|":"  return yytext[0];
[\n]+                            loc.lines(yyleng); loc.step();
[ \t]+                           loc.step();

%%
