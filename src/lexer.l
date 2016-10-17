%{
#include <memory>

#include "driver.hh"
#include "parser.tab.hh"
using namespace goat;
%}

%option noyywrap debug reentrant

%{
#define YY_USER_ACTION loc.columns(yyleng);
#define YY_EXTRA_TYPE std::shared_ptr<std::istream>
%}

%{
#define YY_INPUT(buf, result, max_size) {\
  auto src = yyget_extra(yyscanner); \
  src->read(buf, max_size); \
  result = src->good() ? YY_NULL : src->gcount(); \
}
%}

ident [a-zA-Z\x80-\xff_][a-zA-Z0-9\x80-\xff_]*

%%

%{
  loc.step();
%}

<<EOF>>    return parser::make_END(loc);
program    return parser::make_PROGRAM(loc);
if         return parser::make_IF(loc);
then       return parser::make_THEN(loc);
else       return parser::make_ELSE(loc);
do         return parser::make_DO(loc);
done       return parser::make_DONE(loc);
"start at" return parser::make_START_AT(loc);
repeat     return parser::make_REPEAT(loc);
times      return parser::make_TIMES(loc);
->         return parser::make_RETURNS(loc);
return     return parser::make_RETURN(loc);
{ident}    return parser::make_IDENT(yytext, loc);
"="        return parser::make_EQUALS(loc);
"*"        return parser::make_STAR(loc);
"/"        return parser::make_SLASH(loc);
"+"        return parser::make_PLUS(loc);
"-"        return parser::make_MINUS(loc);
":"        return parser::make_COLON(loc);
","        return parser::make_COMMA(loc);
"("        return parser::make_LPAREN(loc);
")"        return parser::make_RPAREN(loc);
[\n]+      loc.lines(yyleng); loc.step();
[ \t]+     loc.step();

-?[[:digit:]]+("."[[:digit:]]*)? {
  // todo check for overflow
  return parser::make_NUMBER(strtod(yytext, NULL), loc);
}

\"([^\\\"]|\\.)*\"  return parser::make_STRING(yytext, loc);
.          throw parser::syntax_error(loc, "invalid character");
%%

using namespace goat;
int driver::parse(std::shared_ptr<std::istream> src,
                  std::shared_ptr<goat::node::Program> &result) {
  location loc;
  yyscan_t scanner;
  yylex_init_extra(src, &scanner);
  parser parser(scanner, loc, result);
  //parser.set_debug_level(1);
  int ret = parser.parse();
  yylex_destroy(scanner);
  return ret;
}
