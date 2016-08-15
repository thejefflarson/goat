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

%x call
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

[[:alpha:]][[:alnum:]]+? {
/* We make the lexer a little smarter because of a shift reduce conflict
   in the grammar. We need to distinguish between a grouping parenthesis
   and a function call, so we use a start condition for that */
  BEGIN(call); return parser::make_IDENT(yytext, loc);
}
<INITIAL,call>"=" { BEGIN(INITIAL); return parser::make_EQUALS(loc); }
<INITIAL,call>"*" { BEGIN(INITIAL); return parser::make_STAR(loc); }
<INITIAL,call>"/" { BEGIN(INITIAL); return parser::make_SLASH(loc); }
<INITIAL,call>"+" { BEGIN(INITIAL); return parser::make_PLUS(loc); }
<INITIAL,call>"-" { BEGIN(INITIAL); return parser::make_MINUS(loc); }
<INITIAL,call>":" { BEGIN(INITIAL); return parser::make_COLON(loc); }
<INITIAL,call>"," { BEGIN(INITIAL); return parser::make_COMMA(loc); }
<call>"("         { BEGIN(INITIAL); return parser::make_CALL(loc); }
"("           return parser::make_LPAREN(loc);
")"           return parser::make_RPAREN(loc);

[\n]+         loc.lines(yyleng); loc.step();
[ \t]+        loc.step();

-?[[:digit:]]+("."[[:digit:]]*)? {
  // todo check for overflow
  return parser::make_NUMBER(strtod(yytext, NULL), loc);
}

%%

using namespace goat;
int driver::parse(std::shared_ptr<std::istream> src,
                  std::shared_ptr<goat::node::Program> &result) {
  location loc;
  yyscan_t scanner;
  yylex_init_extra(src, &scanner);
  parser parser(scanner, loc, result);
  parser.set_debug_level(1);
  int ret = parser.parse();
  yylex_destroy(scanner);
  return ret;
}
