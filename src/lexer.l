%{
#include "parser.tab.h"
%}

%option bison-bridge
%option bison-locations

%%

program {
  return PROGRAM;
}

if {
  return IF;
}

do {
  return DO;
}

done {
  return DONE;
}

start at {
  return START_AT;
}

repeat {
  return REPEAT;
}

times {
  return TIMES;
}

box {
  return BOX;
}

is {
  return IS;
}

-> {
  return RETURNS;
}

return {
  return RETURN;
}

-?[[:digit:]]+"."[[:digit:]]* {
  yylval->num = atoi(yytext);
  return NUMBER;
}

[[:alnum:]]+ {
  yylval->id = strdup(yytext);
  return IDENT;
}

"="|"("|")"|"*"|"/"|"+"|"-"|":" {
  return yytext[0];
}

[ \t]+

%%
