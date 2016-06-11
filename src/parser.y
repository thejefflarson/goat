
%define parse.error verbose

%token <keyword> PROGRAM "program"
%token <keyword> IF "if"
%token <keyword> THEN "then"
%token <keyword> ELSE "else"
%token <keyword> DO "do"
%token <keyword> DONE "done"
%token <keyword> START_AT "start at"
%token <keyword> REPEAT "repeat"
%token <keyword> TIMES "times"
%token <keyword> BOX "box"
%token <keyword> IS "is"
%token <keyword> RETURNS "returns"
%token <keyword> RETURN "return"
%token <integer> NUMBER "number"
%token <ident> IDENT "identifier"
%token <string> STRING "string"

%left '+' '-'
%left '*' '/'

%right THEN ELSE

%%

program:
  %empty
| program statement
;

statement:
  expression
| declaration
;

expression:
  STRING
| IDENT
| NUMBER
| application
| function
| conditional
| expression operator expression
| '(' expression ')'
;

operator:
  '+'
| '-'
| '/'
| '*'
;

function:
  PROGRAM "(" arguments ")" DO program DONE
;

application:
  IDENT "(" arguments ")"
;

arguments:
  IDENT
| arguments "," IDENT
;

conditional:
  IF expression THEN program DONE
| IF expression THEN program ELSE program DONE
;

type:
  IDENT
| "(" arguments ")" RETURNS IDENT
;

declaration:
  IDENT "=" expression
| IDENT ":" type "=" expression
;
