
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
%token <keyword> RETURNS "->"
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
| statements
;

statements:
  statement
| statements statement
;

statement:
  expression
| declaration
;

string: STRING;
number: NUMBER;
ident: IDENT;

expression:
  string
| number
| ident
| function
| application
| conditional
| math
| '(' expression ')'
;

math:
  expression '+' expression
| expression '-' expression
| expression '/' expression
| expression '*' expression
;

arguments:
  %empty
| declaration
| arguments ',' declaration
;

function:
  PROGRAM '(' arguments ')' DO program DONE
;

application:
  ident '(' call ')'
;

call:
  %empty
| expression
| arguments ',' expression
;

conditional:
  IF expression THEN program DONE
| IF expression THEN program ELSE program DONE
;

type:
  ':' ident
| ':' '(' arguments ')' RETURNS ident
;


declaration:
  ident type
| ident '=' expression
| ident type '=' expression
;
