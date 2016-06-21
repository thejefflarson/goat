%define api.namespace {goat}
%define api.token.constructor
%define api.value.type variant
%define parse.assert

%define parse.trace
%define parse.error verbose

%token PROGRAM "program"
%token IF "if"
%token THEN "then"
%token ELSE "else"
%token DO "do"
%token DONE "done"
%token START_AT "start at"
%token REPEAT "repeat"
%token TIMES "times"
%token BOX "box"
%token IS "is"
%token RETURNS "->"
%token RETURN "return"
%token <double> NUMBER "number"
%token <string> IDENT "identifier"
%token <string> STRING "string"
%printer { yyoutput << $$; } <*>;

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
| ident
| arguments ',' ident
;

function:
  PROGRAM '(' arguments ')' DO program DONE
;

application:
  ident '.' '(' call ')'
;

call:
  %empty
| expression
| call ',' expression
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
