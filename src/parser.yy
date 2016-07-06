%{
#include <string>
#include <vector>
#include <memory>
#include "node.hh"
using namespace std;
using namespace goat::node;
%}

%skeleton "lalr1.cc"
%defines
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

%type <unique_ptr<Program>> program statements;
%type <unique_ptr<Node>> statement;
%type <unique_ptr<String>> string;
%type <unique_ptr<Number>> number;
%type <unique_ptr<Identifier>> ident;


%left '+' '-'
%left '*' '/'

%right THEN ELSE

%%

program:
  %empty
| statements
;

statements:
  statement { $$ = unique_ptr<Program>(new Program()); $$->push_back($<statement>1); }
| statements statement { $1->push_back($<statement>2); }
;

statement:
  expression
| declaration
;

string: STRING { $$ = unique_ptr<String>(new String($1)); }
number: NUMBER { $$ = unique_ptr<Number>(new Number($1)); }
ident: IDENT   { $$ = unique_ptr<Identifier>(new Identifier($1)); }

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
| expression
| arguments ',' expression
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
