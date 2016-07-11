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

%type <shared_ptr<Program>> program expressions;
%type <shared_ptr<Node>> expression;
%type <shared_ptr<String>> string;
%type <shared_ptr<Number>> number;
%type <shared_ptr<Identifier>> ident;
%type <shared_ptr<Operation>> math;
%type <NodeList> arguments;
%type <shared_ptr<Function>> function;
%type <shared_ptr<Application>> application;
%type <shared_ptr<Conditional>> conditional;
%type <TypeList> idents;
%type <shared_ptr<Declaration>> declaration;
%type <shared_ptr<Type>> type;


%left '+' '-'
%left '*' '/'
%left '='

%right THEN ELSE

%%

program:
  %empty { $$ = make_shared<Program>(); }
| expressions
;

expressions:
  expression { $$ = make_shared<Program>(); $$->push_back(move($1)); }
| expressions expression { $1->push_back(move($2)); }
;

string: STRING { $$ = make_shared<String>($1); }
number: NUMBER { $$ = make_shared<Number>($1); }
ident: IDENT   { $$ = make_shared<Identifier>($1); }

expression:
  string { $$ = $1; }
| number { $$ = $1; }
| ident { $$ = $1; }
| declaration { $$ = $1; }
| function { $$ = $1; }
| application { $$ = $1; }
| conditional { $$ = $1; }
| math { $$ = $1; }
| '(' expression ')' { $$ = $2; }
;

math:
  expression '+' expression { $$ = make_shared<Operation>($1, $3, Addition); }
| expression '-' expression { $$ = make_shared<Operation>($1, $3, Subtraction); }
| expression '/' expression { $$ = make_shared<Operation>($1, $3, Division); }
| expression '*' expression { $$ = make_shared<Operation>($1, $3, Multiplication); }
;

arguments:
  %empty { $$ = NodeList(); }
| expression { $$ = NodeList(); $$->push_back(move($1)); }
| arguments ',' expression { $1->push_back(move($3)); }
;

function:
  PROGRAM '(' idents ')' DO program DONE { $$ = make_shared<Function>($3, $6); }
;

application:
  ident '(' arguments ')' { $$ = make_shared<Application>($1, $3); }
;

conditional:
  IF expression THEN program DONE { $$ = make_shared<Conditional>($2, $4); }
| IF expression THEN program ELSE program DONE { $$ = make_shared<Conditional>($2, $4, $6); }
;

idents:
  ident { $$ = TypeList(); $$->push_back(make_shared<Type>(move($1))); }
| idents ',' ident { $1->push_back(make_shared<Type>(move($3))); }
;

type:
  ident { $$ = make_shared<Type>($1); }
| '(' idents ')' RETURNS ident { $$ = make_shared<Type>($5, $2); }
;

declaration:
  ident ':' type { $$ = make_shared<Declaration>($1, $3); }
| ident '=' expression { $$ = make_shared<Declaration>($1, $3); }
| ident ':' type '=' expression { $$ = make_shared<Declaration>($1, $3, $5); }
;
