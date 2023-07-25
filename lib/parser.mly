%{
open Syntax
let dm = Named "dummy"
%}

%token TRUE
%token FALSE
%token LAM
%token DOT
%token <string> ID
%token EOF

%start <exp> expp

%%

exp:
  | TRUE { True dm }
  | FALSE { False dm }
  | LAM; x = ID; DOT; e = exp { Lam (dm, x, Typ (dm, Bool), e) }
  ;

expp:
  | e = exp; EOF { e }
  ;
