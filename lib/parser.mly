%{
open Syntax
open Sugar
%}

%token EOF
%token TRUE
%token FALSE
%token LAM
%token DOT
%token <string> LOW
%token <string> CAP
%token BOOL
%token ARR
%token FORALL
%token LP
%token RP
%token LB
%token RB
%token EQ
%token COMMA
%token COLON
%token REF
%token DRF
%token SRF
%token CAPLAM
%token AT
%token SEND
%token LET

%start <exp> expp
%start <program> program

%%

id:
  | LOW { $1 }
  | CAP { $1 }
  ;

place:
  | LOW { Named $1 }
  | CAP { Pv $1 }
  ;

lblbase: id COLON base { ($1, $3) };
lblbases:
  | lblbase COMMA lblbases { $1 :: $3 }
  | lblbase { [$1] }
  ;

base:
  | BOOL { Bool }
  | typ ARR typ { Arr ($1, $3) }
  | LB lblbases RB { Record $2 }
  ;

typ:
  | place base { Typ ($1, $2) }
  | FORALL CAP typ { Forall ($2, $3) }
  ;

lblexp: id EQ exp { ($1, $3) };
lblexps:
  | lblexp COMMA lblexps { $1 :: $3 }
  | lblexp { [$1] }
  ;

tlam:
  | CAPLAM {}
  | FORALL {}
  ;

exp:
  | TRUE place { True $2 }
  | FALSE place { False $2 }
  | LAM place id typ DOT exp { Lam ($2, $3, $4, $6) }
  | exp exp { App ($1, $2) }
  | LP exp RP { $2 }
  | id { Id $1 }
  | LB lblexps RB place { Rcd ($4, $2) }
  | exp DOT id { Fld ($1, $3) }
  | REF place exp { Rf ($2, $3) }
  | DRF exp { Drf $2 }
  | exp SRF exp { Srf ($1, $3) }
  | tlam id DOT exp { TLam ($2, $4) }
  | exp AT place { TApp ($1, $3) }
  | SEND place exp { Send ($2, $3) }
  ;

expp:
  | e = exp; EOF { e }
  ;

top:
  | LET id EQ exp { Let ($2, [], $4) }
  ;

program:
  | top program { $1 :: $2 }
  | top EOF { [$1] }
  ;