%{
open Syntax
open Sugar
%}

%token EOF
%token TRUE
%token FALSE
%token XOR
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
%token IN
%token AS
%token SELF
%token LEFT
%token RIGHT
%token PLUS
%token CASE

%start <exp> expp
%start <texp> sugar

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
  | SELF EQ CAP IN typ ARR typ { Arr ($5, $7, $3) }
  | SELF CAP DOT typ ARR typ { Arr ($4, $6, $2) }
  | LB lblbases RB { Record $2 }
  | base PLUS base { Sum ($1, $3) }
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
  | exp XOR exp { Xor($1, $3) }
  | LAM place id typ DOT exp { Lam ($2, None, $3, $4, $6) }
  | LAM place AS CAP IN id typ DOT exp { Lam ($2, Some $4, $6, $7, $9) }
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
  | LEFT exp COLON base { Left ($2, $4) }
  | RIGHT exp COLON base { Right ($2, $4) }
  | CASE; c = exp; LEFT; l = id; ARR; le = exp; RIGHT; r = id; ARR; re = exp; { Case (c, l, le, r, re) }
  ;

expp:
  | e = exp; EOF { e }
  ;

sug:
  | LET id EQ sug IN sug { Let ($2, [], $4, $6) }
  | exp { Base $1 }
  ;

sugar:
  | sug EOF { $1 }
  ;

