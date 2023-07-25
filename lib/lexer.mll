{
open Parser
}

let lam = '\\'
let dot = '.'
let low = ['a'-'z']
let cap = ['A'-'Z']
let letter = ['a'-'z' 'A'-'Z']

rule read =
  parse
  | lam { LAM }
  | dot { DOT }
  | "true" { TRUE }
  | "false" { FALSE }
  | "bool" { BOOL }
  | "->" { ARR }
  | "forall" { FORALL }
  | "∀" { FORALL }
  | '(' { LP }
  | ')' { RP }
  | '{' { LB }
  | '}' { RB }
  | '=' { EQ }
  | ',' { COMMA }
  | ':' { COLON }
  | "ref" { REF }
  | low letter* { LOW (Lexing.lexeme lexbuf) }
  | cap letter* { CAP (Lexing.lexeme lexbuf) }
  | ' ' { read lexbuf }
  | eof { EOF }
