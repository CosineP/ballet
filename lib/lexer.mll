{
open Parser
}

let dot = '.'
let low = ['a'-'z']
let cap = ['A'-'Z']
let letter = ['a'-'z' 'A'-'Z']

rule read =
  parse
  | '\\' { LAM }
  | "λ" { LAM }
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
  | ":=" { SRF }
  | ':' { COLON }
  | "ref" { REF }
  | '!' { DRF }
  | "Λ" { CAPLAM }
  | "at" { AT }
  | "send" { SEND }
  | "let" { LET }
  | low letter* { LOW (Lexing.lexeme lexbuf) }
  | cap letter* { CAP (Lexing.lexeme lexbuf) }
  | ' ' { read lexbuf }
  | eof { EOF }
