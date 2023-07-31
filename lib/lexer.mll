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
  | "exists" { EXISTS }
  | "∃" { EXISTS }
  | "μ" { MU }
  | "mu" { MU }
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
  | "xor" { XOR }
  | "⊕" { XOR }
  | "let" { LET }
  | "in" { IN }
  | "as" { AS }
  | "⟳" { SELF}
  | "self" { SELF }
  | "Left" { LEFT }
  | "Right" { RIGHT }
  | '+' { PLUS }
  | "case" { CASE }
  | low letter* { LOW (Lexing.lexeme lexbuf) }
  | cap letter* { CAP (Lexing.lexeme lexbuf) }
  | "α" { CAP (Lexing.lexeme lexbuf) }
  | "β" { CAP (Lexing.lexeme lexbuf) }
  | "γ" { CAP (Lexing.lexeme lexbuf) }
  | ';' [^'\n']* '\n' { read lexbuf }
  | ' ' { read lexbuf }
  | '\n' { read lexbuf }
  | eof { EOF }
