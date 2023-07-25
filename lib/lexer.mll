{
open Parser
}

let lam = '\\'
let dot = '.'
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

rule read =
  parse
  | lam { LAM }
  | dot { DOT }
  | "true" { TRUE }
  | "false" { FALSE }
  | id { ID (Lexing.lexeme lexbuf) }
  | ' ' { read lexbuf }
  | eof { EOF }
