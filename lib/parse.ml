open Lexing
open Lexer
open Parser

let parse s =
  let lexbuf = from_string s in
  expp read lexbuf
