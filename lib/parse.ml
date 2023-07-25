open Lexing
open Lexer
open Parser

let parse_exp s =
  let lexbuf = from_string s in
  expp read lexbuf

let parse s =
  let lexbuf = from_string s in
  program read lexbuf
