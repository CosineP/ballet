open Lexing
open Lexer
open Parser

let parse_exp s =
  let lexbuf = from_string s in
  expp read lexbuf

(* https://borretti.me/article/parsing-menhir-forth *)
(* It only took hours to find an example for this *)
let colnum pos =
  (pos.pos_cnum - pos.pos_bol) - 1

let pos_string pos =
  let l = string_of_int pos.pos_lnum
  and c = string_of_int ((colnum pos) + 1) in
  "line " ^ l ^ ", column " ^ c

let parse s =
  let lexbuf = from_string s in
  try
    sugar read lexbuf
  with Parser.Error ->
    raise (Failure ("Parse error at " ^ (pos_string lexbuf.lex_curr_p)))
