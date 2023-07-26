open Syntax

type texp =
  | Base of exp
  | Seq of exp * exp
  | Let of id * (id * typ) list * texp * texp
  | LetRec of (id * (id * typ) list * texp) list * texp
[@@deriving show]

type top =
  | Type of id * typ
[@@deriving show]

type program = top list
