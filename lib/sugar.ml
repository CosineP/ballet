open Syntax

type texp =
  | Base of exp
  | Seq of exp * exp
[@@deriving show]

type top =
  | Type of id * typ
  | LetRec of (id * (id * typ) list * exp) list
  | Let of id * (id * typ) list * exp
[@@deriving show]

type program = top list
