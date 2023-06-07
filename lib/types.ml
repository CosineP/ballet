open Syntax

exception Todo

let typeof e = match e with
  | True place -> Typ (place, Bool)
  | False place -> Typ (place, Bool)
  | other -> raise Todo

