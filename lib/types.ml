open Syntax

exception Todo
exception No

type env = (string * typ) list

let rec tp gm exp = match exp with
  | True p -> Typ (p, Bool)
  | False p -> Typ (p, Bool)
  | Lam (p, x, t, e) -> 
    let gm = (x, t) :: gm in
    let s = tp gm e in
    Typ (p, Arr (t, s))
  | App (e1, e2) -> (
    match tp gm e1 with
    | Typ (p, Arr (Typ (p', u), t)) -> (
      assert (p = p');
      match tp gm e2 with
      | Typ (p', u') -> (
        assert (p = p');
        assert (u = u');
        t)
      | _ -> raise No)
    | _ -> raise No)
  | _ -> raise Todo

let%test "bl" = tp [] (True Server) = Typ (Server, Bool)
let%test "lam" = tp [] (Lam (Server, "x", Typ (Server, Bool), (True Client))) = Typ (Server, Arr (Typ (Server, Bool), Typ (Client, Bool)))
