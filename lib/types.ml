open Syntax
open Base.Exn

exception Todo

type env = (string * typ) list

[@@@warning "-8"] (* Most closely matches paper rules *)
let rec tp gm exp = match exp with
  | True p -> Typ (p, Bool)
  | False p -> Typ (p, Bool)
  | Lam (p, x, t, e) -> 
    let gm = (x, t) :: gm in
    let s = tp gm e in
    Typ (p, Arr (t, s))
  | App (e1, e2) ->
    let Typ (p, Arr (Typ (p', u), t)) = tp gm e1 in
    assert (p = p');
    let Typ (p', u') = tp gm e2 in
    assert (p = p');
    assert (u = u');
    t
  | Id x -> List.assoc x gm
  | Rcd (p, fs) ->
    Typ (p, Record (List.map (fun (l, e) -> (l, tp gm e)) fs))
  | Fld (e, l) ->
    let Typ (_, Record fs) = tp gm e in
    List.assoc l fs
  | Rf (p, e) ->
    let Typ (p', u) = tp gm e in
    assert (p = p');
    Typ (p, Ref u)
  | Drf e ->
    let Typ (p, Ref u) = tp gm e in
    Typ (p, u)
  | Srf (e1, e2) ->
    let Typ (p, Ref u) = tp gm e1 in
    let Typ (p', u') = tp gm e2 in
    assert (p = p');
    assert (u = u');
    Typ (p, Ref u)
  | _ -> raise Todo

let%test "bl" = tp [] (True Server) = Typ (Server, Bool)
let server_lam = (Lam (Server, "x", Typ (Server, Bool), (True Client)))
let%test "lam" = tp [] server_lam = Typ (Server, Arr (Typ (Server, Bool), Typ (Client, Bool)))
let%test "hetero app" = does_raise @@ fun () -> tp [] (App (server_lam, True Client))
let%test "non-lam app" = does_raise @@ fun () -> tp [] (App (True Client, True Client))
let%test "id" = tp [] (App ((Lam (Server, "x", Typ (Server, Bool), (Id "x"))), (True Server))) = Typ (Server, Bool)
let%test "rec-fld" = tp [] (Fld (Rcd (Server, [("f", (True Server))]), "f")) = Typ (Server, Bool)
let%test "ref" = tp [] (Rf (Server, (True Server))) = Typ (Server, Ref Bool)
let%test "hetero ref" = does_raise @@ fun () -> tp [] (Rf (Server, (True Client)))
let%test "set/deref" = tp [] (Drf (Srf (Rf (Client, True Client), (False Client)))) = Typ (Client, Bool)
let%test "hetero set" = does_raise @@ fun () -> tp [] (Srf (Rf (Client, True Client), (False Server)))
