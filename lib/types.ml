open Syntax
open Base.Exn

exception Todo

type env = (string * typ) list

let psubst p pv gnd = match p with
  | Pv pv' when pv = pv' -> gnd
  | _ -> p
let rec tsubst typ pv gnd = match typ with
  | Typ (p, b) -> Typ (psubst p pv gnd, bsubst b pv gnd)
  | Forall (pv', _) when pv = pv' -> typ
  | Forall (pv', t) -> Forall (pv', tsubst t pv gnd)
and bsubst base pv gnd = match base with
  | Arr (t1, t2) -> Arr (tsubst t1 pv gnd, tsubst t2 pv gnd)
  | Record fs -> Record (List.map (fun (l, t) -> (l, tsubst t pv gnd)) fs)
  | (Bool | Mu _ | Tv _ | Ref _) -> base

[@@@warning "-8"] (* Most closely matches paper rules *)
let rec tp gm exp = match exp with
  | (True p | False p) -> Typ (p, Bool)
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
  | TLam (p, e) -> Forall (p, tp gm e)
  | TApp (e, p) ->
    let Forall (pv, t) = tp gm e in
    tsubst t pv p
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
let lamalpha = Lam (Server, "x", Typ (Pv "a", Bool), Id "x")
let id = TLam ("a", lamalpha)
let%test "polyid" = tp [] (App (TApp (id, Server), (True Server))) = Typ (Server, Bool)
let%test "polyfail" = does_raise @@ fun () -> tp [] (App (TApp (id, Server), (True Client)))
