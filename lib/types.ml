open Syntax
open Base.Exn

exception Todo

type env = (string * typ) list

let psubst_p p pv gnd = match p with
  | Pv pv' when pv = pv' -> gnd
  | _ -> p
let rec psubst_t typ pv gnd = match typ with
  | Typ (p, b) -> Typ (psubst_p p pv gnd, psubst_b b pv gnd)
  | Forall (pv', _) when pv = pv' -> typ
  | Forall (pv', t) -> Forall (pv', psubst_t t pv gnd)
and psubst_b base pv gnd = match base with
  | Arr (t1, t2) -> Arr (psubst_t t1 pv gnd, psubst_t t2 pv gnd)
  | Record fs -> Record (List.map (fun (l, t) -> (l, psubst_t t pv gnd)) fs)
  | (Bool | Mu _ | Tv _ | Ref _) -> base

let rec bsubst_t typ tv gnd = match typ with
  | Typ (p, b) -> Typ (p, bsubst_b b tv gnd)
  | Forall _ -> raise Todo (* Can you unfold a polymorphic recursive type? *)
and bsubst_b base tv gnd = match base with
  | Bool -> base
  | Arr (t1, t2) -> Arr (bsubst_t t1 tv gnd, bsubst_t t2 tv gnd)
  | Record fs -> Record (List.map (fun (l, t) -> (l, bsubst_t t tv gnd)) fs)
  | Mu _ -> raise Todo (* Can you unfold a recursive type under a different type variable? *)
  | Tv tv' when tv = tv' -> gnd
  | Tv _ -> base
  | Ref b -> Ref (bsubst_b b tv gnd)

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
    psubst_t t pv p
  | Unfd (mutvu, e) ->
    let Typ (p, Mu (tv, u)) = tp gm e in
    let Mu (tv', u') = mutvu in
    assert (tv = tv');
    assert (u = u');
    Typ (p, bsubst_b u tv (Mu (tv, u)))
  | Fd (mutvu, e) ->
    let Typ (p, unfd) = tp gm e in
    let Mu (tv, u) = mutvu in
    assert (bsubst_b u tv mutvu = unfd);
    Typ (p, mutvu)

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
let inf = Mu ("a", Ref (Tv "a"))
let fold_unfold_x = Fd (inf, Unfd (inf, Id "x"))
let%test "fold-unfold" = tp [] (Lam (Server, "x", Typ (Server, inf), fold_unfold_x)) = Typ (Server, Arr (Typ (Server, inf), Typ (Server, inf)))
