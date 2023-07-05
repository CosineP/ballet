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
  | Exists (pv', _) when pv = pv' -> typ
  | Exists (pv', t) -> Exists (pv', psubst_t t pv gnd)
and psubst_b base pv gnd = match base with
  | Arr (t1, t2) -> Arr (psubst_t t1 pv gnd, psubst_t t2 pv gnd)
  | Record fs -> Record (List.map (fun (l, t) -> (l, psubst_b t pv gnd)) fs)
  | (Bool | Mu _ | Tv _ | Ref _) -> base

let rec bsubst_t typ tv gnd = match typ with
  | Typ (p, b) -> Typ (p, bsubst_b b tv gnd)
  | Forall _ -> raise Todo (* Can you unfold a polymorphic recursive type? *)
  | Exists _ -> raise Todo (* Can you unfold an existentially qualified type? *)
and bsubst_b base tv gnd = match base with
  | Bool -> base
  | Arr (t1, t2) -> Arr (bsubst_t t1 tv gnd, bsubst_t t2 tv gnd)
  | Record fs -> Record (List.map (fun (l, t) -> (l, bsubst_b t tv gnd)) fs)
  | Mu _ -> raise Todo (* Can you unfold a recursive type under a different type variable? *)
  | Tv tv' when tv = tv' -> gnd
  | Tv _ -> base
  | Ref b -> Ref (bsubst_t b tv gnd)

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
    Typ (p, Record (List.map (fun (l, e) ->
      (l, let Typ (p', u) = tp gm e in assert (p = p'); u)) fs))
  | Fld (e, l) ->
    let Typ (p, Record fs) = tp gm e in
    Typ (p, List.assoc l fs)
  | Rf (p, e) ->
    let t = tp gm e in
    Typ (p, Ref t)
  | Drf e ->
    let Typ (_, Ref t) = tp gm e in
    t
  | Srf (e1, e2) ->
    let Typ (p, Ref t) = tp gm e1 in
    let t' = tp gm e2 in
    assert (t = t');
    Typ (p, Ref t)
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
  | Send (p, e) ->
    let Typ (_, u) = tp gm e in
    Typ (p, u)
  | Pack (p, e, pv, t) ->
    let tpp = tp gm e in
    assert (psubst_t t pv p = tpp);
    (* TODO: Delta *)
    Exists (pv, t)
  | Unpack (pv, x, e1, e2) ->
    let Exists (pv', t1) = tp gm e1 in
    assert (pv = pv');
    let t2 = tp ((x, t1) :: gm) e2 in
    (* TODO: Delta *)
    t2

(* We can do so much more than client/server.  But this makes testing easier *)
let c = Named "Client"
let s = Named "Server"
let%test "bl" = tp [] (True s) = Typ (s, Bool)
let server_lam = (Lam (s, "x", Typ (s, Bool), (True c)))
let%test "lam" = tp [] server_lam = Typ (s, Arr (Typ (s, Bool), Typ (c, Bool)))
let%test "hetero app" = does_raise @@ fun () -> tp [] (App (server_lam, True c))
let%test "non-lam app" = does_raise @@ fun () -> tp [] (App (True c, True c))
let%test "id" = tp [] (App ((Lam (s, "x", Typ (s, Bool), (Id "x"))), (True s))) = Typ (s, Bool)
let%test "rec-fld" = tp [] (Fld (Rcd (s, [("f", (True s))]), "f")) = Typ (s, Bool)
let%test "ref" = tp [] (Rf (s, (True s))) = Typ (s, Ref (Typ (s, Bool)))
let%test "set/deref" = tp [] (Drf (Srf (Rf (c, True c), (False c)))) = Typ (c, Bool)
let%test "hetero set" = does_raise @@ fun () -> tp [] (Srf (Rf (c, True c), (False s)))
let lamalpha = Lam (s, "x", Typ (Pv "a", Bool), Id "x")
let id = TLam ("a", lamalpha)
let%test "polyid" = tp [] (App (TApp (id, s), (True s))) = Typ (s, Bool)
let%test "polyfail" = does_raise @@ fun () -> tp [] (App (TApp (id, s), (True c)))
let inf = Mu ("a", Ref (Typ (c, (Tv "a"))))
let fold_unfold_x = Fd (inf, Unfd (inf, Id "x"))
let%test "fold-unfold" = tp [] (Lam (s, "x", Typ (s, inf), fold_unfold_x)) = Typ (s, Arr (Typ (s, inf), Typ (s, inf)))
let%test "send" = tp [] (Send (c, True s)) = Typ (c, Bool)
let packed = Pack (c, (True c), "P", Typ (Pv "P", Bool))
let unpack = Unpack ("P", "x", packed, Send (s, Id "x"))
let%test "unpack-pack" = tp [] unpack = Typ (s, Bool)
