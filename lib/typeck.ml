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
  | Arr (_, _, pv') when pv = pv' -> base
  | Arr (t1, t2, pv) -> Arr (psubst_t t1 pv gnd, psubst_t t2 pv gnd, pv)
  | Record fs -> Record (List.map (fun (l, t) -> (l, psubst_b t pv gnd)) fs)
  | (Bool | Mu _ | Tv _ | Ref _) -> base

let rec bsubst_t typ tv gnd = match typ with
  | Typ (p, b) -> Typ (p, bsubst_b b tv gnd)
  | Forall _ -> raise Todo (* Can you unfold a polymorphic recursive type? *)
  | Exists _ -> raise Todo (* Can you unfold an existentially qualified type? *)
and bsubst_b base tv gnd = match base with
  | Bool -> base
  | Arr (t1, t2, pv) -> Arr (bsubst_t t1 tv gnd, bsubst_t t2 tv gnd, pv)
  | Record fs -> Record (List.map (fun (l, t) -> (l, bsubst_b t tv gnd)) fs)
  | Mu _ -> raise Todo (* Can you unfold a recursive type under a different type variable? *)
  | Tv tv' when tv = tv' -> gnd
  | Tv _ -> base
  | Ref b -> Ref (bsubst_t b tv gnd)

let rec ok_p dt p = match p with
  | Named _ -> ()
  | Pv pv -> ignore @@ List.find (fun e -> e = pv) dt
and ok_b dt b = match b with
  | (Bool | Tv _) -> ()
  | Arr (t1, t2, pv) -> ok_t (pv::dt) t1; ok_t (pv::dt) t2
  | Record bs -> ignore @@ List.iter (fun (_, b) -> ok_b dt b) bs
  | Mu (_, b) -> ok_b dt b
  | Ref t -> ok_t dt t
and ok_t dt typ = match typ with
  | Typ (p, b) -> ok_p dt p; ok_b dt b
  | (Forall (pv, t) | Exists (pv, t)) -> ok_t (pv :: dt) t

let nextpv = ref 0
let freshpv () = nextpv := !nextpv + 1; "S" ^ (string_of_int !nextpv)

[@@@warning "-8"] (* Most closely matches paper rules *)
let rec tp gm dt exp = match exp with
  | (True p | False p) -> ok_p dt p; Typ (p, Bool)
  | Xor (e1, e2) ->
    let Typ (p, Bool) = tp gm dt e1 in
    let Typ (p', Bool) = tp gm dt e2 in
    assert (p = p');
    Typ (p, Bool)
  | Lam (p, self, x, t1, e) ->
    ok_p dt p;
    let self = match self with
      | None -> freshpv ()
      | Some s -> s in
    let safevar (x, t) = match t with
      | Typ (p', u) when p = p' -> Some (x, Typ (Pv self, u))
      | _ -> None in
    let dt = self :: dt in
    let gm = (x, t1) :: List.filter_map safevar gm in
    let t2 = tp gm dt e in
    Typ (p, Arr (t1, t2, self))
  | App (e1, e2) ->
    let Typ (p, Arr (t1, t2, self)) = tp gm dt e1 in
    let t1' = tp gm dt e2 in
    assert (psubst_t t1 self p = t1');
    psubst_t t2 self p
  | Id x -> List.assoc x gm
  | Rcd (p, fs) ->
    ok_p dt p;
    Typ (p, Record (List.map (fun (l, e) ->
      (l, let Typ (p', u) = tp gm dt e in assert (p = p'); u)) fs))
  | Fld (e, l) ->
    let Typ (p, Record fs) = tp gm dt e in
    Typ (p, List.assoc l fs)
  | Rf (p, e) ->
    ok_p dt p;
    let t = tp gm dt e in
    Typ (p, Ref t)
  | Drf e ->
    let Typ (_, Ref t) = tp gm dt e in
    t
  | Srf (e1, e2) ->
    let Typ (p, Ref t) = tp gm dt e1 in
    let t' = tp gm dt e2 in
    assert (t = t');
    Typ (p, Ref t)
  | TLam (p, e) -> Forall (p, tp gm (p :: dt) e)
  | TApp (e, p) ->
    ok_p dt p;
    let Forall (pv, t) = tp gm dt e in
    psubst_t t pv p
  | Unfd (mutvu, e) ->
    let Typ (p, Mu (tv, u)) = tp gm dt e in
    let Mu (tv', u') = mutvu in
    assert (tv = tv');
    assert (u = u');
    Typ (p, bsubst_b u tv (Mu (tv, u)))
  | Fd (mutvu, e) ->
    let Typ (p, unfd) = tp gm dt e in
    let Mu (tv, u) = mutvu in
    assert (bsubst_b u tv mutvu = unfd);
    Typ (p, mutvu)
  | Send (p, e) ->
    ok_p dt p;
    let Typ (_, u) = tp gm dt e in
    Typ (p, u)
  | Pack (p, e, pv, t) ->
    let tpp = tp gm dt e in
    assert (psubst_t t pv p = tpp);
    ok_t dt (Exists (pv, t));
    Exists (pv, t)
  | Unpack (pv, x, e1, e2) ->
    let Exists (pv', t1) = tp gm dt e1 in
    assert (pv = pv');
    let t2 = tp ((x, t1) :: gm) (pv :: dt) e2 in
    ok_t dt t2;
    t2

(* We can do so much more than client/server.  But this makes testing easier *)
let c = Named "Client"
let s = Named "Server"
let typeof = tp [] []
let pv = "Self"
let%test "bl" = typeof (True s) = Typ (s, Bool)
let server_lam = (Lam (s, Some pv, "x", Typ (s, Bool), (True c)))
let%test "lam" = typeof server_lam = Typ (s, Arr (Typ (s, Bool), Typ (c, Bool), pv))
let%test "hetero app" = does_raise @@ fun () -> typeof (App (server_lam, True c))
let%test "non-lam app" = does_raise @@ fun () -> typeof (App (True c, True c))
let%test "id" = typeof (App ((Lam (s, None, "x", Typ (s, Bool), (Id "x"))), (True s))) = Typ (s, Bool)
let%test "rec-fld" = typeof (Fld (Rcd (s, [("f", (True s))]), "f")) = Typ (s, Bool)
let%test "ref" = typeof (Rf (s, (True s))) = Typ (s, Ref (Typ (s, Bool)))
let%test "set/deref" = typeof (Drf (Srf (Rf (c, True c), (False c)))) = Typ (c, Bool)
let%test "hetero set" = does_raise @@ fun () -> typeof (Srf (Rf (c, True c), (False s)))
let lamalpha = Lam (s, None, "x", Typ (Pv "a", Bool), Id "x")
let id = TLam ("a", lamalpha)
(* Λ is on hold for now!  With the new λ, i'm not sure i even want/need it *)
(* let%test "polyid" = typeof (App (TApp (id, s), (True s))) = Typ (s, Bool) *)
let%test "polyfail" = does_raise @@ fun () -> typeof (App (TApp (id, s), (True c)))
let inf = Mu ("a", Ref (Typ (c, (Tv "a"))))
let fold_unfold_x = Fd (inf, Unfd (inf, Id "x"))
let%test "fold-unfold" = typeof (Lam (s, Some pv, "x", Typ (s, inf), fold_unfold_x)) = Typ (s, Arr (Typ (s, inf), Typ (s, inf), pv))
let%test "send" = typeof (Send (c, True s)) = Typ (c, Bool)
let packed = Pack (c, (True c), "P", Typ (Pv "P", Bool))
let unpack = Unpack ("P", "x", packed, Send (s, Id "x"))
let%test "unpack-pack" = typeof unpack = Typ (s, Bool)
