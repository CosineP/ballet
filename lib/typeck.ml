open Syntax
open Base.Exn

exception Todo

type env = (string * typ) list

let nextpv = ref 0
let freshpv () = nextpv := !nextpv + 1; "S" ^ (string_of_int !nextpv)

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
  | Arr (t1, t2, apv) -> Arr (psubst_t t1 pv gnd, psubst_t t2 pv gnd, apv)
  | Record fs -> Record (List.map (fun (l, t) -> (l, psubst_b t pv gnd)) fs)
  | Ref t1 -> Ref (psubst_t t1 pv gnd)
  | Sum (b1, b2) -> Sum (psubst_b b1 pv gnd, psubst_b b2 pv gnd)
  | (Bool | Mu _ | Tv _) -> base

let%test "arr doesnt change pv" =
  let id = Arr (Typ (Pv "S", Bool), Typ (Pv "S", Bool), "S") in
  psubst_b id "Other" (Named "nothere") = id

let rec bsubst_t typ tv gnd = match typ with
  | Typ (p, b) -> Typ (p, bsubst_b b tv gnd)
  | Forall (pv, t) -> Forall (pv, bsubst_t t tv gnd)
  | Exists (pv, t) -> Exists (pv, bsubst_t t tv gnd)
and bsubst_b base tv gnd = match base with
  | Bool -> base
  | Arr (t1, t2, pv) -> Arr (bsubst_t t1 tv gnd, bsubst_t t2 tv gnd, pv)
  | Record fs -> Record (List.map (fun (l, t) -> (l, bsubst_b t tv gnd)) fs)
  | Sum (b1, b2) -> Sum (bsubst_b b1 tv gnd, bsubst_b b2 tv gnd)
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
  | Sum (b1, b2) -> ok_b dt b1; ok_b dt b2
  | Mu (_, b) -> ok_b dt b
  | Ref t -> ok_t dt t
and ok_t dt typ = match typ with
  | Typ (p, b) -> ok_p dt p; ok_b dt b
  | (Forall (pv, t) | Exists (pv, t)) -> ok_t (pv :: dt) t

let eq_p p1 p2 = p1 = p2
let rec eq_t t1 t2 = match (t1, t2) with
  | (Typ (p1, b1), Typ (p2, b2)) -> eq_p p1 p2 && eq_b b1 b2
  | (Forall (pv1, t1), Forall (pv2, t2) | Exists (pv1, t1), Exists (pv2, t2)) ->
    let canon = freshpv () in
    eq_t (psubst_t t1 pv1 (Named canon)) (psubst_t t2 pv2 (Named canon))
  | _ -> false
and eq_b t1 t2 = match (t1, t2) with
  | (Arr (t1, s1, pv1), Arr (t2, s2, pv2)) ->
    let canon = freshpv () in
    eq_t (psubst_t t1 pv1 (Named canon)) (psubst_t t2 pv2 (Named canon)) &&
    eq_t (psubst_t s1 pv1 (Named canon)) (psubst_t s2 pv2 (Named canon))
  | (Record fs1, Record fs2) ->
    let pairs = (List.combine (List.sort compare fs1) (List.sort compare fs2)) in
    List.for_all (fun ((l1, t1), (l2, t2)) -> l1 = l2 && eq_b t1 t2) pairs
  | (Ref t1, Ref t2) -> eq_t t1 t2
  | (Sum (b1, c1), Sum (b2, c2)) -> eq_b b1 b2 && eq_b c1 c2
  | (Bool, Bool) -> true
  (* We hope everything is substituted by this point to ensure equality works *)
  | (Tv _, _) | (_, Tv _) -> raise (Failure "not substd")
  | (Mu (tv1, b1), Mu (tv2, b2)) ->
    (* Hack: we need a canonical base type. ref t is a base type, so ref
       S(fresh) bool is a canonical base type *)
    let canon = Ref (Typ (Pv (freshpv ()), Bool)) in
    eq_b (bsubst_b b1 tv1 canon) (bsubst_b b2 tv2 canon)
  | _ -> false

let show_env gm =
  List.fold_left (fun acc -> fun (x,t) -> acc ^ x ^ ":" ^ show_typ t ^ "\n") "--------\n" gm

let assert2 f p a b =
  if f a b then () else
    (Format.printf "failed assert2:\n%a\n%a\n" p a p b; raise (Failure "Typechecking assertion failure"))

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
    assert2 eq_t pp_typ (psubst_t t1 self p) t1';
    psubst_t t2 self p
  | Id x -> List.assoc x gm
  | Let (x, e1, e2) ->
    let t = tp gm dt e1 in
    let gm = (x, t) :: gm in
    tp gm dt e2
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
    assert (eq_t t t');
    Typ (p, Ref t)
  | Left (e, u) ->
    let Sum (u1, _) = u in
    let Typ (p, u1') = tp gm dt e in
    assert (eq_b u1' u1);
    Typ (p, u)
  | Right (e, u) ->
    let Sum (_, u2) = u in
    let Typ (p, u2') = tp gm dt e in
    assert (eq_b u2' u2);
    Typ (p, u)
  | Case (ce, lx, le, rx, re) ->
    let Typ (p, Sum (u1, u2)) = tp gm dt ce in
    let t = tp ((lx, Typ (p, u1)) :: gm) dt le in
    let t' = tp ((rx, Typ (p, u2)) :: gm) dt re in
    assert (eq_t t t');
    t
  | TLam (p, e) -> Forall (p, tp gm (p :: dt) e)
  | TApp (e, p) ->
    ok_p dt p;
    let Forall (pv, t) = tp gm dt e in
    psubst_t t pv p
  | Unfd (mutvu, e) ->
    let Typ (p, (Mu (tv, u) as tvu)) = tp gm dt e in
    assert (eq_b tvu mutvu);
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
let c = Named "c"
let s = Named "s"
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

