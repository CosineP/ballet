open Syntax

(* Implements a CEK machine *)
(* Currently actually implements a CSK machine for state and using substitution
   to more closely match my paper rules.  CEK is a future optimization *)

exception Todo
exception Impossible

type loc = int
[@@deriving show]

type vnop =
  | T
  | F
  | LamV of id * exp * env
  | TLamV of pv * vnop
  | RcdV of (label * vnop) list
  | Loc of loc
[@@deriving show]

(* Is this still used? *)
and value = place * vnop
[@@deriving show]

and env = (id * value) list
[@@deriving show]
and penv = (pv * place) list
[@@deriving show]

type ctrl =
  | Exp of exp
  | Val of value
[@@deriving show]

type ctx =
  | Fun of place * id * exp * env
  | Arg of exp
  | Flds of place * (label * vnop) list * label * (label * exp) list
  | Lbl of label
  | RefP of place
  | SendP of place
  | DrfC
  | SrfL of exp
  | SrfR of place * loc
  | TFun of pv
  | TArg of place
[@@deriving show]

type cont = ctx list
[@@deriving show]

let send p q c e k =
  (* i want to use an effect for this but i don't have ocaml 5 *)
  print_endline @@ "MESSAGE (" ^ show_place p ^ "->" ^ show_place q ^ "): ("
    ^ show_ctrl c ^ ", " ^ show_env e ^ ", " ^ show_cont k ^ ")"

let next_loc = ref 0

let floc () = next_loc := !next_loc + 1; !next_loc

type m = {
  pe: penv;
  e: env;
  s: (loc * value) list;
}

let step (c, m, k) = match (c, k) with
  (* i don't like that this is None... but no "step" really happened! *)
  (* Could: split into (admin c k = c k) and (step c e s k = p c e s k) *)
  | (Exp (True p), k) -> (Some p, (Val (p, T), m, k))
  | (Exp (False p), k) -> (Some p, (Val (p, F), m, k))
  | (Exp (Lam (p, x, _, e)), k) -> (Some p, (Val (p, LamV (x, e, m.e)), m, k))
  | (Exp (App (e1, e2)), k) -> (None, (Exp e1, m, Arg e2 :: k))
  | (Exp (Id x), k) -> let (p, v) = List.assoc x m.e in (Some p, (Val (p, v), m, k))
  | (Exp (Rcd (p, (l, e) :: es)), k) -> (Some p, (Exp e, m, Flds (p, [], l, es) :: k))
  | (Exp (Rcd (p, [])), k) -> (Some p, (Val (p, RcdV []), m, k))
  | (Exp (Fld (e, l)), k) -> (None, (Exp e, m, Lbl l :: k))
  | (Exp (Rf (p, e)), k) -> (Some p, (Exp e, m, RefP p :: k))
  | (Exp (Drf e), k) -> (None, (Exp e, m, DrfC :: k))
  | (Exp (Srf (e1, e2)), k) -> (None, (Exp e1, m, SrfL e2 :: k))
  | (Exp (Send (p, e)), k) -> (None, (Exp e, m, SendP p :: k))
  | (Exp (TLam (pv, e)), k) -> (None, (Exp e, m, TFun pv :: k))
  | (Exp (TApp (e, p)), k) -> (None, (Exp e, m, TArg p :: k))
  | (Val (p, LamV (x, e1, env)), Arg e2 :: k) -> (Some p, (Exp e2, m, Fun (p, x, e1, env) :: k))
  | (Val v, Fun (p, x, e, env) :: k) -> (Some p, (Exp e, { m with e = (x, v) :: env }, k))
  | (Val (_, v), Flds (p, vs, vl, (l, e) :: es) :: k) -> (Some p, (Exp e, m, Flds (p, (vl, v) :: vs, l, es) :: k))
  | (Val (_, v), Flds (p, vs, vl, []) :: k) -> (Some p, (Val (p, RcdV ((vl, v) :: vs)), m, k))
  | (Val (p, RcdV es), Lbl l :: k) -> (Some p, (Val (p, List.assoc l es), m, k))
  | (Val (p, v), RefP q :: k) -> let l = floc () in (Some p, (Val (p, Loc l), { m with s = (l, (p, v)) :: m.s }, SendP q :: k))
  | (Val (p, Loc l), DrfC :: k) -> (Some p, (Val (List.assoc l m.s), m, k))
  | (Val (p, Loc l), SrfL e :: k) -> (Some p, (Exp e, m, SrfR (p, l) :: k))
  | (Val v, SrfR (p, l) :: k) -> (Some p, (Val (p, Loc l), { m with s = (l, v) :: m.s (* need to remove old? *) }, k))
  | (Val (p, v), SendP q :: k) -> send p q c m.e k; (Some p, (Val (q, v), m, k))
  | (Val (p, v), TFun pv :: k) -> (Some p, (Val (p, TLamV (pv, v)), m, k))
  | (Val (vp, TLamV (pv, v)), TArg p :: k) -> (None, (Val (vp, v), { m with pe = (pv, p) :: m.pe }, k))
  | _ ->
    print_endline ("unmatched: (" ^ show_ctrl c ^ ", " ^ show_env m.e ^ ", " ^ show_cont k ^ ")");
    raise Todo

let eval e =
  let rec ev p cmk = match cmk with
    | (Val v, m, []) -> (v, m, [])
    | _ ->
      let (q, cmk) = step cmk in
      match (p, q) with
        | (p, Some p') when p = p' -> ev p cmk
        | (p, None) -> ev p cmk
        | (p, Some q) ->
          let (c, m, k) = cmk in
          send p q c m.e k;
          ev q cmk in
  let starting_placement = Named "THE MOTHERFISH" in
  let (v, _, _) = ev starting_placement (Exp e, { pe = []; e = []; s = []; }, []) in
  v

let c = Named "Client"
let s = Named "Server"
let vid = App ((Lam (s, "x", Typ (s, Bool), (Id "x"))), (True s))
let%test "id" = eval vid = (s, T)
let%test "rec" = eval (Rcd (s, [("f", True s)])) = (s, RcdV [("f", T)])
let%test "rec-fld" = eval (Fld (Rcd (s, [("f", True s)]), "f")) = (s, T)
let%test "ref" = eval (Rf (s, (True s))) = (s, Loc 1)
let%test "drf" = eval (Drf (Rf (c, True c))) = (c, T)
let%test "set/deref" = eval (Drf (Srf (Rf (c, True c), (False c)))) = (c, F)
let%test "send" = eval (Send (c, (True s))) = (c, T)
let lamalpha = Lam (s, "x", Typ (Pv "a", Bool), Id "x")
let id = TLam ("a", lamalpha)
let%test "polyid" = eval (App (TApp (id, s), (True s))) = (s, T)
