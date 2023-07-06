open Syntax

(* Implements a CEK machine *)
(* Currently actually implements a CSK machine for state and using substitution
   to more closely match my paper rules.  CEK is a future optimization *)

exception Todo
exception Impossible

type loc = int
[@@deriving show]

(* Is this still used? *)
type vnop =
  | T
  | F
  | LamV of id * exp * env
  | RcdV of (label * vnop) list
  | Loc of loc
[@@deriving show]

(* Is this still used? *)
and value = place * vnop
[@@deriving show]

and env = (id * value) list
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
[@@deriving show]

type cont = ctx list
[@@deriving show]

let send p q c e k =
  (* i want to use an effect for this but i don't have ocaml 5 *)
  print_endline @@ "MESSAGE (" ^ show_place p ^ "->" ^ show_place q ^ "): ("
    ^ show_ctrl c ^ ", " ^ show_env e ^ ", " ^ show_cont k ^ ")"

let next_loc = ref 0

let floc () = next_loc := !next_loc + 1; !next_loc

let step (c, env, s, k) = match (c, k) with
  (* i don't like that this is None... but no "step" really happened! *)
  | (Exp (True p), k) -> (Some p, (Val (p, T), env, s, k))
  | (Exp (False p), k) -> (Some p, (Val (p, F), env, s, k))
  | (Exp (Lam (p, x, _, e)), k) -> (Some p, (Val (p, LamV (x, e, env)), env, s, k))
  | (Exp (App (e1, e2)), k) -> (None, (Exp e1, env, s, Arg e2 :: k))
  | (Val (p, LamV (x, e1, env)), Arg e2 :: k) -> (Some p, (Exp e2, env, s, Fun (p, x, e1, env) :: k))
  | (Val v, Fun (p, x, e, env) :: k) -> (Some p, (Exp e, (x, v) :: env, s, k))
  | (Exp (Id x), k) -> let (p, v) = List.assoc x env in (Some p, (Val (p, v), env, s, k))
  | (Exp (Rcd (p, (l, e) :: es)), k) -> (Some p, (Exp e, env, s, Flds (p, [], l, es) :: k))
  | (Exp (Rcd (p, [])), k) -> (Some p, (Val (p, RcdV []), env, s, k))
  | (Val (_, v), Flds (p, vs, vl, (l, e) :: es) :: k) -> (Some p, (Exp e, env, s, Flds (p, (vl, v) :: vs, l, es) :: k))
  | (Val (_, v), Flds (p, vs, vl, []) :: k) -> (Some p, (Val (p, RcdV ((vl, v) :: vs)), env, s, k))
  | (Exp (Fld (e, l)), k) -> (None, (Exp e, env, s, Lbl l :: k))
  | (Val (p, RcdV es), Lbl l :: k) -> (Some p, (Val (p, List.assoc l es), env, s, k))
  | (Exp (Rf (p, e)), k) -> (Some p, (Exp e, env, s, RefP p :: k))
  | (Val (p, v), RefP q :: k) -> let l = floc () in (Some p, (Val (p, Loc l), env, (l, (p, v)) :: s, SendP q :: k))
  | (Exp (Drf e), k) -> (None, (Exp e, env, s, DrfC :: k))
  | (Val (p, Loc l), DrfC :: k) -> (Some p, (Val (List.assoc l s), env, s, k))
  | (Exp (Srf (e1, e2)), k) -> (None, (Exp e1, env, s, SrfL e2 :: k))
  | (Val (p, Loc l), SrfL e :: k) -> (None, (Exp e, env, s, SrfR (p, l) :: k))
  | (Val v, SrfR (p, l) :: k) -> (None, (Val (p, Loc l), env, (l, v) :: s (* need to remove old? *), k))
  | (Exp (Send (p, e)), k) -> (None, (Exp e, env, s, SendP p :: k))
  | (Val (p, v), SendP q :: k) ->
    send p q c env k;
    (Some p, (Val (q, v), env, s, k))
  | _ ->
    print_endline ("unmatched: (" ^ show_ctrl c ^ ", " ^ show_env env ^ ", " ^ show_cont k ^ ")");
    raise Todo

let eval e =
  let rec ev p cesk = match cesk with
    | (Val v, e, s, []) -> (v, e, s, [])
    | _ ->
      let (q, cesk) = step cesk in
      match (p, q) with
        | (p, Some p') when p = p' -> ev p cesk
        | (p, None) -> ev p cesk
        | (p, Some q) ->
          let (c, e, _, k) = cesk in
          send p q c e k;
          ev q cesk in
  let starting_placement = Named "THE MOTHERFISH" in
  let (v, _, _, _) = ev starting_placement (Exp e, [], [], []) in
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
