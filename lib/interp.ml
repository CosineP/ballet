open Syntax
open Base.Exn

(* Implements a CEK machine *)
(* Currently actually implements a CSK machine for state and using substitution
   to more closely match my paper rules.  CEK is a future optimization *)

exception Todo

type loc = string
[@@deriving show]

(* Is this still used? *)
type vnop =
  | T
  | F
  | LamV of id * exp
  | RcdV of (label * vnop) list
  | Loc of loc
[@@deriving show]

(* Is this still used? *)
type value = place * vnop
[@@deriving show]

type env = (id * exp) list
[@@deriving show]

(* Can i use values / place values somehow here? *)
type ctx =
  | Fun of place * id * exp * env
  | Arg of exp
  | Flds of place * (label * exp) list * label * (label * exp) list
  | Lbl of label
[@@deriving show]

type cont = ctx list
[@@deriving show]

let rec v_of_e e = match e with
  | True p -> (p, T)
  | False p -> (p, F)
  | Lam (p, x, _, e) -> (p, LamV (x, e))
  | Rcd (p, fs) -> (p, RcdV (List.map (fun (l, e) -> let (_, v) = v_of_e e in (l, v)) fs))
  | _ -> raise Todo

let is_v e = not @@ does_raise (fun () -> v_of_e e)

let send p q c e k =
  (* i want to use an effect for this but i don't have ocaml 5 *)
  print_endline @@ "MESSAGE (" ^ show_place p ^ "->" ^ show_place q ^ "): ("
    ^ show_exp c ^ ", " ^ show_env e ^ ", " ^ show_cont k ^ ")"

let step (c, ((env_p, binds) as env), s, k) = match (c, k) with
  (* i don't like that this is None... but no "step" really happened! *)
  | (App (e1, e2), k) -> (None, (e1, env, s, Arg e2 :: k))
  | (Lam (p, x, _, e1), Arg e2 :: k) -> (Some p, (e2, env, s, Fun (p, x, e1, binds) :: k))
  | (ve, Fun (p, x, e, env) :: k) -> (Some p, (e, (p, (x, ve) :: env), s, k))
  | (Id x, k) -> (Some env_p, (List.assoc x binds, env, s, k))
  | (Rcd (p, (l, e) :: es), k) when not (is_v c) -> (Some p, (e, env, s, Flds (p, [], l, es) :: k))
  | (ve, Flds (p, vs, vl, (l, e) :: es) :: k) -> (Some p, (e, env, s, Flds (p, (vl, ve) :: vs, l, es) :: k))
  | (ve, Flds (p, vs, vl, []) :: k) -> (Some p, (Rcd (p, (vl, ve) :: vs), env, s, k))
  | (Fld (e, l), k) -> (None, (e, env, s, Lbl l :: k))
  | (Rcd (p, es), Lbl l :: k) -> (Some p, (List.assoc l es, env, s, k))
  | _ -> raise Todo

let eval e =
  let rec ev p cesk = match cesk with
    | (c, e, s, []) when is_v c -> (c, e, s, [])
    | _ ->
      let (q, cesk) = step cesk in
      match (p, q) with
        | (p, Some p') when p = p' -> ev p cesk
        | (p, None) -> ev p cesk
        | (p, Some q) ->
          let (c, (_, e), _, k) = cesk in
          send p q c e k;
          ev q cesk in
  let starting_placement = Named "THE MOTHERFISH" in
  let (ve, _, _, _) = ev starting_placement (e, (starting_placement, []), [], []) in
  v_of_e ve

let c = Named "Client"
let s = Named "Server"
let vid = App ((Lam (s, "x", Typ (s, Bool), (Id "x"))), (True s))
let%test "id" = eval vid = (s, T)
let%test "rec" = eval (Rcd (s, [("f", vid)])) = (s, RcdV [("f", T)])
let%test "rec-fld" = eval (Fld (Rcd (s, [("f", vid)]), "f")) = (s, T)
