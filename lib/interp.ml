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

(* Can i use values / place values somehow here? *)
type ctx =
  | Fun of place * id * exp
  | Arg of exp
[@@deriving show]

type cont = ctx list
[@@deriving show]

let v_of_e e = match e with
  | True p -> (p, T)
  | False p -> (p, F)
  | Lam (p, x, _, e) -> (p, LamV (x, e))
  | _ -> raise Todo

let rec subst exp x v = match exp with
  | Lam (_, x', _, _) when x = x' -> exp
  | Lam (p, x', t, e) -> Lam (p, x', t, subst e x v)
  | App (e1, e2) -> App (subst e1 x v, subst e2 x v)
  | Id x' when x = x' -> v
  | (True _ | False _ | Id _) -> exp
  | _ -> raise Todo

let step (c, s, k) = match (c, k) with
  (* i don't like that this is None... but no "step" really happened! *)
  | (App (e1, e2), k) -> (None, (e1, s, Arg e2 :: k))
  | (Lam (p, x, _, e1), Arg e2 :: k) -> (Some p, (e2, s, Fun (p, x, e1) :: k))
  | (ve, Fun (p, x, e) :: k) -> (Some p, (subst e x ve, s, k))
  | _ -> raise Todo

let eval e =
  let rec ev p csk = match csk with
    | (c, s, []) when not @@ does_raise (fun () -> v_of_e c) -> (c, s, [])
    | _ ->
      print_endline @@ show_place p;
      let (q, csk) = step csk in
      match (p, q) with
        | (p, Some p') when p = p' -> ev p csk
        | (p, None) -> ev p csk
        | (p, Some q) ->
          let (c, _, k) = csk in
          (* i want to use an effect for this but i don't have ocaml 5 *)
          print_endline @@ "MESSAGE (" ^ show_place p ^ "->" ^ show_place q ^ "): ("
            ^ show_exp c ^ ", " ^ show_cont k ^ ")";
          ev q csk in
  let (ve, _, _) = ev (Named "THE MOTHERFISH") (e, [], []) in
  v_of_e ve

let c = Named "Client"
let s = Named "Server"
let%test "id" = eval (App ((Lam (s, "x", Typ (s, Bool), (Id "x"))), (True s))) = (s, T)
