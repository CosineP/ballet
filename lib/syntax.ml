open Format

exception Todo

type tv = string
[@@deriving show]
type pv = string
[@@deriving show]
type id = string
[@@deriving show]
type label = string
[@@deriving show]

type place =
  | Named of string [@printer fun f -> fprintf f "%s"]
  | Pv of pv [@printer fun f -> fprintf f "%s"]
[@@deriving show]

let s f p = pp_print_string f p

type base =
  | Bool
  | Arr of typ * typ * pv
  | Record of (label * base) list
  | Ref of typ
  | Sum of base * base
  | Mu of tv * base
  | Tv of tv
and typ =
  | Typ of place * base
  | Forall of pv * typ
  | Exists of pv * typ

let rec pp_typ f t = match t with
  | Typ (p, b) -> fprintf f "%a %a" pp_place p pp_base b
  | Forall (p, t) -> s f "∀"; s f p; s f "."; pp_typ f t
  | Exists (p, t) -> s f "∃"; s f p; s f "."; pp_typ f t
and pp_base f b = match b with
  | Bool -> s f "bool"
  | Arr (t1, t2, pv) -> s f "⟳"; s f pv; s f  "."; pp_typ f t1; s f " -> "; pp_typ f t2
  | Record fs -> s f "{ "; List.iter (fun (l, t) -> fprintf f "%s: %a, " l pp_base t) fs; s f "}"
  | Ref t -> s f "ref "; pp_typ f t
  | Sum (b1, b2) ->  pp_base f b1; s f " + "; pp_base f b2
  | Mu (tv, b) -> fprintf f "μ%s.%a" tv pp_base b
  | Tv tv -> s f tv
let show_typ t = asprintf "%a" pp_typ t
let show_base b = asprintf "%a" pp_base b

type exp =
  | True of place
  | False of place
  | Xor of exp * exp
  | Lam of place * pv option * id * typ * exp
  | App of exp * exp
  | Id of id
  | Rcd of place * (label * exp) list
  | Fld of exp * label
  | Rf of place * exp
  | Drf of exp
  | Srf of exp * exp
  | Left of exp * base
  | Right of exp * base
  | Case of exp * id * exp * id * exp
  | TLam of pv * exp
  | TApp of exp * place
  | Fd of base * exp
  | Unfd of base * exp
  | Send of place * exp
  | Pack of place * exp * pv * typ
  | Unpack of pv * id * exp * exp
[@@deriving show]

