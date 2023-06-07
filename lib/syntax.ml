type tv = string
[@@deriving show]
type pv = string
[@@deriving show]
type id = string
[@@deriving show]
type label = string
[@@deriving show]

type place =
  | Server
  | Client
  | Named of string
  | Pv of string
[@@deriving show]

type base =
  | Bool
  | Arr of typ * typ
  | Record of (string * typ) list
  | Mu of string * base
  | Tv of string
  | Ref of base
[@@deriving show]
and typ =
  | Typ of place * base
  | Forall of string * typ
[@@deriving show]

type exp =
  | True of place
  | False of place
  | Lam of place * id * typ * exp
  | App of exp * exp
  | Id of string
  | Rcd of place * (label * exp) list
  | Fld of exp * label
  (* Send as primitive? *)
  | Rf of place * exp
  | Drf of exp
  | Srf of exp * exp
  | TLam of pv * exp
  | TApp of exp * place
  | Fd of exp
  | Unfd of exp
[@@deriving show]

