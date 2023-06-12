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
  | Pv of pv
[@@deriving show]

type base =
  | Bool
  | Arr of typ * typ
  | Record of (label * typ) list
  | Mu of tv * base
  | Tv of tv
  | Ref of base
[@@deriving show]
and typ =
  | Typ of place * base
  | Forall of pv * typ
[@@deriving show]

type exp =
  | True of place
  | False of place
  | Lam of place * id * typ * exp
  | App of exp * exp
  | Id of id
  | Rcd of place * (label * exp) list
  | Fld of exp * label
  (* Send as primitive? *)
  | Rf of place * exp
  | Drf of exp
  | Srf of exp * exp
  | TLam of pv * exp
  | TApp of exp * place
  | Fd of base * exp
  | Unfd of base * exp
[@@deriving show]

