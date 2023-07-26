type tv = string
[@@deriving show]
type pv = string
[@@deriving show]
type id = string
[@@deriving show]
type label = string
[@@deriving show]

type place =
  | Named of string
  | Pv of pv
[@@deriving show]

type base =
  | Bool
  | Arr of typ * typ * pv
  | Record of (label * base) list
  | Mu of tv * base
  | Tv of tv
  | Ref of typ
[@@deriving show]
and typ =
  | Typ of place * base
  | Forall of pv * typ
  | Exists of pv * typ
[@@deriving show]

type exp =
  | True of place
  | False of place
  | Xor of exp * exp
  | Lam of place * id * typ * exp
  | App of exp * exp
  | Id of id
  | Rcd of place * (label * exp) list
  | Fld of exp * label
  | Rf of place * exp
  | Drf of exp
  | Srf of exp * exp
  | TLam of pv * exp
  | TApp of exp * place
  | Fd of base * exp
  | Unfd of base * exp
  | Send of place * exp
  | Pack of place * exp * pv * typ
  | Unpack of pv * id * exp * exp
[@@deriving show]

