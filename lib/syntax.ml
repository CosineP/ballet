type tv = string
type pv = string
type id = string
type label = string

type place =
  | Server
  | Client
  | Named of string
  | Pv of string

type base =
  | Bool
  | Arr of typ * typ
  | Record of (string * typ) list
  | Mu of string * base
  | Tv of string
  | Ref of base
and typ =
  | Typ of place * base
  | Forall of string * typ

type exp =
  | True of place
  | False of place
  | Lam of place * id * typ * exp
  | App of exp * exp
  | Rcd of place * (label * exp) list
  | Fld of exp * label
  (* Send as primitive? *)
  | Rf of place * exp (* unplaced refs make this... weird? *)
  | Drf of exp
  | Srf of exp * exp
  | TLam of pv * exp
  | TApp of exp * pv
  | Fd of exp
  | Unfd of exp

