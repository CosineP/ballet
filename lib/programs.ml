(* Example programs and such *)

open Parse
open Typeck
open Desugar
open Interp

open Base.Exn

let trace e = print_endline (show_value e); e

let run s =
  let e = desugar [] (parse s) in
  ignore (typeof e);
  eval e

let bad s =
  let e = desugar [] (parse s) in
  does_raise @@ fun () -> typeof e

let typstr s = typeof (desugar [] (parse s))
let typandval s t =
  let e = desugar [] (parse s) in
  assert (t = typeof e);
  eval e

let%test "good λ" = run {|
  let y = true c in
  (λc x c bool.true c ⊕ send c y) true c
|} = (c, F)

let%test "more generic λ" = run {|
  let y = true c in
  (λc as Self in x Self bool.true Self ⊕ y) true c
|} = (c, F)

let%test "bad λ good use" = bad {|
  let y = true c in
  (λc x c bool.true c ⊕ y) true c
|}

let%test "bad λ" = bad {|
  let y = true c in
  (send s (λc x c bool.true c ⊕ y)) true c
|}

let%test "left" = typandval "Left true c: bool + {l: bool}" (Typ (c, Sum (Bool, Record [("l", Bool)]))) = (c, L T)
let%test "case" = typandval {|
  case Left true c: bool + {l: bool}
  Left x -> (x xor false c)
  Right r -> (false c)
|} (Typ (c, Bool)) = (c, T)
