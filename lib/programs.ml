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

let%test "2ndorder" = typandval {|
  (λc f c c bool -> c bool.f true c) (λc x c bool.x)
|} (Typ (c, Bool)) = (c, T)

let rec alias aliases p = match aliases with
  | [] -> p
  | (x,t)::rest -> alias rest (Str.global_replace (Str.regexp x) t p)

let good_aliases =  [
  ({|\[\]:consumer|}, "fold list consumer Left true s: list unfd consumer");
  ({|list unfd consumer|}, "() + {x: ref consumer, next: list consumer}");
  ({|list consumer|}, "μα.() + {x: ref consumer, next: α}");
  ({|\bconsumer\b|}, "∃P.P (⟳S.S event -> S ())");
  (* Order: we can talk about list event and list bool both! *)
  ({|\bevent\b|}, "bool");
  ({|\[\]:bool|}, "fold list bool Left true s: list unfd bool");
  ({|list unfd bool|}, "() + {x: bool, next: list bool}");
  ({|list bool|}, "μα.() + {x: bool, next: α}");
  ({|()|}, "bool");
]
let traces s = print_endline s; s

let%test "simple list" = ignore @@ run @@ traces @@ alias good_aliases {|
  ref s []:consumer
|}; true

let%test "list ops" = run @@ traces @@ alias good_aliases {|
  let cons (args: s { e: bool, l: list bool }) = fold list bool Right {x = args.e, next = args.l} s: list unfd bool in
  ; No letrec yet
  ; let axor (a: list bool) = case unfd e of
  ;   Left j -> n ⊕ axor
  let example = cons { e = true s, l = cons { e = true s, l = cons { e = false s, l = cons { e = true s, l = []:bool } s } s } s } s in
  case (unfold list bool example)
    Left v -> (false s)
    Right n -> (n.x)
|} = (s, T)

let%test "workspace" = ignore @@ run @@ traces @@ alias good_aliases {|
  case (unfold list bool example)
    Left n -> (n.e)
    Right v -> (false s)
|}; true

let%test "prod-cons so-far" = run @@ traces @@ alias good_aliases {|
  let consumers = ref s []:consumer in
  let queue = ref s []:event in
  ; TODO: put fold around whole expression. Eventually automatically fd/unfd
  ; So, this would work if we didn't curry. But because we curry, e ends up
  ; in the inner lambda's environment, which means we're not allowed to "know"
  ; it lives on the server. Not sure what that says about the language or the
  ; program.
  ; Using a record to get around this for now
  let cons (args: s { e: ref consumer, l: list consumer }) = fold list consumer Right {x = args.e, next = args.l} s: list unfd consumer in
  let consev (args: s { e: event, l: list event }) = fold list event Right {x = args.e, next = args.l} s: list unfd event in
  let listen = λs c consumer.consumers := cons { e = ref s c, l = !consumers } s in
  let enqueue (e: s event) = queue := consev { e = e, l = !queue } s in
  let produce = ΛP.λs e P event.enqueue (send s e) in
  true c
|} = (c, T)

