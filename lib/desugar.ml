open Syntax
open Parse

let s = Named "s"
let dm = Named "dummy"
let tru = True s
let pparse s = let e = parse s in print_endline @@ show_exp @@ e; e
(* Parser tests *)
let%test "parse true" = parse "true s" = tru
let%test "parse lam" = parse {|λs x s bool.true s|} = Lam (s, "x", Typ (s, Bool), tru)
let%test "parse app" = parse {|(λs x s bool.true s) true s|} = App (Lam (s, "x", Typ (s, Bool), tru), tru)
let%test "parse id" = parse {|λs x s bool.x|} = Lam (s, "x", Typ (s, Bool), Id "x")
let%test "parse rcd" = parse {|{x = true s, y = true s} s|} = Rcd (s, ["x", tru; "y", tru])
let%test "parse rcd typ" = parse {|λs x s {x: bool, y: bool}.true s|} = Lam (s, "x", Typ (s, Record ["x", Bool; "y", Bool]), tru)
let%test "parse fld" = parse "x.field" = Fld (Id "x", "field")
let%test "parse ref" = parse "ref s true s" = Rf (s, tru)
let%test "parse drf" = parse "!x" = Drf (Id "x")
let%test "parse srf" = parse "x := true s" = Srf (Id "x", tru)
let lamalpha = Lam (s, "x", Typ (Pv "A", Bool), Id "x")
let id = TLam ("A", lamalpha)
let%test "parse polyid" = parse {|ΛA.λs x A bool.x|} = id
let%test "parse polyapp" = parse {|x at s true s|} = App (TApp (Id "x", s), tru)
let%test "parse send" = parse {|send c true s|} = Send (Named "c", tru)
