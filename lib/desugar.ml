open Syntax
open Sugar
open Typeck
open Parse

exception Todo

let s = Named "s"
let dm = Named "dm"
let tru = True s
let trace e = print_endline (show_exp e); e
let pparse s = trace (parse_exp s)
(* Parser tests *)
let%test "parse true" = parse_exp "true s" = tru
let%test "parse lam" = parse_exp {|λs x s bool.true s|} = Lam (s, None, "x", Typ (s, Bool), tru)
let%test "parse app" = parse_exp {|(λs x s bool.true s) true s|} = App (Lam (s, None, "x", Typ (s, Bool), tru), tru)
let%test "parse id" = parse_exp {|λs x s bool.x|} = Lam (s, None, "x", Typ (s, Bool), Id "x")
let%test "parse rcd" = parse_exp {|{x = true s, y = true s} s|} = Rcd (s, ["x", tru; "y", tru])
let%test "parse rcd typ" = parse_exp {|λs x s {x: bool, y: bool}.true s|} = Lam (s, None, "x", Typ (s, Record ["x", Bool; "y", Bool]), tru)
let%test "parse fld" = parse_exp "x.field" = Fld (Id "x", "field")
let%test "parse ref" = parse_exp "ref s true s" = Rf (s, tru)
let%test "parse drf" = parse_exp "!x" = Drf (Id "x")
let%test "parse srf" = parse_exp "x := true s" = Srf (Id "x", tru)
let lamalpha = Lam (s, None, "x", Typ (Pv "A", Bool), Id "x")
let id = TLam ("A", lamalpha)
let%test "parse polyid" = parse_exp {|ΛA.λs x A bool.x|} = id
let%test "parse polyapp" = parse_exp {|x at s true s|} = App (TApp (Id "x", s), tru)
let%test "parse send" = parse_exp {|send c true s|} = Send (Named "c", tru)

(* Sugar parser tests *)
let%test "parse let" = parse {|let x = true s in true s|} = Let ("x", [], Base tru, Base tru)

let rec desugar gm exp = match exp with
  | Let (x, args, e1, e2) -> (match List.rev args with
    | [] ->
      (* Let-type-inference is easy! *)
      let e1 = desugar gm e1 in
      let [@warning "-8"] Typ (p, _) as t = tp gm [] e1 in
      App (Lam (p, None, x, t, desugar ((x, t)::gm) e2), e1)
    | (a,t)::rrest ->
      let e1 = desugar gm e1 in
      desugar gm (Let (x, List.rev rrest, (Base (Lam (dm, None, a, t, e1))), e2)))
  | Seq _ -> raise Todo
  | LetRec _ -> raise Todo
  | Base e -> e

let mtrace e = if false then trace e else e
let suggood sug desug = mtrace (desugar [] (parse sug)) = mtrace (parse_exp desug)
let%test "let" = suggood
  {|let x = true s in false c|}
  {|(λs x s bool.false c) true s|}

let%test "2 lets" = suggood
  {|let x = true s in let y = false c in x|}
  {|(λs x s bool.(λc y c bool.x) false c) true s|}

let%test "comments" = suggood
  {|
  ; My big comment here
  let x = true s in
  ; More comment!
  false c
  ; Finishing with a comment
  |}
  {|(λs x s bool.false c) true s|}
