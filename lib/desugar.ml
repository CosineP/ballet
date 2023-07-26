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
let%test "parse let" = parse {|let x = true s|} = [Let ("x", [], tru)]

let rec desugar gm tops outer = match tops with
  | [] -> outer
  | t::rest -> (match t with
    | Let (x, args, e) -> (match List.rev args with
      | [] ->
        (* Let-type-inference is easy! *)
        let t = tp gm [] e in
        App (Lam (dm, None, x, t, desugar ((x, t)::gm) rest outer), e)
      | (a,t)::rrest ->
        desugar gm (Let (x, List.rev rrest, (Lam (dm, None, a, t, e))) :: rest) outer)
    | _ -> raise Todo)

let mtrace e = if false then trace e else e
let suggood sug desug = mtrace (desugar [] (parse sug) (Id "main")) = mtrace (parse_exp desug)
let%test "let" = suggood
  {|let x = true s let main = false c|}
  {|(λdm x s bool.(λdm main c bool.main) false c) true s|}
