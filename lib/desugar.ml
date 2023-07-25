open Syntax
open Parse

let c = Named "Client"
let s = Named "Server"
let dm = Named "dummy"
(* Parser tests *)
let%test "parse true" = parse "true" = (True dm)
