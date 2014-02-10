

open Expr
open Typing
open Conv

let lam x ty tm = Bound(Abst, make_name x, ty, abst (make_name x) tm)
let pi x ty tm = Bound(Pi, make_name x, ty, abst (make_name x) tm)
let sigma x ty tm = Bound(Sig, make_name x, ty, abst (make_name x) tm)
let forall x ty tm = Bound(Forall, make_name x, ty, abst (make_name x) tm)
let exists x ty tm = Bound(Exists, make_name x, ty, abst (make_name x) tm)

let bool_type = Sort (Expr.Type)
let bool_bool = Sort (Expr.Bool)

let (^) t1 t2 = App(t1, t2)
let cast t1 t2 = Cast(Ctxt [], t1, t2)

let main () = 

  Printf.printf "t=%a\n" print_term (lam "x" bool_type (bool_bool^bool_bool))

let () = main()
