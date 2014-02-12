

open Expr
open Typing
open Conv

let lam x ty tm = Bound(Abst, name_of x, ty, abst (name_of x) tm)
let pi x ty tm = Bound(Pi, name_of x, ty, abst (name_of x) tm)

let bool_type = Sort (Expr.Type Expr.Z)
let bool_bool = Sort (Expr.Bool)

let (^) t1 t2 = App(t1, t2)


let main () =

  let x = Const(Local, make_name "x", bool_type) in
  Printf.printf "t=%a\n" print_term (lam x bool_type (x^x))

let () = main ()
