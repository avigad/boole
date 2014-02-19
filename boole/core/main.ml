

open Expr
open Typing
open Conv

let lam x ty tm = Bound(Abst, name_of x, ty, abst (name_of x) tm)
let pi x ty tm = Bound(Pi, name_of x, ty, abst (name_of x) tm)
let lpi v t = LBound(LPi, v, t)
let llam v t = LBound(LAbst, v, t)

let type0 = Sort (Expr.Type Expr.Z)
let bool = Sort (Expr.Bool)

let (^) t1 t2 = App(t1, t2)
let (@) t l = LApp(t, l)

let main () =

  let x = Const(Local, make_name "x", type0) in
  let t = lam x type0 (x^x) in
  let ty = Typing.type_raw conv t in
  Printf.printf "%a : %a" print_term t print_term ty

let () = main ()
