

open Expr
open Typing
open Conv
open Unif


let lam x ty tm = Bound(Abst, name_of x, ty, abst (name_of x) tm)
let pi x ty tm = Bound(Pi, name_of x, ty, abst (name_of x) tm)

let type0 = Sort (Expr.Type Expr.Z)

let (^) t1 t2 = App(t1, t2)

let top s t = TopLevel(make_name s, ([], t), [])

let main () =

  let a = top "A" type0 in
  let x = Const(Local, make_name "x", a) in
  let a_to_a = pi x a a in
  let f = top "f" a_to_a in
  let t = lam x a (f^(f^x)) in
  let ty = Typing.type_raw conv t in
  Printf.printf "%a : %a\n" print_term t print_term ty

let () = main ()
