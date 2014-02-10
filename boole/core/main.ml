

open Expr
open Typing
open Conv

let name_of cst =
match cst with
  | Const(a, _) -> a
  | Mvar(a, _) -> a
  | _ -> assert false

let lam x ty tm = Bound(Abst, name_of x, ty, abst (name_of x) tm)
let pi x ty tm = Bound(Pi, name_of x, ty, abst (name_of x) tm)
let sigma x ty tm = Bound(Sig, name_of x, ty, abst (name_of x) tm)
let forall x ty tm = Bound(Forall, name_of x, ty, abst (name_of x) tm)
let exists x ty tm = Bound(Exists, name_of x, ty, abst (name_of x) tm)

let bool_type = Sort (Expr.Type)
let bool_bool = Sort (Expr.Bool)

let (^) t1 t2 = App(t1, t2)
let cast t1 t2 = Cast(Ctxt [], t1, t2)

let main () =

  let x = Const(make_name "x", bool_type) in
  Printf.printf "t=%a\n" print_term (lam x bool_type (x^x))

let () = main ()
