open Expr
open Typing
open Conv
open Elab
open Unif

let lam x ty tm = Bound(Abst, name_of x, ty, abst (name_of x) tm)
let pi x ty tm = Bound(Pi, name_of x, ty, abst (name_of x) tm)

let type0 = Sort (Expr.Type Expr.Z)

let (^) t1 t2 = App(t1, t2)

let top s t = TopLevel(make_name s, ([], t), [])

let local s t = Const(Local, make_name s, t)

let main () =

  let a = top "A" type0 in
  let x = local "x" a in
  let ty = local "X" type0 in
  let a_to_a = pi x a a in
  let f = top "f" a_to_a in
  let dummy = local "_" ty in
  let poly_id = pi ty type0 (pi dummy ty ty) in
  let g = top "g" poly_id in
  let t = lam x a (f^(f^x)) in
  let m1 = fresh_mvar (make_name "m") type0 in
  (* let m2 = fresh_mvar (make_name "m") type0 in *)
  let u = lam x a ((g^m1)^x) in
  Typing.check_core stdout conv t;
  let cs = Elab.make_type_constr t in
  Elab.print_cstr_list stdout cs;
  print_newline ();
  let cs = Elab.make_type_constr u in
  Elab.print_cstr_list stdout cs;
  print_newline ();
  let m = Unif.first_order Conv.hd_beta_norm cs Unif.empty_assnt in
  Typing.check_core stdout conv u;
  Typing.check_core stdout conv (mvar_subst m u)

let () = main ()
