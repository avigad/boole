
open Expr
open Elab

exception UnsolvableConstr of constr list

type mvar_assnt = Expr.t NMap.t

let first_order (csts : constr) (m : mvar_assnt) = m
  
