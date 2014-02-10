(*****************************************************************

  conv.ml

 description: various conversion helpers, including computing
 beta-normal forms


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

open Expr

let hd_beta t =
  match t with
    | App (Bound (Abst, v, _, t1), t2) ->
      subst t2 t1
    | _ -> t
