(*****************************************************************

 typing.ml

 description: basic type inference for elaborated
              Boole terms.


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

exception TypeError of Expr.t * Expr.t * Expr.t

exception NotAType of Expr.t * Expr.t

exception NotAPi of Expr.t * Expr.t

exception NotASig of Expr.t * Expr.t

exception KindError of Expr.t * Expr.t

val max_level : Expr.level -> Expr.level -> Expr.level

val pi_level : Expr.level -> Expr.level -> Expr.level

val type_raw : Conv.conv -> Expr.t -> Expr.t

