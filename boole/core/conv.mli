type reduction

type conv

val hd_beta_step : reduction

val hd_beta_norm : reduction

val unfold : Expr.name list -> Expr.t Expr.NMap.t -> reduction

val conv : conv

val reduce : reduction -> Expr.t -> Expr.t

val check_conv : conv -> Expr.t -> Expr.t -> bool
