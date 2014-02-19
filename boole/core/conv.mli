val hd_beta_step : Expr.t -> Expr.t

val hd_beta_norm : Expr.t -> Expr.t

module NMap : Map.S with type key = Expr.name

val unfold : Expr.t -> Expr.name list -> Expr.t NMap.t -> Expr.t

val conv : Expr.t -> Expr.t -> bool
