
exception TypeError of Expr.t * Expr.t * Expr.t

exception NotASort of Expr.t * Expr.t

exception NotAPi of Expr.t * Expr.t

exception NotASig of Expr.t * Expr.t

exception SortError of Expr.t * Expr.t

exception KindHasNoType

val max_sort : Expr.sort -> Expr.sort -> Expr.sort

val pi_sort : Expr.sort -> Expr.sort -> Expr.sort

val type_raw : (Expr.t -> Expr.t -> bool) -> Expr.t -> Expr.t
