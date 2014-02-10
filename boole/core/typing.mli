type constr = Equals of Expr.ctxt * Expr.t * Expr.t
exception TypeError of Expr.t * Expr.t * Expr.t
exception NotASort of Expr.t * Expr.t
exception NotAPi of Expr.t * Expr.t
exception NotASig of Expr.t * Expr.t
type constraints = constr list
val max_sort : Expr.sort -> Expr.sort -> Expr.sort
val type_raw : Expr.t -> Expr.t * constr list
