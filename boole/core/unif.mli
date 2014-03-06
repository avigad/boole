
exception UnsolvableConstr of Elab.constr list

type subst

val empty_subst : subst

val mvar_subst : subst -> Expr.t -> Expr.t

type unif = Conv.reduction -> Elab.constr list -> subst -> subst

val first_order : unif

val elab : unif -> Conv.reduction -> Expr.t -> Expr.t
