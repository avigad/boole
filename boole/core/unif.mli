
exception UnsolvableConstr of Elab.constr list

type mvar_assnt

val empty_assnt : mvar_assnt

val mvar_subst : mvar_assnt -> Expr.t -> Expr.t

val first_order : Conv.reduction -> Elab.constr list -> mvar_assnt -> mvar_assnt
