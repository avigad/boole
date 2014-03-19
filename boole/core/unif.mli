
exception UnsolvableConstr of Elab.constrs

type subst

val empty_subst : subst

val mvar_subst : subst -> Expr.t -> Expr.t

type unif = Conv.reduction -> Elab.constr list -> subst -> subst

val fo_unif : unif

val ho_unif : unif

val elab : unif -> Conv.reduction -> Expr.t -> Expr.t

val print_subst : out_channel -> subst -> unit
