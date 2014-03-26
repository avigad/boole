
exception UnsolvableConstr of Elab.constrs

exception MvarNoVal of Expr.t * Expr.name list

type subst

type hints

type unif_info = 
    {red : Conv.reduction; 
     conv : Conv.conv; 
     hints : hints}

val empty_subst : subst

val mvar_subst : subst -> Expr.t -> Expr.t

type unif = unif_info -> Elab.constr list -> subst -> subst

val fo_unif : unif

val ho_unif : unif

val elab : unif -> unif_info -> Expr.t -> Expr.t

val empty_hints : hints

val add_hint : Expr.t -> hints -> hints

val print_subst : out_channel -> subst -> unit
