
exception UnsolvableConstr of Elab.constr list

type mvar_assnt

val first_order : Elab.constr -> mvar_assnt -> mvar_assnt
