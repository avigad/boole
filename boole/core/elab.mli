
type constr = 
    Eq of Expr.t * Expr.t 
  | HasType of Expr.t * Expr.t
  | IsType of Expr.t

type constrs = constr list

val type_raw : Expr.t -> Expr.t

val make_type_constr : Expr.t -> constrs

val print_cstr : out_channel -> constr -> unit

val print_cstrs : out_channel -> constrs -> unit

val decorate : Expr.t -> Expr.t
