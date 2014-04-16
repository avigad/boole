
type constr = 
    Eq of bool * Expr.t * Expr.t 
  | HasType of bool * Expr.t * Expr.t
  | IsType of bool * Expr.t

type constrs = constr list

val print_cstr : out_channel -> constr -> unit

val print_cstrs : out_channel -> constrs -> unit

val type_raw : Expr.t -> Expr.t

val decorate : Expr.t -> Expr.t

val make_type_constr : Expr.t -> constrs
