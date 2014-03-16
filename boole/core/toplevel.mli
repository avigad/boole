exception NotFound of string

val top_ctxt : Context.t ref

val make_var : string -> Expr.t
val pi : string -> Expr.t -> Expr.t -> Expr.t
val lambda : string -> Expr.t -> Expr.t -> Expr.t
val sigma : string -> Expr.t -> Expr.t -> Expr.t
val app : Expr.t -> Expr.t -> Expr.t
val fst : Expr.t -> Expr.t
val snd : Expr.t -> Expr.t
val pair : string -> Expr.t -> Expr.t -> Expr.t -> Expr.t

val wild : unit -> Expr.t
val dummy : Expr.t
val type0 : Expr.t
val type1 : Expr.t

val elab : Expr.t -> Expr.t
val check : Expr.t -> unit

val add_top : string -> Expr.t -> unit