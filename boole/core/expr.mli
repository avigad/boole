
type name

type sort = Type | Kind | Bool

type binder = Forall | Exists | Pi | Sig | Abst

type t =
    Sort of sort
  | Const of name * t
  | DB of int
  | Bound of binder * name * t * t
  | App of t * t
  | Fst of t
  | Snd of t
  | Pair of name * t * t * t
  | Cast of ctxt * t * t
  | Eq of t * t
  | Mvar of name * t
and ctxt = Ctxt of t list

val abst : name -> t -> t

val subst : t -> t -> t

val compare : t -> t -> int

val equal : t -> t -> bool

val fresh_var : name -> t -> name * t

val make_name : string -> name

val print_term : out_channel -> t -> unit
