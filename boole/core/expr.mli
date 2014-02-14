
type name

type index

type level = Var of index | Max of level * level | Z | Suc of level

type sort = Type of level | Bool | Kind

type cst = Toplevel | Local | Mvar

type binder = Pi | Abst

type ubinder = LPi | LAbst

type t = 
    Sort of sort 
  | Const of cst * name * t 
  | DB of int 
  | Bound of binder * name * t * t 
  | App of t * t 
  | LBound of ubinder * index * t
  | LApp of t * level

val sort_leq : sort -> sort -> bool

val abst : name -> t -> t

val subst : t -> t -> t

val subst_l : index -> level -> t -> t

val compare : t -> t -> int

val equal : t -> t -> bool

val fresh_var : name -> t -> name * t

val make_name : string -> name

val make_index : string -> index

(* Precondition: 
   when calling name_of t, t must be a -constant-!*)
val name_of : t -> name

val print_term : out_channel -> t -> unit

val get_app : t -> t * t list
