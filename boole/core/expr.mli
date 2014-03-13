
type name

type index

type level = Var of index | Max of level * level | Z | Suc of level
             | LProd of level * level

type sort = Type of level

type cst = Local | Mvar

type binder = Pi | Abst | Sig

type proj = Fst | Snd

type t = 
    Sort of sort
  | TopLevel of name * toplevel * level list
  | Const of cst * name * t
  | DB of int 
  | Bound of binder * name * t * t 
  | App of t * t
  | Pair of name * t * t * t
  | Proj of proj * t
and
  toplevel = index list * t

module NMap : Map.S with type key = name

val sort_leq : sort -> sort -> bool

val abst : name -> t -> t

val subst : t -> t -> t

val subst_l : index -> level -> t -> t

val subst_ls : index list -> level list -> t -> t

val compare : t -> t -> int

val equal : t -> t -> bool

val fresh_var : name -> t -> name * t

val fresh_mvar : name -> t -> t

val open_t : name -> t -> t -> name * t

val make_name : string -> name

val make_index : string -> index

(* Precondition: 
   when calling name_of t, t must be a -constant-!*)
val name_of : t -> name

val string_of_name : name -> string

val print_term : out_channel -> t -> unit

val get_app : t -> t * t list

val free_vars : t -> name list

val has_mvars : t -> bool
