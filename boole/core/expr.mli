(*****************************************************************

  expr.ml

 description: types and expressions in Boole


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

type name

type index

type level = 
    Var of index 
  | Max of level * level 
  | Z 
  | Suc of level
  | LProd of level * level

type cst = Local | Mvar

type binder = Pi | Abst | Sig

type proj = Fst | Snd

type info = {implicit : bool; cast : bool}

val default_info : info

type t = 
    Type of level
  | TopLevel of name * toplevel * level list
  | Const of cst * name * t
  | DB of int 
  | Bound of info * binder * name * t * t 
  | App of t * t
  | Pair of name * t * t * t
  | Proj of proj * t
and
  toplevel = index list * t



module NMap : Map.S with type key = name



val level_leq : level -> level -> bool

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
   when calling name_of t, t must be a constant*)
val name_of : t -> name

val string_of_name : name -> string

val print_term : out_channel -> t -> unit

val print_term_list : out_channel -> t list -> unit

val get_app : t -> t * t list

val make_app : t -> t list -> t

val make_abst : t list -> t -> t

val make_pi : t list -> t -> t

val free_vars : t -> name list

val get_mvars : t -> t list

val has_mvars : t -> bool
