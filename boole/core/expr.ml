(*****************************************************************

  expr.ml

 description: types and expressions in Boole


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

type name = String.t

type index = String.t

type level = Var of index | Max of level * level | Z | Suc of level

let rec level_leq l1 l2 =
  match l1, l2 with
    | Z, _ -> true
    | Var i, Var j -> i = j
    | l, Max(m1, m2) -> level_leq l m1 || level_leq l m2
    | Max(l1, l2), m -> level_leq l1 m && level_leq l2 m
    | Suc l1, Suc l2 -> level_leq l1 l2
    | l1, Suc l2 -> level_leq l1 l2
    | _, Z -> false
    | _, Var _ -> false

type sort = Type of level | Bool

let sort_leq s1 s2 =
  match s1, s2 with
    | Bool, _ -> true
    | Type l1, Type l2 -> level_leq l1 l2
    | _ -> false

type cst = Toplevel | Local | Mvar

type binder = Pi | Abst

type t = 
    Sort of sort 
  | Const of cst * name * t
  | DB of int 
  | Bound of binder * name * t * t 
  | App of t * t


      
let rec abst_n v t n = 
  match t with
    | Sort _ | DB _ -> t
    | Const (Local, a, _) when a = v -> DB n
    | Const _ -> t
    | Bound (binder, a, ty, tm) -> 
      Bound (binder, a, abst_n v ty n, abst_n v tm (n+1))
    | App (t1, t2) -> App (abst_n v t1 n, abst_n v t2 n)


let abst v t = abst_n v t 0


let rec subst_n u t n =
  match t with
    | Sort _ | Const _ -> t
    | DB i when i = n -> u
    | DB i when i < n -> DB (n - 1)
    | DB i -> DB i
    | Bound (binder, a, ty, tm) ->
      Bound (binder, a, subst_n u ty n, subst_n u tm (n+1))
    | App (t1, t2) -> App (subst_n u t1 n, subst_n u t2 n)

let subst u t = subst_n u t 0

let rec compare t1 t2 =
  match t1, t2 with
    | Const(c1, a1, _), Const(c2, a2, _) -> 
      let c = Pervasives.compare c1 c2 in
      if c = 0 then
        Pervasives.compare a1 a2
      else c
    | Const _, _ -> -1
    | Sort a, Sort b -> Pervasives.compare a b
    | Sort _, Const _ -> 1
    | Sort _ , _ -> -1
    | DB n, DB m -> Pervasives.compare n m
    | DB _, Const _ | DB _, Sort _ -> 1
    | DB _, _ -> -1
    | Bound (b1, _, ty1, t1), Bound(b2, _, ty2, t2) ->
      let c = Pervasives.compare b1 b2 in
      if c = 0 then
        let c_ty = compare ty1 ty2 in
        if c_ty = 0 then compare t1 t2
        else c_ty
      else c
    | Bound _, Const _ | Bound _, Sort _ | Bound _, DB _ -> 1
    | Bound _, _ -> -1
    | App(t1, u1), App(t2, u2) ->
      let c_t = compare t1 t2 in
      if c_t = 0 then compare u1 u2 else c_t
    | App _, Const _ | App _, Sort _ | App _, DB _ | App _, Bound _ -> 1

let equal t1 t2 = (compare t1 t2 = 0)

let var_count = ref (-1)

let fresh_var v t = 
  var_count := !var_count + 1;
  let name = v^(string_of_int !var_count) in
  (name, Const(Local, name , t))

let rec string_of_level i =
  match i with
    | Var i -> i
    | Max (i, j) -> "max("^(string_of_level i)^","^(string_of_level j)^")"
    | Z -> "0"
    | Suc i -> "s("^(string_of_level i)^")"

let string_of_sort s =
  match s with
    | Type i -> "Type"^(string_of_level i)
    | Bool -> "Bool"

let string_of_binder b =
  match b with
    | Pi -> "pi" 
    | Abst -> "lam"

open Printf

let make_name a = a

let make_index i = i

let name_of cst =
match cst with
  | Const(_, a, _) -> a
  | _ -> assert false

let rec print_term o t =
  match t with
    Sort s -> fprintf o "%s" (string_of_sort s)
  | Const(_, a, _) -> fprintf o "%s" a
  | DB i -> fprintf o "DB(%s)" (string_of_int i)
  | Bound(b, a, ty, tm) ->
    let tm = subst (Const (Local, a, ty)) tm in
    fprintf o "%s %s : %a.%a" (string_of_binder b) a
      print_term ty print_term tm
  | App(t1, t2) ->
    fprintf o "(%a %a)" print_term t1 print_term t2


let rec free_vars t =
  match t with
    | Sort _ | DB _ -> []
    | Const(Local, a, t) -> a::free_vars t
    | Const _ -> []
    | Bound (_, _, t1, t2) -> (free_vars t1) @ (free_vars t2)
    | App (t1, t2) -> (free_vars t1) @ (free_vars t2)

let rec get_app t =
  match t with
    | App (t1, t2) ->
      let hd, ts = get_app t1 in
      (hd, t2::ts)
    | _ -> (t, [])
