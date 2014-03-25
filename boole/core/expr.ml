(*****************************************************************

  expr.ml

 description: types and expressions in Boole


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

type name = String.t


module NMap = Map.Make(
  struct 
    type t = name 
    let compare = Pervasives.compare 
  end)

type index = String.t

type level = 
    Var of index 
  | Max of level * level 
  | Z 
  | Suc of level
  | LProd of level * level

(* TODO: this is far from complete, it returns false for
   constraints which may be true. We need to take a set of
   constraints as a parameter*)
let rec level_leq l1 l2 =
  match l1, l2 with
    | Z, _ -> true
    | Var i, Var j -> i = j
    | l, Max(m1, m2) -> level_leq l m1 || level_leq l m2
    | Max(l1, l2), m -> level_leq l1 m && level_leq l2 m
    | Suc l1, Suc l2 -> level_leq l1 l2
    | l1, Suc l2 -> level_leq l1 l2
    | LProd (l1, l2), m -> level_leq l2 Z || 
      (level_leq l1 m && level_leq l2 m)
    | l, LProd (m1, m2) -> (level_leq l Z && level_leq m2 Z) ||
      (level_leq l m1 || level_leq l m2)
    | _, Z -> false
    | _, Var _ -> false

type cst = Local | Mvar

type binder = Pi | Abst | Sig

type proj = Fst | Snd

type t = 
    Type of level
  | TopLevel of name * toplevel * level list
  | Const of cst * name * t
  | DB of int 
  | Bound of binder * name * t * t 
  | App of t * t
  | Pair of name * t * t * t
  | Proj of proj * t
and
  (*TODO: add constraints *)
  toplevel = index list * t
      
let rec abst_n v t n = 
  match t with
    | Type _ | DB _ -> t
    | TopLevel _ -> t
    | Const (Local, a, _) when a = v -> DB n
    | Const (Local, _, _) | Const (Mvar, _, _) -> t
    | Bound (binder, a, ty, tm) -> 
      let ty_abst = abst_n v ty n in
      let tm_abst = abst_n v tm (n+1) in
      Bound (binder, a, ty_abst, tm_abst)
    | App (t1, t2) -> App (abst_n v t1 n, abst_n v t2 n)
    | Pair (a, ty, t1, t2) ->
      let ty_abst = abst_n v ty (n+1) in
      let t1_abst = abst_n v t1 n in
      let t2_abst = abst_n v t2 n in
      Pair(a, ty_abst, t1_abst, t2_abst)
    | Proj (p, t) -> Proj (p, abst_n v t n)

let abst v t = abst_n v t 0


let rec subst_n u t n =
  match t with
    | Type _ | Const _
    | TopLevel _ -> t
    | DB i when i = n -> u
    | DB i -> DB i
    | Bound (binder, a, ty, tm) ->
      let ty_sub = subst_n u ty n in
      let tm_sub = subst_n u tm (n+1) in
      Bound (binder, a, ty_sub, tm_sub)
    | App (t1, t2) -> App (subst_n u t1 n, subst_n u t2 n)
    | Pair (a, ty, t1, t2) ->
      let ty_sub = subst_n u ty (n+1) in
      let t1_sub = subst_n u t1 n in
      let t2_sub = subst_n u t2 n in
      Pair (a, ty_sub, t1_sub, t2_sub)
    | Proj (p, t) -> Proj (p, subst_n u t n)


let subst u t = subst_n u t 0

let rec compare t1 t2 =
  match t1, t2 with
    | TopLevel (a1, (_, t1), _), TopLevel (a2, (_, t2), _) ->
      let c = Pervasives.compare a1 a2 in
      if c = 0 then
        compare t1 t2
      else c
    | TopLevel _, _ -> -1
    | Const(c1, a1, _), Const(c2, a2, _) -> 
      let c = Pervasives.compare c1 c2 in
      if c = 0 then
        Pervasives.compare a1 a2
      else c
    | Const _, TopLevel _ -> 1
    | Const _, _ -> -1
    | Type a, Type b -> Pervasives.compare a b
    | Type _, Const _ | Type _, TopLevel _ -> 1
    | Type _ , _ -> -1
    | DB n, DB m -> Pervasives.compare n m
    | DB _, Const _ | DB _, Type _ | DB _, TopLevel _ -> 1
    | DB _, _ -> -1
    | Bound (b1, _, ty1, t1), Bound(b2, _, ty2, t2) ->
      let c = Pervasives.compare b1 b2 in
      if c = 0 then
        let c_ty = compare ty1 ty2 in
        if c_ty = 0 then compare t1 t2
        else c_ty
      else c
    | Bound _, Const _ | Bound _, Type _ 
    | Bound _, DB _ | Bound _, TopLevel _ -> 1
    | Bound _, _ -> -1
    | App(t1, u1), App(t2, u2) ->
      let c_t = compare t1 t2 in
      if c_t = 0 then compare u1 u2 else c_t
    | App _, Const _ | App _, Type _ | App _, DB _ 
    | App _, Bound _ | App _, TopLevel _ -> 1
    | App _, _ -> -1
    | Pair (_, ty1, t1, u1), Pair(_, ty2, t2, u2) -> 
      let c_ty = compare ty1 ty2 in
      if c_ty = 0 then
        let c_t = compare t1 t2 in
        if c_t = 0 then compare u1 u2
        else c_t
      else c_ty
    | Pair _, Const _ | Pair _, Type _ | Pair _, DB _ 
    | Pair _, Bound _ | Pair _, TopLevel _ | Pair _ , App _ -> 1
    | Pair _, _ -> -1
    | Proj (p1, t1), Proj (p2, t2) ->
      let c = Pervasives.compare p1 p2 in
      if c = 0 then compare t1 t2 else c
    | Proj _, _ -> -1

let rec subst_level v l1 l2 =
  match l2 with
    | Var a when a = v -> l1
    | Var _ | Z -> l2
    | Suc m -> Suc (subst_level v l1 m)
    | Max (m1, m2) -> Max(subst_level v l1 m1, subst_level v l1 m2)
    | LProd (m1, m2) -> LProd(subst_level v l1 m1, subst_level v l1 m2)

let rec subst_l v l t =
  match t with
    | DB _
    | TopLevel _ -> t
    | Const(c, a, ty) ->
      let ty_s = subst_l v l ty in
      Const(c, a, ty_s)
    | Type m ->
      let m_s = subst_level v l m in
      Type m_s
    | Bound(b, a, ty, body) ->
      let ty_s = subst_l v l ty in
      let body_s = subst_l v l body in
      Bound(b, a , ty_s, body_s)
    | App(t1, t2) ->
      let t1_s = subst_l v l t1 in
      let t2_s = subst_l v l t2 in
      App(t1_s, t2_s)
    | Pair (a, ty, t1, t2) ->
      let ty_s = subst_l v l ty in
      let t1_s = subst_l v l t1 in
      let t2_s = subst_l v l t2 in
      Pair (a, ty_s, t1_s, t2_s)
    | Proj (p, t) -> 
      let t_s = subst_l v l t in
      Proj (p, t_s)

let equal t1 t2 = (compare t1 t2 = 0)

let rec subst_ls is ls ty =
  match is, ls with
      [], [] -> ty
    | i::is, l::ls -> subst_ls is ls (subst_l i l ty)
    | _ -> assert false

let var_count = ref (-1)

let mvar_count = ref (-1)

let level_count = ref (-1)

let fresh_var v t = 
  incr var_count;
  let name = v^(string_of_int !var_count) in
  (name, Const(Local, name , t))

let fresh_mvar v t = 
  incr mvar_count;
  let name = v^(string_of_int !mvar_count) in
  Const(Mvar, name , t)

let fresh_level v =
  incr level_count;
  let level = v^(string_of_int !level_count) in
  Var level

let open_t v ty tm =
  let (a, c) = fresh_var v ty in
  (a, subst c tm)

let rec free_vars t =
  match t with
    | Type _ | DB _ | TopLevel _ -> []
    | Const(Local, a, t) -> a::free_vars t
    | Const _ -> []
    | Bound (_, _, t1, t2) -> (free_vars t1) @ (free_vars t2)
    | App (t1, t2) -> (free_vars t1) @ (free_vars t2)
    | Pair(_, ty, t1, t2) ->
      (free_vars ty) @ (free_vars t1) @ (free_vars t2)
    | Proj (_, t) -> free_vars t

let rec ivars l =
  match l with
    | Var i -> [i]
    | Z -> []
    | Suc l -> ivars l
    | Max (l1, l2) -> (ivars l1)@(ivars l2)
    | LProd (l1, l2) -> (ivars l1)@(ivars l2)

let rec get_mvars t =
  match t with
    | Type l -> ivars l
    | DB _ | TopLevel _ -> []
    | Const (Mvar, m, t) -> m::get_mvars t
    | Const (Local, _, t) -> get_mvars t
    | Bound (_, _, t1, t2) -> get_mvars t1 @ get_mvars t2
    | App (t1, t2) -> get_mvars t1 @ get_mvars t2
    | Pair(_, ty, t1, t2) ->
      (get_mvars ty) @ (get_mvars t1) @ (get_mvars t2)
    | Proj (_, t) -> get_mvars t

let has_free_vars t = not (free_vars t = [])

let has_mvars t = not (get_mvars t = [])

let rec get_app t =
  match t with
    | App (t1, t2) ->
      let hd, ts = get_app t1 in
      (hd, t2::ts)
    | _ -> (t, [])

let rec make_app t args =
  match args with
    | [] -> t
    | u::us -> make_app (App (t, u)) us


let rec make_bnd b vars t =
  match vars with
    | [] -> t
    | v::vs -> 
        begin match v with
          | Const(Local, a, ty) ->
              let v_t = abst a t in
              make_bnd b vs (Bound (b, a, ty, v_t))
          | _ -> invalid_arg "make_bnd"
        end


let make_abst vars t = make_bnd Abst vars t

let make_pi vars t = make_bnd Pi vars t


let rec int_of_level i =
  match i with
    | Z -> Some 0
    | Suc j -> begin
      match int_of_level j with
        | Some k -> Some (k+1)
        | None -> None
    end
    | _ -> None

let rec string_of_level i =
  match int_of_level i with
      Some m -> string_of_int m
    | None ->
        begin match i with
          | Var i -> i
          | Max (i, j) -> 
              "max("^(string_of_level i)^","^(string_of_level j)^")"
          | LProd (i, j) ->
              "i_max("^(string_of_level i)^","^(string_of_level j)^")"
          | Z -> "0"
          | Suc i -> "s("^(string_of_level i)^")"
        end

let string_of_binder b =
  match b with
    | Pi -> "Π" 
    | Abst -> "λ"
    | Sig -> "Σ"

open Printf

let make_name a = a

let make_index i = i

let name_of cst =
match cst with
  | Const(_, a, _) -> a
  | _ -> invalid_arg "name_of"


let string_of_name a = a

let rec print_term o t =
  match t with
      Type l -> 
        let s = match int_of_level l with
          | Some 0 -> "Bool"
          | Some 1 -> "Type"
          | _ -> "Type "^(string_of_level l)
        in
        fprintf o "%s" s
    | TopLevel (a, _, _) -> fprintf o "%s" a
    | Const(Local, a, _) -> fprintf o "%s" a
    | Const(Mvar, a, _) -> fprintf o "?%s" a
    | DB i -> fprintf o "DB(%s)" (string_of_int i)
    | Bound(b, a, ty, tm) ->
      let tm = subst (Const (Local, a, ty)) tm in
      if not (List.mem a (free_vars tm)) then
        begin
          match b with
            | Pi  -> fprintf o "(%a -> %a)" print_term ty print_term tm
            | Sig -> fprintf o "(%a * %a)" print_term ty print_term tm
            | _   ->
                fprintf o "%s _ : %a.%a" (string_of_binder b)
                  print_term ty print_term tm
        end
      else
        fprintf o "%s %s : %a.%a" (string_of_binder b) a
        print_term ty print_term tm
    | App(t1, t2) ->
      fprintf o "(%a %a)" print_term t1 print_term t2
    | Pair(_, _, t1, t2) ->
      fprintf o "(%a, %a)" print_term t1 print_term t2
    | Proj(Fst, t) ->
      fprintf o "fst(%a)" print_term t
    | Proj(Snd, t) ->
      fprintf o "snd(%a)" print_term t

let print_term_list o ts =
  List.iter (fun t -> fprintf o "%a " print_term t) ts
