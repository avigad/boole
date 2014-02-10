(*****************************************************************

  expr.ml

 description: types and expressions in Boole


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

type name = String.t

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
and 
  ctxt = Ctxt of t list

      
let rec abst_n v t n = 
  match t with
    | Sort _ | DB _ -> t
    | Const (a, _) when a = v -> DB n
    | Const _ -> t
    | Bound (binder, a, ty, tm) -> 
      Bound (binder, a, abst_n v ty n, abst_n v tm (n+1))
    | App (t1, t2) -> App (abst_n v t1 n, abst_n v t2 n)
    | Fst tm -> Fst (abst_n v tm n)
    | Snd tm -> Snd (abst_n v tm n)
    | Pair (a, t1, t2, t3) -> 
      Pair (a, abst_n v t1 (n+1), abst_n v t2 n, abst_n v t3 n)
    | Cast (Ctxt tel, tm, ty) ->
      let tel = List.map (fun t -> abst_n v t n) tel in
      Cast(Ctxt tel, abst_n v tm n, abst_n v ty n)
    | Eq (t1, t2) -> Eq (abst_n v t1 n, abst_n v t2 n)
    | Mvar (a, t) -> Mvar (a, abst_n v t n)


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
    | Fst t -> Fst (subst_n u t n)
    | Snd t -> Snd (subst_n u t n)
    | Pair (a, t1, t2, t3) -> 
      Pair (a, subst_n u t1 (n+1), subst_n u t2 n, subst_n u t3 n)
    | Cast (Ctxt tel, t1, t2) -> 
      let tel = List.map (fun t -> subst_n u t n) tel in
      Cast (Ctxt tel, subst_n u t1 n, subst_n u t2 n)
    | Eq (t1, t2) -> Eq (subst_n u t1 n, subst_n u t2 n)
    | Mvar (a, t) -> Mvar (a, subst_n u t n)

let subst u t = subst_n u t 0

let rec compare t1 t2 =
  match t1, t2 with
    | Const(a, _), Const(b, _) -> Pervasives.compare a b
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
    | App _, _ -> -1
    | Fst t1, Fst t2 -> compare t1 t2
    | Fst _, Const _ | Fst _, Sort _ | Fst _, DB _ | Fst _, Bound _ | Fst _, App _ -> 1
    | Fst _, _ -> -1
    | Snd t1, Snd t2 -> compare t1 t2
    | Snd _, Const _ | Snd _, Sort _ | Snd _, DB _ | Snd _, Bound _ | Snd _, App _ | Snd _, Fst _ -> 1
    | Snd _, _ -> -1
    | Pair(_, t1, u1, v1), Pair(_, t2, u2, v2) ->
      let c_t = compare t1 t2 in
      if c_t = 0 then
        let c_u = compare u1 u2 in
        if c_u = 0 then compare v1 v2
        else c_u
      else c_t
    | Pair _, Const _ | Pair _, Sort _ | Pair _, DB _ | Pair _, Bound _ 
    | Pair _, App _ | Pair _, Fst _ | Pair _, Snd _ -> 1
    | Pair _, _ -> -1
    | Eq(t1, u1), Eq(t2, u2) -> 
      let c_t = compare t1 t2 in
      if c_t = 0 then compare u1 u2 else c_t
    | Eq _, Const _ | Eq _, Sort _ | Eq _, DB _ | Eq _, Bound _ 
    | Eq _, App _ | Eq _, Fst _ | Eq _, Snd _ | Eq _, Pair _ -> 1
    | Eq _, _ -> -1
    | Cast (_, t1, u1), Cast(_, t2, u2) -> 
      let c_t = compare t1 t2 in
      if c_t = 0 then compare u1 u2 else c_t
    | Cast _, Const _ | Cast _, Sort _ | Cast _, DB _ | Cast _, Bound _ 
    | Cast _, App _ | Cast _, Fst _ | Cast _, Snd _ | Cast _, Pair _ | Cast _, Eq _ -> 1
    | Cast _, _ -> -1
    | Mvar(a, _), Mvar(b, _) -> Pervasives.compare a b
    | Mvar _, _ -> 1

let equal t1 t2 = (compare t1 t2 = 0)

let var_count = ref (-1)

let fresh_var v t = 
  var_count := !var_count + 1;
  let name = v^(string_of_int !var_count) in
  (name, Const(name , t))
