(*****************************************************************

  typing.ml

 description: Basic type checking


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

open Expr

exception TypeError of Expr.t * Expr.t * Expr.t

exception NotASort of Expr.t * Expr.t

exception NotAPi of Expr.t * Expr.t

exception NotASig of Expr.t * Expr.t

exception SortError of Expr.t * Expr.t

let max_sort s1 s2 =
  match s1, s2 with
    | Type i, Type j -> Type (Max (i, j))

let pi_sort s1 s2 =
  match s1, s2 with
    | Type i, Type j -> Type (LProd (i, j))

let rec type_raw conv t =
  match t with
    | Sort (Type i) -> Sort (Type (Suc i))
    | TopLevel (_, (is, ty), ls) -> subst_ls is ls ty
    (* Do we ever need to check that this is well-kinded? *)
    (* This is done once for top-level constants, and
       local variables should checked at creation *)
    | Const (_, _, ty) -> ty
    | DB _ -> assert false
    | Bound (b, v, t1, t2) ->
      let t1_ty = type_raw conv t1 in
      let vname, t2 = open_t v t1 t2 in
      let t2_ty = type_raw conv t2 in
      begin match b with
        | Pi ->
          begin match t1_ty, t2_ty with
            | Sort s1, Sort s2 -> Sort (pi_sort s1 s2)
            | Sort _, _ -> raise (NotASort (t2, t2_ty))
            | _, _ -> raise (NotASort (t1, t1_ty))
          end
        | Sig ->
          begin match t1_ty, t2_ty with
            | Sort s1, Sort s2 -> Sort (max_sort s1 s2)
            | Sort _, _ -> raise (NotASort (t2, t2_ty))
            | _, _ -> raise (NotASort (t1, t1_ty))
          end
        | Abst -> 
          (* Check to see if t2 is well-kinded *)
          let _ = type_raw conv t2_ty in
          Bound(Pi, v, t1, abst vname t2_ty)
      end
    | App (t1, t2) ->
      let t1_ty = type_raw conv t1 in
      let t2_ty = type_raw conv t2 in
      begin
        match t1_ty with
          | Bound (Pi, _, ty_arg, ty_body) when conv t2_ty ty_arg ->
            subst t2 ty_body
          | Bound (Pi, _, ty_arg, _) -> 
            raise (TypeError (t2, t2_ty, ty_arg))
          | _ -> raise (NotAPi (t1, t1_ty))
      end
    | Pair (a, ty, t1, t2) ->
      let t1_ty = type_raw conv t1 in
      let ty_sub_t1 = subst t1 ty in
      let t2_ty = type_raw conv t2 in
      if conv t2_ty ty_sub_t1 then
        let _, ty = open_t a t1_ty ty in
        let _ = type_raw conv ty in
        Bound (Sig, a, t1_ty, ty)
      else
        raise (TypeError (t2, t2_ty, ty_sub_t1))
    | Proj (Fst, t) ->
      let t_ty = type_raw conv t in
      begin match t_ty with
        | Bound (Pi, _, ty_arg, _) -> ty_arg
        | _ -> raise (NotASig (t, t_ty))
      end
    | Proj (Snd, t) ->
      let t_ty = type_raw conv t in
      begin match t_ty with
        | Bound (Pi, _, _, ty_body) ->
          let fst_t = Proj (Fst, t) in
          subst fst_t ty_body
        | _ -> raise (NotASig (t, t_ty))
      end
