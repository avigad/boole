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

exception KindHasNoType

let max_sort s1 s2 =
  match s1, s2 with
    | Bool, Type i -> Type i 
    | Type i, Bool -> Type i
    | Bool, Bool -> Bool
    | Type i, Type j -> Type (Max (i, j))
    | Kind, _ | _, Kind -> assert false


let pi_sort s1 s2 =
  match s1, s2 with
    | _, Bool -> Bool
    | x, y -> max_sort x y

let rec type_raw conv t =
  match t with
    | Sort (Type i) -> Sort (Type (Suc i))
    | Sort Bool -> Sort (Type Z)
    | Sort Kind -> raise KindHasNoType
    (* Do we ever need to check that this is well-kinded? *)
    | Const (_, _, ty) -> ty
    | DB _ -> assert false
    | Bound (b, v, t1, t2) ->
      let t1_ty = type_raw conv t1 in
      let vname, vc = fresh_var v t1 in
      let t2 = subst vc t2 in
      let t2_ty = type_raw conv t2 in
      begin match b with
        | Pi -> 
          begin match t1_ty, t2_ty with
            | Sort Kind, Sort _ -> raise (SortError (t1, t1_ty)) 
            | Sort _, Sort Kind -> raise (SortError (t2, t2_ty))
            | Sort s1, Sort s2 -> Sort (pi_sort s1 s2)
            | Sort _, _ -> raise (NotASort (t2, t2_ty))
            | _, _ -> raise (NotASort (t1, t1_ty))
          end
        | Abst -> 
          (* Check to see if t2 is well-kinded *)
          let _ = type_raw conv t2_ty in
          Bound(Pi, v, t1, abst vname t2)
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

    | LBound (b, i, t) ->
      let t_ty = type_raw conv t in
      begin match b with
        | LPi ->
          begin match t_ty with
            | Sort _ -> Sort Kind
            | _ -> raise (NotASort (t, t_ty))
          end
        | LAbst ->
          let _ = type_raw conv t_ty in
          LBound (LPi, i, t_ty)
      end
    | LApp (t, l) -> 
      let t_ty = type_raw conv t in
      begin
        match t_ty with
          | LBound (LPi, i, body) -> subst_l i l body
          | _ -> raise (NotAPi (t, t_ty))
      end
