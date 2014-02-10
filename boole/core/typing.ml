(*****************************************************************

  typing.ml

 description: Basic type checking


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

open Expr

type constr = Equals of Expr.ctxt * Expr.t * Expr.t

exception TypeError of Expr.t * Expr.t * Expr.t

exception NotASort of Expr.t * Expr.t

exception NotAPi of Expr.t * Expr.t

exception NotASig of Expr.t * Expr.t

type constraints = constr list

let max_sort s1 s2 =
  match s1, s2 with
    | Kind, _ | _, Kind -> Kind
    | Bool, s | s, Bool -> s
    | Type, Type -> Type

let rec type_raw t =
  match t with
    | Sort Type -> (Sort Kind, [])
    | Sort Bool -> (Sort Type, [])
    | Sort Kind -> assert false
    (* Do we ever need to check that this is well-kinded? *)
    | Const (_, ty) -> (ty, [])
    | DB _ -> assert false
    | Bound (b, v, t1, t2) ->
      let (t1_ty, c1) = type_raw t1 in
      let vname, vc = fresh_var v t1 in
      let t2 = subst vc t2 in
      let (t2_ty, c2) = type_raw t2 in
      begin match b with
        | Pi | Sig -> 
          begin match t1_ty, t2_ty with
            | Sort s1, Sort s2 -> (Sort (max_sort s1 s2), c1@c2)
            | Sort _, _ -> raise (NotASort (t2, t2_ty))
            | _, _ -> raise (NotASort (t1, t1_ty))
          end
        | Forall | Exists ->
          begin match t1_ty, t2_ty with
            | Sort _, Sort Bool -> (Sort Bool, c1@c2)
            | _, Sort Bool -> raise (NotASort (t1, t1_ty))
            | _, _ -> raise (TypeError (t2, t2_ty, Sort Bool))
          end
        | Abst -> 
          (* Check to see if t2 is well-kinded *)
          let _, c3 = type_raw t2_ty in
          (Bound(Pi, v, t1, abst vname t2), c1@c2@c3)
      end
    | App (t1, t2) ->
      let (t1_ty, c1) = type_raw t1 in
      let (t2_ty, c2) = type_raw t2 in
      begin
        match t1_ty with
          | Bound (Pi, _, ty_arg, ty_body) when equal t2_ty ty_arg ->
            (subst t2 ty_body, c1@c2)
          | Bound (Pi, _, ty_arg, _) -> 
            raise (TypeError (t2, t2_ty, ty_arg))
          | _ -> raise (NotAPi (t1, t1_ty))
      end
    | Cast (ctxt, t1, t2) -> 
      let (t1_ty, c1) = type_raw t1 in
      let (t2_ty, c2) = type_raw t2 in
      begin
        match t2_ty with
          | Sort _ -> 
            let new_cstr = Equals (ctxt, t1_ty, t2) in
            (t1, new_cstr::c1@c2)
          | _ -> raise (NotASort (t2, t2_ty))
      end
    | Fst t ->
      let (t_ty, c) = type_raw t in
      begin
        match t_ty with
          | Bound(Sig, _, ty, _) -> (ty, c)
          | _ -> raise (NotASig (t, t_ty))
      end
    | Snd t ->
      let (t_ty, c) = type_raw t in
      begin
        match t_ty with
          | Bound(Sig, _, _, tm) -> (subst (Fst t) tm, c)
          | _ -> raise (NotASig (t, t_ty))
      end
    | Pair (a, t1, t2, t3) ->
      let (t2_ty, c2) = type_raw t2 in
      let (name, v) = fresh_var a t2_ty in
      let (t1_ty, c1) = type_raw (subst v t1) in
      begin
        match t1_ty with
          | Sort _ ->
            let (t3_ty, c3) = type_raw t3 in
            let t3_expected = subst t2 t1 in
            if equal t3_expected t3_ty then
              (Bound (Sig, a, t2_ty, abst name t1), c1@c2@c3)
                  else raise (TypeError (t3, t3_ty, t3_expected))
          | _ -> raise (NotASort (subst v t1, t1_ty))
      end
    | Eq (t1, t2) -> 
      let _, c1 = type_raw t1 in
      let _, c2 = type_raw t2 in
      (Sort Bool, c1@c2)
    | Mvar (_, t) -> 
      let (ty, c) = type_raw t in
      begin
        match ty with
          | Sort _ -> (ty, c)
          | _ -> raise (NotASort (t, ty))
      end

