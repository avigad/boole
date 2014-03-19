(*****************************************************************

  typing.ml

 description: Basic type checking


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

open Expr

exception TypeError of Expr.t * Expr.t * Expr.t

exception NotAType of Expr.t * Expr.t

exception NotAPi of Expr.t * Expr.t

exception NotASig of Expr.t * Expr.t

exception KindError of Expr.t * Expr.t

let rec max_level i j = 
  match i, j with
    | Suc i', Suc j' -> Suc (max i' j')
    | Z, _ -> j
    | _, Z -> i
    | _ -> Max (i, j)

let pi_level i j = 
  match i, j with
    | _, Z -> Z
    | Z, _ -> j
    | _, Suc _ -> max i j
    | _ -> LProd (i, j)

let rec type_raw (conv : Conv.conv) t =
  (* Printf.printf "\n\nChecking %a...\n\n" print_term t; *)
  match t with
    | Type i -> Type (Suc i)
    | TopLevel (_, (is, ty), ls) -> subst_ls is ls ty
    (* Do we ever need to check that this is well-kinded? *)
    (* This is done once for top-level constants, and
       local variables should checked at creation *)
    | Const (_, _, ty) -> ty
    | DB _ -> assert false
    | Bound (b, v, ty, tm) ->
      let ty_ty = type_raw conv ty in
      let vname, open_tm = open_t v ty tm in
      let tm_ty = type_raw conv open_tm in
      begin match b with
        | Pi ->
          begin match ty_ty, tm_ty with
            | Type s1, Type s2 -> Type (pi_level s1 s2)
            | Type _, _ -> raise (NotAType (tm, tm_ty))
            | _, _ -> raise (NotAType (ty, ty_ty))
          end
        | Sig ->
          begin match ty_ty, tm_ty with
            | Type s1, Type s2 -> Type (max_level s1 s2)
            | Type _, _ -> raise (NotAType (tm, tm_ty))
            | _, _ -> raise (NotAType (ty, ty_ty))
          end
        | Abst -> 
          (* Check to see if t2 is well-kinded *)
          let _ = type_raw conv tm_ty in
          Bound(Pi, v, ty, abst vname tm_ty)
      end
    | App (t1, t2) ->
      let t1_ty = type_raw conv t1 in
      let t2_ty = type_raw conv t2 in
      begin
        match t1_ty with
          | Bound (Pi, _, ty_arg, ty_body) 
              when Conv.check_conv conv t2_ty ty_arg ->
            subst t2 ty_body
          | Bound (Pi, _, ty_arg, _) ->
            raise (TypeError (t2, t2_ty, ty_arg))
          | _ -> raise (NotAPi (t1, t1_ty))
      end
    | Pair (a, ty, t1, t2) ->
      let t1_ty = type_raw conv t1 in
      let ty_sub_t1 = subst t1 ty in
      let t2_ty = type_raw conv t2 in
      if Conv.check_conv conv t2_ty ty_sub_t1 then
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

