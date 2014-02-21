

open Expr

type constr = Eq of Expr.t * Expr.t | HasType of Expr.t * Expr.t
                | IsSort of Expr.t

(* level constraints are not generated or even checked! *)
let rec type_constr t cs =
  match t with
    (*TODO: make the universes correct! *)
    | Sort (Type _) -> (Sort (Type Z), cs)
    (*Invariant: TopLevel constants
      are fully elaborated *)
    | TopLevel (_, (_, ty), _) -> (ty, cs)
    | Const(Local, _, ty) -> (ty, cs)
    | Const(Mvar, _, ty) ->
      let ty_sort, cs' = type_constr ty cs in
      (ty, HasType (t, ty)::IsSort ty_sort::cs')
    | DB _ -> assert false
    | Bound(b, a, t1, t2) -> 
      let (a_var, t2) = open_t a t1 t2 in
      let t1_ty, c1 = type_constr t1 cs in
      let t2_ty, c2 = type_constr t2 c1 in
      begin match b with
        | Pi -> begin match t1_ty, t2_ty with
            | Sort _, Sort _ -> 
              (*TODO: insert meta-variable here? *)
              (Sort (Type Z), c2)
            | Sort _, _ -> raise (Typing.NotASort (t2, t2_ty))
            | _, _ -> raise (Typing.NotASort (t1, t1_ty))
          end
        | Sig -> begin match t1_ty, t2_ty with
            | Sort _, Sort _ -> 
              (*TODO: insert meta-variable here? *)
              (Sort (Type Z), c2)
            | Sort _, _ -> raise (Typing.NotASort (t2, t2_ty))
            | _, _ -> raise (Typing.NotASort (t1, t1_ty))
          end
        | Abst -> 
          let _, cs' = type_constr t2_ty cs in
          (Bound(Pi, a, t1, abst a_var t2_ty), cs')
      end
    | App(t1, t2) ->
      let t1_ty, c1 = type_constr t1 cs in
      let t2_ty, c2 = type_constr t2 c1 in
      begin match t1_ty with
        (*TODO: don't generate a constraint if t2_ty is
          convertible with ty*)
        | Bound(Pi, _, ty, body) ->
          (subst t2 body, Eq (t2_ty, ty)::c2)
        | _ -> raise (Typing.NotAPi (t1, t1_ty))
      end      
    | Pair (a, ty, t1, t2) ->
      let t1_ty, c1 = type_constr t1 cs in
      let ty_sub_t1 = subst t1 ty in
      let t2_ty, c2 = type_constr t2 c1 in
      let _, ty = open_t a t1_ty ty in
      let _, c_ty = type_constr ty c2 in
      let out_cstr = Eq (ty_sub_t1, t2_ty)::c_ty in
        (Bound (Sig, a, t1_ty, ty), out_cstr)
    | Proj (Fst, t) ->
      let t_ty, c1 = type_constr t cs in
      begin match t_ty with
        | Bound (Pi, _, ty_arg, _) -> 
          (ty_arg, c1)
        | _ -> raise (Typing.NotASig (t, t_ty))
      end
    | Proj (Snd, t) ->
      let t_ty, c1 = type_constr t cs in
      begin match t_ty with
        | Bound (Pi, _, _, ty_body) ->
          let fst_t = Proj (Fst, t) in
          (subst fst_t ty_body, c1)
        | _ -> raise (Typing.NotASig (t, t_ty))
      end

