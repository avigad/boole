

open Expr

type constr = Eq of Expr.t * Expr.t | HasType of Expr.t * Expr.t
                | IsSort of Expr.t

(* level constraints are not generated or even checked! *)
let rec type_constr t cs =
  match t with
    (*TODO: make the universes correct! *)
    | Sort (Type _) -> (Sort (Type Z), cs)
    | Sort Bool -> (Sort (Type Z), cs)
    | Sort Kind -> raise Typing.KindHasNoType
    (*Invariant: TopLevel constants
      are fully elaborated *)
    | Const(TopLevel, _, ty) -> (ty, cs)
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
            | Sort s1, Sort s2 when s1 != Kind && s2 != Kind -> 
              (Sort (Typing.pi_sort s1 s2), c2)
            | Sort Kind, Sort _ -> raise (Typing.SortError (t1, t1_ty)) 
            | Sort _, Sort Kind -> raise (Typing.SortError (t2, t2_ty))
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
    | LBound(_, _, t) ->
      type_constr t cs
    | LApp (t, _) -> 
      type_constr t cs
