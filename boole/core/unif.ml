
open Expr
open Elab

exception CannotUnify of Expr.t * Expr.t

exception UnsolvableConstr of constr list

type mvar_assnt = Expr.t NMap.t

let empty_assnt = NMap.empty

let rec mvar_subst m t =
  match t with
    | Sort _ |  TopLevel _ | DB _ -> t
    | Const (Local, a, ty) -> Const (Local, a, mvar_subst m ty)
    | Const (Mvar, a, ty) ->
        if NMap.mem a m then 
          NMap.find a m
        else
          Const (Mvar, a, mvar_subst m ty)
    | Bound (b, a, ty, body) ->
        Bound( b, a, mvar_subst m ty, mvar_subst m body)
    | App (t1, t2) ->
        App (mvar_subst m t1, mvar_subst m t2)
    | Pair (a, ty, t1, t2) ->
        Pair (a, mvar_subst m ty, mvar_subst m t1, mvar_subst m t2)
    | Proj (p, t) -> Proj(p, mvar_subst m t)

let rec occurs x t =
  match t with
    | Sort _ |  TopLevel _ | DB _ -> false
    | Const (Local, _, ty) -> occurs x ty
    | Const (Mvar, a, _) when x = a -> true
    | Const (Mvar, _, ty) -> occurs x ty
    | Bound (_, _, ty, body) -> occurs x ty || occurs x body
    | App (t1, t2) -> occurs x t1 || occurs x t2
    | Pair (_, ty, t1, t2) ->
        occurs x ty || occurs x t1 || occurs x t2
    | Proj (_, t) -> occurs x t


let rec fo_step conv t1 t2 m =
  let t1 = Conv.reduce conv t1 in
  let t2 = Conv.reduce conv t2 in
  match t1, t2 with
    | (Const(Mvar, a, _) as mv), t
    | t, (Const(Mvar, a, _) as mv) ->
        if NMap.mem a m then
          fo_step conv (mvar_subst m mv) t m
        else
          let t_sub = mvar_subst m t in
          if occurs a t_sub then
            raise (CannotUnify (t1, t2))
          else
            NMap.add a t_sub m
    | Const(Local, a1, _), Const(Local, a2, _)
    (*TODO: should we check level coherence here? *)
    | TopLevel(a1, _, _), TopLevel(a2, _, _) ->
        if a1 = a2 then m else raise (CannotUnify (t1, t2))
    | App(t1, u1), App(t2, u2) ->
        let m_t = fo_step conv t1 t2 m in
        fo_step conv u1 u2 m_t
    | Bound(b1, a1, ty1, u1), Bound(b2, _, ty2, u2) ->
        if b1 = b2 then
          let m_ty = fo_step conv ty1 ty2 m in
          let _, u1_o = open_t a1 ty1 u1 in
          (* open with the same name, to get alpha equality *)
          let _, u2_o = open_t a1 ty2 u2 in
          fo_step conv u1_o u2_o m_ty
        else
          raise (CannotUnify (t1, t2))
    | Proj(p1, u1), Proj(p2, u2) ->
        if p1 = p2
        then fo_step conv u1 u2 m
        else raise (CannotUnify (t1, t2))
    | Pair(a1, ty1, t1, u1), Pair(_, ty2, t2, u2) ->
        let dummy = Sort (Type Z) in
        let _, ty1_o = open_t a1 dummy ty1 in
        let _, ty2_o = open_t a1 dummy ty2 in
        let m_ty = fo_step conv ty1_o ty2_o m in
        let m_t = fo_step conv t1 t2 m_ty in
        fo_step conv u1 u2 m_t
    | _ -> raise (CannotUnify (t1, t2))
            

let rec first_order r csts m = 
  match csts with
    | [] -> m
    | Eq (t1, t2)::cs ->
        let m_t = fo_step r t1 t2 m in
        first_order r cs m_t
    | _::cs -> first_order r cs m
  
