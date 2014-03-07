
open Expr
open Elab

exception CannotUnify of Expr.t * Expr.t

exception UnsolvableConstr of constr list

type subst = Expr.t NMap.t

type unif = Conv.reduction -> Elab.constr list -> subst -> subst

let empty_subst = NMap.empty

let in_dom a s = NMap.mem a s

let subst_add a t s = NMap.add a t s

let rec mvar_subst s t =
  match t with
    | Sort _ |  TopLevel _ | DB _ -> t
    | Const (Local, a, ty) -> Const (Local, a, mvar_subst s ty)
    | Const (Mvar, a, ty) ->
        if NMap.mem a s then 
          NMap.find a s
        else
          Const (Mvar, a, mvar_subst s ty)
    | Bound (b, a, ty, body) ->
        Bound( b, a, mvar_subst s ty, mvar_subst s body)
    | App (t1, t2) ->
        App (mvar_subst s t1, mvar_subst s t2)
    | Pair (a, ty, t1, t2) ->
        Pair (a, mvar_subst s ty, mvar_subst s t1, mvar_subst s t2)
    | Proj (p, t) -> Proj(p, mvar_subst s t)

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


let rec fo_step conv t1 t2 s =
  let t1 = Conv.reduce conv t1 in
  let t2 = Conv.reduce conv t2 in
  match t1, t2 with
    | (Const(Mvar, a, _) as mv), t
    | t, (Const(Mvar, a, _) as mv) ->
        if in_dom a s then
          fo_step conv (mvar_subst s mv) t s
        else
          let t_sub = mvar_subst s t in
          if occurs a t_sub then
            raise (CannotUnify (t1, t2))
          else
            subst_add a t_sub s
    | Const(Local, a1, _), Const(Local, a2, _)
    (*TODO: should we check level coherence here? *)
    | TopLevel(a1, _, _), TopLevel(a2, _, _) ->
        if a1 = a2 then s else raise (CannotUnify (t1, t2))
    | App(t1, u1), App(t2, u2) ->
        let m_t = fo_step conv t1 t2 s in
        fo_step conv u1 u2 m_t
    | Bound(b1, a1, ty1, u1), Bound(b2, _, ty2, u2) ->
        if b1 = b2 then
          let m_ty = fo_step conv ty1 ty2 s in
          let _, u1_o = open_t a1 ty1 u1 in
          (* open with the same name, to get alpha equality *)
          let _, u2_o = open_t a1 ty2 u2 in
          fo_step conv u1_o u2_o m_ty
        else
          raise (CannotUnify (t1, t2))
    | Proj(p1, u1), Proj(p2, u2) ->
        if p1 = p2
        then fo_step conv u1 u2 s
        else raise (CannotUnify (t1, t2))
    | Pair(a1, ty1, t1, u1), Pair(_, ty2, t2, u2) ->
        let dummy = Sort (Type Z) in
        let _, ty1_o = open_t a1 dummy ty1 in
        let _, ty2_o = open_t a1 dummy ty2 in
        let m_ty = fo_step conv ty1_o ty2_o s in
        let m_t = fo_step conv t1 t2 m_ty in
        fo_step conv u1 u2 m_t
    | _ -> raise (CannotUnify (t1, t2))
            

let rec fo_unif r csts s = 
  match csts with
    | [] -> s
    | Eq (t1, t2)::cs ->
        let m_t = fo_step r t1 t2 s in
        fo_unif r cs m_t
    | _::cs -> fo_unif r cs s

let elab unif conv t =
  let cst = make_type_constr t in
  let s = unif conv cst empty_subst in
  mvar_subst s t

let occurs_rigid a t = occurs a t
  
let rec rigid_rigid t1 t2 =
  match t1, t2 with
    | Const(Mvar, _, _), _
    | _, Const(Mvar, _, _) ->
        assert false
    | Const(Local, a1, _), Const(Local, a2, _)
    (*TODO: should we check level coherence here? *)
    | TopLevel(a1, _, _), TopLevel(a2, _, _) ->
        if a1 = a2 then [] else raise (CannotUnify (t1, t2))
    | App(t1, u1), App(t2, u2) ->
        [Eq (t1, t2); Eq (u1, u2)]
    | Bound(b1, a1, ty1, u1), Bound(b2, _, ty2, u2) ->
        if b1 = b2 then
          let _, u1_o = open_t a1 ty1 u1 in
          (* open with the same name, to get alpha equality *)
          let _, u2_o = open_t a1 ty2 u2 in
          [Eq (ty1, ty2); Eq (u1_o, u2_o)]
        else
          raise (CannotUnify (t1, t2))
    | Proj(p1, u1), Proj(p2, u2) ->
        if p1 = p2
        then [Eq (u1, u2)]
        else raise (CannotUnify (t1, t2))
    | Pair(a1, ty1, t1, u1), Pair(_, ty2, t2, u2) ->
        let dummy = Sort (Type Z) in
        let _, ty1_o = open_t a1 dummy ty1 in
        let _, ty2_o = open_t a1 dummy ty2 in
        [Eq (ty1_o, ty2_o); Eq (t1, t2); Eq (u1, u2)]
    | _ -> raise (CannotUnify (t1, t2))


type branch = Branch of constr list list

(* TODO: make this proper ho unification *)
let flex_rigid mvar args_m r s = 
  let hd_r, args_r = Expr.get_app r in
  let arg_cstr = 
    List.map2 (fun a b -> Eq (a, b)) args_m args_r
  in
  subst_add mvar hd_r s, arg_cstr
  

let rec ho_step conv t1 t2 s =
  let t1, t2 = Conv.reduce conv t1, Conv.reduce conv t2 in
  let hd1, args1 = Expr.get_app t1 in
    match hd1 with
    | Const(Mvar, a, _) -> 
        begin try
                if in_dom a s then
                  ho_step conv (mvar_subst s t1) t2 s
                else if occurs_rigid a t2 then
                  raise (CannotUnify (t1, t2))
                else
                  let r = mvar_subst s t2 in
                  flex_rigid a args1 r s
          with Invalid_argument _ ->
          raise (CannotUnify (t1, t2))
        end
    | _ -> let hd2, _ = Expr.get_app t2 in
           begin match hd2 with
             | Const (Mvar, _, _) -> ho_step conv t2 t1 s
             | _ -> s, rigid_rigid t1 t2
           end

let rec ho_unif conv constr s =
  match constr with
    | [] -> s
    | Eq (t1, t2)::cs ->
        let s', cs' = ho_step conv t1 t2 s in
        ho_unif conv (cs'@cs) s'
    | _::cs ->  ho_unif conv cs s


(* (\* The type of unification hints *\) *)
(* type hint =  *)

(* (\* Return the list of potentially applicable unification hints *\) *)
(* val get_hints = *)

(* (\* Apply a given hint to the current problem *\) *)
(* val apply_hint =  *)


(* let rec higher_order r csts m hints = *)
(*   match csts with *)
      
  
