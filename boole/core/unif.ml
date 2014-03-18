
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
    | Type _ |  TopLevel _ | DB _ -> t
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
    | Type _ |  TopLevel _ | DB _ -> false
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
        let dummy = Type Z in
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
  Printf.printf "\n\nconstraints for %a:\n%a\n\n" Expr.print_term t Elab.print_cstrs cst;
  let s = unif conv cst empty_subst in
  mvar_subst s t

type branch = Branch of (subst * constrs) list | Postpone

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
        let dummy = Type Z in
        let _, ty1_o = open_t a1 dummy ty1 in
        let _, ty2_o = open_t a1 dummy ty2 in
        [Eq (ty1_o, ty2_o); Eq (t1, t2); Eq (u1, u2)]
    | _ -> raise (CannotUnify (t1, t2))


let one_branch s c = Branch [(s, c)]


(*TODO: explain this function *)
(* (note: this is the imitation part of Huet's 
   higher order unification algorithm) *)
let imitate mvar args_m hd args s =
  let rec args_vars args tpe = 
    match args with
      | [] -> []
      | (Const(Local, a, ty) as c)::ags ->
          begin match tpe with
            | Bound (Pi, _, _, tm) ->
                let _, tm = Expr.open_t a ty tm in
                c :: args_vars ags tm
            | _ -> assert false
          end
      | _::ags -> begin match tpe with
          | Bound (Pi, a, ty, tm) ->
            let b, tm = Expr.open_t a ty tm in
            Const (Local, b, ty) :: (args_vars ags tm)
          | _ -> assert false
      end
  in
  let args_vars = args_vars args_m (Elab.type_raw mvar) in
  let rec body tm args cstrs =
    match args with
      | [] -> (tm, cstrs)
      | u::us ->
          let u_ty = Elab.type_raw u in
          (* TODO: get the name for u_arg from
             the type of hd *)
          let u_mvar = Expr.fresh_mvar (make_name "u_arg") u_ty in
          let u_app = make_app u_mvar args_vars in
          let u_ts = make_app u_mvar args_m in
          body (App (tm, u_app)) us (Eq (u_ts, u)::cstrs)
  in
  (* TODO: treat the case hd = Local var *)
  let body, constr = body hd args [] in
  let body = make_abst args_vars body in
  Printf.printf "\n\n body = %a \n\n" print_term body;
  let s = subst_add (Expr.name_of mvar) body s in
  s, constr

let project conv mvar arg_m rhs s =
  let ty_m = Elab.type_raw mvar in
  let rhs_ty = Elab.type_raw rhs in
  let rec args_proj args tpe = 
    match args with
      | [] -> [], []
      | t::ts -> begin match tpe with
          | Bound (Pi, a, ty, tm) ->
            let b, tm = Expr.open_t a ty tm in
            let args, proj = args_proj ts tm in
            let args = Const(Local, b, ty) :: args in
            let proj = 
              if Conv.check_conv conv ty rhs_ty then
                (Const (Local, b, ty), t) :: proj
              else
                proj
            in
            args, proj
                
          | _ -> assert false
      end
  in
  let args, proj = args_proj arg_m ty_m in
  let args = List.rev args in
  List.map (
    fun (x, t) ->
      let p_x = make_abst args x in
      Printf.printf "\n\n proj = %a \n\n" print_term p_x;
      let s = subst_add (Expr.name_of mvar) p_x s in
      s, [Eq (t, rhs)]
  ) proj

(* let flex_rigid mvar args_m r s =  *)
(*   let hd_r, args_r = Expr.get_app r in *)
(*   let arg_cstr =  *)
(*     List.map2 (fun a b -> Eq (a, b)) args_m args_r *)
(*   in *)
(*   one_branch (subst_add (Expr.name_of mvar) hd_r s) arg_cstr *)

let flex_rigid conv mvar args_m r s = 
  let hd_r, args_r = Expr.get_app r in
  let imit = imitate mvar args_m hd_r args_r s in
  let proj = project conv mvar args_m r s in
  Branch (imit::proj)

let rec ho_step red t1 t2 s =
  let t1, t2 = Conv.reduce red t1, Conv.reduce red t2 in
  let hd1, args1 = Expr.get_app t1 in
  let hd2, _ = Expr.get_app t2 in
    match hd1, hd2 with
    | Const(Mvar, a, _), _ -> 
        begin try
                if in_dom a s then
                  ho_step red (mvar_subst s t1) t2 s
                else if occurs_rigid a t2 then
                  raise (CannotUnify (t1, t2))
                else
                  let r = mvar_subst s t2 in
                  (* TODO: make this parametric in conv *)
                  flex_rigid Conv.conv hd1 args1 r s
          with Invalid_argument _ ->
          raise (CannotUnify (t1, t2))
        end
    | _, Const (Mvar, _, _) -> ho_step red t2 t1 s
    | _ -> one_branch s (rigid_rigid t1 t2)


let rec try_branch t1 t2 branches unif =
  match branches with
    | [] -> raise (CannotUnify (t1, t2))
    | (s, cs)::bs -> 
        try 
          unif s cs
        with CannotUnify _ ->
          try_branch t1 t2 bs unif

let rec ho_unif conv constr s =
  try
    match constr with
      | [] -> s
      | Eq (t1, t2)::cs ->
          begin match ho_step conv t1 t2 s
            with
              | Branch bs -> 
                  try_branch t1 t2 bs 
                    (fun s' cs' -> ho_unif conv (cs'@cs) s')
              | Postpone ->
                (*TODO: this may not terminate! *)
                (*Create a flag for previously postponed problems*)
                  ho_unif conv (cs@[Eq (t1, t2)]) s
          end
      | _::cs ->  ho_unif conv cs s
  with
      CannotUnify _ -> raise (UnsolvableConstr constr)

(* (\* The type of unification hints *\) *)
(* type hint =  *)

(* (\* Return the list of potentially applicable unification hints *\) *)
(* val get_hints = *)

(* (\* Apply a given hint to the current problem *\) *)
(* val apply_hint =  *)

(* let rec higher_order r csts m hints = *)
(*   match csts with *)
      
  
