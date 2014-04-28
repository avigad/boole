
open Expr
open Elab

exception UFail

exception UnsolvableConstr of Elab.constrs

exception MvarNoVal of Expr.t * Expr.t list

type subst = Expr.t NMap.t

type branch = (subst * Elab.constrs) list

type hints = subst -> Elab.constr -> branch

type branch_fail = Branch of branch | Postpone

type unif_info = {red : Conv.reduction; conv : Conv.conv; hints : hints}

type unif = unif_info -> Elab.constr list -> subst -> subst

let print_subst o s =
  NMap.iter 
    (fun a t -> Printf.fprintf o "%s |-> %a\n"
      (string_of_name a) print_term t)
    s


let empty_subst = NMap.empty

let in_dom a s = NMap.mem a s

let add_subst a t s = NMap.add a t s

let rec mvar_subst s t =
  match t with
    | Type _ |  TopLevel _ | DB _ -> t
    | Const (Local, a, ty) -> Const (Local, a, mvar_subst s ty)
    | Const (Mvar, a, ty) ->
        if NMap.mem a s then 
          mvar_subst s (NMap.find a s)
        else
          Const (Mvar, a, mvar_subst s ty)
    | Bound (i, b, a, ty, body) ->
        let a', open_body = Expr.open_t a ty body in
        let subst_ty = mvar_subst s ty in
        let subst_body = mvar_subst s open_body in
        Bound (i, b, a, subst_ty, Expr.abst a' subst_body)
          
    | App (t1, t2) ->
        App (mvar_subst s t1, mvar_subst s t2)
    | Pair (a, ty, t1, t2) ->
        let dummy = Type Z in
        let a', open_ty = Expr.open_t a dummy ty in
        let ty_subst = mvar_subst s open_ty in
        let t1_subst = mvar_subst s t1 in
        let t2_subst = mvar_subst s t2 in
        Pair (a, Expr.abst a' ty_subst, t1_subst, t2_subst)
    | Proj (p, t) -> Proj(p, mvar_subst s t)

let rec occurs x t =
  match t with
    | Type _ |  TopLevel _ | DB _ -> false
    | Const (Local, _, ty) -> occurs x ty
    | Const (Mvar, a, _) when x = a -> true
    | Const (Mvar, _, ty) -> occurs x ty
    | Bound (_, _, _, ty, body) -> occurs x ty || occurs x body
    | App (t1, t2) -> occurs x t1 || occurs x t2
    | Pair (_, ty, t1, t2) ->
        occurs x ty || occurs x t1 || occurs x t2
    | Proj (_, t) -> occurs x t


let rec fo_step red t1 t2 s =
  let t1 = Conv.reduce red t1 in
  let t2 = Conv.reduce red t2 in
  match t1, t2 with
    | (Const(Mvar, a, _) as mv), t
    | t, (Const(Mvar, a, _) as mv) ->
        if in_dom a s then
          fo_step red (mvar_subst s mv) t s
        else
          let t_sub = mvar_subst s t in
          if occurs a t_sub then
            raise UFail
          else
            add_subst a t_sub s
    | Const(Local, a1, _), Const(Local, a2, _)
    | TopLevel(a1, _, _), TopLevel(a2, _, _) ->
        if a1 = a2 then s else raise UFail
    | App(t1, u1), App(t2, u2) ->
        let m_t = fo_step red t1 t2 s in
        fo_step red u1 u2 m_t
    | Bound(_, b1, a1, ty1, u1), Bound(_, b2, _, ty2, u2) ->
        if b1 = b2 then
          let m_ty = fo_step red ty1 ty2 s in
          let _, u1_o = open_t a1 ty1 u1 in
          (* open with the same name, to get alpha equality *)
          let _, u2_o = open_t a1 ty2 u2 in
          fo_step red u1_o u2_o m_ty
        else
          raise UFail
    | Proj(p1, u1), Proj(p2, u2) ->
        if p1 = p2
        then fo_step red u1 u2 s
        else raise UFail
    | Pair(a1, ty1, t1, u1), Pair(_, ty2, t2, u2) ->
        let dummy = Type Z in
        let _, ty1_o = open_t a1 dummy ty1 in
        let _, ty2_o = open_t a1 dummy ty2 in
        let m_ty = fo_step red ty1_o ty2_o s in
        let m_t = fo_step red t1 t2 m_ty in
        fo_step red u1 u2 m_t
    | _ -> raise UFail
            

let rec fo_unif i csts s = 
  match csts with
    | [] -> s
    | Eq (_, t1, t2)::cs ->
        let m_t = fo_step i.red t1 t2 s in
        fo_unif i cs m_t
    | _::cs -> fo_unif i cs s

let elab unif info t =
  let cst = make_type_constr t in
  (* Printf.printf "constraints: %a\n" print_cstrs cst; *)
  let s = unif info cst empty_subst in
  let t_sub = mvar_subst s t in
  let m_t_sub = Expr.get_mvars t_sub in
  if m_t_sub = [] then
    t_sub
  else
    raise (MvarNoVal (t_sub, m_t_sub))

let occurs_rigid a t = occurs a t
  
let destruct t1 t2 =
  match t1, t2 with
    | Const(Mvar, _, _), _
    | _, Const(Mvar, _, _) ->
        assert false
    | Const(Local, a1, _), Const(Local, a2, _)
    | TopLevel(a1, _, _), TopLevel(a2, _, _) ->
        if a1 = a2 then [] else raise UFail
    | App(t1, u1), App(t2, u2) ->
        [Eq (false, t1, t2); Eq (false, u1, u2)]
    | Bound(_, b1, a1, ty1, u1), Bound(_, b2, _, ty2, u2) ->
        if b1 = b2 then
          let _, u1_o = open_t a1 ty1 u1 in
          (* open with the same name, to get alpha equality *)
          let _, u2_o = open_t a1 ty2 u2 in
          [Eq (false, ty1, ty2); Eq (false, u1_o, u2_o)]
        else
          raise UFail
    | Proj(p1, u1), Proj(p2, u2) ->
        if p1 = p2
        then [Eq (false, u1, u2)]
        else raise UFail
    | Pair(a1, ty1, t1, u1), Pair(_, ty2, t2, u2) ->
        let dummy = Type Z in
        let _, ty1_o = open_t a1 dummy ty1 in
        let _, ty2_o = open_t a1 dummy ty2 in
        [Eq (false, ty1_o, ty2_o); Eq (false, t1, t2); Eq (false, u1, u2)]
    | _ -> raise UFail


let apply_hint hints s c = 
  match hints s c with
    | [] -> Postpone
    | l -> Branch l

let rigid_rigid info t1 t2 s =
  try
    Branch [(s, destruct t1 t2)]
  with UFail  ->
    apply_hint info.hints s (Eq (false, t1, t2))


(* This is the imitation part of Huet's 
   higher order unification algoritm *)
let imitate mvar args_m hd args s =
  let rec args_vars args tpe = 
    match args with
      | [] -> []
      | (Const(Local, a, ty) as c)::ags ->
          begin match tpe with
            | Bound (_, Pi, _, _, tm) ->
                let _, tm = Expr.open_t a ty tm in
                c :: args_vars ags tm
            | _ -> assert false
          end
      | _::ags -> begin match tpe with
          | Bound (_, Pi, a, ty, tm) ->
            let b, tm = Expr.open_t a ty tm in
            Const (Local, b, ty) :: (args_vars ags tm)
          | _ -> assert false
      end
  in
  let args_vars = args_vars args_m (Elab.type_raw mvar) in
  let rec body tm args cstrs =
    match List.rev args with
      | [] -> (tm, cstrs)
      | u::us ->
          let u_ty = Elab.type_raw u in
          (* TODO: get the name for u_arg from
             the type of hd *)
          let u_mvar = Expr.fresh_mvar (make_name "u_arg") u_ty in
          let u_app = make_app u_mvar args_vars in
          let u_ts = make_app u_mvar args_m in
          body (App (tm, u_app)) us (Eq (false, u_ts, u)::cstrs)
  in
  let body, constr = body hd args [] in
  let body = make_abst args_vars body in

  let s = add_subst (Expr.name_of mvar) body s in
  s, constr

(* This is the projection part from Huet's algorithm *)
let project conv mvar arg_m rhs s =
  let ty_m = Elab.type_raw mvar in
  let rhs_ty = Elab.type_raw rhs in
  let rec args_proj args tpe = 
    match args with
      | [] -> [], []
      | t::ts -> begin match tpe with
          | Bound (_, Pi, a, ty, tm) ->
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
      let s = add_subst (Expr.name_of mvar) p_x s in
      s, [Eq (false, t, rhs)]
  ) proj

let flex_rigid conv mvar args_m r s = 
  let hd_r, args_r = Expr.get_app r in
  let imit = imitate mvar args_m hd_r args_r s in
  let proj = project conv mvar args_m r s in
  Branch (imit::proj)

let rec eq_step info t1 t2 s =
  let t1, t2 = Conv.reduce info.red t1, Conv.reduce info.red t2 in
  let hd1, args1 = Expr.get_app t1 in
  let hd2, _ = Expr.get_app t2 in
    match hd1, hd2 with
    | Const(Mvar, a, _), _ -> 
        begin try
                if in_dom a s then
                  eq_step info (mvar_subst s t1) t2 s
                else if occurs_rigid a t2 then
                  raise UFail
                else
                  let r = mvar_subst s t2 in
                  flex_rigid info.conv hd1 args1 r s
          with Invalid_argument _ ->
          raise UFail
        end
    | _, Const (Mvar, _, _) -> eq_step info t2 t1 s
    | _ -> rigid_rigid info t1 t2 s


let rec try_branch branches unif c cs =
  match branches with
    | [] -> raise UFail
    | (s, cs')::bs -> 
        try
          unif s (cs'@cs)
        with UFail ->
          try_branch bs unif c cs

let is_trivial info c s =
  match c with
    | Eq (_, t1, t2) -> 
        let t1_s, t2_s = mvar_subst s t1, mvar_subst s t2 in
        Conv.check_conv info.conv t1_s t2_s
    | HasType (_, t, ty) ->
        let t_s, ty_s = mvar_subst s t, mvar_subst s ty in
        let t_ty = Elab.type_raw t_s in
        Conv.check_conv info.conv t_ty ty_s
    | _ -> false  


let ty_step _ _ _ _ (* info *) (* t *) (* ty *) (* s *) =
  raise UFail

let ho_step info c s =
  try
    match c with
      | Eq (_, t1, t2) -> eq_step info t1 t2 s
      | HasType (_, t, ty) -> ty_step info t ty s
      | _ -> raise UFail
  with UFail -> apply_hint info.hints s c

let is_postponed c =
  match c with
    | Eq (b, _, _) -> b
    | HasType (b, _, _) -> b
    | IsType (b, _) -> b

let set_postponed c =
  match c with
    | Eq (_, t1, t2) -> Eq (true, t1, t2)
    | HasType (_, t, ty) -> HasType (true, t, ty)
    | IsType (_, t) -> IsType (true, t)

let rec ho_unif info constr s =
  try
    match constr with
      | [] -> s
      | c::cs ->
          if is_trivial info c s then ho_unif info cs s
            else begin
              match ho_step info c s with
                | Branch bs ->
                    try_branch bs (fun s cs -> ho_unif info cs s) c cs
                | Postpone ->
                    if not (is_postponed c) then
                      let c' = set_postponed c in
                      ho_unif info (cs@[c']) s
                    else
                      raise (UnsolvableConstr constr)
            end
  with
      UFail -> raise (UnsolvableConstr constr)


let add_ty_hint t hints =
  fun s c ->
    let br = hints s c in
    match c with
      | HasType (_, _, ty) ->
          let ty_s = mvar_subst s ty in
          let hd_t, _ = get_app t in
          let hd_ty, _ = get_app ty_s in
          if Expr.equal hd_t hd_ty then
            (s, [Eq (false, t, ty)])::br
          else
            br
      | _ -> br

(* let add_eq_hint t1 t2 hints = assert false *)

let empty_hints _ _ = []
