(*****************************************************************

  conv.ml

 description: various conversion helpers, including computing
 beta-normal forms


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

open Expr

exception ConstantUndefined of Expr.t

type reduction = Expr.t -> Expr.t

type conv = Expr.t -> Expr.t -> bool

let hd_beta_step t =
  match t with
    | App (Bound (Abst, _, _, t1), t2) ->
      subst t2 t1
    | Proj (Fst, Pair(_, _, t, _)) -> t
    | Proj (Snd, Pair(_, _, _, t)) -> t
    | Type _ | Const _ | DB _
    | Bound _ | App _ | Pair _ 
    | TopLevel _ | Proj _ -> t



let rec hd_beta_norm t =
  match t with
    | App (Bound (Abst, _, _, t1), t2) ->
      hd_beta_norm (subst t2 t1)
    | Proj (Fst, Pair(_, _, t, _)) -> 
      hd_beta_norm t
    | Proj (Snd, Pair(_, _, _, t)) -> 
      hd_beta_norm t
    | Type _ | Const _ | DB _
    | Bound _ | App _ | Pair _ | Proj _ | TopLevel _ -> t



let rec unfold names m t =
  match t with
    | TopLevel (a, top, ls) when List.mem a names ->
      begin try
              let def = NMap.find a m in
              let is, _ = top in
              subst_ls is ls def
        with Not_found -> raise (ConstantUndefined t)
      end
    | TopLevel _
    | Const _ | Type _ | DB _ -> t
    | Bound (b, a, ty, tm) ->
      let ty_u, tm_u = unfold names m ty, unfold names m tm in
      Bound (b, a, ty_u, tm_u)
    | App (t1, t2) -> App (unfold names m t1, unfold names m t2)
    | Pair (a, ty, t1, t2) ->
      let ty_u = unfold names m ty in
      let t1_u, t2_u = unfold names m t1, unfold names m t2 in
      Pair (a, ty_u, t1_u, t2_u)
    | Proj (p, t) -> Proj (p, unfold names m t)


let rec beta_eq t1 t2 =
  let h1 = hd_beta_norm t1 in
  let h2 = hd_beta_norm t2 in
  begin match h1, h2 with
    | Bound(b1, _, ty1, t1), Bound(b2, _, ty2, t2) ->
      (b1 = b2) && (beta_eq ty1 ty2) && (beta_eq t1 t2)
    | Pair(_, ty1, t1, u1), Pair(_, ty2, t2, u2) ->
      (beta_eq ty1 ty2) && (beta_eq t1 t2) && (beta_eq u1 u2)
    | Proj (p1, t1), Proj (p2, t2) ->
      (p1 = p2) && (beta_eq t1 t2)
    | _, _ -> Expr.equal h1 h2
  end



let rec conv t1 t2 =
  if t1 == t2 then true
  else begin
    let h1, tl1 = get_app (hd_beta_norm t1) in
    let h2, tl2 = get_app (hd_beta_norm t2) in
    let args =
      begin try
              List.for_all2 conv tl1 tl2
        with Invalid_argument _ -> false
      end
    in
    if args then
      begin match h1, h2 with
        | Bound(Pi, _, ty1, tm1), Bound(Pi, _, ty2, tm2) ->
            (beta_eq ty1 ty2) && (conv tm1 tm2)
        | Bound _, Bound _ -> beta_eq h1 h2
        | Type s1, Type s2 -> Expr.level_leq s1 s2 
        | _, _ -> Expr.equal h1 h2
      end
    else false
  end

let reduce r = r

let check_conv c = c
