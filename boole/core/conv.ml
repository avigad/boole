(*****************************************************************

  conv.ml

 description: various conversion helpers, including computing
 beta-normal forms


 Authors:
 Jeremy Avigad
 Cody Roux


******************************************************************)

open Expr

let hd_beta_step t =
  match t with
    | App (Bound (Abst, _, _, t1), t2) ->
      subst t2 t1
    | _ -> t


let rec hd_beta_norm t =
  match t with
    | App (Bound (Abst, _, _, t1), t2) ->
      hd_beta_norm (subst t2 t1)
    | _ -> t


module NMap = Map.Make(
  struct 
    type t = name 
    let compare = Pervasives.compare 
  end)

let rec unfold t names m =
  match t with
    | Const(Toplevel, a, _) when List.mem a names ->
      begin try
              NMap.find a m
        with Not_found -> t
      end
    | Const _ | Sort _ | DB _ -> t
    | Bound (b, a, ty, tm) ->
      let uty, utm = unfold ty names m, unfold tm names m in
      Bound (b, a, uty, utm)
    | App (t1, t2) -> App (unfold t1 names m, unfold t2 names m)


let rec beta_eq t1 t2 =
  let h1, tl1 = get_app (hd_beta_norm t1) in
  let h2, tl2 = get_app (hd_beta_norm t2) in
  let args =
    begin try
            List.for_all2 beta_eq tl1 tl2
      with Invalid_argument _ -> false
    end
  in
  if args then
    begin match h1, h2 with
      | Bound(b1, _, ty1, tm1), Bound(b2, _, ty2, tm2) ->
        (b1 = b2) && (beta_eq ty1 ty2) && (beta_eq tm1 tm2)
      | _, _ -> Expr.equal h1 h2
    end
  else false


let rec conv t1 t2 =
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
      | Sort s1, Sort s2 -> Expr.sort_leq s1 s2 
      | _, _ -> Expr.equal h1 h2
    end
  else false

