

open Expr

type constr =   Eq of bool * Expr.t * Expr.t 
              | HasType of bool * Expr.t * Expr.t
              | IsType of bool * Expr.t

type constrs = constr list

let print_cstr o c = 
  match c with
    | Eq (_, t1, t2) -> Printf.fprintf o "%a ?== %a" print_term t1 print_term t2
    | HasType (_, t1, t2) -> Printf.fprintf o "%a ?: %a" print_term t1 print_term t2
    | IsType (_, t) -> Printf.fprintf o "%a ?: Type?" print_term t

let print_cstrs o cs =
  let rec print_lst_aux cs =
    begin match cs with
      | [] -> ()
      | [c] -> print_cstr o c
      | c::cs ->
          print_cstr o c;
          Printf.fprintf o ", ";
          print_lst_aux cs
    end
  in
  Printf.fprintf o "{";
  print_lst_aux cs;
  Printf.fprintf o "}"

let rec type_raw t =
  match t with
    | Type _ -> Type Z
    | TopLevel (_, (_, ty), _) -> ty
    | Const(Local, _, ty) -> ty
    | Const(Mvar, _, ty) ->
        let ty_sort = type_raw ty in
        begin match ty_sort with
          | Type _
          | Const(Mvar, _, _) -> ty
          | _ -> raise (Typing.NotAType(ty, ty_sort))
        end
    | DB _ -> assert false
    | Bound(i, b, a, t1, t2) ->
        let (a_var, t2) = open_t a t1 t2 in
        let t1_ty = type_raw t1 in
        let t2_ty = type_raw t2 in
        begin match b with
          | Pi -> 
              begin match t1_ty, t2_ty with
              | Type _, Type _ -> Type Z
              | Type _, _ -> raise (Typing.NotAType (t2, t2_ty))
              | _, _ -> raise (Typing.NotAType (t1, t1_ty))
          end
          | Sig -> begin match t1_ty, t2_ty with
              | Type _, Type _ -> Type Z
              | Type _, _ -> raise (Typing.NotAType (t2, t2_ty))
              | _, _ -> raise (Typing.NotAType (t1, t1_ty))
          end
          | Abst -> Bound(i, Pi, a, t1, abst a_var t2_ty)
        end
    | App(t1, t2) ->
        let t1_ty = type_raw t1 in
        begin match t1_ty with
          | Bound(_, Pi, _, _, body) -> subst t2 body
          | _ -> raise (Typing.NotAPi (t1, t1_ty))
        end      
    | Pair (a, ty, t1, _) ->
        let t1_ty = type_raw t1 in
        let _, ty = open_t a t1_ty ty in
        Bound (default_info, Sig, a, t1_ty, ty)
    | Proj (Fst, t) ->
        let t_ty = type_raw t in
        begin match t_ty with
          | Bound (_, Sig, _, ty_arg, _) -> ty_arg
          | _ -> raise (Typing.NotASig (t, t_ty))
        end
    | Proj (Snd, t) ->
        let t_ty = type_raw t in
        begin match t_ty with
          | Bound (_, Sig, _, _, ty_body) ->
              let fst_t = Proj (Fst, t) in
              subst fst_t ty_body
          | _ -> raise (Typing.NotASig (t, t_ty))
        end


(* level constraints are not generated or even checked! *)
let rec type_constr conv t cs =
  match t with
    (*TODO: make the universes correct! *)
    | Type _ -> (Type Z, cs)
    (*Invariant: TopLevel constants
      are fully elaborated *)
    | TopLevel (_, (_, ty), _) -> (ty, cs)
    | Const(Local, _, ty) -> (ty, cs)
    | Const(Mvar, _, ty) ->
        let ty_sort, cs' = type_constr conv ty cs in
        begin match ty_sort with
          | Type _ -> 
              (ty, HasType (false, t, ty)::cs')
          | Const(Mvar, _, _) ->
              (ty, HasType (false, t, ty)::IsType (false, ty_sort)::cs')
          | _ -> raise (Typing.NotAType(ty, ty_sort))
        end
    | DB _ -> assert false
    | Bound(i, b, a, t1, t2) ->
        let (a_var, t2) = open_t a t1 t2 in
        let t1_ty, c1 = type_constr conv t1 cs in
        let t2_ty, c2 = type_constr conv t2 c1 in
        begin match b with
          | Pi -> begin match t1_ty, t2_ty with
              | Type _, Type _ -> 
                  (*TODO: insert meta-variable here? *)
                  (Type Z, c2)
              | Type _, _ -> raise (Typing.NotAType (t2, t2_ty))
              | _, _ -> raise (Typing.NotAType (t1, t1_ty))
          end
          | Sig -> begin match t1_ty, t2_ty with
              | Type _, Type _ -> 
                  (*TODO: insert meta-variable here? *)
                  (Type Z, c2)
              | Type _, _ -> raise (Typing.NotAType (t2, t2_ty))
              | _, _ -> raise (Typing.NotAType (t1, t1_ty))
          end
          | Abst -> 
              let _, cs' = type_constr conv t2_ty c2 in
              (Bound(i, Pi, a, t1, abst a_var t2_ty), cs')
        end
    | App(t1, t2) ->
        let t1_ty, c1 = type_constr conv t1 cs in
        let t2_ty, c2 = type_constr conv t2 c1 in
        begin match t1_ty with
          | Bound(_, Pi, _, ty, body) 
              when Conv.check_conv conv t2_ty ty ->
              (subst t2 body, c2)
          | Bound(_, Pi, _, ty, body) ->
              (subst t2 body, Eq (false, t2_ty, ty)::c2)
          | _ -> raise (Typing.NotAPi (t1, t1_ty))
        end      
    | Pair (a, ty, t1, t2) ->
        let t1_ty, c1 = type_constr conv t1 cs in
        let ty_sub_t1 = subst t1 ty in
        let t2_ty, c2 = type_constr conv t2 c1 in
        let _, ty = open_t a t1_ty ty in
        let _, c_ty = type_constr conv ty c2 in
        let out_cstr = Eq (false, ty_sub_t1, t2_ty)::c_ty in
        (Bound (default_info, Sig, a, t1_ty, ty), out_cstr)
    | Proj (Fst, t) ->
        let t_ty, c1 = type_constr conv t cs in
        begin match t_ty with
          | Bound (_, Sig, _, ty_arg, _) -> 
              (ty_arg, c1)
          | _ -> raise (Typing.NotASig (t, t_ty))
        end
    | Proj (Snd, t) ->
        let t_ty, c1 = type_constr conv t cs in
        begin match t_ty with
          | Bound (_, Sig, _, _, ty_body) ->
              let fst_t = Proj (Fst, t) in
              (subst fst_t ty_body, c1)
          | _ -> raise (Typing.NotASig (t, t_ty))
        end

let make_type_constr t = snd (type_constr Conv.conv t [])

let bound b s ty bod =
  let x = make_name s in
  Bound (default_info, b, x, ty, abst x bod)

let pi s ty tm = bound Pi s ty tm

let lambda s ty tm = bound Abst s ty tm

let sigma s ty tm = bound Sig s ty tm

let app t1 t2 = 
  App (t1, t2)

let fst t = Proj (Fst, t)

let snd t = Proj (Snd, t)

let pair s ty t1 t2 =
  let x = make_name s in
  Pair(x, abst x ty, t1, t2)

let type0 = Type Z

let type1 = Type (Suc Z)

let dummy = Type Z

let magic prop =
  let magic_name = Expr.make_name "Boole_magic" in
  Const (Local, magic_name, prop)

let wild ctxt = 
    let ty = fresh_mvar (make_name "T") (Type (Suc Z)) in
    let ty_cst = make_pi ctxt ty in
    let m = fresh_mvar (make_name "m") ty_cst in
    make_app m (List.rev ctxt)

let coerce ty1 ty2 = 
  let arrow = Bound(default_info, Pi, make_name "_", ty1, ty2) in
  fresh_mvar (make_name "Coercion_") arrow

let top name ty = TopLevel (make_name name, ([], ty), [])

let eq = 
  let x = Const(Local, make_name "X", type1) in
  let y = Const(Local, make_name "Y", type1) in
  let eq_ty = pi "X" type1 (pi "Y" type1 (pi "_" x (pi "_" y type0))) in
  top "Eq" eq_ty

let cast_tm = 
  let x = Const(Local, make_name "X", type1) in
  let y = Const(Local, make_name "Y", type1) in
  let eq_x_y = app (app (app (app eq type1) type1) x) y in
  let cast_ty = pi "X" type1 (pi "Y" type1 (pi "e" eq_x_y (pi "_" x y))) in
  top "Cast" cast_ty

let cast ty1 ty2 x ctxt =
  app (app (app (app cast_tm ty1) ty2) (wild ctxt)) x


let deco_mvar a ctxt =
  if string_of_name a = "Boole_wild" then
    wild ctxt
  else
    assert false

let rec deco_cst t ctxt = 
  match type_raw t with
    | Bound({implicit=true; _}, Pi, _, _, _) -> deco_cst (App (t, wild ctxt)) ctxt
    | _ -> t


let rec deco t ctxt =
  match t with
    | Const(Mvar, a, _) -> deco_mvar a ctxt
    | Const _ | TopLevel _ | Type _ -> deco_cst t ctxt
    | DB _ -> assert false
    | App (t1, t2) ->
        let t1' = deco t1 ctxt in
        let t2' = deco t2 ctxt in
        begin match type_raw t1' with
          | Bound({implicit=true; _}, Pi, _, _, _) -> App (App(t1', wild ctxt), t2')
          | Bound({cast=true; _}, Pi, _, dom, _) ->
              let arg_ty = type_raw t2' in
              App (t1', cast arg_ty dom t2' ctxt)
          | _ ->   App (t1', t2')
        end
    | Proj (p, t') ->
        Proj (p, deco t' ctxt)
    | Bound (i, b, a, ty, tm) ->
        let ty' = deco ty ctxt in
        let a', open_tm = Expr.open_t a ty' tm in
        let c = Const (Local, a', ty') in
        let tm' = deco open_tm (c::ctxt) in
        Bound (i, b, a, ty', abst a' tm')
    | Pair (a, ty, t1, t2) ->
        let t1' = deco t1 ctxt in
        let t2' = deco t2 ctxt in
        let ty_1 = type_raw t1' in
        let a', open_ty = Expr.open_t a ty_1 ty in
        let c = Const (Local, a', ty_1) in
        let ty' = deco open_ty (c::ctxt) in
        Pair (a, abst a' ty', t1', t2')

let decorate t = deco t []
