

open Expr

type constr = Eq of Expr.t * Expr.t | HasType of Expr.t * Expr.t
                | IsType of Expr.t

type constrs = constr list

let print_cstr o c = 
  match c with
    | Eq (t1, t2) -> Printf.fprintf o "%a ?== %a" print_term t1 print_term t2
    | HasType (t1, t2) -> Printf.fprintf o "%a ?: %a" print_term t1 print_term t2
    | IsType t -> Printf.fprintf o "%a ?: Type?" print_term t

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
    | Bound(b, a, t1, t2) ->
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
          | Abst -> Bound(Pi, a, t1, abst a_var t2_ty)
        end
    | App(t1, t2) ->
        let t1_ty = type_raw t1 in
        begin match t1_ty with
          | Bound(Pi, _, _, body) -> subst t2 body
          | _ -> raise (Typing.NotAPi (t1, t1_ty))
        end      
    | Pair (a, ty, t1, _) ->
        let t1_ty = type_raw t1 in
        let _, ty = open_t a t1_ty ty in
        Bound (Sig, a, t1_ty, ty)
    | Proj (Fst, t) ->
        let t_ty = type_raw t in
        begin match t_ty with
          | Bound (Pi, _, ty_arg, _) -> ty_arg
          | _ -> raise (Typing.NotASig (t, t_ty))
        end
    | Proj (Snd, t) ->
        let t_ty = type_raw t in
        begin match t_ty with
          | Bound (Pi, _, _, ty_body) ->
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
              (ty, HasType (t, ty)::cs')
          | Const(Mvar, _, _) ->
              (ty, HasType (t, ty)::IsType ty_sort::cs')
          | _ -> raise (Typing.NotAType(ty, ty_sort))
        end
    | DB _ -> assert false
    | Bound(b, a, t1, t2) ->
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
              (Bound(Pi, a, t1, abst a_var t2_ty), cs')
        end
    | App(t1, t2) ->
        let t1_ty, c1 = type_constr conv t1 cs in
        let t2_ty, c2 = type_constr conv t2 c1 in
        begin match t1_ty with
          | Bound(Pi, _, ty, body) 
              when Conv.check_conv conv t2_ty ty ->
              (subst t2 body, c2)
          | Bound(Pi, _, ty, body) ->
              (subst t2 body, Eq (t2_ty, ty)::c2)
          | _ -> raise (Typing.NotAPi (t1, t1_ty))
        end      
    | Pair (a, ty, t1, t2) ->
        let t1_ty, c1 = type_constr conv t1 cs in
        let ty_sub_t1 = subst t1 ty in
        let t2_ty, c2 = type_constr conv t2 c1 in
        let _, ty = open_t a t1_ty ty in
        let _, c_ty = type_constr conv ty c2 in
        let out_cstr = Eq (ty_sub_t1, t2_ty)::c_ty in
        (Bound (Sig, a, t1_ty, ty), out_cstr)
    | Proj (Fst, t) ->
        let t_ty, c1 = type_constr conv t cs in
        begin match t_ty with
          | Bound (Pi, _, ty_arg, _) -> 
              (ty_arg, c1)
          | _ -> raise (Typing.NotASig (t, t_ty))
        end
    | Proj (Snd, t) ->
        let t_ty, c1 = type_constr conv t cs in
        begin match t_ty with
          | Bound (Pi, _, _, ty_body) ->
              let fst_t = Proj (Fst, t) in
              (subst fst_t ty_body, c1)
          | _ -> raise (Typing.NotASig (t, t_ty))
        end
          
let make_type_constr t = snd (type_constr Conv.conv t [])

let magic prop =
  let magic_name = Expr.make_name "Boole_magic" in
  Const (Local, magic_name, prop)

let rec deco t ctxt =
  match t with
    | Const(Mvar, a, _) ->
        if Expr.string_of_name a = "Boole_wild" then
          let ty = fresh_mvar (make_name "T") (Type (Suc Z)) in
          let ty_cst = make_pi ctxt ty in
          let m = fresh_mvar (make_name "m") ty_cst in
          make_app m (List.rev ctxt)
        else
          assert false
    | Const _ | TopLevel _ | Type _ ->
        t
    | DB _ -> assert false
    | App (t1, t2) ->
        let t1' = deco t1 ctxt in
        let t2' = deco t2 ctxt in
        App (t1', t2')
    | Proj (p, t') ->
        Proj (p, deco t' ctxt)
    | Bound (b, a, ty, tm) ->
        let ty' = deco ty ctxt in
        let a', open_tm = Expr.open_t a ty' tm in
        let c = Const (Local, a', ty') in
        let tm' = deco open_tm (c::ctxt) in
        Bound (b, a, ty', abst a' tm')
    | Pair (a, ty, t1, t2) ->
        let t1' = deco t1 ctxt in
        let t2' = deco t2 ctxt in
        let ty_1 = type_raw t1' in
        let a', open_ty = Expr.open_t a ty_1 ty in
        let c = Const (Local, a', ty_1) in
        let ty' = deco open_ty (c::ctxt) in
        Pair (a, abst a' ty', t1', t2')

let decorate t = deco t []
