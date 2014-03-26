
open Expr
open Typing
open Context


exception NotFound of string

exception TypingError

exception UnifError

let top_ctxt = ref (new_ctxt "top")

let dummy = Type Z

let make_var s =
    let x = make_name s in
  try
    let top = get_decl x !top_ctxt in
    TopLevel(x, top, [])
  with Not_found -> 
    Const(Local, x, dummy)


let bound b s ty bod =
  let x = make_name s in
  Bound (b, x, ty, abst x bod)

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

(* TODO: make this top-level? *)
let magic a t =
  let magic_a = Expr.make_name ("magic_" ^ Expr.string_of_name a) in
  Const(Local, magic_a, t)


let make_goals t mvars =
  let subst = List.fold_left 
    (fun s m -> match m with
      | Const (Mvar, a, ty) ->
          let goal = magic a ty in
          Unif.add_subst a goal s
      | _ -> assert false)
    Unif.empty_subst
    mvars
  in
  List.iter
    (fun m ->
      match m with
        | Const (Mvar, a, ty) ->
            let ty_s = Unif.mvar_subst subst ty in
            top_ctxt := Context.add_goal a ty_s !top_ctxt
        | _ -> assert false)
    mvars;
  Unif.mvar_subst subst t
  

let check_core t =
  let ty = Typing.type_raw Conv.conv t in
  match free_vars ty with
      [] ->
        Printf.printf "%a : %a\n" print_term t print_term ty
    | a::_ -> raise (NotFound (string_of_name a))

(* let elab t = Unif.elab Unif.fo_unif Conv.hd_beta_norm t *)
let elab t = 
  let u_info = {Unif.red = Conv.hd_beta_norm; 
                Unif.conv = Conv.conv; 
                Unif.hints = !top_ctxt.hints} in
  try
    Unif.elab Unif.ho_unif u_info t
  with Unif.MvarNoVal (t, ms) ->
    make_goals t ms

let wild = Const(Mvar,Expr.make_name "Boole_wild", type1)

let print_type_err t t1 t2 t3 =
  Printf.eprintf
    "Type Error: in %a:\n%a is of type %a, but is expected to be of type %a\n" 
    print_term t print_term t1 print_term t2 print_term t3

let err t = Printf.eprintf "In the term %a:\n" print_term t

(*TODO: clean this up *)
let call_with_handle f t =
  try
    f t
  with
    | NotFound s ->
        err t;
        Printf.eprintf
          "Unknown identifier: %s\n" s;
        raise TypingError
    | TypeError (t1, t2, t3) ->
        err t;
        print_type_err t t1 t2 t3;
        raise TypingError
    | NotAPi (t1, t2) ->
        err t;
        Printf.eprintf
          "Type Error: %a has type %a, which is expected to be a Pi type\n"
          print_term t1 print_term t2;
        raise TypingError
    | NotASig (t1, t2) ->
        err t;
        Printf.eprintf 
          "Type Error: %a has type %a, which is expected to be a Sigma type\n"
          print_term t1 print_term t2;
        raise TypingError
    | NotAType (t1, t2) ->
        err t;
        Printf.eprintf 
          "Type Error: %a has type %a which is expected to be Type\n"
          print_term t1 print_term t2;
        raise TypingError
    | Unif.UnsolvableConstr cs ->
        Printf.eprintf
          "Unification Error: cannot solve constraints\n%a\n" Elab.print_cstrs cs;
        raise UnifError
    | Unif.MvarNoVal (t,m) ->
        Printf.eprintf
          "Unification Error: in %a: cannot find a value for ?%s\n"
          Expr.print_term t (Expr.string_of_name
                               (Expr.name_of (List.hd m)));
        raise UnifError

let check t = 
    let t1 = Elab.decorate t in
    let t2 = call_with_handle elab t1 in
    call_with_handle check_core t2

let add_top s t = 
  let t1 = Elab.decorate t in
  let t2 = call_with_handle elab t1 in
  call_with_handle
    (fun t -> match Typing.type_raw Conv.conv t with
      | Type _ ->
          let x = make_name s in
          let x_tm = TopLevel(x, ([], t), []) in
          check_core x_tm;
          top_ctxt := add_decl x t !top_ctxt
      | ty -> raise (NotAType (t, ty)))
    t2

let add_hint t =
  check t;
  top_ctxt := add_hint t !top_ctxt
