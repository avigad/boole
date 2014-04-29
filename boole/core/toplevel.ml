
open Expr
open Typing
open Context


exception NotFound of string

exception TypingError

exception UnifError

(* The basic context which is loaded by default *)

let top_ctxt = ref (new_ctxt "top")

(* Helper constants and functions for defining terms *)

let dummy = Type Z

let make_var s =
    let x = make_name s in
  try
    let top = get_decl x !top_ctxt in
    TopLevel(x, top, [])
  with Not_found -> 
    Const(Local, x, dummy)

let ibound i b s ty bod =
  let x = make_name s in
  Bound (i, b, x, ty, abst x bod)

let bound b s ty bod = ibound default_info b s ty bod

let pi s ty tm = bound Pi s ty tm

let ipi s ty tm = ibound {implicit = true; cast = false} Pi s ty tm

let cpi s ty tm = ibound {implicit = false; cast = true} Pi s ty tm

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

let wild = Const(Mvar,Expr.make_name "Boole_wild", type1)

let magic a t =
  let magic_a = Expr.make_name ("magic_" ^ Expr.string_of_name a) in
  Const(Local, magic_a, t)

(* Base functions for declaring constants and hints *)

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
  let goals = 
    List.fold_left
      (fun gs m ->
        match m with
          | Const (Mvar, a, ty) ->
              let ty_s = Unif.mvar_subst subst ty in
              top_ctxt := Context.add_goal a ty_s !top_ctxt;
              ty_s::gs
              
          | _ -> assert false)
      [] mvars
  in
  (Unif.mvar_subst subst t, goals)
  

let check_core t =
  let ty = Typing.type_raw Conv.conv t in
  match free_vars ty with
      [] ->
        Printf.printf "%a : %a\n" print_term t print_term ty
    | a::_ -> raise (NotFound (string_of_name a))

let elab t = 
  let u_info = {Unif.red = Conv.hd_beta_norm; 
                Unif.conv = Conv.conv; 
                Unif.hints = !top_ctxt.hints} in
  try
    (Unif.elab Unif.ho_unif u_info t, [])
  with Unif.MvarNoVal (t, ms) ->
    make_goals t ms

let print_type_err t t1 t2 t3 =
  Printf.eprintf
    "Type Error: in %a:\n%a is of type %a, but is expected to be of type %a\n" 
    print_term t print_term t1 print_term t2 print_term t3

let err t = Printf.eprintf "In the term %a:\n" print_term t

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

let print_goals goals =
  let i = ref 1 in
  if goals = [] then
    ()
  else begin
    Printf.printf "Remaining goals:\n\n";
    List.iter (
      fun g -> 
        Printf.printf "%d: %a\n" !i print_term g
    ) goals;
    Printf.printf "\n"
  end
  
let check t = 
    let t1 = Elab.decorate t in
    let t2, goals = call_with_handle elab t1 in
    call_with_handle check_core t2;
    print_goals goals

(* Functions for adding new fields to the top context *)

let add_top s t = 
  let t1 = Elab.decorate t in
  let t2, goals = call_with_handle elab t1 in
  call_with_handle
    (fun t -> match Typing.type_raw Conv.conv t with
      | Type _ ->
          let x = make_name s in
          let x_tm = TopLevel(x, ([], t), []) in
          check_core x_tm;
          top_ctxt := add_decl x t !top_ctxt
      | ty -> raise (NotAType (t, ty)))
    t2;
  print_goals goals

let add_hint t =
  call_with_handle (fun t -> ignore (Typing.type_raw Conv.conv t)) t;
  top_ctxt := add_hint t !top_ctxt
