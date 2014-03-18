
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

let check_core t =
  let ty = Typing.type_raw Conv.conv t in
  match free_vars ty with
      [] ->
        Printf.printf "%a : %a\n" print_term t print_term ty
    | a::_ -> raise (NotFound (string_of_name a))

(* let elab t = Unif.elab Unif.fo_unif Conv.hd_beta_norm t *)
let elab t = Unif.elab Unif.ho_unif Conv.hd_beta_norm t


let wild = Const(Mvar,Expr.make_name "Boole_wild", type1)

let print_type_err t t1 t2 t3 =
  Printf.eprintf
    "Type Error: in %a:\n%a is of type %a, but is expected to be of type %a\n" 
    print_term t print_term t1 print_term t2 print_term t3

let err t = Printf.eprintf "In the term %a:\n" print_term t

(*TODO: clean this up *)
let wrap_call f t =
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

let check t = 
    let t1 = Elab.decorate t in
    let t2 = wrap_call elab t1 in
    wrap_call check_core t2

let add_top s t = 
  let t1 = Elab.decorate t in
  let t2 = wrap_call elab t1 in
  wrap_call
    (fun t -> match Typing.type_raw Conv.conv t with
      | Type _ ->
          let x = make_name s in
          let x_tm = TopLevel(x, ([], t), []) in
          check_core x_tm;
          top_ctxt := add_decl x t !top_ctxt
      | ty -> raise (NotAType (t, ty)))
    t2

