
open Expr
open Typing
open Context


exception NotFound of string


let top_ctxt = ref (new_ctxt "top")

let dummy = Sort (Type Z)

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

let type0 = Sort (Type Z)

let type1 = Sort (Type (Suc Z))

let check_core t =
  let ty = type_raw Conv.conv t in
  match free_vars ty with
      [] ->
        Printf.printf "%a : %a\n" print_term t print_term ty
    | a::_ -> raise (NotFound (string_of_name a))

(* let elab t = Unif.elab Unif.fo_unif Conv.hd_beta_norm t *)
let elab t = Unif.elab Unif.ho_unif Conv.hd_beta_norm t


let wild () =
  let ty = fresh_mvar (make_name "T") type1 in
  fresh_mvar (make_name "m") ty


let print_type_err t t1 t2 t3 =
  Printf.eprintf
    "Type Error: in %a:\n%a is of type %a, but is expected to be of type %a\n" 
    print_term t print_term t1 print_term t2 print_term t3


let elab_call f t =
  try
    let t = elab t in
    f t
  with
    | NotFound s ->
        Printf.eprintf
          "Unknown identifier: %s\n" s
    | TypeError (t1, t2, t3) ->
      print_type_err t t1 t2 t3
    | NotAPi (t1, t2) ->
        Printf.eprintf
          "Type Error: %a has type %a, which is expected to be a Pi type\n"
          print_term t1 print_term t2
    | NotASig (t1, t2) ->
        Printf.eprintf 
          "Type Error: %a has type %a, which is expected to be a Sigma type\n"
          print_term t1 print_term t2
    | NotASort (t1, t2) ->
        Printf.eprintf 
          "Type Error: %a has type %a which is expected to be a sort\n"
          print_term t1 print_term t2


let check t = elab_call check_core t

let add_top s t = elab_call
  (fun t -> match type_raw Conv.conv t with
      | Sort _ ->
        let x = make_name s in
        let x_tm = TopLevel(x, ([], t), []) in
        check_core x_tm;
        top_ctxt := add_decl x t !top_ctxt
    | ty -> raise (NotASort (t, ty)))
  t

