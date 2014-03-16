
module NMap = Expr.NMap

type term = Expr.t
type index = Expr.index

type decl = index list * term

type t = 
    {
      name            : string;
      decls           : decl NMap.t;
      hyps            : decl NMap.t;
      defs            : decl NMap.t;
      rew_rules       : decl NMap.t;
      classes         : decl NMap.t;
      class_def       : decl NMap.t;
      class_instances : decl NMap.t;
      goals           : decl NMap.t;
      parent          : t option
    }
        
  
let new_map = NMap.empty
    
let new_ctxt name =
  {
    name = name;
    decls           = new_map ;
    hyps            = new_map ;
    defs            = new_map ;
    rew_rules       = new_map ;
    classes         = new_map ;
    class_def       = new_map ;
    class_instances = new_map ;
    goals           = new_map ;
    parent          = None
  }

let add_decl a t ctxt =
  {ctxt with
    decls = NMap.add a ([], t) ctxt.decls}

let get_decl a ctxt =
  NMap.find a ctxt.decls