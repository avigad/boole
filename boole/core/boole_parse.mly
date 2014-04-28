%{
  open Toplevel
%}
%token <string> IDENT
%token LPAREN RPAREN
%token LSQ RSQ
%token LBRACK RBRACK
%token LANGLE RANGLE
%token ABST
%token FST SND
%token MAPSTO
%token ARROW
%token COMMA
%token COLON
%token MBAR
%token COLONEQ
%token VAR
%token HINT
%token DEF
%token CHECK
%token EOL
%token BOOL
%token TYPE
%token WILD
%token TILDE
%token POUND
%start top
%type <unit> top
%%

expr :
   | expr expr_1
      { Toplevel.app $1 $2 }
   | expr_1
      { $1 }
;

expr_1 :
   | IDENT
       { Toplevel.make_var $1 }
   | WILD
       { Toplevel.wild }
   | BOOL
       { Toplevel.type0 }
   | TYPE
       { Toplevel.type1 }
   | LPAREN expr RPAREN
       { $2 }
   | TILDE LSQ IDENT COLON expr RSQ expr
       { Toplevel.cpi $3 $5 $7}
   | POUND LSQ IDENT COLON expr RSQ expr
       { Toplevel.ipi $3 $5 $7}
   | LSQ IDENT COLON expr RSQ expr
       { Toplevel.pi $2 $4 $6}
   | ABST IDENT COLON expr MAPSTO expr
       { Toplevel.lambda $2 $4 $6}
   | LBRACK IDENT COLON expr MBAR expr RBRACK
       { Toplevel.sigma $2 $4 $6}
   | expr ARROW expr
       { Toplevel.pi "_" $1 $3 }
   | FST expr
       { Toplevel.fst $2 }
   | SND expr
       { Toplevel.snd $2 }
   | LANGLE expr COMMA expr COLON LSQ IDENT RSQ expr RANGLE
       { Toplevel.pair $7 $9 $2 $4 }
;



top :
     VAR IDENT COLON expr EOL
       { Toplevel.add_top $2 $4 }
   | CHECK expr EOL
       { Toplevel.check $2 }
   | HINT expr EOL
       { Toplevel.add_hint $2 }
   | EOL
       { () }
;
