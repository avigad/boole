OCAMLC=ocp-ocamlc
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex
FLAGS=-annot -w @A-E

all: expr.cmo conv.cmo typing.cmo elab.cmo unif.cmo toplevel.cmo boole_parse.cmo boole_lex.cmo main.cmo
	 $(OCAMLC) $(FLAGS) expr.cmo conv.cmo typing.cmo elab.cmo unif.cmo toplevel.cmo boole_parse.cmo boole_lex.cmo main.cmo -o boole_top

expr.cmo : expr.mli expr.ml
	$(OCAMLC) -c $(FLAGS) expr.mli expr.ml

conv.cmo : expr.cmo conv.mli conv.ml
	$(OCAMLC) -c $(FLAGS) conv.mli conv.ml

typing.cmo : expr.cmo conv.cmo typing.mli typing.ml
	$(OCAMLC) -c $(FLAGS) typing.mli typing.ml

elab.cmo : expr.cmo conv.cmo typing.cmo elab.mli elab.ml
	$(OCAMLC) -c $(FLAGS) elab.mli elab.ml

unif.cmo : expr.cmo elab.cmo unif.mli unif.ml
	$(OCAMLC) -c $(FLAGS) unif.mli unif.ml

boole_lex.cmo : expr.cmo conv.cmo elab.cmo typing.cmo toplevel.cmo boole_parse.ml boole_lex.ml
	$(OCAMLC) -c $(FLAGS) boole_lex.ml

boole_parse.cmo : expr.cmo conv.cmo elab.cmo typing.cmo toplevel.cmo boole_parse.ml
	$(OCAMLC) -c $(FLAGS) boole_parse.mli boole_parse.ml

boole_lex.ml : expr.cmo conv.cmo elab.cmo typing.cmo toplevel.cmo boole_parse.cmo boole_lex.mll
	$(OCAMLLEX) boole_lex.mll

boole_parse.ml : expr.cmo conv.cmo elab.cmo typing.cmo toplevel.cmo boole_parse.mly
	$(OCAMLYACC) boole_parse.mly

toplevel.cmo : expr.cmo conv.cmo elab.cmo typing.cmo unif.cmo toplevel.mli toplevel.ml
	$(OCAMLC) -c $(FLAGS) toplevel.mli toplevel.ml

main.cmo : expr.cmo conv.cmo typing.cmo elab.cmo unif.cmo toplevel.cmo boole_parse.cmo boole_lex.cmo main.ml
	$(OCAMLC) -c $(FLAGS) main.ml
