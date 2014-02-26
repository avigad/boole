OCAMLC=ocp-ocamlc

FLAGS=-annot -w @A-E

all: expr.cmo conv.cmo typing.cmo elab.cmo unif.cmo main.ml
	 $(OCAMLC) $(FLAGS) expr.cmo conv.cmo typing.cmo elab.cmo unif.cmo main.ml -o boole_ml

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