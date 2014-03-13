NAME = boole_top

OCAMLC=ocp-ocamlc

OCAMLYACC=ocamlyacc

OCAMLLEX=ocamllex

FLAGS=-annot,"-w @a-e"

OCAMLBUILD=ocamlbuild

OPTIONS=-cflags $(FLAGS)

.PHONY: native byte clean stat

native:
	$(OCAMLBUILD) $(OPTIONS) main.native
	mv main.native $(NAME)

byte:
	$(OCAMLBUILD) $(OPTIONS) main.byte
	mv main.byte $(NAME)

clean:
	$(OCAMLBUILD) $(OPTIONS) -clean
