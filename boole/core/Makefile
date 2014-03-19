NAME = boole_top

OCAMLC=ocp-ocamlc

OCAMLYACC=ocamlyacc

OCAMLLEX=ocamllex

CFLAGS=-annot,"-w @a-e"

LFLAGS=-g

OCAMLBUILD=ocamlbuild

OPTIONS=-verbose 0 -cflags $(CFLAGS) -lflags $(LFLAGS)

.PHONY: native byte clean stat

native:
	$(OCAMLBUILD) $(OPTIONS) main.native
	mv main.native $(NAME)

byte:
	$(OCAMLBUILD) $(OPTIONS) main.byte
	mv main.byte $(NAME)

clean:
	$(OCAMLBUILD) $(OPTIONS) -clean
