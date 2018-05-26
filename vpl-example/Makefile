.PHONY: clean tester

OCB_FLAGS = -use-ocamlfind -package vpl

OCB = ocamlbuild $(OCB_FLAGS)

tester: Example.ml
	$(OCB) tester.native
	./tester.native

clean:
	$(OCB) -clean
	rm -f *.vo Example.ml Example.mli *.glob
	rm -f *~ .*.aux

Example.ml ExtractExample.vo: ExtractExample.v Example.vo Makefile fix_extract.sh
	coqc ExtractExample.v && ./fix_extract.sh Example.ml Example.mli

Example.vo: Example.v
	coqc Example.v
