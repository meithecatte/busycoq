COQMFFLAGS := -Q . BusyCoq

ALLVFILES := LibTactics.v Helper.v TM.v Compute.v Flip.v Cyclers.v TranslatedCyclers.v Extraction.v \
		Individual.v FixedBin.v ShiftOverflow.v Skelet34.v Skelet35.v Skelet1.v

all: build verify skelet1

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) extraction.ml extraction.mli skelet1.mli skelet1.ml *.cmi *.cmx *.o verify skelet1

verify: extraction.mli extraction.ml main.ml
	ocamlopt.opt -o $@ $^

skelet1: skelet1.mli skelet1.ml skelet1_main.ml
	ocamlfind ocamlopt -o $@ -linkpkg -package zarith $^

extraction.mli extraction.ml: Extraction.vo
skelet1.mli skelet1.ml: Skelet1.vo
Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
