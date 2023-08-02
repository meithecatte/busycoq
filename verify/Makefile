COQMFFLAGS := -Q . BusyCoq

ALLVFILES := LibTactics.v Helper.v TM.v Compute.v Flip.v Cyclers.v TranslatedCyclers.v Extraction.v Individual.v FixedBin.v ShiftOverflow.v Skelet34.v

all: build verify

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) extraction.ml extraction.mli *.cmi *.cmx *.o verify

verify: extraction.mli extraction.ml main.ml
	ocamlopt.opt -o $@ $^

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
