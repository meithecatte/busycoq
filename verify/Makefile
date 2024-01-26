COQMFFLAGS := -Q . BusyCoq

ALLVFILES := LibTactics.v Helper.v DirectedList.v TM.v Compute.v Flip.v Permute.v DirectedCompute.v Subtape.v \
	Cyclers.v TranslatedCyclers.v BackwardsReasoning.v Bouncers.v Individual.v \
	BB52.v Individual52.v FixedBin.v ShiftOverflow.v Skelet10.v Skelet15.v Skelet17.v Skelet26.v Skelet33.v Skelet34.v Skelet35.v Skelet1.v Extraction.v \
	BB33.v Individual33.v

all: check verify skelet1

Makefile.coq: Makefile $(ALLVFILES)
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

check: Makefile.coq
	$(MAKE) -f Makefile.coq

%.vo: %.v Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) extraction.ml extraction.mli skelet1.mli skelet1.ml *.cmi *.cmx *.o verify skelet1

verify: extraction.mli extraction.ml main.ml
	ocamlopt.opt -o $@ $^

skelet1: skelet1.mli skelet1.ml skelet1_main.ml
	ocamlopt -o $@ $^

extraction.mli extraction.ml: Extraction.vo
skelet1.mli skelet1.ml: Skelet1.vo

-include Makefile.coq

.PHONY: build clean
