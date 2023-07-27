COQMFFLAGS := -Q . BusyCoq

ALLVFILES := LibTactics.v Helper.v TM.v Cyclers.v Compute.v

all: build verify

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) cyclers.ml cyclers.mli verify

verify: cyclers.mli cyclers.ml main.ml
	ocamlopt.opt -o $@ $^

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
