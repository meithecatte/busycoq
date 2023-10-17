(** * Extraction to OCaml *)

From Coq Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.
From BusyCoq Require Export BB52 Cyclers TranslatedCyclers BackwardsReasoning Bouncers.

Module ECyclers := Cyclers BB52.
Module ETranslatedCyclers := TranslatedCyclers BB52.
Module EBackwardsReasoning := BackwardsReasoning BB52.
Module EBouncers := Bouncers BB52.

Extraction Language OCaml.
Extraction "extraction.ml" nat_of_int
  ECyclers.verify_cycler
  ETranslatedCyclers.verify_tcycler
  EBackwardsReasoning.verify_backwards
  EBouncers.verify_bouncer.
