(** * Extraction to OCaml *)

From Coq Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.
From BusyCoq Require Export TranslatedCyclers.

Inductive state := A | B | C | D | E.
Inductive sym := S0 | S1.

Module Ctx <: Ctx.
  Definition Q := state.
  Definition Sym := sym.
  Definition q0 := A.
  Definition s0 := S0.

  Definition eqb_q (a b : Q) :=
    match a, b with
    | A, A => true
    | B, B => true
    | C, C => true
    | D, D => true
    | E, E => true
    | _, _ => false
    end.

  Lemma eqb_q_spec : forall a b, reflect (a = b) (eqb_q a b).
  Proof.
    intros [] []; constructor; (reflexivity || discriminate).
  Qed.

  Definition eqb_sym (a b : Sym) :=
    match a, b with
    | S0, S0 => true
    | S1, S1 => true
    | _, _ => false
    end.

  Lemma eqb_sym_spec : forall a b, reflect (a = b) (eqb_sym a b).
  Proof.
    intros [] []; constructor; (reflexivity || discriminate).
  Qed.
End Ctx.

Module ECyclers := Cyclers Ctx.
Module ETranslatedCyclers := TranslatedCyclers Ctx.

Extraction Language OCaml.
Extraction "extraction.ml" nat_of_int
  ECyclers.verify_cycler
  ETranslatedCyclers.verify_tcycler.
