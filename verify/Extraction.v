(** * Extraction to OCaml *)

From Coq Require Extraction.
From Coq Require Import Lists.List. Import ListNotations.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.
From BusyCoq Require Export BackwardsReasoning.

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

  Definition all_qs := [A; B; C; D; E].

  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.

  Definition all_syms := [S0; S1].

  Lemma all_syms_spec : forall a, In a all_syms.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.
End Ctx.

Module ECyclers := Cyclers Ctx.
Module ETranslatedCyclers := TranslatedCyclers Ctx.
Module EBackwardsReasoning := BackwardsReasoning Ctx.

Extraction Language OCaml.
Extraction "extraction.ml" nat_of_int
  ECyclers.verify_cycler
  ETranslatedCyclers.verify_tcycler
  EBackwardsReasoning.verify_backwards.
