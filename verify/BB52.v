(** * Instantiating the development to machines with 5 states and 2 symbols *)

From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Inductive state := A | B | C | D | E.
Inductive sym := S0 | S1.

Module BB52 <: Ctx.
  Definition Q := state.
  Definition Sym := sym.
  Definition q0 := A.
  Definition s0 := S0.

  Definition eqb_q (a b : Q): {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition eqb_sym (a b : Sym): {a = b} + {a <> b}.
    decide equality.
  Defined.

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
End BB52.
