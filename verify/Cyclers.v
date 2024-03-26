(** * Cyclers *)

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Program.Tactics.
From BusyCoq Require Export Permute.
Set Default Goal Selector "!".

Module Cyclers (Ctx : Ctx).
  Module Permute := Permute Ctx. Export Permute.

Lemma cycle_nonhalting :
  forall {tm : TM} {c c' k},
  c = c' ->
  c -[ tm ]->> S k / c' ->
  ~ halts tm c.
Proof.
  introv E Hgt0. subst c'.
  apply progress_nonhalt_simple with (C := fun (_: nat) => c);
    intros; subst; eauto.
Qed.

Local Obligation Tactic := simpl; intros; subst;
  eauto 3 using cycle_nonhalting, skip_halts.

Program Definition verify_cycler (tm : TM) (n k : nat) :
  {~ halts tm c0} + {True} :=
  bind c <- cmultistep tm n starting;
  bind c' <- cmultistep tm k c;
  match k with
  | 0 => No
  | S k => Reduce (eqb c c')
  end.

End Cyclers.
