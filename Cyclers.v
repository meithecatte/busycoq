(** * Cyclers *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From BusyCoq Require Import LibTactics.
From BusyCoq Require Import TM.
Set Default Goal Selector "!".

Section TMs.
  Context {Q Sym : Type}.

  Notation TM := (TM Q Sym).
  Notation tape := (tape Sym).

Lemma eventually_exceeds :
  forall a d h, d > 0 ->
  exists k, a + k * d > h.
Proof.
  introv H.
  induction h.
  - exists 1. lia.
  - destruct IHh as [k IH].
    exists (S k). lia.
Qed.

Lemma cycle_chain :
  forall (tm : TM) c n k,
  c -[ tm ]->* k / c ->
  c -[ tm ]->* (n * k) / c.
Proof.
  introv H.
  induction n.
  - apply multistep_0.
  - simpl. eapply multistep_trans; eassumption.
Qed.

Lemma cycle_nonhalting :
  forall (tm : TM) c0 c1 n k,
  k > 0 ->
  c0 -[ tm ]->* n / c1 ->
  c1 -[ tm ]->* k / c1 ->
  ~ halts tm c0.
Proof.
  introv Hgt0 Hn Hk [h [ch [Hh Hhalting]]].
  destruct (eventually_exceeds n k h Hgt0) as [r Hr].
  assert (Hreach : c0 -[ tm ]->* (n + r * k) / c1).
  { eapply multistep_trans.
    - exact Hn.
    - apply cycle_chain. exact Hk. }
  assert (Hsplit : exists w, w > 0 /\ h + w = n + r * k).
  { exists (n + r * k - h). lia. }
  destruct Hsplit as [w [Hwgt0 Ehw]].
  rewrite <- Ehw in Hreach.
  apply rewind_split in Hreach.
  destruct Hreach as [ch' [Hh' Hw]].
  assert (Ech' : ch = ch').
  { eapply multistep_deterministic; eassumption. }
  rewrite <- Ech' in Hw.
  eapply halting_no_multistep in Hhalting.
  - apply Hhalting in Hw. contradiction.
  - assumption.
Qed.

End TMs.
