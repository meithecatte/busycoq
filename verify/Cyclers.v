(** * Cyclers *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.
From BusyCoq Require Import Helper.
From BusyCoq Require Import TM.
From BusyCoq Require Import Compute.
Set Default Goal Selector "!".

Section TMs.
  Context {Q Sym : Type}.
  Variable q0 : Q.
  Variable s0 : Sym.

  Variable eqb_sym : Sym -> Sym -> bool.
  Variable eqb_sym_spec : forall a b, reflect (a = b) (eqb_sym a b).

  Variable eqb_q : Q -> Q -> bool.
  Variable eqb_q_spec : forall a b, reflect (a = b) (eqb_q a b).

  Notation TM := (TM Q Sym).
  Notation tape := (tape Sym).
  Notation ctape := (ctape Sym).
  Notation c0 := (c0 q0 s0).
  Notation starting := (starting q0 s0).
  Notation cmultistep := (cmultistep s0).
  Notation eqb := (eqb s0 eqb_sym eqb_q).
  Notation lift := (lift s0).

Definition verify_cycler (tm : TM) (n k : nat) : bool :=
  match cmultistep tm n starting with
  | Some c =>
    match cmultistep tm k c with
    | Some c' => (0 <? k) && eqb c c'
    | None => false
    end
  | None => false
  end.

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
  forall (tm : TM) c1 c2 n k,
  k > 0 ->
  c1 -[ tm ]->* n / c2 ->
  c2 -[ tm ]->* k / c2 ->
  ~ halts tm c1.
Proof.
  introv Hgt0 Hn Hk [h [ch [Hh Hhalting]]].
  destruct (eventually_exceeds n k h Hgt0) as [r Hr].
  assert (Hreach : c1 -[ tm ]->* (n + r * k) / c2).
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

Theorem verify_cycler_correct : forall tm n k,
  verify_cycler tm n k = true -> ~ halts tm c0.
Proof.
  introv H. unfold verify_cycler in H.
  destruct (cmultistep tm n starting) as [c |] eqn:E; try discriminate.
  destruct (cmultistep tm k c) as [c' |] eqn:E'; try discriminate.
  rewrite andb_true_iff, Nat.ltb_lt in H. destruct H as [Hgt0 H].
  assert (Hs : reflect (lift c = lift c') (eqb c c'))
    by (apply eqb_spec; assumption).
  inverts Hs as Elift Eeqb; try congruence.

  apply cmultistep_some in E, E'.
  rewrite lift_starting in E.
  rewrite <- Elift in E'.
  eapply cycle_nonhalting; eassumption.
Qed.

End TMs.

Extraction Language OCaml.
Extraction "cyclers.ml" verify_cycler nat_of_int.
