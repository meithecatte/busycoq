(** * Flip: swapping left and right *)

From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lia.
From BusyCoq Require Export Compute.
Set Default Goal Selector "!".

Module Flip (Ctx : Ctx).
  Module Compute := Compute Ctx. Export Compute.

Definition flip_dir (d : dir) :=
  match d with
  | L => R
  | R => L
  end.

Definition flip_tape (t : tape) :=
  match t with
  | l {{s}} r => r {{s}} l
  end.

Definition flip (tm : TM) : TM := fun qs =>
  match tm qs with
  | Some (s, d, q) => Some (s, flip_dir d, q)
  | None => None
  end.

Lemma flip_involutive : forall tm,
  flip (flip tm) = tm.
Proof.
  intros tm. apply functional_extensionality.
  intros [q s]. unfold flip.
  destruct (tm (q, s)) as [[[s' []] q'] |]; reflexivity.
Qed.

Definition flip_conf (c : Q * tape) : Q * tape :=
  match c with
  | q;; t => q;; flip_tape t
  end.

Lemma flip_conf_involutive : forall c,
  flip_conf (flip_conf c) = c.
Proof.
  intros [q [[l s] r]]. reflexivity.
Qed.

Lemma flip_step : forall tm c c',
  c -[ tm ]-> c' ->
  flip_conf c -[ flip tm ]-> flip_conf c'.
Proof.
  introv H.
  inverts H as E.
  - simpl. apply step_right.
    unfold flip. rewrite E. reflexivity.
  - simpl. apply step_left.
    unfold flip. rewrite E. reflexivity.
Qed.

Lemma flip_multistep : forall tm n c c',
  c -[ tm ]->> n / c' ->
  flip_conf c -[ flip tm ]->> n / flip_conf c'.
Proof.
  induction n; introv H; inverts H as Hstep Hrest.
  - apply multistep_0.
  - eauto using flip_step, multistep_S.
Qed.

Lemma flip_halting : forall tm c,
  halting tm c -> halting (flip tm) (flip_conf c).
Proof.
  intros tm [q [[l s] r]].
  unfold halting, flip. simpl.
  intros H. rewrite H.
  reflexivity.
Qed.

Lemma flip_halts_in : forall tm c n,
  halts_in tm c n -> halts_in (flip tm) (flip_conf c) n.
Proof.
  introv H.
  destruct H as [ch [Hexec Hhalting]].
  apply flip_multistep in Hexec.
  apply flip_halting in Hhalting.
  eexists. split; eassumption.
Qed.

Lemma flip_halts : forall tm c,
  halts tm c -> halts (flip tm) (flip_conf c).
Proof.
  introv H. destruct H as [n H].
  exists n. apply flip_halts_in. assumption.
Qed.

Lemma flip_halts_iff : forall tm c,
  halts tm c <-> halts (flip tm) (flip_conf c).
Proof.
  introv. split.
  - apply flip_halts.
  - intros H. apply flip_halts in H.
    rewrite flip_involutive, flip_conf_involutive in H.
    exact H.
Qed.

Lemma flip_c0 : flip_conf c0 = c0.
Proof. reflexivity. Qed.

End Flip.
