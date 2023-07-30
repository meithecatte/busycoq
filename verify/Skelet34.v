(** * Skelet #34 *)

(** Following https://www.sligocki.com/2023/02/02/skelet-34.html *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import List. Import ListNotations.
From Coq Require Import PArith.BinPos.
From Coq Require Import NArith.BinNat.
From BusyCoq Require Import Extraction. Import ETranslatedCyclers.
Set Default Goal Selector "!".

Notation "0" := S0.
Notation "1" := S1.
Notation side := (Stream sym).

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, C)
  | B, 0 => Some (0, R, C)  | B, 1 => Some (0, R, B)
  | C, 0 => Some (1, L, D)  | C, 1 => Some (0, L, A)
  | D, 0 => Some (1, L, E)  | D, 1 => None
  | E, 0 => Some (1, L, A)  | E, 1 => Some (1, R, A)
  end.

(** Trivial lemmas, but [simpl] in these situations leaves a mess. *)
Lemma move_left_const : forall s0 s r,
  move_left (const s0 {{s}} r) = const s0 {{s0}} s >> r.
Proof. reflexivity. Qed.

Lemma move_right_const : forall l s s0,
  move_right (l {{s}} const s0) = l << s {{s0}} const s0.
Proof. reflexivity. Qed.

(** [assumption] and [eassumption] both refuse to instantiate [forall]s. *)

Ltac apply_assumption :=
  match goal with
  | H: _ |- _ => apply H
  end.

Ltac prove_step_left := apply step_left; reflexivity.
Ltac prove_step_right := apply step_right; reflexivity.
Ltac prove_step := prove_step_left || prove_step_right.
Ltac simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  simpl.
Ltac step := eapply evstep_step; [prove_step | simpl_tape].
Ltac execute := repeat step; try apply evstep_refl.
Ltac follow_assm := eapply evstep_trans; [apply_assumption; assumption |].
Ltac follow_hyp H := eapply evstep_trans; [apply H; assumption |].

Tactic Notation "follow" := follow_assm.
Tactic Notation "follow" constr(H) := follow_hyp H.

Ltac triv := introv; repeat (step || follow); try apply evstep_refl.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "l <{{ q }} r" := (q;; tl l {{hd l}} r)  (at level 30, q at next level).
Notation "l {{ q }}> r" := (q;; l {{hd r}} tl r)  (at level 30, q at next level).

Fixpoint L (n : positive) : side :=
  match n with
  | xH => const 0 << 1 << 0 << 0 << 0
  | xO n => L n << 0 << 0 << 0 << 0
  | xI n => L n << 1 << 0 << 0 << 0
  end.

Fixpoint R (n : positive) : side :=
  match n with
  | xH => 1 >> 1 >> const 0
  | xO n => 1 >> 0 >> R n
  | xI n => 1 >> 1 >> R n
  end.

Definition counter (n m : positive) : Q * tape :=
  L n <{{C}} 1 >> 0 >> 1 >> 0 >> R m.

Lemma left_inc : forall n r,
  L n <{{C}} r -->* L (Pos.succ n) {{B}}> r.
Proof.
  induction n; triv.
Qed.

Inductive has0 : positive -> Prop :=
  | has0_0 n: has0 (n~0)
  | has0_1 n: has0 n -> has0 (n~1).

Inductive all1 : positive -> Prop :=
  | all1_H:   all1 1
  | all1_1 n: all1 n -> all1 (n~1).

Lemma right_inc_has0 : forall n l,
  has0 n ->
  l << 0 {{C}}> R n -->* l <{{A}} 0 >> R (Pos.succ n).
Proof.
  introv H. generalize dependent l. induction H; triv.
Qed.

Corollary counter_inc : forall n m,
  has0 m ->
  counter n m -->* counter (Pos.succ n) (Pos.succ m).
Proof.
  introv H. unfold counter.
  follow left_inc. execute.
  follow right_inc_has0. execute.
Qed.
