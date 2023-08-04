(** * Utilities for proving individual machines *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From BusyCoq Require Export Extraction. Export ETranslatedCyclers.
Set Default Goal Selector "!".

Notation "0" := S0.
Notation "1" := S1.
Notation side := (Stream sym).

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
  simpl;
  try rewrite <- const_unfold.
Ltac finish := apply evstep_refl.
Ltac step := eapply evstep_step; [prove_step | simpl_tape].
Ltac execute := repeat (try finish; step).
Ltac follow_assm := eapply evstep_trans; [apply_assumption; eauto |].
Ltac follow_hyp H := eapply evstep_trans; [apply H; eauto |].

Tactic Notation "follow" := follow_assm.
Tactic Notation "follow" constr(H) := follow_hyp H.

Ltac triv := introv; repeat (try finish; (step || follow)).

Notation "l <{{ q }} r" := (q;; tl l {{hd l}} r)  (at level 30, q at next level).
Notation "l {{ q }}> r" := (q;; l {{hd r}} tl r)  (at level 30, q at next level).
