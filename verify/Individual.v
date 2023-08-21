(** * Utilities for proving individual machines *)

From Coq Require Export Lists.Streams.
From Coq Require Import Lia.
From BusyCoq Require Export Extraction. Export ECyclers.
Set Default Goal Selector "!".

Notation "0" := S0.
Notation "1" := S1.

(** Trivial lemmas, but [simpl] in these situations leaves a mess. *)
Lemma move_left_const : forall s0 s r,
  move_left (const s0 {{s}} r) = const s0 {{s0}} s >> r.
Proof. reflexivity. Qed.

Lemma move_right_const : forall l s s0,
  move_right (l {{s}} const s0) = l << s {{s0}} const s0.
Proof. reflexivity. Qed.

Lemma evstep_refl' : forall tm c c',
  c = c' ->
  c -[ tm ]->* c'.
Proof. intros. subst c'. auto. Qed.

Ltac lia_refl := solve [repeat (lia || f_equal)].

Ltac prove_step_left := apply @step_left; reflexivity.
Ltac prove_step_right := apply @step_right; reflexivity.
Ltac prove_step := prove_step_left || prove_step_right.
Ltac simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  simpl;
  try rewrite <- const_unfold.
Ltac finish_progress := apply progress_base; prove_step.
Ltac finish_evstep := apply evstep_refl'; try (reflexivity || lia_refl).
Ltac finish := finish_evstep || finish_progress.
Ltac step := (eapply evstep_step || eapply progress_step); [prove_step | simpl_tape].
Ltac execute := introv; repeat (try solve [finish]; step).
Ltac do_adjust H ty :=
  lazymatch ty with
  | _ -> ?ty => do_adjust H ty
  | ?c1 -[ _ ]->* _ =>
    lazymatch goal with
    | |- ?c2 -[ _ ]->* _ =>
      replace c2 with c1; [apply H | reflexivity || lia_refl]
    end
  end.

Ltac adjust H := let ty := type of H in do_adjust H ty.
Ltac adjusted H := apply H || adjust H.
Ltac follow_hyp H := eapply evstep_trans; [adjusted H; eauto |].
Ltac follow_assm :=
  match goal with
  | H: _ |- _ => follow_hyp H
  end.

Tactic Notation "follow" := follow_assm.
Tactic Notation "follow" constr(H) := follow_hyp H.

Ltac triv := intros; repeat (try solve [finish]; (step || follow)).

Notation "l <{{ q }} r" := (q;; tl l {{hd l}} r)  (at level 30, q at next level).
Notation "l {{ q }}> r" := (q;; l {{hd r}} tl r)  (at level 30, q at next level).
