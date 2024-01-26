(** * Subtape: computing the behavior on a segment of the tape *)

From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export DirectedCompute.
Set Default Goal Selector "!".

Module Subtape (Ctx : Ctx).
  Module DirectedCompute := DirectedCompute Ctx. Export DirectedCompute.

(** We use the directional formulation here, so that
    "the tape just got outside the segment" is easy to represent. *)
Notation subtape := (dir * list Sym * list Sym)%type.

Notation subconf := (Q * subtape)%type.

Definition sublift (c : subtape) (ll rr : list Sym) : dtape :=
  match c with
  | (d, l, r) => (d, l ++ ll, r ++ rr)
  end.

Definition substep_at (tm : TM) (q : Q) (s : Sym) (l r : list Sym)
    : option subconf :=
  match tm (q, s) with
  | Some (s', L, q') => Some (q';; (L, l, s' :: r))
  | Some (s', R, q') => Some (q';; (R, s' :: l, r))
  | None => None
  end.

Lemma undir_left : forall l s r, undir (L, l, s :: r) = move_left (l {{s}} r).
Proof. destruct l; reflexivity. Qed.

Lemma undir_right : forall l s r, undir (R, s :: l, r) = move_right (l {{s}} r).
Proof. destruct l; reflexivity. Qed.

Lemma step_left_lift : forall tm q q' s s' l r,
  tm (q, s) = Some (s', L, q') ->
  lift (q;; l {{s}} r) -[ tm ]-> lift (q';; left (l {{s'}} r)).
Proof.
  introv H.
  unfold lift. rewrite lift_left.
  exact (step_left H).
Qed.

Lemma step_right_lift : forall tm q q' s s' l r,
  tm (q, s) = Some (s', R, q') ->
  lift (q;; l {{s}} r) -[ tm ]-> lift (q';; right (l {{s'}} r)).
Proof.
  introv H.
  unfold lift. rewrite lift_right.
  exact (step_right H).
Qed.

Lemma substep_at_some : forall tm q s l r q' t' ll rr,
  substep_at tm q s l r = Some (q';; t') ->
  lift (q;; (l ++ ll) {{s}} (r ++ rr)) -[ tm ]->
    lift (q';; undir (sublift t' ll rr)).
Proof.
  introv H. unfold substep_at in H.
  destruct (tm (q, s)) as [[[s' []] q''] |] eqn:Etm; inverts H;
   unfold sublift; simpl app.
  - rewrite undir_left. apply step_left_lift. assumption.
  - rewrite undir_right. apply step_right_lift. assumption.
Qed.

Definition substep (tm : TM) (c : subconf) : option subconf :=
  match c with
  | q;; (L, l, r) =>
    match l with
    | s :: l => substep_at tm q s l r
    | [] => None
    end
  | q;; (R, l, r) =>
    match r with
    | s :: r => substep_at tm q s l r
    | [] => None
    end
  end.

Arguments substep : simpl never.

Lemma substep_some : forall tm q q' t t' ll rr,
  substep tm (q, t) = Some (q', t') ->
  lift (q;; undir (sublift t ll rr)) -[ tm ]->
    lift (q';; undir (sublift t' ll rr)).
Proof with try discriminate; apply substep_at_some; assumption.
  introv H. destruct t as [[[] l] r]; simpl in H.
  - destruct l...
  - destruct r...
Qed.

Local Hint Resolve substep_some : core.

Fixpoint submultistep (tm : TM) (n : nat) (c : subconf) : option subconf :=
  match n with
  | 0 => Some c
  | S n =>
    match substep tm c with
    | Some c' => submultistep tm n c'
    | None => None
    end
  end.

Lemma submultistep_some : forall tm n q q' t t' ll rr,
  submultistep tm n (q, t) = Some (q', t') ->
  lift (q;; undir (sublift t ll rr)) -[ tm ]->>
    n / lift (q';; undir (sublift t' ll rr)).
Proof.
  induction n; introv H.
  - inverts H. auto.
  - simpl in H. destruct (substep tm (q, t)) as [[] |] eqn:E; try discriminate.
    eauto.
Qed.

End Subtape.
