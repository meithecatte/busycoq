(** * Things common to shift-overflow machines *)

(** This is mostly the [b] function, which expresses the distance to the
    next power of two. *)

From BusyCoq Require Import Helper.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
Set Default Goal Selector "!".

(** We use a definition of [b] shifted by 1 compared to the informal proof, i.e.
    we can do [n + b n] is the farthest we can go without reaching a new power
    of two. *)
Fixpoint b (n : positive) : N :=
  match n with
  | xH => N0
  | xO n' => N.succ_double (b n')
  | xI n' => N.double (b n')
  end.

Inductive has0 : positive -> Prop :=
  | has0_0 n: has0 (n~0)
  | has0_1 n: has0 n -> has0 (n~1).

#[export] Hint Constructors has0 : core.

Inductive all1 : positive -> Prop :=
  | all1_H:   all1 1
  | all1_1 n: all1 n -> all1 (n~1).

Lemma b0_all1 : forall n, b n = N0 -> all1 n.
Proof.
  induction n; introv H.
  - apply all1_1, IHn.
    simpl in H. lia.
  - simpl in H. lia.
  - apply all1_H.
Qed.

Lemma bn0_has0 : forall n, (b n > 0)%N -> has0 n.
Proof.
  induction n; introv H; simpl; simpl in H.
  - apply has0_1, IHn. lia.
  - apply has0_0.
  - lia.
Qed.

Lemma b_succ : forall n, (b n > 0)%N -> b (Pos.succ n) = N.pred (b n).
Proof. induction n; simpl; lia. Qed.

Lemma b_add : forall u n,
  (u <= b n -> b (u :+ n) = b n - u)%N.
Proof.
  apply (N.induction (fun u => forall n, u <= b n -> b (u :+ n) = b n - u)%N).
  - intuition.
  - introv H. simpl. lia.
  - intros u IH n H.
    rewrite het_add_succ_l, b_succ; rewrite IH; lia.
Qed.

Corollary b_add_self : forall n,
  b (b n :+ n) = 0%N.
Proof.
  introv. rewrite b_add; lia.
Qed.

Lemma b0_succ : forall n, b n = 0%N -> b (Pos.succ n) = (Npos n).
Proof.
  introv H. apply b0_all1 in H.
  induction H.
  - reflexivity.
  - simpl. rewrite IHall1. lia.
Qed.
