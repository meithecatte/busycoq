(** * Various generic lemmas that aren't present in the standard library *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.
From Coq Require Import Lists.Streams.
From Coq Require Import Lia.
From BusyCoq Require Export LibTactics.
Set Default Goal Selector "!".

Lemma Cons_unfold : forall A (xs : Stream A),
  xs = Cons (hd xs) (tl xs).
Proof.
  introv. destruct xs. reflexivity.
Qed.

Lemma const_unfold : forall T (x : T),
  const x = Cons x (const x).
Proof.
  introv.
  rewrite Cons_unfold at 1.
  reflexivity.
Qed.

Lemma reflect_sym : forall A (x y : A) b,
  reflect (x = y) b -> reflect (y = x) b.
Proof.
  introv H. destruct H; constructor; congruence.
Qed.

Lemma eventually_exceeds :
  forall d h, d > 0 ->
  exists k, k * d > h.
Proof.
  introv H.
  induction h.
  - exists 1. lia.
  - destruct IHh as [k IH].
    exists (S k). lia.
Qed.
