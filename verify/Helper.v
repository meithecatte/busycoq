(** * Various generic lemmas that aren't present in the standard library *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
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

(** We define our own [reflect] in [Prop] instead of [Set],
    as we don't want it to occur in the extracted programs. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

#[global]
Hint Constructors reflect : bool.

Lemma reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  introv H. destruct H; intuition.
Qed.

Lemma iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  destr_bool; intuition.
Qed.

Lemma reflect_sym : forall A (x y : A) b,
  reflect (x = y) b -> reflect (y = x) b.
Proof.
  introv H. destruct H; intuition.
Qed.

Lemma reflect_andb : forall P Q p q,
  reflect P p ->
  reflect Q q ->
  reflect (P /\ Q) (p && q).
Proof.
  introv H1 H2. destruct H1, H2; constructor; intuition.
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

Fixpoint Str_app {A} (xs : list A) (ys : Stream A) : Stream A :=
  match xs with
  | [] => ys
  | x :: xs => Cons x (Str_app xs ys)
  end.

Lemma strong_induction : forall (P : nat -> Prop),
  (forall n, (forall k, k < n -> P k) -> P n) ->
  forall n, P n.
Proof.
  introv H. introv.
  enough (H' : forall k, k <= n -> P k).
  { apply H'. constructor. }
  induction n; introv G.
  - inverts G. apply H. introv G. inverts G.
  - inverts G.
    + apply H. introv G. apply IHn. lia.
    + auto.
Qed.
