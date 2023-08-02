(** * Various generic lemmas that aren't present in the standard library *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
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

Lemma N_strong_induction : forall (P : N -> Prop),
  (forall n, (forall k, (k < n)%N -> P k) -> P n) ->
  forall n, P n.
Proof.
  introv H.
  assert (G: forall n : nat, P (N.of_nat n)).
  { induction n using strong_induction.
    apply H. introv G.
    replace k with (N.of_nat (N.to_nat k))
      by apply N2Nat.id.
    apply H0. lia. }
  introv.
  replace n with (N.of_nat (N.to_nat n))
    by apply N2Nat.id.
  apply G.
Qed.

Definition het_add (a : N) (b : positive) : positive :=
  match a with
  | N0 => b
  | Npos a => a + b
  end.

Notation "a :+ b" := (het_add a b)  (at level 50, left associativity).

Lemma het_add_succ : forall a b, N.succ a :+ b = a :+ Pos.succ b.
Proof.
  introv. destruct a; unfold ":+", N.succ; lia.
Qed.

Lemma het_add_succ_l : forall a b, N.succ a :+ b = Pos.succ (a :+ b).
Proof.
  introv. destruct a; unfold ":+", N.succ; lia.
Qed.

Lemma pos_het_add : forall a b, (N.pos (a :+ b) = a + N.pos b)%N.
Proof.
  introv. destruct a; unfold ":+"; lia.
Qed.

Fixpoint pow2' (k : nat) : positive :=
  match k with
  | O => 1
  | S k => (pow2' k)~0
  end.

Definition pow2 (k : nat) : N := Npos (pow2' k).

Arguments pow2 _ : simpl never.

Lemma pow2_S : forall k,
  pow2 (S k) = N.double (pow2 k).
Proof. introv. unfold pow2. simpl. lia. Qed.

Lemma pow2_gt0 : forall k, (pow2 k > 0)%N.
Proof. unfold pow2. lia. Qed.
