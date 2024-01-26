(** * DirectedList: Lists that have a notion of direction. *)

(**
 * We want to represent the two sides of a Turing machine's tape as lists,
 * with the first element being the one closest to the machine head. This
 * yields a nice formulation, with one issue: the first element will always get
 * printed first by Coq.

 * With some notation hacks, it would be possible to at least have Coq
 * understand us when we write a list "backwards", but there's no way to have
 * it use the direction we'd like in its responses – trust me, I've tried it
 * all.

 * The solution is to have the left and right side of the tape be separate
 * types, even if only differing by an irrelevant type parameter. *)

From Coq Require Import JMeq.
From Coq Require Import List. Import ListNotations.
From BusyCoq Require Export Helper.
Set Default Goal Selector "!".

Infix "==" := JMeq (at level 70, no associativity).

Inductive dir : Type := L | R.

Definition flip_dir (d : dir) :=
  match d with
  | L => R
  | R => L
  end.

Lemma flip_dir_involutive : forall d,
  flip_dir (flip_dir d) = d.
Proof. intros []; reflexivity. Qed.

Inductive dlist (A : Type) (d : dir) : Type :=
  | dnil : dlist A d
  | dcons : A -> dlist A d -> dlist A d.
Arguments dnil {A} {d}.
Arguments dcons {A} {d}.

(* [dlist A L] grows to the left, so the head of the list is on the right.
 * Likewise, [dlist A R] grows to the right, so the head of the list is on
 * the left. *)

Notation "xs <: x" := (@dcons _ L x xs) (at level 61, left associativity).
Notation "x :> xs" := (@dcons _ R x xs) (at level 60, right associativity).
Notation "< [ ]" := (@dnil _ L) (format "< [ ]").
Notation "[ ] >" := (@dnil _ R) (format "[ ] >").

Notation "< [ x ; .. ; y ]" := (dcons y .. (dcons x <[]) ..)
  (format "< [ '[' x ;  '/' .. ;  '/' z ']' ]").
Notation "[ x ; .. ; y ] >" := (dcons x .. (dcons y []>) ..)
  (format "[ '[' x ;  '/' .. ;  '/' z ']' ] >").

Fixpoint to_dlist {A} {d} (xs : list A) : dlist A d :=
  match xs with
  | [] => dnil
  | x :: xs => dcons x (to_dlist xs)
  end.

Fixpoint dflip {A} {d} (xs : dlist A d) : dlist A (flip_dir d) :=
  match xs with
  | dnil => dnil
  | dcons x xs => dcons x (dflip xs)
  end.

Lemma dflip_involutive : forall {A} d (xs : dlist A d),
  dflip (dflip xs) == xs.
Proof.
  destruct d; simpl flip_dir; induction xs; simpl; try rewrite IHxs; auto.
Qed.

Lemma dflip_to_dlist : forall A d (xs : list A),
  @dflip _ d (to_dlist xs) = to_dlist xs.
Proof.
  induction xs; simpl; congruence.
Qed.

Fixpoint app {A} {d} (xs ys : dlist A d) : dlist A d :=
  match xs with
  | dnil => ys
  | dcons x xs => dcons x (app xs ys)
  end.

Notation "ys <+ xs" := (@app _ L xs ys) (at level 61, left associativity).
Notation "xs +> ys" := (@app _ R xs ys) (at level 60, right associativity).

Definition tl {A} {d} (xs : dlist A d) : dlist A d :=
  match xs with
  | dnil => dnil
  | dcons x xs => xs
  end.

Fixpoint drepeat {A} {d} (x : A) (n : nat) : dlist A d :=
  match n with
  | O => dnil
  | S n => dcons x (drepeat x n)
  end.

Lemma to_dlist_repeat : forall A d (x : A) n,
  @to_dlist _ d (repeat x n) = drepeat x n.
Proof.
  induction n; simpl; congruence.
Qed.

Fixpoint dfirstn {A} {d} (n : nat) (xs : dlist A d) : dlist A d :=
  match n with
  | O => dnil
  | S n =>
    match xs with
    | dnil => dnil
    | dcons x xs => dcons x (dfirstn n xs)
    end
  end.

Arguments dfirstn : simpl nomatch.

Lemma dfirstn_less : forall n k A d (xs ys : dlist A d),
  dfirstn (n + k) xs = dfirstn (n + k) ys ->
  dfirstn n xs = dfirstn n ys.
Proof.
  induction n; introv H.
  - reflexivity.
  - destruct xs as [| x xs]; destruct ys as [| y ys];
    simpl in H; try (discriminate || reflexivity).
    simpl. inverts H as H. apply IHn in H.
    congruence.
Qed.

#[export] Hint Resolve dfirstn_less : core.
