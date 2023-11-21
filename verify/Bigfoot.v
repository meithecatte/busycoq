(** * Bigfoot *)

From Coq Require Import PeanoNat. Import Nat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From BusyCoq Require Import Individual33. Import Individual33.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (2, R, A)  | A, 2 => Some (1, L, C)
  | B, 0 => Some (2, L, C)  | B, 1 => Some (1, R, B)  | B, 2 => Some (2, R, B)
  | C, 0 => None            | C, 1 => Some (2, L, A)  | C, 2 => Some (1, L, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "12" := (fun x => x << 1 << 2).
Notation "21" := (fun x => x << 2 << 1).
Notation "11" := (fun x => x << 1 << 1).
Notation "22" := (fun x => x << 2 << 2).

Definition T (a b c : nat) :=
  const 0 <: repeat a 12 <: repeat b 11 <{{A}} repeat c 11 :> const 0.

Lemma goright_A : forall n l r,
  l {{A}}> repeat n 11 :> r -->* l <: repeat n 22 {{A}}> r.
Proof.
  induction n; triv.
  rewrite (repeat_shift 22). finish.
Qed.

Lemma goright_B : forall n l r,
  l {{B}}> repeat n 11 :> r -->* l <: repeat n 11 {{B}}> r.
Proof.
  induction n; triv.
  rewrite (repeat_shift 11). finish.
Qed.

Lemma goleft_A : forall n l r,
  l <: repeat n 22 <{{A}} r -->* l <{{A}} repeat n 11 r.
Proof.
  induction n; triv.
  rewrite (repeat_shift 11). finish.
Qed.

Lemma goleft_C : forall n l r,
  l <: repeat n 22 <{{C}} r -->* l <{{C}} repeat n 11 r.
Proof.
  induction n; triv.
  rewrite (repeat_shift 11). finish.
Qed.

Lemma modstep : forall n l,
  l <: repeat 6 11 <{{A}} repeat n 11 :> const 0 -->*
  l <{{A}} repeat (n + 8) 11 :> const 0.
Proof.
  intros.
  repeat (execute; follow goright_A; execute;
    (follow goleft_A || follow goleft_C)).
  execute. finish.
  repeat rewrite <- (repeat_shift 11).
  rewrite add_comm. reflexivity.
Qed.

Lemma eat_mod : forall k n l,
  l <: repeat (k * 6) 11 <{{A}} repeat n 11 :> const 0 -->*
  l <{{A}} repeat (k * 8 + n) 11 :> const 0.
Proof.
  induction k.
  - triv.
  - intros. simpl repeat at 1.
    follow modstep. triv.
Qed.

(** XXX: notation abuse. 12 is defined with <:, but we use it on the RHS
    to mean 21 *)
Lemma goleft_12: forall n l r,
  l <: repeat n 12 <{{A}} r -->* l <{{A}} repeat n 12 :> r.
Proof.
  induction n; triv.
  rewrite (repeat_shift 12). finish.
Qed.

Lemma goright_12 : forall n l r,
  l {{B}}> repeat n 12 :> r -->* l <: repeat n 21 {{B}}> r.
Proof.
  induction n; triv.
  rewrite (repeat_shift 21). finish.
Qed.

Lemma align_12 : forall n l,
  l << 1 <: repeat n 21 = l <: repeat n 12 << 1.
Proof.
  induction n; intros.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma align_11 : forall n l,
  l << 1 <: repeat n 11 = l <: repeat n 11 << 1.
Proof.
  induction n; intros.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma bounce_left : forall n r,
  const 0 <: repeat n 12 <{{A}} r -->*
  const 0 <: repeat n 12 << 1 {{B}}> r.
Proof.
  intros.
  follow goleft_12. execute.
  follow goright_12. rewrite align_12.
  finish.
Qed.

Lemma T0: forall a k c',
  T a (k * 6) (S c') -->+ T a (k * 8 + c') 2.
Proof.
  intros. unfold T.
  follow eat_mod. follow bounce_left.

  follow goright_B. rewrite align_11, add_succ_r. execute.
Qed.

Lemma T1: forall a k c',
  T a (k * 6 + 1) (S c') -->+ T (S a) (k * 8 + c') 3.
Proof.
  intros. unfold T.
  rewrite repeat_add. follow eat_mod.
  execute.

  follow goright_A. execute. follow goleft_A. execute.
  follow bounce_left. execute.
  follow goright_B. rewrite align_11, add_succ_r. execute.
Qed.

Lemma T2: forall a k c,
  T (S a) (k * 6 + 2) c -->+ T a (k * 8 + c + 3) 2.
Proof.
  intros. unfold T.
  rewrite repeat_add. follow eat_mod. start_progress.

  follow goright_A. execute. follow goleft_A. execute.
  follow goright_A. execute. follow goleft_C. execute.
  follow goright_A. execute. follow goleft_A. execute.
  follow bounce_left. execute.

  follow goright_B. rewrite align_11. execute. finish.
  rewrite (repeat_add _ _ 3). reflexivity.
Qed.

Lemma T3: forall a k c,
  T a (k * 6 + 3) c -->+ T a (k * 8 + c + 1) 5.
Proof.
  intros. unfold T.

