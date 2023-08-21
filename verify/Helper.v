(** * Various generic lemmas that aren't present in the standard library *)

From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Lia.
From Coq Require Import ZifyClasses.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
From Coq Require Import ZArith.
From BusyCoq Require Export LibTactics.
Set Default Goal Selector "!".

(* sig *)
Notation "[: x :]" := (exist _ x _).

(* sumbool *)
Notation Yes := (left _ _).
Notation No := (right _ _).
Notation Reduce x := (if x then Yes else No).
Notation "a && b" := (if a then b else No).

(* sumor *)
Notation "!!" := (inright _).
Notation "[|| x ||]" := (inleft [: x :]).
Notation "'bind' x <- a ; b" := (match a with | [|| x ||] => b | !! => No end)
  (right associativity, at level 60, x pattern).
Notation "'bind' x <-- a ; b" := (match a with | [|| x ||] => b | !! => !! end)
  (right associativity, at level 60, x pattern).

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

Lemma het_add_Z : forall a b, Z.pos (a :+ b) = (Z.of_N a + Z.pos b)%Z.
Proof.
  introv. destruct a; unfold ":+"; lia.
Qed.

#[global] Instance Op_het_add : BinOp het_add :=
  { TBOp := Z.add; TBOpInj := het_add_Z }.
Add Zify BinOp Op_het_add.

Lemma het_add_succ_l : forall a b, N.succ a :+ b = Pos.succ (a :+ b).
Proof. lia. Qed.

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

Ltac Zify.zify_pre_hook ::=
  unfold pow2 in *; simpl pow2' in *.

Section StripPrefix.
  Variable A : Type.
  Variable eqb : forall (a b : A), {a = b} + {a <> b}.

Program Fixpoint strip_prefix (xs ys : list A) : {zs | ys = xs ++ zs} + {True} :=
  match xs, ys with
  | [], ys => [|| ys ||]
  | _, [] => !!
  | x :: xs, y :: ys =>
    if eqb x y then
      match strip_prefix xs ys with
      | [|| zs ||] => [|| zs ||]
      | !! => !!
      end
    else
      !!
  end.
End StripPrefix.

Arguments strip_prefix {A} eqb !xs !ys.
