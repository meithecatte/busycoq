(** * Skelet #17 *)

From BusyCoq Require Import Individual52.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From Coq Require Import PeanoNat.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => None
  | B, 0 => Some (0, L, C)  | B, 1 => Some (1, R, E)
  | C, 0 => Some (0, L, D)  | C, 1 => Some (1, L, C)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, L, B)
  | E, 0 => Some (0, R, B)  | E, 1 => Some (0, R, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Fixpoint left10 (n : nat) (l : side) : side :=
  match n with
  | O => l
  | S n => left10 n l << 1 << 0
  end.

Fixpoint right10 (n : nat) (r : side) : side :=
  match n with
  | O => r
  | S n => 1 >> 0 >> right10 n r
  end.

(* list representation: the list starts with the element
 * closest to the tape head *)
Fixpoint lower (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | [x] => left10 x (const 0)
  | x::xs => left10 x (lower xs << 1)
  end.

Fixpoint lowerR (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | [x] => right10 x (const 0)
  | x::xs => right10 x (1 >> lowerR xs)
  end.

Arguments lower : simpl nomatch.
Arguments lowerR : simpl nomatch.

Lemma shift_left10 : forall n l,
  left10 n (l << 1 << 0) = left10 n l << 1 << 0.
Proof.
  induction n.
  - auto.
  - introv. simpl. rewrite IHn. reflexivity.
Qed.

Lemma fold_left10 : forall n l,
  left10 n l << 1 << 0 = left10 (S n) l.
Proof. reflexivity. Qed.

Lemma add_left10 : forall a b l,
  left10 a (left10 b l) = left10 (a + b) l.
Proof.
  induction a; introv.
  - reflexivity.
  - simpl. repeat rewrite <- shift_left10.
    rewrite IHa. reflexivity.
Qed.

Lemma shift_right10 : forall n r,
  right10 n (1 >> 0 >> r) = 1 >> 0 >> right10 n r.
Proof.
  induction n.
  - auto.
  - introv. simpl. rewrite IHn. reflexivity.
Qed.

Lemma goright_10 : forall n l r,
  l |> right10 n r -->* left10 n l |> r.
Proof.
  induction n.
  - triv.
  - execute. follow IHn.
    rewrite shift_left10. finish.
Qed.

Lemma even10_left : forall n l r,
  left10 (n + n) l <| r -->* l <| right10 (n + n) r.
Proof.
  induction n.
  - triv.
  - execute.
    rewrite <- plus_n_Sm. execute.
    follow IHn.
    repeat rewrite shift_right10. finish.
Qed.

Lemma lower_merge : forall x y ys,
  left10 x (lower (y :: ys)) = lower (x + y :: ys).
Proof.
  introv.
  destruct ys as [| y0 ys]; simpl; apply add_left10.
Qed.

Lemma lowerR_succ : forall x xs,
  lowerR (S x :: xs) = 1 >> 0 >> lowerR (x :: xs).
Proof.
  intros x [| x' xs]; reflexivity.
Qed.

Lemma goright_nonzero : forall xs x x' y ys,
  Forall (fun n => n <> O) xs ->
  lower (y :: ys) |> lowerR (x :: xs ++ [S x']) -->*
  lower (x' :: rev xs ++ (S x + y) :: ys) |> const 0.
Proof.
  induction xs; introv Hxs.
  - simpl lowerR. follow goright_10. execute.
    follow goright_10.
    finish. repeat f_equal.
    rewrite fold_left10, lower_merge.
    reflexivity.
  - inverts Hxs as Ha Hxs.
    destruct a as [| a]. { congruence. }
    simpl lowerR. follow goright_10.
    simpl lowerR. rewrite lowerR_succ. execute.
    rewrite fold_left10, lower_merge.
    change (lower (S x + y :: ys) << 1)
      with (lower (O :: S x + y :: ys)).
    follow IHxs.
    rewrite <- plus_n_O, <- app_assoc. finish.
Qed.
