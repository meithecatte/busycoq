(** * Skelet #17 *)

From BusyCoq Require Import Individual52.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From Coq Require Import PeanoNat. Import Nat.
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

(** ** Representing (10)^n *)

(* Perhaps it'd be wise to look into a better way of doing these kinds
    of manipulations at some point. Appending a list to a stream is
    a reasonable thing to do... *)

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

Lemma shift_left10 : forall n l,
  left10 n (l << 1 << 0) = left10 n l << 1 << 0.
Proof.
  induction n.
  - auto.
  - introv. simpl. rewrite IHn. reflexivity.
Qed.

Lemma fold_left10_r : forall n l,
  left10 n l << 1 << 0 = left10 (S n) l.
Proof. reflexivity. Qed.

Lemma fold_left10_l : forall n l,
  left10 n (l << 1 << 0) = left10 (S n) l.
Proof. exact shift_left10. Qed.

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

(** ** List-of-exponents representation *)

(* the list starts with the element closest to the tape head *)

(* Note: [lowerL'] and [lowerR'] assume a (10)^n term will get prepended, and
   thus emit the separator for it. This could be written without an auxiliary
   definition, but this form is much easier to state lemmas about. *)
Fixpoint lowerL' (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => left10 x (lowerL' xs) << 1
  end.

Definition lowerL (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => left10 x (lowerL' xs)
  end.

Fixpoint lowerR' (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => 1 >> right10 x (lowerR' xs)
  end.

Definition lowerR (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => right10 x (lowerR' xs)
  end.

Definition lower (xs : list nat) : Q * tape :=
  lowerL xs <| lowerR' [].

Lemma lowerL_merge : forall x y ys,
  left10 x (lowerL (y :: ys)) = lowerL (x + y :: ys).
Proof.
  introv.
  destruct ys as [| y0 ys]; simpl; apply add_left10.
Qed.

Lemma lowerL_nonempty : forall xs,
  xs <> [] ->
  lowerL' xs = lowerL xs << 1.
Proof.
  introv H.
  destruct xs; try congruence.
  reflexivity.
Qed.

Lemma fold_lowerL' : forall x xs,
  left10 x (lowerL' xs) << 1 = lowerL' (x :: xs).
Proof. reflexivity. Qed.

Lemma fold_lowerR' : forall x xs,
  1 >> right10 x (lowerR' xs) = lowerR' (x :: xs).
Proof. reflexivity. Qed.

Arguments lowerL : simpl never.
Arguments lowerL' : simpl never.
Arguments lowerR : simpl never.
Arguments lowerR' : simpl never.

(** Basic machine behavior *)

Lemma goright_10 : forall n l r,
  l |> right10 n r -->* left10 n l |> r.
Proof.
  induction n.
  - triv.
  - execute. follow IHn.
    rewrite shift_left10. finish.
Qed.

Lemma goleft_even10 : forall n l r,
  Even n ->
  left10 n l <| r -->* l <| right10 n r.
Proof.
  introv H. destruct H as [n' H]. rewrite H.
  simpl. rewrite <- plus_n_O. clear n H. rename n' into n.
  generalize dependent l. generalize dependent r.
  induction n.
  - triv.
  - execute.
    rewrite <- plus_n_Sm. execute.
    follow IHn.
    repeat rewrite shift_right10. finish.
Qed.

Lemma goleft_odd10 : forall n l r,
  Even n ->
  left10 (S n) (l << 1) <| r -->* left10 n (l << 1 << 0 << 1) |> r.
Proof.
  introv H.
  simpl left10. rewrite <- shift_left10.
  follow goleft_even10. execute.
  follow goright_10. finish.
Qed.

(** ** Higher-level behavior *)

Arguments left10 : simpl never.
Arguments right10 : simpl never.

Lemma goright_nonzero : forall xs x x' y ys,
  Forall (fun n => n <> O) xs ->
  lowerL (y :: ys) |> lowerR (x :: xs ++ [S x']) -->*
  lowerL (x' :: rev xs ++ (S x + y) :: ys) |> const 0.
Proof.
  induction xs; introv Hxs.
  - follow goright_10. execute.
    rewrite lowerL_merge.
    follow goright_10. finish.
  - inverts Hxs as Ha Hxs.
    destruct a as [| a]. { congruence. }
    follow goright_10. execute.
    rewrite fold_left10_r, lowerL_merge.
    change (lowerL (S x + y :: ys) << 1)
      with (lowerL (O :: S x + y :: ys)).
    follow IHxs.
    rewrite <- plus_n_O, <- app_assoc. finish.
Qed.

Lemma goright_nonzero' : forall xs x y ys,
  Forall (fun n => n <> O) xs ->
  lowerL (y :: ys) |> lowerR' (xs ++ [S x]) -->*
  lowerL (x :: rev xs ++ (S y) :: ys) |> const 0.
Proof.
  introv Hxs.
  apply goright_nonzero with (x := O). assumption.
Qed.

Lemma app_nonempty_r : forall A (xs ys : list A),
  ys <> [] -> xs ++ ys <> [].
Proof.
  introv H. destruct xs.
  - apply H.
  - discriminate.
Qed.

Lemma cons_nonempty : forall A (x : A) xs,
  x :: xs <> [].
Proof. discriminate. Qed.

#[export] Hint Resolve app_nonempty_r : core.
#[export] Hint Immediate cons_nonempty : core.

Lemma goleft_even : forall xs l r,
  Forall Even xs ->
  l <> [] ->
  lowerL (xs ++ l) <| lowerR' r -->*
  lowerL l <| lowerR' (rev xs ++ r).
Proof.
  induction xs as [| x xs]; introv Heven Hl.
  - finish.
  - inverts Heven as Hx Hxs.
    simpl lowerL. follow goleft_even10.
    rewrite lowerL_nonempty by auto. execute.
    rewrite fold_lowerR'. follow IHxs.
    rewrite <- app_assoc. finish.
Qed.

#[export] Hint Resolve -> Odd_succ : core.
#[export] Hint Resolve Forall_rev : core.

Lemma increment : forall x xs y z zs,
  Forall (fun n => n <> O) xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (S x :: xs ++ y :: z :: zs) -->*
  lower (x :: xs ++ y :: S z :: zs).
Proof.
  introv Hnonzero Heven Hx Hy.
  follow goleft_even10.
  rewrite lowerL_nonempty by auto. execute.
  rewrite fold_lowerR'.
  follow goleft_even.
  destruct y. { destruct Hy. lia. }
  unfold lowerL. unfold lowerL'. fold lowerL'.
  follow goleft_odd10. (* could get -->+ here *)
  rewrite fold_left10_r, fold_lowerL'.
  follow goright_nonzero'.
  rewrite rev_involutive. execute.
Qed.

Lemma increment_odd : forall x y xs,
  Odd (S x) ->
  lower (S x :: y :: xs) -->*
  lower (x :: S y :: xs).
Proof.
  introv Hx. follow goleft_odd10. execute.
Qed.

(* This corresponds to overflow followed by empty in Chris Xu's writeup.
   The config [lower (xs ++ [S y; O])] he lists isn't visited. *)
Lemma overflow : forall x xs y,
  Forall (fun n => n <> O) xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (S x :: xs ++ [y]) -->*
  lower (x :: xs ++ [S y; 1; 0; 0]%nat).
Proof.
  introv Hnonzero Heven Hx Hy.
  follow (goleft_even (S x :: xs)). rewrite app_nil_r.
  destruct y. { destruct Hy. lia. }
  unfold lowerL, lowerL'. rewrite <- fold_left10_l.
  follow goleft_even10. execute.

  change (const 0 << 1 << 1 << 1 << 0 << 1 << 1 << 0)
    with (lowerL [1; 1; 0; 0])%nat.
  follow goright_nonzero. rewrite rev_involutive.
  execute.
  replace (S (y + 1)) with (S (S y)) by lia. finish.
Qed.
