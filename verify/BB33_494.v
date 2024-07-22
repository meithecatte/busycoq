(** * Unofficial holdout ID 494 1RB2LA0LA_2LC---2RA_0RA2RC1LC *)
(** Coq proof by Jason Yuen. Proof sketch by Matthew House. *)

From BusyCoq Require Import Individual33.
From Coq Require Import PeanoNat Decidable.
From Coq Require Import Lia.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (2, L, A)  | A, 2 => Some (0, L, A)
  | B, 0 => Some (2, L, C)  | B, 1 => None            | B, 2 => Some (2, R, A)
  | C, 0 => Some (0, R, A)  | C, 1 => Some (2, R, C)  | C, 2 => Some (1, L, C)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma merge_1 : forall (r : side) (n : nat) (s1 : sym),
  [s1]^^n *> s1 >> r = [s1]^^(S n) *> r.
Proof.
  intros. rewrite lpow_S, Str_app_assoc, <- lpow_shift'. trivial.
Qed.

Lemma merge_2 : forall (r : side) (n : nat) (s1 s2 : sym),
  [s1; s2]^^n *> s1 >> s2 >> r = [s1; s2]^^(S n) *> r.
Proof.
  intros. rewrite lpow_S, Str_app_assoc, <- lpow_shift'. trivial.
Qed.

Lemma merge_3 : forall (r : side) (n : nat) (s1 s2 s3 : sym),
  [s1; s2; s3]^^n *> s1 >> s2 >> s3 >> r = [s1; s2; s3]^^(S n) *> r.
Proof.
  intros. rewrite lpow_S, Str_app_assoc, <- lpow_shift'. trivial.
Qed.

Lemma l12_r20 : forall (t : nat) (l r : side),
  l <* <[1; 2]^^t <{{A}} r -->*
  l <{{A}} [2; 0]^^t *> r.
Proof.
  induction t. { execute. }
  execute. follow IHt. rewrite merge_2. finish.
Qed.

Lemma r20_2_l12 : forall (t : nat) (r : side),
  const 0 <{{A}} [2; 0]^^t *> 2 >> r -->*
  const 0 <* [2; 1]^^(S t) {{A}}> r.
Proof.
  induction t. { execute. }
  intros. rewrite <- merge_2. follow IHt. execute.
Qed.

(* 0^∞ (12)^t A> 1^(u+1) => 0^∞ (12)^(t+1) A> 1^u *)
Lemma R2 : forall (t u : nat) (r : side),
  const 0 <* [2; 1]^^t {{A}}> [1]^^(S u) *> r -->*
  const 0 <* [2; 1]^^(S t) {{A}}> [1]^^u *> r.
Proof.
  execute. follow l12_r20. follow r20_2_l12. trivial.
Qed.

(* 0^∞ A> 1^s => 0^∞ (12)^s A> *)
Lemma R2_finish : forall (s : nat) (r : side),
  const 0 {{A}}> [1]^^s *> r -->*
  const 0 <* [2; 1]^^s {{A}}> r.
Proof.
  induction s. { trivial. }
  intros. rewrite <- merge_1. follow IHs. follow (R2 s 0 r). trivial.
Qed.

Lemma r20_l12 : forall (t : nat) (r : side),
  const 0 <{{A}} [2; 0]^^t *> r -->*
  const 0 <* [2; 1]^^t {{A}}> 0 >> r.
Proof.
  induction t. { execute. }
  intros. rewrite <- merge_2. follow IHt. execute.
Qed.

(* 0^∞ (12)^(t+1) A> 00000 (202)^u => 0^∞ (12)^t A> 00000 (202)^(u+1) *)
Lemma R3 : forall (t u : nat) (r : side),
  const 0 <* [2; 1]^^(S t) {{A}}> 0 >> 0 >> 0 >> 0 >> 0 >> [2; 0; 2]^^u *> r -->*
  const 0 <* [2; 1]^^t {{A}}> 0 >> 0 >> 0 >> 0 >> 0 >> [2; 0; 2]^^(S u) *> r.
Proof.
  execute. follow l12_r20. follow r20_l12. trivial.
Qed.

(* 0^∞ (12)^s A> 00000 => 0^∞ A> 00000 (202)^s *)
Lemma R3_finish : forall (s : nat) (r : side),
  const 0 <* [2; 1]^^s {{A}}> 0 >> 0 >> 0 >> 0 >> 0 >> r -->*
  const 0 {{A}}> 0 >> 0 >> 0 >> 0 >> 0 >> [2; 0; 2]^^s *> r.
Proof.
  induction s. { trivial. }
  intros. follow (R3 s 0 r). follow IHs. simpl. rewrite merge_3. trivial.
Qed.

(* C(a,b,c) = 0^∞ (12)^a 2^b C> 202 (202)^c 000 *)
Definition C (a b c : nat) (r : side) : Q * tape :=
  const 0 <* [2; 1]^^a <* [2]^^b {{C}}> [2; 0; 2]^^(S c) *> 0 >> 0 >> 0 >> r.

Lemma l2_r1 : forall (n : nat) (l r : side),
  l <* [2]^^n <{{C}} r -->*
  l <{{C}} [1]^^n *> r.
Proof.
  induction n. { execute. }
  intros. execute. follow IHn. rewrite merge_1. trivial.
Qed.

(* C(0,b,c) -> C(b+2,1,c-1)         [c ≥ 1] *)
Lemma C_0b1 : forall (b c : nat) (r : side),
  C 0 b (c + 1) r -->* C (b + 2) 1 c r.
Proof.
  execute. follow l2_r1. execute. rewrite merge_1. follow R2_finish.
  execute. follow l12_r20. follow r20_2_l12.
  rewrite Nat.add_comm. execute.
Qed.

Lemma r1_l2 : forall (n : nat) (l r : side),
  l {{C}}> [1]^^n *> r -->*
  l <* [2]^^n {{C}}> r.
Proof.
  induction n. { execute. }
  intros. execute. follow IHn. rewrite merge_1. trivial.
Qed.

(* C(1,b,c) -> C(b+5,1,c-1)         [c ≥ 1] *)
Lemma C_1b1 : forall (b c : nat) (r : side),
  C 1 b (c + 1) r -->* C (b + 5) 1 c r.
Proof.
  execute. follow l2_r1. execute. follow r1_l2. repeat rewrite merge_1.
  execute. follow l2_r1. execute. repeat rewrite merge_1. follow R2_finish.
  replace (S (S (S (S (S b))))) with (b + 5 - 0) by lia.
  execute. follow l12_r20. follow r20_l12.
  replace (b + 5 - 0) with (b + 5) by lia. unfold C. execute.
Qed.

Lemma l2_r0 : forall (n : nat) (l r : side),
  l <* [2]^^n <{{A}} r -->*
  l <{{A}} [0]^^n *> r.
Proof.
  induction n. { execute. }
  intros. execute. follow IHn. rewrite merge_1. trivial.
Qed.

(* C(a,b,0) -> C(1,5,a-3) 0^b 202   [a ≥ 3] *)
Lemma C_3b0 : forall (a b : nat) (r : side),
  C (a + 3) b 0 r -->+ C 1 5 a ([0]^^b *> 2 >> 0 >> 2 >> r).
Proof.
  intros. replace (a + 3) with (2 + a + 1) by lia.
  execute. follow l2_r1. execute. follow r1_l2.
  execute. follow l2_r1. execute. follow r1_l2.
  execute. follow l2_r0. execute. follow l12_r20.
  rewrite merge_2. follow r20_l12. follow R3_finish.
  repeat rewrite merge_1. execute.
Qed.

(* C(a,b,c) -> C(a-2,b+7,c-1)       [a ≥ 2, c ≥ 1] *)
Lemma C_2b1 : forall (a b c : nat) (r : side),
  C (a + 2) b (c + 1) r -->* C a (b + 7) c r.
Proof.
  intros. rewrite (Nat.add_comm a), (Nat.add_comm b), (Nat.add_comm c).
  execute. follow l2_r1. execute. follow r1_l2.
  execute. follow l2_r1. execute. follow r1_l2.
  repeat rewrite merge_1. execute.
Qed.

(* D(a,c) = C(a,1,c) *)
Definition D (a c : nat) (r : side) : Q * tape :=
  C a 1 c r.

Lemma C_2k_b_k : forall (k a b c : nat) (r : side),
  C (2*k+a) b (k+c) r -->* C a (7*k+b) c r.
Proof.
  induction k; intros. { finish. }
  replace (2 * S k + a) with (2*k+a+2) by lia.
  replace (S k + c) with (k+c+1) by lia. follow C_2b1. follow IHk. finish.
Qed.

(* D(2k+0,c)     -> D(7k+3,c-k-1)              [c ≥ k+1]
   D(2k+1,c)     -> D(7k+6,c-k-1)              [c ≥ k+1] *)
Lemma D_gt : forall (k c : nat) (r : side),
  D k (c+(k/2)+1) r -->* D (3*k+(k/2)+3) c r.
Proof.
  intros. unfold D.
  rewrite (Nat.div_mod k 2) at 1 by lia. replace (c+(k/2)+1) with ((k/2)+(c+1)) by lia.
  follow C_2k_b_k. cases (Nat.Even_Odd_dec k).
  - destruct e. replace k with (x*2) by lia.
    rewrite Nat.div_mul, Nat.Div0.mod_mul by lia.
    follow C_0b1. finish.
  - destruct o. replace k with (1+x*2) by lia.
    rewrite Nat.div_add, Nat.Div0.mod_add by lia. change (1/2) with 0%nat.
    follow C_1b1. finish.
Qed.

(* D(2k+0,c)     -> D(10,2k-2c-4) 0^(7c+1) 202 [c ≤ k-2]
   D(2k+1,c)     -> D(10,2k-2c-3) 0^(7c+1) 202 [c ≤ k-2] *)
Lemma D_lt : forall (k c : nat) (r : side),
  D (k+2*c+4) c r -->+ D 10 k ([0]^^(7*c+1) *> 2 >> 0 >> 2 >> r).
Proof.
  intros. unfold D.
  replace (k+2*c+4) with (2*c+(k+1+3)) by lia. replace c with (c+0) at 2 by lia.
  follow C_2k_b_k. eapply progress_evstep_trans. { apply C_3b0. }
  follow C_1b1. finish.
Qed.

(* a_i is this sequence: 10, 38, 136, 479, 1679, 5879, 20579, 72029, ... *)
Fixpoint a (i : nat) : nat :=
  match i with
  | O => 10
  | S i => 3 * a i + (a i / 2) + 3
  end.

Lemma a_le_aS : forall (i : nat),
  7 * a i + 5 <= 2 * a (S i).
Proof.
  intros. cbn[a]. pose proof (Nat.mul_succ_div_gt (a i) 2) as H. lia.
Qed.

(* c_i is this sequence: 0, 6, 26, 95, 335, 1175, 4115, 14405, ... *)
Fixpoint c (i : nat) : nat :=
  match i with
  | O => 0
  | S i => c i + (a i / 2) + 1
  end.

Lemma a_le_5c10 : forall (i : nat),
  a i <= 5 * c i + 10.
Proof.
  induction i. { trivial. }
  cbn[a c]. pose proof (Nat.mul_succ_div_gt (a i) 2) as H. lia.
Qed.

(* C_i is this sequence: 0, 6, 34, 116, 433, 1479, 5267, 18271, ... *)
Fixpoint cc (t : nat) : nat :=
  match t with
  | O => 0
  | S i => a i - 2 * (cc i - c i) - 4
  end.

Lemma cc_bounds : forall (i : nat),
  c i <= cc i /\ 2 * cc i + 6 <= c (S i).
Proof.
  induction i as [| i [H1 H2]]. { split; trivial. }
  cbn[cc]. split.
  - enough (2 * c (S i) <= a i + 2 * c i + 2) by lia. cbn[c].
    pose proof (Nat.Div0.mul_div_le (a i) 2) as H.
    lia.
  - assert (Ha4: 4 <= a i). { clear H1 H2. induction i; cbn[a]; lia. }
    pose proof (a_le_aS i) as Hi.
    pose proof (a_le_aS (S i)) as HSi.
    pose proof (a_le_5c10 (S (S i))) as Hac.
    lia. (* lia is really good at inequality bash *)
Qed.

Lemma D_step_cc : forall (i : nat) (r : side), exists (r' : side),
  D (a i) (cc i - c i) r -->+
  D (a 0) (cc (S i) - c 0) r'.
Proof.
  intros. simpl c. exists ([0]^^(7 * (cc i - c i) + 1) *> 2 >> 0 >> 2 >> r).
  assert (Ha: a i = (a i - 2 * (cc i - c i) - 4) + 2 * (cc i - c i) + 4).
  { destruct (cc_bounds (S i)) as [H _]. cbn[c cc] in H. lia. }
  (* todo: "follow D_lt." doesn't work *)
  rewrite Ha. eapply progress_evstep_trans. { apply D_lt. }
  cbn[cc]. finish.
Qed.

Lemma c_monotone : forall (i j : nat),
  c i <= c (j + i).
Proof.
  induction j. { trivial. }
  simpl. lia.
Qed.

Lemma D_step_a : forall (i j : nat) (r : side),
  D (a i) (cc (j+i+1) - c i) r -->*
  D (a (S i)) (cc (j+i+1) - c (S i)) r.
Proof.
  intros.
  assert (Hcc: (a i)/2+1 <= cc (j+i+1) - c i).
  { pose proof (c_monotone (S i) j) as H1. cbn[c] in H1.
    replace (j + S i) with (j+i+1) in H1 by lia.
    destruct (cc_bounds (j+i+1)) as [H2 _]. lia. }
  replace (cc (j+i+1) - c i) with
    ((cc (j+i+1) - c i - (a i) / 2 - 1) + (a i) / 2 + 1) by lia.
  follow D_gt. cbn[c]. finish.
Qed.

Lemma D_step_a_lt : forall (i j : nat) (r : side), (i < j) ->
  D (a i) (cc j - c i) r -->*
  D (a (S i)) (cc j - c (S i)) r.
Proof.
  intros. replace j with ((j-i-1)+i+1) by lia. follow D_step_a. finish.
Qed.

Lemma D_step_a_minus : forall (i j : nat) (r : side),
  D (a (i - S j)) (cc i - c (i - S j)) r -->*
  D (a (i - j)) (cc i - c (i - j)) r.
Proof.
  intros.
  destruct (Compare_dec.le_lt_dec i j). { finish. }
  follow D_step_a_lt. { lia. }
  finish.
Qed.

Lemma D_step_a_finish : forall (i : nat) (r : side),
  D (a 0) (cc i - c 0) r -->*
  D (a i) (cc i - c i) r.
Proof.
  intros. replace 0%nat with (i - S i) by lia. induction (S i). { finish. }
  follow D_step_a_minus. exact IHn.
Qed.

Lemma D_next : forall (i : nat) (r : side), exists (r' : side),
  D (a 0) (cc i - c 0) r -->+
  D (a 0) (cc (S i) - c 0) r'.
Proof.
  intros. destruct (D_step_cc i r) as [r' H]. exists r'.
  follow D_step_a_finish. exact H.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (D (a 0) (cc 0 - c 0) (const 0)).
  { apply evstep_trans with (C 1 5 (0+1) (const 0)).
    { unfold C. do 105 step. finish. }
    follow C_1b1. finish. }
  apply progress_nonhalt_simple with (i0 := (0%nat, const 0))
    (C := fun '(i, r) => D (a 0) (cc i - c 0) r).
  intros [i r]. destruct (D_next i r) as [r' H]. exists (S i, r'). exact H.
Qed.
