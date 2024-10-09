(** * Unofficial holdout ID 642 1RB2LB---_1RC2RB1LC_0LA0RB1LB *)

From BusyCoq Require Import Individual33.
From Coq Require Import PeanoNat Decidable.
From Coq Require Import Lia.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (2, L, B)  | A, 2 => None
  | B, 0 => Some (1, R, C)  | B, 1 => Some (2, R, B)  | B, 2 => Some (1, L, C)
  | C, 0 => Some (0, L, A)  | C, 1 => Some (0, R, B)  | C, 2 => Some (1, L, B)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma merge_1 : forall (r : side) (n : nat) (s1 : sym),
  [s1]^^n *> s1 >> r = [s1]^^(S n) *> r.
Proof.
  intros. rewrite lpow_S, Str_app_assoc, <- lpow_shift'. trivial.
Qed.

(* B> 1^t => 2^t B> *)
Lemma r1_l2 : forall (t : nat) (l r : side),
  l {{B}}> [1]^^t *> r -->*
  l <* [2]^^t {{B}}> r.
Proof.
  induction t. { execute. }
  intros. rewrite <- merge_1. follow IHt. execute.
Qed.

(* 2^(2t) <B => <B 1^(2t) *)
Lemma l22_b_r11 : forall (t : nat) (l r : side),
  l <* [2]^^(t*2) <{{B}} r -->*
  l <{{B}} [1]^^(t*2) *> r.
Proof.
  induction t. { execute. }
  intros. replace (S t * 2) with (S (S (t*2))) by trivial.
  rewrite <- merge_1. rewrite <- merge_1. follow IHt. execute.
Qed.

(* 2^(2t) <C => <C 1^(2t) *)
Lemma l22_c_r11 : forall (t : nat) (l r : side),
  l <* [2]^^(t*2) <{{C}} r -->*
  l <{{C}} [1]^^(t*2) *> r.
Proof.
  induction t. { execute. }
  intros. replace (S t * 2) with (S (S (t*2))) by trivial.
  rewrite <- merge_1. rewrite <- merge_1. follow IHt. execute.
Qed.

(* 1 C> 1^(2t+3) 0^∞ => 2221 C> 0 1^(2t+1) 0^∞ *)
Lemma l1r111_l2221r01 : forall (t : nat) (l : side),
  l << 1 {{C}}> [1]^^(t*2+3) *> const 0 -->*
  l << 2 << 2 << 2 << 1 {{C}}> 0 >> [1]^^(t*2+1) *> const 0.
Proof.
  intros. replace (t*2+3) with (S ((t+1)*2)) by lia. execute.
  follow r1_l2. execute.
  follow l22_b_r11. replace ((t+1)*2) with (2+t*2) by lia. execute.
  follow r1_l2. rewrite merge_1. execute.
  follow l22_b_r11. rewrite merge_1. execute. rewrite merge_1.
  follow r1_l2. rewrite <- merge_1. execute.
  follow l22_b_r11. execute.
  follow r1_l2. execute.
  follow l22_c_r11. rewrite merge_1. finish.
Qed.

(* C> 1^(2s+2) 0 1^(2t+3) 0^∞ => 11 C> 1^(2s+4) 0 1^(2t+1) 0^∞ *)
Lemma r110111_step : forall (s t : nat) (l : side),
  l {{C}}> [1]^^(s*2+2) *> 0 >> [1]^^(t*2+3) *> const 0 -->*
  l << 1 << 1 {{C}}> [1]^^(s*2+4) *> 0 >> [1]^^(t*2+1) *> const 0.
Proof.
  intros. replace (s*2+2) with (S (s*2+1)) by trivial. set (t*2+3). set (t*2+1). execute.
  follow r1_l2. execute.
  follow l1r111_l2221r01. set (t*2+1). execute.
  follow l22_c_r11. execute.
  follow r1_l2. execute.
  follow l22_b_r11. execute.
Qed.

(* C> 1^(2s+2) 0 1^(2t+1) 0^∞ => 1^(2t) C> 0 1^(2s+2t+5) 0^∞ *)
Lemma r110111_finish : forall (t s : nat) (l : side),
  l {{C}}> [1]^^(s*2+2) *> 0 >> [1]^^(t*2+1) *> const 0 -->*
  l <* [1]^^(t*2) {{C}}> 0 >> [1]^^(s*2+t*2+5) *> const 0.
Proof.
  induction t.
  { intros. replace (s*2+2) with (S (s*2+1)) by trivial. execute.
    follow r1_l2. execute.
    follow l22_b_r11. repeat rewrite merge_1. execute. }
  intros. replace (S t * 2 + 1) with (t * 2 + 3) by lia.
  follow r110111_step. replace (s * 2 + 4) with ((S s)*2+2) by lia.
  follow IHt. repeat rewrite merge_1. finish.
Qed.

(* 11 2^(2s) 1 C> 0 1^(2t+3) 0^∞ => 2^(2s+6) 1 C> 0 1^(2t+1) 0^∞ *)
Lemma l11221r0111_step : forall (s t : nat) (l : side),
  l << 1 << 1 <* [2]^^(s*2) << 1 {{C}}> 0 >> [1]^^(t*2+3) *> const 0 -->*
  l <* [2]^^(s*2+6) << 1 {{C}}> 0 >> [1]^^(t*2+1) *> const 0.
Proof.
  intros. set (t*2+3). set (t*2+1). execute.
  follow l22_b_r11. execute.
  follow r1_l2. execute.
  follow l22_c_r11. execute.
  follow r1_l2. execute.
  follow l1r111_l2221r01. repeat rewrite merge_1. finish.
Qed.

(* 1^(2s+1) C> 0 1^(2s+2t+1) 0^∞ => 2^(6s) 1 C> 0 1^(2t+1) 0^∞ *)
Lemma l11221r0111_finish : forall (s t : nat) (l : side),
  l <* [1]^^(s*2+1) {{C}}> 0 >> [1]^^(s*2+t*2+1) *> const 0 -->*
  l <* [2]^^(s*6) << 1 {{C}}> 0 >> [1]^^(t*2+1) *> const 0.
Proof.
  induction s. { trivial. }
  intros. replace (S s * 2 + 1) with (S (S (s*2+1))) by lia. do 2 rewrite <- merge_1.
  replace (S s * 2 + t * 2 + 1) with (s * 2 + (S t) * 2 + 1) by lia.
  follow IHs. replace (s*6) with (s*3*2) by lia. replace (S t * 2 + 1) with (t*2+3) by lia.
  follow l11221r0111_step. finish.
Qed.

(* 1 C> 1^(2s+2) 0 1^(2t+1) 0^∞ => 2^(6t) 1 C> 0 1^(2s+5) 0^∞ *)
Lemma l1r110111_step : forall (s t : nat) (l : side),
  l << 1 {{C}}> [1]^^(s*2+2) *> 0 >> [1]^^(t*2+1) *> const 0 -->*
  l <* [2]^^(t*6) << 1 {{C}}> 0 >> [1]^^(s*2+5) *> const 0.
Proof.
  intros.
  follow r110111_finish. rewrite merge_1. replace (S (t * 2)) with (t*2+1) by lia.
  replace (s*2+t*2+5) with (t*2+(s+2)*2+1) by lia.
  follow l11221r0111_finish. finish.
Qed.

(* 0^∞ 1 C> 1^(2s+2) 0 1^(2t+3) 0^∞ => 0^∞ 11 C> 1^(6t+6) 0 1^(2s+5) 0^∞
   Note: "0^∞ 1 C> 1^(2s+2) 0 1 0^∞" doesn't follow the pattern. *)
Lemma l1_l11 : forall (s t : nat),
  const 0 << 1 {{C}}> [1]^^(s*2+2) *> 0 >> [1]^^(t*2+3) *> const 0 -->*
  const 0 << 1 << 1 {{C}}> [1]^^(t*6+6) *> 0 >> [1]^^(s*2+5) *> const 0.
Proof.
  intros. replace (t*2+3) with ((t+1)*2+1) by lia.
  follow l1r110111_step. execute. replace ((t+1)*6) with ((1+t*3+2)*2) by lia.
  follow l22_b_r11. execute.
  follow r1_l2. execute.
  follow l22_c_r11. replace ((t*3+2)*2) with (4+t*6) by lia. repeat rewrite merge_1. execute.
Qed.

(* 0^∞ 11 C> 1^(2s+2) 0 1^(2t+1) 0^∞ => 0^∞ 1 C> 1^(6t+2) 0 1^(2s+5) 0^∞ *)
Lemma l11_l1 : forall (s t : nat),
  const 0 << 1 << 1 {{C}}> [1]^^(s*2+2) *> 0 >> [1]^^(t*2+1) *> const 0 -->+
  const 0 << 1 {{C}}> [1]^^(t*6+2) *> 0 >> [1]^^(s*2+5) *> const 0.
Proof.
  intros.
  follow l1r110111_step. set (s*2+5). execute. replace (t*6) with (t*3*2) by lia.
  follow l22_b_r11. execute.
  follow r1_l2. execute.
  follow l22_c_r11. repeat rewrite merge_1. execute.
Qed.

(* 0^∞ 11 C> 1^(2s+2) 0 1^(2t+1) 0^∞ => 0^∞ 11 C> 1^(6s+12) 0 1^(6t+5) 0^∞ *)
Lemma l11_next : forall (s t : nat),
  const 0 << 1 << 1 {{C}}> [1]^^(s*2+2) *> 0 >> [1]^^(t*2+1) *> const 0 -->+
  const 0 << 1 << 1 {{C}}> [1]^^(s*6+12) *> 0 >> [1]^^(t*6+5) *> const 0.
Proof.
  intros.
  (* "follow l11_l1." doesn't work *)
  eapply progress_evstep_trans. { apply l11_l1. }
  replace (t*6+2) with (t*3*2+2) by lia. replace (s*2+5) with ((s+1)*2+3) by lia.
  follow l1_l11. finish.
Qed.

(* D(s, t) = 0^∞ 11 C> 1^(2s+2) 0 1^(2t+1) 0^∞ *)
Definition D s t : Q * tape :=
  const 0 << 1 << 1 {{C}}> [1]^^(s*2+2) *> 0 >> [1]^^(t*2+1) *> const 0.

(* D(s, t) => D(3s+5, 3t+2). This is l11_next rewritten in terms of D. *)
Lemma D_next : forall (s t : nat),
  D s t -->+ D (s*3+5) (t*3+2).
Proof.
  intros. unfold D.
  (* "follow l11_next." doesn't work *)
  eapply progress_evstep_trans. { apply l11_next. } finish.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (D 0 0). { execute. }
  apply progress_nonhalt_simple with (C := fun '(s, t) => D s t) (i0 := (0%nat, 0%nat)).
  intros [s t]. exists (s*3+5, t*3+2). apply D_next.
Qed.
