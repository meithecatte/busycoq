(** * Skelet #34 *)

(** Following https://www.sligocki.com/2023/02/02/skelet-34.html *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import PeanoNat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat.
From BusyCoq Require Import Extraction. Import ETranslatedCyclers.
Set Default Goal Selector "!".

Notation "0" := S0.
Notation "1" := S1.
Notation side := (Stream sym).

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, C)
  | B, 0 => Some (0, R, C)  | B, 1 => Some (0, R, B)
  | C, 0 => Some (1, L, D)  | C, 1 => Some (0, L, A)
  | D, 0 => Some (1, L, E)  | D, 1 => None
  | E, 0 => Some (1, L, A)  | E, 1 => Some (1, R, A)
  end.

(** Trivial lemmas, but [simpl] in these situations leaves a mess. *)
Lemma move_left_const : forall s0 s r,
  move_left (const s0 {{s}} r) = const s0 {{s0}} s >> r.
Proof. reflexivity. Qed.

Lemma move_right_const : forall l s s0,
  move_right (l {{s}} const s0) = l << s {{s0}} const s0.
Proof. reflexivity. Qed.

(** [assumption] and [eassumption] both refuse to instantiate [forall]s. *)

Ltac apply_assumption :=
  match goal with
  | H: _ |- _ => apply H
  end.

Ltac prove_step_left := apply step_left; reflexivity.
Ltac prove_step_right := apply step_right; reflexivity.
Ltac prove_step := prove_step_left || prove_step_right.
Ltac simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  simpl.
Ltac finish := apply evstep_refl.
Ltac step := eapply evstep_step; [prove_step | simpl_tape].
Ltac execute := repeat step; try finish.
Ltac follow_assm := eapply evstep_trans; [apply_assumption; eauto |].
Ltac follow_hyp H := eapply evstep_trans; [apply H; eauto |].

Tactic Notation "follow" := follow_assm.
Tactic Notation "follow" constr(H) := follow_hyp H.

Ltac triv := introv; repeat (step || follow); try finish.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "l <{{ q }} r" := (q;; tl l {{hd l}} r)  (at level 30, q at next level).
Notation "l {{ q }}> r" := (q;; l {{hd r}} tl r)  (at level 30, q at next level).
Notation "s >>> r" := (Str_app s r)  (at level 25, right associativity).
Notation "l <<< s" := (Str_app s l)  (at level 24, left associativity).
Notation pow s n := (concat (repeat s n)).

Notation P := Pos.succ.

Fixpoint L' (n : positive) : side :=
  match n with
  | xH => const 0 << 1 << 0 << 0 << 0
  | xO n => L' n << 0 << 0 << 0 << 0
  | xI n => L' n << 1 << 0 << 0 << 0
  end.

Definition L (n : N) : side :=
  match n with
  | N0 => const 0
  | Npos n => L' n
  end.

Fixpoint R (n : positive) : side :=
  match n with
  | xH => 1 >> 1 >> const 0
  | xO n => 1 >> 0 >> R n
  | xI n => 1 >> 1 >> R n
  end.

Definition D n m : Q * tape :=
  L n <{{C}} 1 >> 0 >> 1 >> 0 >> R m.

Lemma L_inc : forall n r,
  L n <{{C}} r -->* L (N.succ n) {{B}}> r.
Proof.
  destruct n as [|n].
  - triv.
  - induction n; triv.
Qed.

Inductive has0 : positive -> Prop :=
  | has0_0 n: has0 (n~0)
  | has0_1 n: has0 n -> has0 (n~1).

Hint Constructors has0 : core.

Inductive all1 : positive -> Prop :=
  | all1_H:   all1 1
  | all1_1 n: all1 n -> all1 (n~1).

Lemma R_inc_has0 : forall n l,
  has0 n ->
  l << 0 {{C}}> R n -->* l <{{A}} 0 >> R (P n).
Proof.
  introv H. generalize dependent l. induction H; introv.
  - triv.
  - execute. follow. execute.
Qed.

Corollary D_inc : forall n m,
  has0 m ->
  D n m -->* D (N.succ n) (P m).
Proof.
  introv H. unfold D.
  follow L_inc. execute.
  follow R_inc_has0. execute.
Qed.

Lemma R_inc_all1 : forall n l,
  all1 n ->
  l << 0 {{C}}> R n -->* l <{{C}} R (P n).
Proof.
  introv H. generalize dependent l. induction H; triv.
Qed.

Fixpoint K' (n : positive) : side :=
  match n with
  | xH =>    const 0 << 1 << 0 << 0
  | xO n => K' n << 0 << 0 << 0 << 0
  | xI n => K' n << 0 << 1 << 0 << 0
  end.

Definition K (n : N) : side :=
  match n with
  | N0 => const 0
  | Npos n => K' n
  end.

Lemma L_as_K : forall n,
  L n = K n << 0.
Proof.
  destruct n as [| n].
  - apply const_unfold.
  - simpl. induction n; simpl; try rewrite IHn; reflexivity.
Qed.

Definition E n a m : Q * tape :=
  K n <{{C}} 1 >> 0 >> 1 >> a >> R m.

Theorem start_reset : forall n m,
  all1 m ->
  D n m -->* E (N.succ n) 1 (P m).
Proof.
  introv H. unfold D.
  follow L_inc. rewrite L_as_K.
  execute. follow R_inc_all1.
  execute.
Qed.

Lemma eat_LI : forall l t,
  l << 1 << 0 << 0 << 0 <{{C}} R t -->*
  l <{{C}} R (t~1~1).
Proof. triv. Qed.

Lemma eat_KI : forall l t,
  has0 t ->
  l << 0 << 1 << 0 << 0 <{{C}} R t -->*
  l <{{C}} R (4 * P t).
Proof.
  introv H. execute.
  follow R_inc_has0. execute.
Qed.

Inductive bin : nat -> Type :=
  | bb : bin 0
  | b0 {k} : bin k -> bin (S k)
  | b1 {k} : bin k -> bin (S k).

Reserved Notation "c -S-> c'" (at level 40, c' at next level).

Inductive bin_succ : forall {k}, bin k -> bin k -> Prop :=
  | succ_b0 {k} (n : bin k)    : (b0 n) -S-> (b1 n)
  | succ_b1 {k} (n n' : bin k) : n -S-> n'  ->  b1 n -S-> b0 n'

  where "c -S-> c'" := (bin_succ c c').

Inductive bin_plus {k} : nat -> bin k -> bin k -> Prop :=
  | plus_0 n : bin_plus 0 n n
  | plus_S u n n' n'' :
    n -S-> n' ->
    bin_plus    u  n' n'' ->
    bin_plus (S u) n n''.

Hint Constructors bin_succ bin_plus : core.

Lemma plus_S' : forall k u (n n' n'' : bin k),
  bin_plus u n n' ->
  n' -S-> n'' ->
  bin_plus (S u) n n''.
Proof.
  introv H. induction H; eauto.
Qed.

Lemma bin_plus_b0 : forall k u (n n' : bin k),
  bin_plus u n n' ->
  bin_plus (2 * u) (b0 n) (b0 n').
Proof.
  introv H. induction H.
  - auto.
  - replace (2 * S u) with (S (S (2 * u))) by lia.
    eauto.
Qed.

Fixpoint bin_min k : bin k :=
  match k with
  | O => bb
  | S k => b0 (bin_min k)
  end.

Fixpoint bin_max k : bin k :=
  match k with
  | O => bb
  | S k => b1 (bin_max k)
  end.

Lemma pow2_gt0 : forall k, 2 ^ k > 0.
Proof. induction k; simpl; lia. Qed.

Lemma inc_to_max : forall k,
  bin_plus (2^k - 1) (bin_min k) (bin_max k).
Proof.
  induction k.
  - auto.
  - replace (2 ^ S k - 1) with (S (2 * (2 ^ k - 1))).
    + eapply plus_S'.
      * simpl. apply bin_plus_b0. eassumption.
      * constructor.
    + assert (2 ^ k > 0) by apply pow2_gt0.
      simpl. lia.
Qed.

Fixpoint pow4 (k : nat) (n : positive) : positive :=
  match k with
  | O => n
  | S k => pow4 k (n~0~0)
  end.

Fixpoint Lk {k} (n : bin k) (l : side) :=
  match n with
  | bb => l
  | b0 n => Lk n l << 0 << 0 << 0 << 0
  | b1 n => Lk n l << 1 << 0 << 0 << 0
  end.

Lemma Lk_inc : forall k (n n' : bin k),
  n -S-> n' -> forall l r,
  Lk n l <{{C}} r -->* Lk n' l {{B}}> r.
Proof.
  introv H. induction H; triv.
Qed.

Lemma LaR_inc : forall l k (n n' : bin k) a m,
  has0 m ->
  n -S-> n' ->
  Lk n  l <{{C}} 1 >> 0 >> 1 >> a >> R m -->*
  Lk n' l <{{C}} 1 >> 0 >> 1 >> a >> R (P m).
Proof.
  introv Hm Hn. destruct a;
    follow Lk_inc; execute; follow R_inc_has0; execute.
Qed.

Fixpoint R_incs (n : nat) (m : positive) : Prop :=
  match n with
  | O => True
  | S n => has0 m /\ R_incs n (P m)
  end.

Lemma R_incs_less : forall n n' m,
  n' < n ->
  R_incs n m -> R_incs n' m.
Proof.
  induction n; introv Hlt H.
  - inversion Hlt.
  - destruct n' as [| n'].
    + apply I.
    + destruct H as [H1 H2].
      split.
      * exact H1.
      * apply IHn; [lia | assumption].
Qed.

Fixpoint incr (n : nat) (m : positive) : positive :=
  match n with
  | O => m
  | S n => incr n (P m)
  end.

Lemma LaR_incs : forall l k u (n n' : bin k) a m,
  bin_plus u n n' ->
  R_incs u m ->
  Lk n  l <{{C}} 1 >> 0 >> 1 >> a >> R m -->*
  Lk n' l <{{C}} 1 >> 0 >> 1 >> a >> R (incr u m).
Proof.
  introv H. generalize dependent m. induction H; introv Hr.
  - finish.
  - inverts Hr as Hr0 Hr1. follow LaR_inc.
    follow IHbin_plus. finish.
Qed.

Corollary LaR_max : forall l k a m,
  R_incs (2 ^ k - 1) m ->
  Lk (bin_min k) l <{{C}} 1 >> 0 >> 1 >> a >> R m -->*
  Lk (bin_max k) l <{{C}} 1 >> 0 >> 1 >> a >> R (incr (2 ^ k - 1) m).
Proof.
  introv H.
  apply LaR_incs.
  + apply inc_to_max.
  + assumption.
Qed.

Lemma eat_bin_max : forall k l t,
  has0 t ->
  Lk (bin_max k) (l << 0 << 1 << 0 << 0) <{{C}} R t -->*
  l <{{C}} 1 >> 0 >> 1 >> 0 >> R (pow4 k (P t)).
Proof.
  induction k; introv H.
  - follow eat_KI. finish.
  - simpl. follow eat_LI. follow (IHk l (t~1~1)%positive). finish.
Qed.

Definition f (m : positive) (a : sym) (k : nat) : positive :=
  let t := incr (2 ^ k - 1) m in
  match a with
  | 0 => t~0~0
  | 1 => t~1~0
  end.

Lemma has0_f : forall m a k, has0 (f m a k).
Proof. destruct a; introv; simpl; constructor. Qed.

Hint Resolve has0_f : core.

Lemma drop_KI : forall l m k a,
  R_incs (2 ^ k - 1) m ->
  Lk (bin_min k) (l << 0 << 1 << 0 << 0) <{{C}} 1 >> 0 >> 1 >> a >> R m -->*
  l <{{C}} 1 >> 0 >> 1 >> 0 >> R (pow4 k (P (f m a k))).
Proof.
  introv H.
  follow LaR_max.
  replace (1 >> 0 >> 1 >> a >> R (incr (2 ^ k - 1) m)) with (R (f m a k))
    by (destruct a; reflexivity).
  follow eat_bin_max. finish.
Qed.

Lemma prepare_K : forall n, exists k n',
  K' n = Lk (bin_min k) (K n' << 0 << 1 << 0 << 0)
  /\ 2 ^ k - 1 < Pos.to_nat n /\ (n' < N.pos n)%N.
Proof.
  induction n.
  - destruct IHn as [k [n' IH]].
    exists O, (Npos n). repeat split.
    + apply Pos2Nat.is_pos.
    + lia.
  - destruct IHn as [k [n' [EIH IH]]].
    exists (S k), n'. repeat split.
    + simpl. rewrite EIH. reflexivity.
    + rewrite Pos2Nat.inj_xO. simpl. lia.
    + lia.
  - exists O, N0. split.
    + simpl. rewrite const_unfold at 1. reflexivity.
    + simpl. lia.
Qed.

Theorem step_reset : forall (n m : positive) a,
  R_incs (Pos.to_nat n) m ->
  exists (n' : N) (m' : positive),
  E (Npos n) a m -->* E n' 0 m' /\
  (n' < Npos n)%N /\ R_incs (N.to_nat n') m'.
Proof.
  introv H.
  destruct (prepare_K n) as [k [n' [EK [HK Hless]]]].
  exists n'. repeat eexists.
  - unfold E. simpl. rewrite EK.
    follow drop_KI. { eapply R_incs_less; eassumption. }
    finish.
  - exact Hless.
  - exact H.
