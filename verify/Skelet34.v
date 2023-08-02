(** * Skelet #34 *)

(** Following https://www.sligocki.com/2023/02/02/skelet-34.html *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import PeanoNat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
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
Ltac execute := repeat (try finish; step).
Ltac follow_assm := eapply evstep_trans; [apply_assumption; eauto |].
Ltac follow_hyp H := eapply evstep_trans; [apply H; eauto |].

Tactic Notation "follow" := follow_assm.
Tactic Notation "follow" constr(H) := follow_hyp H.

Ltac triv := introv; repeat (step || follow); try finish.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation "l <{{ q }} r" := (q;; tl l {{hd l}} r)  (at level 30, q at next level).
Notation "l {{ q }}> r" := (q;; l {{hd r}} tl r)  (at level 30, q at next level).
Notation "s >>> r" := (Str_app s r)  (at level 25, right associativity).
Notation "l <<< s" := (Str_app s l)  (at level 24, left associativity).
Notation pow s n := (concat (repeat s n)).

Notation P := Pos.succ.

Definition het_add (a : N) (b : positive) : positive :=
  match a with
  | N0 => b
  | Npos a => a + b
  end.

Notation "a :+ b" := (het_add a b)  (at level 50, left associativity).

Lemma het_add_succ : forall a b, N.succ a :+ b = a :+ P b.
Proof.
  introv. destruct a; unfold ":+", N.succ; lia.
Qed.

Lemma het_add_succ_l : forall a b, N.succ a :+ b = P (a :+ b).
Proof.
  introv. destruct a; unfold ":+", N.succ; lia.
Qed.

Lemma pos_het_add : forall a b, (N.pos (a :+ b) = a + N.pos b)%N.
Proof.
  introv. destruct a; unfold ":+"; lia.
Qed.

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

(** We use a definition of [b] shifted by 1 compared to the informal proof, i.e.
    we can do [n + b n] is the farthest we can go without reaching a new power
    of two. *)
Fixpoint b (n : positive) : N :=
  match n with
  | xH => N0
  | xO n' => N.succ_double (b n')
  | xI n' => N.double (b n')
  end.

Inductive has0 : positive -> Prop :=
  | has0_0 n: has0 (n~0)
  | has0_1 n: has0 n -> has0 (n~1).

Hint Constructors has0 : core.

Inductive all1 : positive -> Prop :=
  | all1_H:   all1 1
  | all1_1 n: all1 n -> all1 (n~1).

Lemma b0_all1 : forall n, b n = N0 -> all1 n.
Proof.
  induction n; introv H.
  - apply all1_1, IHn.
    simpl in H. lia.
  - simpl in H. lia.
  - apply all1_H.
Qed.

Lemma bn0_has0 : forall n, (b n > 0)%N -> has0 n.
Proof.
  induction n; introv H; simpl; simpl in H.
  - apply has0_1, IHn. lia.
  - apply has0_0.
  - lia.
Qed.

Lemma b_succ : forall n, (b n > 0)%N -> b (P n) = N.pred (b n).
Proof. induction n; simpl; lia. Qed.

Lemma b_add : forall u n,
  (u <= b n -> b (u :+ n) = b n - u)%N.
Proof.
  apply (N.induction (fun u => forall n, u <= b n -> b (u :+ n) = b n - u)%N).
  - intuition.
  - introv H. simpl. lia.
  - intros u IH n H.
    rewrite het_add_succ_l, b_succ; rewrite IH; lia.
Qed.

Corollary b_add_self : forall n,
  b (b n :+ n) = 0%N.
Proof.
  introv. rewrite b_add; lia.
Qed.

Lemma b0_succ : forall n, b n = 0%N -> b (P n) = (Npos n).
Proof.
  introv H. apply b0_all1 in H.
  induction H.
  - reflexivity.
  - simpl. rewrite IHall1. lia.
Qed.

Lemma L_inc : forall n r,
  L n <{{C}} r -->* L (N.succ n) {{B}}> r.
Proof.
  destruct n as [|n].
  - triv.
  - induction n; triv.
Qed.

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

Corollary D_run : forall u n m,
  (u <= b m)%N ->
  D n m -->* D (u + n) (u :+ m).
Proof.
  apply (N.induction (fun u =>
    forall n m, (u <= b m)%N -> D n m -->* D (u + n) (u :+ m))).
  - (* morphism bullshit *) intuition.
  - (* u = 0 *) introv H. finish.
  - intros u IH n m H.
    follow D_inc. { apply bn0_has0. lia. }
    replace (N.succ u + n)%N with (u + N.succ n)%N by lia.
    replace (N.succ u :+ m)%N with (u :+ P m)%N
      by (rewrite het_add_succ; reflexivity).
    apply IH. rewrite b_succ; lia.
Qed.

Corollary D_finish : forall n m,
  D n m -->* D (b m + n) (b m :+ m).
Proof. introv. apply D_run. lia. Qed.

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

Corollary start_reset' : forall n m,
  all1 m ->
  D n m -->+ E (N.succ n) 1 (P m).
Proof.
  introv H.
  apply evstep_progress.
  - apply start_reset. assumption.
  - discriminate.
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

Inductive bin_plus {k} : N -> bin k -> bin k -> Prop :=
  | plus_0 n : bin_plus N0 n n
  | plus_S u n n' n'' :
    n -S-> n' ->
    bin_plus         u  n' n'' ->
    bin_plus (N.succ u) n n''.

Hint Constructors bin_succ bin_plus : core.

Lemma plus_S' : forall k u (n n' n'' : bin k),
  bin_plus u n n' ->
  n' -S-> n'' ->
  bin_plus (N.succ u) n n''.
Proof.
  introv H. induction H; eauto.
Qed.

Lemma bin_plus_b0 : forall k u (n n' : bin k),
  bin_plus u n n' ->
  bin_plus (N.double u) (b0 n) (b0 n').
Proof.
  introv H. induction H.
  - auto.
  - replace (N.double (N.succ u)) with (N.succ (N.succ (N.double u))) by lia.
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

Lemma inc_to_max : forall k,
  bin_plus (pow2 k - 1) (bin_min k) (bin_max k).
Proof.
  induction k.
  - auto.
  - replace (pow2 (S k) - 1)%N with (N.succ (N.double (pow2 k - 1))).
    + eapply plus_S'.
      * apply bin_plus_b0. eassumption.
      * constructor.
    + assert (pow2 k > 0)%N by apply pow2_gt0.
      rewrite pow2_S. lia.
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

(*
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
  *)

Lemma LaR_incs : forall l k u (n n' : bin k) a m,
  bin_plus u n n' ->
  (u <= b m)%N ->
  Lk n  l <{{C}} 1 >> 0 >> 1 >> a >> R m -->*
  Lk n' l <{{C}} 1 >> 0 >> 1 >> a >> R (u :+ m).
Proof.
  introv H.
  generalize dependent m. induction H; introv Hr.
  - finish.
  - follow LaR_inc. { apply bn0_has0. lia. }
    follow IHbin_plus. { rewrite b_succ; lia. }
    replace (u :+ P m)%N with (N.succ u :+ m)%N
      by (rewrite het_add_succ; reflexivity).
    finish.
Qed.

Corollary LaR_max : forall l k a m,
  (pow2 k - 1 <= b m)%N ->
  Lk (bin_min k) l <{{C}} 1 >> 0 >> 1 >> a >> R m -->*
  Lk (bin_max k) l <{{C}} 1 >> 0 >> 1 >> a >> R (pow2 k - 1 :+ m).
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
  let t := (pow2 k - 1 :+ m) in
  match a with
  | 0 => t~0~0
  | 1 => t~1~0
  end.

Lemma has0_f : forall m a k, has0 (f m a k).
Proof. destruct a; introv; simpl; constructor. Qed.

Hint Resolve has0_f : core.

Lemma drop_KI : forall l m k a,
  (pow2 k - 1 <= b m)%N ->
  Lk (bin_min k) (l << 0 << 1 << 0 << 0) <{{C}} 1 >> 0 >> 1 >> a >> R m -->*
  l <{{C}} 1 >> 0 >> 1 >> 0 >> R (pow4 k (P (f m a k))).
Proof.
  introv H.
  follow LaR_max.
  replace (1 >> 0 >> 1 >> a >> R (pow2 k - 1 :+ m)) with (R (f m a k))
    by (destruct a; reflexivity).
  follow eat_bin_max. finish.
Qed.

Lemma prepare_K : forall (n : N), (n > 0)%N -> exists (k : nat) (n' : N),
  K n = Lk (bin_min k) (K n' << 0 << 1 << 0 << 0)
  /\ (n = pow2 k + pow2 (S k) * n')%N.
Proof.
  destruct n as [| n]. { lia. }
  intros _.
  induction n.
  - exists O, (Npos n). auto.
  - destruct IHn as [k [n' [EIH IH]]].
    exists (S k), n'. split.
    + simpl. simpl in EIH. rewrite EIH. reflexivity.
    + unfold pow2, pow2'. fold pow2'.
      unfold pow2, pow2' in IH. fold pow2' in IH.
      lia.
  - exists O, N0. repeat split.
    simpl. rewrite const_unfold at 1. reflexivity.
Qed.

Theorem step_reset : forall n m a,
  (n <= b m)%N ->
  (n > 0)%N ->
  exists (n' : N) (m' : positive),
  E n a m -->* E n' 0 m' /\
  (n' < n)%N /\ (n' <= b m')%N.
Proof.
  introv Hinvariant Hgt0.
  destruct (prepare_K n Hgt0) as [k [n' [EK En']]].
  exists n'. eexists. repeat split.
  - unfold E. rewrite EK.
    follow drop_KI. { lia. }
    finish.
  - rewrite En'. unfold pow2. nia.
  - admit.
Admitted.

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

Corollary do_reset : forall n m a,
  (n <= b m)%N ->
  (n > 0)%N ->
  exists m',
  E n a m -->* E 0 0 m'.
Proof.
  induction n using N_strong_induction; introv Hinvariant Hgt0.
  destruct (step_reset n m a Hinvariant Hgt0)
    as [n' [m' [Hsteps [Hless Hinvariant']]]].
  destruct n' as [| n'].
  - exists m'. exact Hsteps.
  - assert (G: exists m'', E (Npos n') 0 m' -->* E 0 0 m'').
    { apply H; try assumption; reflexivity. }
    destruct G as [m'' G]. exists m''.
    follow Hsteps. apply G.
Qed.

Theorem D_next : forall m, exists m',
  D 0 m -->+ D 0 m'.
Proof.
  introv.
  assert (H: exists m', E (N.succ (b m)) 1 (P (b m :+ m)) -->* E 0 0 m').
  { apply do_reset; try lia.
    rewrite b0_succ, pos_het_add.
    - lia.
    - apply b_add_self. }
  destruct H as [m' H]. exists m'.
  eapply evstep_progress_trans. { apply D_finish. }
  eapply progress_evstep_trans. { apply start_reset', b0_all1, b_add_self. }
  rewrite N.add_0_r.
  follow H. finish.
Qed.

Theorem D_nonhalt : forall m, ~ halts tm (D 0 m).
Proof.
  introv.
  apply progress_nonhalt with (P := fun c => exists m, c = D 0 m).
  - clear m. introv H. destruct H as [m H]. subst.
    destruct (D_next m) as [m' Hrun].
    exists (D 0 m'); eauto.
  - eauto.
Qed.

Lemma enters_D : c0 -->* D 0 1441.
Proof. execute. Qed.

Corollary nonhalt : ~ halts tm c0.
Proof.
  destruct (with_counter _ _ _ enters_D) as [n H].
  eapply skip_halts.
  - eassumption.
  - apply D_nonhalt.
Qed.
