(** * Skelet #35 *)

(** Note: this is mostly a copy of Skelet34.v – the machines are similar
    enough that the proofs check out. *)

From BusyCoq Require Import Individual52 FixedBin ShiftOverflow. Import Individual52.
From Coq Require Import PeanoNat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, C)
  | B, 0 => Some (0, R, C)  | B, 1 => Some (0, R, B)
  | C, 0 => Some (1, L, D)  | C, 1 => Some (0, L, A)
  | D, 0 => Some (1, L, E)  | D, 1 => None
  | E, 0 => Some (1, L, A)  | E, 1 => Some (0, L, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

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
  induction u using N.peano_ind; introv H.
  - finish.
  - follow D_inc.
    replace (N.succ u + n)%N with (u + N.succ n)%N by lia.
    replace (N.succ u :+ m)%N with (u :+ P m)%N by lia.
    apply IHu. rewrite b_succ; lia.
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

Lemma LaR_incs : forall l k u (n n' : bin k) a m,
  bin_plus u n n' ->
  (u <= b m)%N ->
  Lk n  l <{{C}} 1 >> 0 >> 1 >> a >> R m -->*
  Lk n' l <{{C}} 1 >> 0 >> 1 >> a >> R (u :+ m).
Proof.
  introv H.
  generalize dependent m. induction H; introv Hr.
  - finish.
  - follow LaR_inc.
    follow IHbin_plus. { rewrite b_succ; lia. }
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

Local Hint Resolve has0_f : core.

Lemma f_lt : forall m a k, exists x,
  (P (f m a k) = 4 * (pow2 k - 1 :+ m) + x /\
  x <= 3)%positive.
Proof.
  introv. destruct a.
  - exists 1%positive. unfold f. lia.
  - exists 3%positive. unfold f. lia.
Qed.

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
    + lia.
  - exists O, N0. repeat split.
    simpl. rewrite const_unfold at 1. reflexivity.
Qed.

Lemma pow4_shift : forall k n,
  (pow4 k n~0~0 = (pow4 k n)~0~0)%positive.
Proof.
  induction k; introv.
  - reflexivity.
  - simpl. rewrite IHk. reflexivity.
Qed.

Lemma b_pow4 : forall k n,
  (b (pow4 k n) = pow2 (2 * k) * (b n + 1) - 1)%N.
Proof.
  unfold pow2.
  induction k; introv; simpl pow4; simpl pow2'.
  - lia.
  - rewrite pow4_shift. simpl b.
    rewrite IHk.
    rewrite <- plus_n_Sm.
    lia.
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
  - rewrite En'. nia.
  - destruct (f_lt m a k) as [x [E Hx]].
    rewrite b_pow4, E.
    replace (4 * (pow2 k - 1 :+ m) + x)%positive
      with (N.pos x :+ 4 * (pow2 k - 1 :+ m))
      by lia.
    rewrite b_add by (simpl; lia).
    replace (b (4 * (pow2 k - 1 :+ m)))
      with (N.succ_double (N.succ_double (b (pow2 k - 1 :+ m))))
      by reflexivity.
    transitivity (b (pow2 k - 1 :+ m)).
    + rewrite b_add by lia. nia.
    + nia.
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
    rewrite b0_succ.
    - lia.
    - apply b_add_self. }
  destruct H as [m' H]. exists m'.
  eapply evstep_progress_trans. { apply D_finish. }
  eapply progress_evstep_trans. { apply start_reset'. auto. }
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
