(** * Skelet #33 *)

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
  | E, 0 => Some (1, L, A)  | E, 1 => Some (1, R, E)
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
  L n <{{C}} 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> R m.

Lemma L_inc : forall n r,
  L n <{{C}} r -->* L (N.succ n) {{B}}> r.
Proof.
  destruct n as [|n].
  - triv.
  - induction n; triv.
Qed.

Lemma R_inc_has0 : forall n l,
  has0 n ->
  l << 1 {{E}}> R n -->* l <{{A}} 0 >> R (P n).
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
    follow IHu. { rewrite b_succ; lia. }
    finish.
Qed.

Corollary D_finish : forall n m,
  D n m -->* D (b m + n) (b m :+ m).
Proof. introv. apply D_run. lia. Qed.

Lemma R_inc_all1 : forall n l,
  all1 n ->
  l << 1 {{E}}> R n -->* l <{{C}} R (P n).
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

Definition E n m : Q * tape :=
  K n <{{C}} 1 >> 0 >> 1 >> 0 >> R m.

Theorem start_reset : forall n m,
  all1 m ->
  D n m -->+ E (N.succ n) (P m)~1.
Proof.
  introv H. unfold D.
  follow L_inc. rewrite L_as_K.
  apply evstep_progress; try discriminate.
  execute. follow R_inc_all1.
  execute.
Qed.

Lemma eat_LI : forall l t,
  l << 1 << 0 << 0 << 0 <{{C}} R t -->*
  l <{{C}} R (t~1~1).
Proof. triv. Qed.

Lemma eat_KI : forall l t,
  has0 t ->
  has0 (P t) ->
  l << 0 << 1 << 0 << 0 <{{C}} R t -->*
  l <{{C}} R (P (P t))~0~0.
Proof.
  introv H HP. execute.
  destruct t.
  - follow R_inc_has0. execute.
  - follow R_inc_has0. execute.
    follow R_inc_has0. { inversion HP. exact H1. }
    execute.
  - inversion H.
Qed.

Fixpoint pow4 (k : nat) (n : positive) : positive :=
  match k with
  | O => n
  | S k => pow4 k (n~0~0)
  end.

(* n and l are in the wrong order? *)
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

Lemma LaR_inc : forall l k (n n' : bin k) m,
  has0 m ->
  has0 (P m) ->
  n -S-> n' ->
  Lk n  l <{{C}} 1 >> 0 >> 1 >> 0 >> R m -->*
  Lk n' l <{{C}} 1 >> 0 >> 1 >> 0 >> R (P (P m)).
Proof.
  introv Hm HPm Hn. follow Lk_inc. execute.
  follow R_inc_has0. execute. follow R_inc_has0. execute.
Qed.

Lemma LaR_incs : forall l k u (n n' : bin k) m,
  bin_plus u n n' ->
  (2 * u <= b m)%N ->
  Lk n  l <{{C}} 1 >> 0 >> 1 >> 0 >> R m -->*
  Lk n' l <{{C}} 1 >> 0 >> 1 >> 0 >> R (2 * u :+ m).
Proof.
  introv H.
  generalize dependent m. induction H; introv Hr.
  - finish.
  - follow LaR_inc. { apply bgt0_has0. rewrite b_succ; lia. }
    follow IHbin_plus. { rewrite b_succ; rewrite b_succ; lia. }
    finish.
Qed.

Corollary LaR_max : forall l k m,
  (2 * (pow2 k - 1) <= b m)%N ->
  Lk (bin_min k) l <{{C}} 1 >> 0 >> 1 >> 0 >> R m -->*
  Lk (bin_max k) l <{{C}} 1 >> 0 >> 1 >> 0 >> R (2 * (pow2 k - 1) :+ m).
Proof.
  introv H.
  apply LaR_incs.
  + apply inc_to_max.
  + assumption.
Qed.

Lemma eat_bin_max : forall k l t,
  has0 t ->
  has0 (P t) ->
  Lk (bin_max k) (l << 0 << 1 << 0 << 0) <{{C}} R t -->*
  l <{{C}} 1 >> 0 >> 1 >> 0 >> R (P (pow4 k (P t))).
Proof.
  induction k; introv H HP.
  - follow eat_KI. finish.
  - simpl. follow eat_LI. follow (IHk l (t~1~1)%positive).
    * apply has0_0.
    * finish.
Qed.

Definition f (m : positive) (k : nat) : positive :=
  (2 * (pow2 k - 1) :+ m)~0.

Lemma has0_f : forall m k, has0 (f m k).
Proof. introv. simpl. constructor. Qed.

Local Hint Resolve has0_f : core.

Lemma drop_KI : forall l m k,
  (2 * (pow2 k - 1) <= b m)%N ->
  Lk (bin_min k) (l << 0 << 1 << 0 << 0) <{{C}} 1 >> 0 >> 1 >> 0 >> R m -->*
  l <{{C}} 1 >> 0 >> 1 >> 0 >> R (P (pow4 k (f m k)~1)).
Proof.
  introv H.
  follow LaR_max.
  replace (1 >> 0 >> 1 >> 0 >> R (2 * (pow2 k - 1) :+ m)) with (R (f m k)~0)
    by reflexivity.
  follow eat_bin_max.
  - apply has0_1. apply has0_f.
  - finish.
Qed.

Lemma prepare_K : forall (n : N), (n > 1)%N -> exists (k : nat) (n' : N),
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

Lemma b_pow4_f : forall m k k',
  (b (pow4 k (f m k')~1) > 0)%N.
Proof.
  introv.
  destruct k.
  - simpl b. lia.
  - rewrite b_pow4. simpl b. lia.
Qed.

Lemma b_pow2 : forall k,
  (b (pow2' k) = pow2 k - 1)%N.
Proof.
  unfold pow2.
  induction k; introv; simpl pow2'.
  - trivial.
  - simpl b. rewrite IHk. lia.
Qed.

Lemma pow2_add : forall n m,
  (pow2 (n + m) = pow2 n * pow2 m)%N.
Proof.
  introv. induction n.
  - lia.
  - simpl pow2. rewrite pow2_S, IHn. lia.
Qed.

(* n = 1, or n starts with 11 in binary *)
Inductive leads : N -> Prop :=
  | leads_1: leads 1
  | leads_add1 n: leads n -> leads (2 * n + 1)
  | leads_add0 n: leads n -> (n > 1)%N -> leads (2 * n).

Lemma not_leads_2 : ~ leads 2.
Proof. intro H. inversion H; cases n; lia. Qed.

Lemma leads_add0_rev : forall n,
  leads (2 * n) ->
  leads n.
Proof.
  introv H. inversion H.
  (* why is this proof so awkward? *)
  - cases n; lia.
  - cases n; cases n0; lia.
  - cases n; cases n0; try lia. inversion H0. rewrite <- H4. assumption.
Qed.

Lemma leads_pow2_rev : forall k n,
  leads (pow2 k * n) ->
  leads n.
Proof.
  induction k.
  - introv. replace (pow2 0 * n)%N with n by lia. trivial.
  - introv. replace (pow2 (S k) * n)%N with (2 * (pow2 k * n))%N by lia.
    intro H. apply IHk. apply leads_add0_rev. assumption.
Qed.

Lemma leads_add1_rev : forall n,
  (n > 0)%N ->
  leads (2 * n + 1) ->
  leads n.
Proof.
  introv Hn H. inversion H.
  (* why is this proof so awkward? *)
  - cases n; lia.
  - cases n; cases n0; try lia. inversion H0. rewrite <- H3. assumption.
  - cases n; cases n0; lia.
Qed.

Lemma leads_pow2_sub1 : forall k n,
  leads n ->
  leads (pow2 k * (n + 1) - 1).
Proof.
  introv H. induction k.
  - replace (pow2 0 * (n + 1) - 1)%N with n by lia. assumption.
  - replace (pow2 (S k) * (n + 1) - 1)%N
      with (2 * (pow2 k * (n + 1) - 1) + 1)%N by lia.
    apply leads_add1. assumption.
Qed.

Lemma leads_3_pow2 : forall q r,
  (r < pow2 q)%N ->
  leads (3 * pow2 q + r).
Proof.
  induction q; introv H.
  - rewrite N.lt_1_r in H. rewrite H.
    replace (3 * pow2 0 + 0)%N with (2 * 1 + 1)%N by lia.
    apply leads_add1. apply leads_1.
  - destruct r as [| [r | r |]].
    + replace (3 * pow2 (S q) + 0)%N with (2 * (3 * pow2 q))%N by lia.
      apply leads_add0; try lia.
      replace (3 * pow2 q)%N with (3 * pow2 q + 0)%N by lia.
      apply IHq. lia.
    + replace (3 * pow2 (S q) + N.pos r~1)%N with (2 * (3 * pow2 q + N.pos r) + 1)%N by lia.
      apply leads_add1. apply IHq. lia.
    + replace (3 * pow2 (S q) + N.pos r~0)%N with (2 * (3 * pow2 q + N.pos r))%N by lia.
      apply leads_add0; try lia. apply IHq. lia.
    + replace (3 * pow2 (S q) + 1)%N with (2 * (3 * pow2 q) + 1)%N by lia.
      apply leads_add1.
      replace (3 * pow2 q)%N with (3 * pow2 q + 0)%N by lia.
      apply IHq. lia.
Qed.

Theorem step_reset_odd : forall n m,
  E (2 * n + 1) m -->* E n m~1~0.
Proof. introv. destruct n; execute. Qed.

Theorem step_reset : forall n m,
  (n > 1)%N ->
  (exists q r, b m = 3 * pow2 q + r /\ 2 * n <= r < pow2 q)%N ->
  leads n ->
  exists (n' : N) (m' : positive),
  E n m -->* E n' m' /\
  (n' > 0)%N /\ (n' < n)%N /\
  (exists q r, b m' = 3 * pow2 q + r /\ 2 * n' <= r < pow2 q)%N /\
  leads n'.
Proof.
  introv Hgt1 [q [r [Hinv1a [Hinv1b Hinv1c]]]] Hinvariant2.
  destruct (prepare_K n Hgt1) as [k [n' [EK En']]].
  assert (Hn': (n' > 0)%N).
  { destruct n'; try lia. destruct k; try lia.
    simpl in En'. rewrite En' in Hinvariant2.
    replace (pow2 (S k)) with (pow2 k * 2)%N in Hinvariant2 by lia.
    apply leads_pow2_rev in Hinvariant2.
    contradict (not_leads_2 Hinvariant2). }
  exists n', (P (pow4 k (f m k)~1)). repeat split.
  - unfold E. rewrite EK.
    follow drop_KI. { lia. }
    finish.
  - assumption.
  - rewrite En'. nia.
  - exists (q + 2 * k + 2).
    exists (pow2 (2 * k + 2) * (r - 2 * (pow2 k - 1)) + 3 * pow2 (2 * k) - 2)%N.
    repeat constructor.
    + destruct k. { simpl b. rewrite Hinv1a. repeat rewrite pow2_add. lia. }
      simpl pow4. rewrite pow4_shift. simpl b. rewrite b_pow4.
      replace (b (f m (S k))~1)
        with (4 * b (2 * (pow2 (S k) - 1) :+ m) + 2)%N by (simpl b; lia).
      rewrite b_add by lia. rewrite Hinv1a.
      repeat rewrite pow2_add. replace (2 * S k) with (S (S (2 * k))) by lia. nia.
    + transitivity r; try nia.
      transitivity (pow2 (2 * k + 2) * (r - 2 * (pow2 k - 1)))%N; try lia.
      assert (2 <= pow2 (2 * k + 2))%N. { rewrite pow2_add. lia. }
      transitivity (2 * (r - 2 * (pow2 k - 1)))%N; nia.
    + repeat rewrite pow2_add. nia. (* nia is so overpowered *)
  - apply leads_add1_rev; try lia. apply (leads_pow2_rev k).
    replace (pow2 k + pow2 (S k) * n')%N with (pow2 k * (2 * n' + 1))%N in En' by lia.
    rewrite <- En'. assumption.
Qed.

Lemma n0_1_2 : forall n,
  (n = 0)%N \/ (n = 1)%N \/ (n > 1)%N.
Proof.
  introv.
  destruct (N.le_gt_cases n 1) as [H | H].
  - rewrite N.le_1_r in H. destruct H.
    + left. assumption.
    + right. left. assumption.
  - right. right. exact (N.lt_gt _ _ H).
Qed.

Corollary do_reset : forall n m,
  (n >= 1)%N ->
  (exists q r, b m = 3 * pow2 q + r /\ 2 * n <= r < pow2 q)%N ->
  leads n ->
  exists m',
  E n m -->* E 1 m' /\
  leads (b m').
Proof.
  induction n using N_strong_induction.
  introv Hge1 Hinvariant Hinvariant2.
  apply N.ge_le, N.lt_eq_cases in Hge1.
  destruct Hge1 as [Hgt1 | Heq1]. 2: {
    exists m. rewrite Heq1. constructor; auto.
    destruct Hinvariant as [q [r [Hinv1a [Hinv1b Hinv1c]]]].
    rewrite Hinv1a. apply leads_3_pow2. assumption. }
  destruct (step_reset n m (N.lt_gt _ _ Hgt1) Hinvariant Hinvariant2)
    as [n' [m' [Hsteps [Hpos [Hless' [Hinvariant' Hinvariant2']]]]]].
  destruct (n0_1_2 n') as [n0' | [n1' | n2']].
  - rewrite n0' in Hpos. contradict (N.lt_irrefl _ (N.gt_lt _ _ Hpos)).
  - rewrite n1' in Hsteps. exists m'.
    constructor. { exact Hsteps. }
    destruct Hinvariant' as [q' [r' [Hinv1a' [Hinv1b' Hinv1c']]]].
    rewrite Hinv1a'. apply leads_3_pow2. assumption.
  - assert (G: exists m'', E n' m' -->* E 1 m'' /\ leads (b m'')).
    { apply H; try assumption. lia. }
    destruct G as [m'' [G1 G2]]. exists m''.
    constructor; try assumption.
    follow Hsteps. apply G1.
Qed.

Lemma all1_P_pow2 : forall n,
  all1 n ->
  exists k,
  (P n = pow2' k)%N.
Proof.
  induction n; introv H.
  - inversion H. destruct (IHn H1) as [k Hk]. exists (S k). lia.
  - inversion H.
  - exists 1%nat. reflexivity.
Qed.

Theorem E_next : forall m,
  leads (b m) ->
  exists m',
  E 1 m -->+ E 1 m' /\
  leads (b m').
Proof.
  introv Hinvariant.
  assert (H: exists m', E (b m) (P (b m~1 :+ m~1))~1~1~0 -->* E 1 m' /\
    leads (b m')).
  { apply do_reset; try assumption.
    - inversion Hinvariant; try lia. cases n; lia.
    - assert (Hk: exists k, (P (b m~1 :+ m~1) = pow2' k)%N).
      { apply all1_P_pow2. auto. }
      destruct Hk as [k Hk].
      exists (S k), (pow2 (S k) - 7)%N. repeat constructor.
      + rewrite Hk. simpl b. rewrite b_pow2. lia.
      + rewrite pow2_S. unfold pow2. rewrite <- Hk. simpl b. lia. (* found by guess & check *)
      + lia. }
  destruct H as [m' [H Hinvariant']]. exists m'. constructor; try assumption.
  eapply (evstep_progress_trans _ _ (D 0 m~1)). { execute. }
  eapply evstep_progress_trans. { apply D_finish. }
  eapply progress_evstep_trans. { apply start_reset. auto. }
  replace (N.succ (b m~1 + 0)) with (2 * (b m) + 1)%N by (simpl b; lia).
  follow step_reset_odd.
  assumption.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (E 1 17). { execute. }
  apply progress_nonhalt with
    (P := fun c => exists m, E 1 m = c /\ leads (b m)).
  - intros c [m [Heq Hleads]]. subst c.
    destruct (E_next m Hleads) as [m' [Hsteps Hleads']].
    eauto.
  - exists 17%positive. repeat split.
    simpl b. replace 14%N with (2 * (2 * (2 * 1 + 1) + 1))%N by lia.
    apply leads_add0; try lia. apply leads_add1. apply leads_add1. apply leads_1.
Qed.
