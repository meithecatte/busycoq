(** * Translated Cyclers *)

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Program.Tactics.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Module TranslatedCyclers (Ctx : Ctx).
  Module Flip := Flip Ctx. Export Flip.

(** [EqTake] holds if the first [n] symbols on a particular side of the
    tape match. *)
Fixpoint EqTake (n : nat) (xs ys : side): Prop :=
  match n with
  | 0 => True
  | S n =>
    match xs, ys with
    | Cons x xs, Cons y ys => x = y /\ EqTake n xs ys
    end
  end.

Arguments EqTake !n !xs !ys.
Arguments firstn [A] !n !l.

Lemma EqTake_0 : forall xs ys, EqTake 0 xs ys.
Proof. constructor. Qed.
Local Hint Immediate EqTake_0 : core.

Lemma EqTake_refl : forall n xs, EqTake n xs xs.
Proof.
  induction n; introv.
  - exact I.
  - destruct xs as [x xs].
    simpl. auto.
Qed.
Local Hint Immediate EqTake_refl : core.

Lemma EqTake_sym : forall n xs ys,
  EqTake n xs ys -> EqTake n ys xs.
Proof.
  induction n; introv H.
  - exact I.
  - destruct xs, ys.
    simpl. simpl in *.
    destruct H. auto.
Qed.

Corollary EqTake_sym_iff : forall n xs ys,
  EqTake n xs ys <-> EqTake n ys xs.
Proof. introv. split; auto using EqTake_sym. Qed.

Lemma EqTake_trans : forall n xs ys zs,
  EqTake n xs ys -> EqTake n ys zs -> EqTake n xs zs.
Proof.
  induction n; introv H1 H2.
  - exact I.
  - destruct xs, ys, zs.
    simpl. simpl in *.
    destruct H1, H2. split.
    + congruence.
    + eauto.
Qed.

Lemma EqTake_less : forall n k xs ys,
  EqTake (n + k) xs ys -> EqTake n xs ys.
Proof.
  induction n; introv H.
  - exact I.
  - destruct xs, ys.
    simpl. simpl in H. destruct H as [E H].
    split; try assumption.
    eapply IHn, H.
Qed.

Local Hint Immediate EqTake_less : core.

Lemma EqTake_firstn : forall n xs ys,
  EqTake n (lift_side xs) (lift_side ys) <->
    lift_side (firstn n xs) = lift_side (firstn n ys).
Proof with intuition; congruence.
  induction n.
  - introv. split; auto.
  - introv. destruct xs; destruct ys; simpl.
    + split; auto.
    + rewrite const_unfold. simpl.
      rewrite (IHn []), firstn_nil. simpl...
    + rewrite const_unfold. simpl.
      rewrite (IHn _ []), firstn_nil. simpl...
    + rewrite IHn...
Qed.

Local Hint Resolve -> EqTake_firstn : core.
Local Hint Resolve <- EqTake_firstn : core.

Program Definition eqb_take (n : nat) (xs ys : list Sym)
    : {EqTake n (lift_side xs) (lift_side ys)}
      + {~ EqTake n (lift_side xs) (lift_side ys)} :=
  Reduce (eqb_side (firstn n xs) (firstn n ys)).

(** [EqLimit] checks that the tapes match if you don't look more
    than [n] steps left. *)
Definition EqLimit (n : nat) (t t' : tape): Prop :=
  match t, t' with
  | l {{s}} r, l' {{s'}} r' =>
    EqTake n l l' /\ s = s' /\ r = r'
  end.

Local Hint Unfold EqLimit : core.

Lemma EqLimit_move_left : forall n t t',
  EqLimit (S n) t t' ->
  EqLimit n (move_left t) (move_left t').
Proof.
  introv H.
  destruct t as [[[u l] s] r].
  destruct t' as [[[u' l'] s'] r'].
  simpl in H. simpl.
  destruct H as [[Eu El] [Es Er]].
  repeat split; try assumption; congruence.
Qed.

Lemma EqLimit_move_right : forall n t t',
  EqLimit n t t' ->
  EqLimit (S n) (move_right t) (move_right t').
Proof.
  introv H.
  destruct t as [[l s] [u r]].
  destruct t' as [[l' s'] [u' r']].
  simpl in H. simpl.
  destruct H as [El [Es Eur]].
  repeat split; try assumption; congruence.
Qed.

Local Hint Resolve EqLimit_move_left EqLimit_move_right : core.

Lemma EqLimit_refl : forall n t, EqLimit n t t.
Proof.
  intros n [[l s] r]. auto.
Qed.

Local Hint Immediate EqLimit_refl : core.

Lemma EqLimit_trans : forall n t1 t2 t3,
  EqLimit n t1 t2 -> EqLimit n t2 t3 -> EqLimit n t1 t3.
Proof.
  intros n [[l1 s1] r1] [[l2 s2] r2] [[l3 s3] r3] H1 H2.
  destruct H1 as [H1a [H1b H1c]].
  destruct H2 as [H2a [H2b H2c]].
  repeat split; try congruence.
  eapply EqTake_trans; eassumption.
Qed.

Lemma EqLimit_less : forall n k t t',
  EqLimit (n + k) t t' -> EqLimit n t t'.
Proof.
  intros n k [[l s] r] [[l' s'] r'] H.
  simpl in H. destruct H.
  eauto.
Qed.

Local Hint Immediate EqLimit_less : core.

Local Obligation Tactic := program_simplify; intuition.

Program Definition eqb_limit (n : nat) (t t' : ctape)
    : {EqLimit n (lift_tape t) (lift_tape t')}
      + {~ EqLimit n (lift_tape t) (lift_tape t')} :=
  match t, t' with
  | l {{s}} r, l' {{s'}} r' =>
    eqb_take n l l' && (eqb_sym s s' && Reduce (eqb_side r r'))
  end.

(** We define a refinement of the Turing machine step relation,
    that makes sure we don't go further left than a specified point
    on the tape. *)
Reserved Notation "c =[ tm ]=> c'" (at level 40).

Inductive lstep (tm : TM) : nat * (Q * tape) -> nat * (Q * tape) -> Prop :=
  | lstep_left k q q' s s' l r :
    tm (q, s) = Some (s', L, q') ->
    (S k, q;; l {{s}} r) =[ tm ]=> (k, q';; move_left (l {{s'}} r))
  | lstep_right k q q' s s' l r :
    tm (q, s) = Some (s', R, q') ->
    (k, q;; l {{s}} r) =[ tm ]=> (S k, q';; move_right (l {{s'}} r))

  where "c =[ tm ]=> c'" := (lstep tm c c').

Local Hint Constructors lstep : core.

(** And the indexed multistep relation: *)
Reserved Notation "c =[ tm ]=>> n / c'" (at level 40, n at next level).

Inductive lmultistep (tm : TM)
    : nat -> nat * (Q * tape) -> nat * (Q * tape) -> Prop :=
  | lmultistep_0 c : c =[ tm ]=>> 0 / c
  | lmultistep_S n c c' c'' :
    c  =[ tm ]=>  c' ->
    c' =[ tm ]=>> n / c'' ->
    c  =[ tm ]=>> S n / c''

  where "c =[ tm ]=>> n / c'" := (lmultistep tm n c c').

Local Hint Constructors lmultistep : core.

Local Arguments move_left : simpl never.
Local Arguments move_right : simpl never.

Lemma lstep_EqLimit : forall tm k q t1 t2 k' q' t1',
  EqLimit k t1 t2 ->
  (k, q;; t1) =[ tm ]=> (k', q';; t1') ->
  exists t2', EqLimit k' t1' t2' /\ (k, q;; t2) =[ tm ]=> (k', q';; t2').
Proof.
  introv Heq Hstep.
  destruct t1 as [[l1 s1] r1].
  destruct t2 as [[l2 s2] r2].
  destruct Heq as [Heq [Es Er]].
  subst s2 r2. rename s1 into s, r1 into r.
  inverts Hstep as Htm.
  - exists (move_left (l2 {{s'}} r)). auto 6.
  - exists (move_right (l2 {{s'}} r)). auto 6.
Qed.

Lemma lmultistep_EqLimit : forall tm n k q t1 t2 k' q' t1',
  (k, q;; t1) =[ tm ]=>> n / (k', q';; t1') ->
  EqLimit k t1 t2 ->
  exists t2', EqLimit k' t1' t2' /\ (k, q;; t2) =[ tm ]=>> n / (k', q';; t2').
Proof.
  induction n; introv Hexec Heq; inverts Hexec as Hstep Hrest.
  - exists t2. auto.
  - destruct c' as [kk [qq tt1]].
    eapply lstep_EqLimit in Hstep; try exact Heq.
    destruct Hstep as [tt2 [Heqq Hstep]].
    eapply IHn in Hrest; try exact Heqq.
    destruct Hrest as [t2' [Heq' Hrest]].
    eauto.
Qed.

Lemma lstep_step : forall tm k c k' c',
  (k, c) =[ tm ]=> (k', c') ->
  c -[ tm ]-> c'.
Proof.
  introv H. inverts H as Htm; constructor; assumption.
Qed.

Local Hint Immediate lstep_step : core.

Lemma lmultistep_multistep : forall tm n k c k' c',
  (k, c) =[ tm ]=>> n / (k', c') ->
  c -[ tm ]->> n / c'.
Proof.
  induction n; introv H; inverts H as Hstep Hrest.
  - auto.
  - destruct c'0 as [kk cc].
    eauto.
Qed.

Local Hint Resolve lmultistep_multistep : core.

(** This allows us to describe the behavior of a translated cycler: *)
Theorem tcycle_nonhalting : forall tm n k k' q t t',
  (k, q;; t) =[ tm ]=>> S n / (k', q;; t') ->
  k <= k' ->
  EqLimit k t t' ->
  ~ halts tm (q;; t).
Proof.
  introv Hrun Hle Heq.
  replace k' with (k + (k' - k)) in * by lia. clear Hle.
  apply progress_nonhalt_cond with (C := fun t0 => q;; t0)
    (P := fun t0 => EqLimit k t t0).
  - intros t0 Ht.
    eapply lmultistep_EqLimit in Hrun; try exact Ht.
    destruct Hrun as [t2 []].
    exists t2. repeat split.
    + eauto.
    + eauto using EqLimit_trans.
  - auto.
Qed.

Local Obligation Tactic := program_simplify; autorewrite with core;
  try (apply lstep_left || apply lstep_right); auto.

Program Definition clstep (tm : TM) (k : nat) (c : Q * ctape)
    : { '(k', c') | (k, lift c) =[ tm ]=> (k', lift c') } + {True} :=
  match c with
  | q;; l {{s}} r =>
    match tm (q, s) with
    | None => !!
    | Some (s', L, q') =>
      match k with
      | 0 => !!
      | S k => [|| (k, q';; left (l {{s'}} r)) ||]
      end
    | Some (s', R, q') => [|| (S k, q';; right (l {{s'}} r)) ||]
    end
  end.

Local Obligation Tactic := program_simplify; eauto.

Program Fixpoint clmultistep (tm : TM) (n : nat) (k : nat) (c : Q * ctape)
    : { '(k', c') | (k, lift c) =[ tm ]=>> n / (k', lift c') } + {True} :=
  match n with
  | 0 => [|| (k, c) ||]
  | S n' =>
    bind (k', c') <-- clstep tm k c;
    bind kc <-- clmultistep tm n' k' c';
    [|| kc ||]
  end.

Local Obligation Tactic := program_simplify;
  eauto 3 using skip_halts, tcycle_nonhalting.

Program Definition verify_tcycler_r (tm : TM) (n0 n1 k : nat)
    : {~ halts tm c0} + {True} :=
  bind q;; t <- cmultistep tm n0 starting;
  bind (k', q';; t') <- clmultistep tm n1 k (q;; t);
  match n1 with
  | 0 => No
  | S n1 => le_dec k k' && (eqb_q q q' && Reduce (eqb_limit k t t'))
  end.

Program Definition verify_tcycler (tm : TM) (d : dir) (n0 n1 k : nat)
    : {~ halts tm c0} + {True} :=
  match d with
  | L => Reduce (verify_tcycler_r (flip tm) n0 n1 k)
  | R => verify_tcycler_r tm n0 n1 k
  end.

End TranslatedCyclers.
