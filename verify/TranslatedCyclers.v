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

(** [EqLimit] checks that the tapes match if you don't look more
    than [n] steps left. *)
Definition EqLimit (n : nat) (t t' : tape): Prop :=
  match t, t' with
  | l {{s}} r, l' {{s'}} r' =>
    dfirstn n l = dfirstn n l' /\ s = s' /\ r = r'
  end.

Local Hint Unfold EqLimit : core.

Lemma EqLimit_move_left : forall n t t',
  EqLimit (S n) t t' ->
  EqLimit n (move_left t) (move_left t').
Proof.
  introv H.
  destruct t as [[[| u l] s] r];
    destruct t' as [[[| u' l'] s'] r'];
    destruct H as [Hl [Hs Hr]];
    simpl in Hl; try congruence;
    simpl; repeat split; congruence.
Qed.

Lemma EqLimit_move_right : forall n t t',
  EqLimit n t t' ->
  EqLimit (S n) (move_right t) (move_right t').
Proof.
  introv H.
  destruct t as [[l s] r].
  destruct t' as [[l' s'] r'].
  destruct H as [Hl [Hs Hr]].
  simpl. repeat split; congruence.
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
Qed.

Lemma EqLimit_less : forall n k t t',
  EqLimit (n + k) t t' -> EqLimit n t t'.
Proof.
  intros n k [[l s] r] [[l' s'] r'] H.
  simpl in H. destruct H.
  split; eauto.
Qed.

Local Hint Immediate EqLimit_less : core.

Local Obligation Tactic := program_simplify; intuition.

Program Definition eqb_limit (n : nat) (t t' : tape)
    : {EqLimit n t t'} + {~ EqLimit n t t'} :=
  match t, t' with
  | l {{s}} r, l' {{s'}} r' =>
    eqb_side (dfirstn n l) (dfirstn n l') &&
      (eqb_sym s s' && Reduce (eqb_side r r'))
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
  destruct t1 as [[l s] r].
  destruct t2 as [[l' s'] r'].
  destruct Heq as [Heq [Es Er]].
  subst s' r'.
  inverts Hstep as Htm.
  - exists (move_left (l' {{s'}} r)). auto 6.
  - exists (move_right (l' {{s'}} r)). auto 6.
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
  apply progress_nonhalt with (P := fun '(q0, t0) => q = q0 /\ EqLimit k t t0).
  - intros [q0 t0] [Hq Ht]. subst q0.
    eapply lmultistep_EqLimit in Hrun; try exact Ht.
    destruct Hrun as [t2 []].
    exists (q, t2). repeat split.
    + apply EqLimit_trans with t'; eauto.
    + eauto.
  - auto.
Qed.

Local Obligation Tactic := program_simplify;
  try (apply lstep_left || apply lstep_right); auto.

Program Definition clstep (tm : TM) (k : nat) (c : Q * tape)
    : { '(k', c') | (k, c) =[ tm ]=> (k', c') } + {True} :=
  match c with
  | q;; l {{s}} r =>
    match tm (q, s) with
    | None => !!
    | Some (s', L, q') =>
      match k with
      | 0 => !!
      | S k => [|| (k, q';; move_left (l {{s'}} r)) ||]
      end
    | Some (s', R, q') => [|| (S k, q';; move_right (l {{s'}} r)) ||]
    end
  end.

Local Obligation Tactic := program_simplify; eauto.

Program Fixpoint clmultistep (tm : TM) (n : nat) (k : nat) (c : Q * tape)
    : { '(k', c') | (k, c) =[ tm ]=>> n / (k', c') } + {True} :=
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
  bind q;; t <- cmultistep tm n0 c0;
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
