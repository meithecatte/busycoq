(** * Translated Cyclers *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Import Helper.
From BusyCoq Require Import TM.
From BusyCoq Require Import Compute.
Set Default Goal Selector "!".

Section TMs.
  Context {Q Sym : Type}.
  Variable q0 : Q.
  Variable s0 : Sym.

  Variable eqb_sym : Sym -> Sym -> bool.
  Variable eqb_sym_spec : forall a b, reflect (a = b) (eqb_sym a b).

  Variable eqb_q : Q -> Q -> bool.
  Variable eqb_q_spec : forall a b, reflect (a = b) (eqb_q a b).

  Notation TM := (TM Q Sym).
  Notation tape := (tape Sym).
  Notation ctape := (ctape Sym).
  Notation c0 := (c0 q0 s0).
  Notation starting := (starting q0 s0).
  Notation cmultistep := (cmultistep s0).
  Notation eqb := (eqb s0 eqb_sym eqb_q).
  Notation lift := (lift s0).
  Notation left := (left s0).
  Notation right := (right s0).
  Notation empty_side := (empty_side s0 eqb_sym).
  Notation eqb_side := (eqb_side s0 eqb_sym).
  Notation lift_side := (lift_side s0).
  Notation lift_tape := (lift_tape s0).

(** [EqTake] holds if the first [n] symbols on a particular side of the
    tape match. *)
Fixpoint EqTake (n : nat) (xs ys : Stream Sym): Prop :=
  match n with
  | 0 => True
  | S n =>
    match xs, ys with
    | Cons x xs, Cons y ys => x = y /\ EqTake n xs ys
    end
  end.

Lemma EqTake_refl : forall n xs, EqTake n xs xs.
Proof.
  induction n; introv.
  - exact I.
  - destruct xs as [x xs].
    simpl. auto.
Qed.

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

Definition eqb_take (n : nat) (xs ys : list Sym) : bool :=
  eqb_side (firstn n xs) (firstn n ys).

Lemma eqb_take_cons : forall n x y xs xs',
  eqb_take (S n) (x :: xs) (y :: xs') = eqb_sym x y && eqb_take n xs xs'.
Proof.
  reflexivity.
Qed.

Lemma empty_side_firstn : forall n xs,
  reflect (EqTake n (lift_side xs) (const s0)) (empty_side (firstn n xs)).
Admitted.

Lemma eqb_take_spec : forall n xs ys,
  reflect (EqTake n (lift_side xs) (lift_side ys)) (eqb_take n xs ys).
Proof.
  induction n; introv.
  - apply ReflectT. exact I.
  - destruct xs as [| x xs].
    + unfold eqb_take. rewrite firstn_nil. apply iff_reflect.
      rewrite EqTake_sym_iff. apply reflect_iff.
      apply empty_side_firstn.
    + destruct ys as [| y ys].
      * unfold eqb_take. rewrite firstn_nil. apply empty_side_firstn.
      * rewrite eqb_take_cons.
        specialize (IHn xs ys). apply reflect_iff in IHn. simpl.
        apply iff_reflect. rewrite IHn, andb_true_iff.
        apply ZifyClasses.and_morph. (* fuck it *)
        ** apply reflect_iff, eqb_sym_spec.
        ** apply iff_refl.
Qed.

(** [EqLimit] checks that the tapes match if you don't look more
    than [n] steps left. *)
Definition EqLimit (n : nat) (t t' : tape): Prop :=
  match t, t' with
  | l {{s}} r, l' {{s'}} r' =>
    EqTake n l l' /\ s = s' /\ r = r'
  end.

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

Lemma EqLimit_refl : forall n t, EqLimit n t t.
Proof.
  intros n [[l s] r].
  repeat split.
  apply EqTake_refl.
Qed.

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
  split; try assumption.
  eapply EqTake_less; eassumption.
Qed.

Definition eqb_limit (n : nat) (t t' : ctape) : bool :=
  match t, t' with
  | l {{s}} r, l' {{s'}} r' =>
    eqb_take n l l' && eqb_sym s s' && eqb_side r r'
  end.

Lemma eqb_limit_spec : forall n t t',
  reflect (EqLimit n (lift_tape t) (lift_tape t')) (eqb_limit n t t').
Proof.
  introv.
  destruct t as [[l s] r].
  destruct t' as [[l' s'] r'].
  apply iff_reflect. simpl.
  repeat rewrite andb_true_iff. rewrite and_assoc.
  apply ZifyClasses.and_morph.
  { apply reflect_iff, eqb_take_spec. }
  apply ZifyClasses.and_morph.
  - apply reflect_iff, eqb_sym_spec.
  - apply reflect_iff, eqb_side_spec, eqb_sym_spec.
Qed.

(** We define a refinement of the Turing machine step relation,
    that makes sure we don't go further left than a specified point
    on the tape. *)
Reserved Notation "c =[ tm ]=> c'" (at level 40).

Inductive lstep (tm : TM) : nat * (Q * tape) -> nat * (Q * tape) -> Prop :=
  | lstep_left k q q' s s' l r :
    tm (q, s) = Some (s', L, q') ->
    (S k, q; l {{s}} r) =[ tm ]=> (k, q'; (move_left (l {{s'}} r)))
  | lstep_right k q q' s s' l r :
    tm (q, s) = Some (s', R, q') ->
    (k, q; l {{s}} r) =[ tm ]=> (S k, q'; (move_right (l {{s'}} r)))

  where "c =[ tm ]=> c'" := (lstep tm c c').

(** And the indexed multistep relation: *)
Reserved Notation "c =[ tm ]=>* n / c'" (at level 40, n at next level).

Inductive lmultistep (tm : TM)
    : nat -> nat * (Q * tape) -> nat * (Q * tape) -> Prop :=
  | lmultistep_0 c : c =[ tm ]=>* 0 / c
  | lmultistep_S n c c' c'' :
    c  =[ tm ]=>  c' ->
    c' =[ tm ]=>* n / c'' ->
    c  =[ tm ]=>* S n / c''

  where "c =[ tm ]=>* n / c'" := (lmultistep tm n c c').

Arguments move_left : simpl never.
Arguments move_right : simpl never.

Lemma lstep_EqLimit : forall tm k q t1 t2 k' q' t1',
  EqLimit k t1 t2 ->
  (k, q; t1) =[ tm ]=> (k', q'; t1') ->
  exists t2', EqLimit k' t1' t2' /\ (k, q; t2) =[ tm ]=> (k', q'; t2').
Proof.
  introv Heq Hstep.
  destruct t1 as [[l1 s1] r1].
  destruct t2 as [[l2 s2] r2].
  destruct Heq as [Heq [Es Er]].
  subst s2 r2. rename s1 into s, r1 into r.
  inverts Hstep as Htm.
  - exists (move_left (l2 {{s'}} r)). split.
    + apply EqLimit_move_left. repeat split. assumption.
    + apply lstep_left. assumption.
  - exists (move_right (l2 {{s'}} r)). split.
    + apply EqLimit_move_right. repeat split. assumption.
    + apply lstep_right. assumption.
Qed.

Lemma lmultistep_EqLimit : forall tm n k q t1 t2 k' q' t1',
  EqLimit k t1 t2 ->
  (k, q; t1) =[ tm ]=>* n / (k', q'; t1') ->
  exists t2', EqLimit k' t1' t2' /\ (k, q; t2) =[ tm ]=>* n / (k', q'; t2').
Proof.
  induction n; introv Heq Hexec; inverts Hexec as Hstep Hrest.
  - exists t2. split.
    + assumption.
    + constructor.
  - destruct c' as [kk [qq tt1]].
    eapply lstep_EqLimit in Hstep; try exact Heq.
    destruct Hstep as [tt2 [Heqq Hstep]].
    eapply IHn in Hrest; try exact Heqq.
    destruct Hrest as [t2' [Heq' Hrest]].
    exists t2'. split.
    + assumption.
    + eapply lmultistep_S; eassumption.
Qed.

Lemma lstep_step : forall tm k c k' c',
  (k, c) =[ tm ]=> (k', c') ->
  c -[ tm ]-> c'.
Proof.
  introv H. inverts H as Htm; constructor; assumption.
Qed.

Lemma lmultistep_multistep : forall tm n k c k' c',
  (k, c) =[ tm ]=>* n / (k', c') ->
  c -[ tm ]->* n / c'.
Proof.
  induction n; introv H; inverts H as Hstep Hrest.
  - apply multistep_0.
  - destruct c'0 as [kk cc].
    apply lstep_step in Hstep.
    apply IHn in Hrest.
    eapply multistep_S; eassumption.
Qed.

(** This allows us to describe the behavior of a translated cycler: *)
Lemma tcycle_chain : forall tm n k k' q t t' i,
  (k, q; t) =[ tm ]=>* n / (k + k', q; t') ->
  EqLimit k t t' ->
  exists t'', EqLimit k t t'' /\ q; t -[ tm ]->* (i * n) / q; t''.
Proof.
  introv Hexec Heq.
  induction i.
  - exists t. split.
    + apply EqLimit_refl.
    + apply multistep_0.
  - destruct IHi as [t1 [Heq1 Hexec1]].
    apply lmultistep_EqLimit with (t2 := t1) in Hexec; try exact Heq1.
    destruct Hexec as [t2 [Heq2 Hexec2]].
    eexists t2. split.
    + apply EqLimit_less in Heq2.
      eauto using EqLimit_trans.
    + apply lmultistep_multistep in Hexec2.
      simpl. rewrite Nat.add_comm.
      eauto using multistep_trans.
Qed.

Theorem tcycle_nonhalting : forall tm n k k' q t t',
  (k, q; t) =[ tm ]=>* n / (k + k', q; t') ->
  EqLimit k t t' ->
  n > 0 ->
  ~ halts tm (q; t).
Proof.
  introv Hrun Heq Hgt0 Hhalt.
  destruct Hhalt as [h Hhalt].
  apply (eventually_exceeds n h) in Hgt0.
  destruct Hgt0 as [i Hexceeds].
  eapply tcycle_chain in Hrun; try assumption.
  destruct Hrun as [t'' [_ Hrun]].
  eapply exceeds_halt; eassumption.
Qed.

Definition clstep (tm : TM) (c : nat * (Q * ctape))
    : option (nat * (Q * ctape)) :=
  match c with
  | (k, q; l {{s}} r) =>
    match tm (q, s) with
    | None => None
    | Some (s', L, q') =>
      match k with
      | 0 => None
      | S k => Some (k, q'; left (l {{s'}} r))
      end
    | Some (s', R, q') => Some (S k, q'; right (l {{s'}} r))
    end
  end.

Lemma clstep_lstep : forall tm k c k' c',
  clstep tm (k, c) = Some (k', c') ->
  (k, lift c) =[ tm ]=> (k', lift c').
Proof.
  introv H.
  destruct c as [q [[l s] r]].
  simpl. simpl in H.
  destruct (tm (q; s)) as [[[s' []] q1] |] eqn:E; try discriminate.
  - destruct k as [| k]; try discriminate.
    inverts H as; simpl.
    rewrite lift_left. apply lstep_left. assumption.
  - inverts H as; simpl.
    rewrite lift_right. apply lstep_right. assumption.
Qed.

Arguments clstep : simpl never.

Fixpoint clmultistep (tm : TM) (n : nat) (c : nat * (Q * ctape))
    : option (nat * (Q * ctape)) :=
  match n with
  | 0 => Some c
  | S n' =>
    match clstep tm c with
    | Some c' => clmultistep tm n' c'
    | None => None
    end
  end.

Lemma clmultistep_some : forall tm n k c k' c',
  clmultistep tm n (k, c) = Some (k', c') ->
  (k, lift c) =[ tm ]=>* n / (k', lift c').
Proof.
  induction n; introv H; simpl in H.
  - inverts H. apply lmultistep_0.
  - destruct (clstep tm (k; c)) as [[kk cc] |] eqn:E; try discriminate.
    apply IHn in H. apply clstep_lstep in E.
    eauto using lmultistep_S.
Qed.

Definition verify_tcycler (tm : TM) (n0 n1 k : nat) :=
  match cmultistep tm n0 starting with
  | Some c1 =>
    match clmultistep tm n1 (k, c1) with
    | Some (k', c1') =>
      match c1, c1' with
      | q; t, q'; t' =>
        (0 <? n1) && (k <=? k') && eqb_q q q' && eqb_limit k t t'
      end
    | None => false
    end
  | None => false
  end.

Theorem verify_tcycler_correct : forall tm n0 n1 k,
  verify_tcycler tm n0 n1 k = true -> ~ halts tm c0.
Proof.
  introv H. unfold verify_tcycler in H.
  destruct (cmultistep tm n0 starting) as [c1 |] eqn:E0; try discriminate.
  destruct (clmultistep tm n1 (k, c1)) as [[k' c1'] |] eqn:E1; try discriminate.
  destruct c1 as [q t]. destruct c1' as [q' t'].
  destruct (Nat.ltb_spec 0 n1); try discriminate.
  destruct (Nat.leb_spec k k'); try discriminate.
  destruct (eqb_q_spec q q'); try discriminate. subst q'.
  destruct (eqb_limit_spec k t t'); try discriminate.

  apply cmultistep_some in E0.
  apply clmultistep_some in E1.
  eapply skip_halts; try exact E0.
  replace k' with (k + (k' - k)) in E1 by lia.
  eapply tcycle_nonhalting; eassumption.
Qed.

End TMs.
