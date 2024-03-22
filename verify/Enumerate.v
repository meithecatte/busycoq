(** * Enumerate: TNF enumeration *)

From Coq Require Import Lists.Streams.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From BusyCoq Require Export Permute.
From BusyCoq Require Import Pigeonhole.
Set Default Goal Selector "!".

From Coq Require Import Arith.PeanoNat.

Module Enumerate (Ctx : Ctx).
  Module Permute := Permute Ctx. Export Permute.

(** To justify only enumerating machines that start with 1RB, we need
    to prove that all the other machines won't take many steps to write
    their first 1 (or a non-zero symbol in the case of non-binary Turing
    machines). *)

Inductive ReachedNZ (tm : TM) : Q -> Prop :=
  | reached_halt q :
    tm (q, s0) = None ->
    ReachedNZ tm q
  | reached_nz q s d q' :
    tm (q, s0) = Some (s, d, q') ->
    s <> s0 ->
    ReachedNZ tm q.

(** [tm] visits the sequence of states [q :: qs] before writing its first
    non-zero symbol. *)
Inductive zvisits (tm : TM) : Q -> list Q -> Prop :=
  | zvisits_done q :
    ReachedNZ tm q ->
    zvisits tm q []
  | zvisits_step q d q' qs :
    tm (q, s0) = Some (s0, d, q') ->
    zvisits tm q' qs ->
    zvisits tm q (q' :: qs).

Local Hint Constructors ReachedNZ zvisits : core.

(** This sequence is unique for each [q]. *)
Lemma zvisits_unique : forall {tm qs qs' q},
  zvisits tm q qs ->
  zvisits tm q qs' ->
  qs = qs'.
Proof.
  induction qs as [| a qs IH]; introv H1 H2;
    inverts H1; inverts H2;
    try lazymatch goal with
    | H: ReachedNZ _ _ |- _ => inverts H
    end;
    try congruence.
  assert (a = q'). { congruence. }
  subst. f_equal. eauto.
Qed.

(** Therefore, [q] cannot occur in [qs] – otherwise a suffix would
    violate uniqueness. *)
Lemma zvisits_In_skipn : forall {tm qs q q'},
  zvisits tm q qs ->
  In q' qs ->
  exists n, zvisits tm q' (skipn (S n) qs).
Proof.
  induction qs as [| a qs IH].
  - contradiction.
  - introv Hvisits Hin. inverts Hvisits as Etm Hvisits.
    destruct Hin as [E | Hin].
    + subst a. exists 0. auto.
    + specialize (IH _ _ Hvisits Hin).
      destruct IH as [n IH].
      exists (S n). auto.
Qed.

Lemma zvisits_In : forall tm qs q,
  zvisits tm q qs ->
  ~ In q qs.
Proof.
  introv H1 Hin.
  destruct (zvisits_In_skipn H1 Hin) as [n H2].
  pose proof (zvisits_unique H1 H2) as E.
  assert (E': length qs = length (skipn (S n) qs)).
  { f_equal. exact E. }
  rewrite skipn_length in E'.
  assert (Hqs : length qs = 0) by lia.
  apply length_zero_iff_nil in Hqs. subst qs.
  exact Hin.
Qed.

(** Hence, elements in [qs] do not repeat. *)
Lemma zvisits_not_repeats : forall tm qs q,
  repeats qs ->
  ~ zvisits tm q qs.
Proof.
  introv H. generalize dependent q.
  induction H; introv Hvisits.
  - (* repeats_head *)
    inverts Hvisits as E Hvisits.
    apply zvisits_In in Hvisits. contradiction.
  - (* repeats_cons *)
    inverts Hvisits as E Hvisits.
    apply IHrepeats in Hvisits. contradiction.
Qed.

(** We can say more: the elements in [q :: qs] do not repeat. *)
Lemma zvisits_not_repeats' : forall tm qs q,
  zvisits tm q qs ->
  ~ repeats (q :: qs).
Proof.
  introv Hvisits Hrepeats.
  inverts Hrepeats as H.
  - (* repeats_head *)
    apply zvisits_In in Hvisits. contradiction.
  - (* repeats_cons *)
    eapply zvisits_not_repeats in H. eauto.
Qed.

Proposition zvisits_bound : forall tm q qs,
  zvisits tm q qs ->
  length qs < length all_qs.
Proof.
  introv Hvisits.
  enough (~ length all_qs <= length qs) by lia.
  introv Hpigeon.
  assert (Hrepeats : repeats (q :: qs)).
  { apply pigeonhole_principle with all_qs.
    - apply <- Forall_forall. auto.
    - simpl. lia. }
  apply zvisits_not_repeats' in Hvisits.
  contradiction.
Qed.

(** Any halting machine has a [zvisits] sequence. *)
Proposition halts_zvisits : forall tm q,
  halts tm (q;; tape0) ->
  exists qs, zvisits tm q qs.
Proof.
  introv Hhalts.
  destruct Hhalts as [k [ch [Hsteps Hhalted]]].
  remember (q;; tape0) as c.
  generalize dependent q.
  induction Hsteps as [| n c c' ch Hstep Hrest IH]; introv E; subst c.
  - eauto.
  - inverts Hstep as Etm;
    destruct (eqb_sym s' s0) as [E | E]; subst; eauto;
    fold tape0 in *; autorewrite with tape in *;
    specialize (IH Hhalted q' eq_refl);
    destruct IH as [qs IH]; eauto.
Qed.

Lemma zero_step : forall tm q d q',
  tm (q, s0) = Some (s0, d, q') ->
  q;; tape0 -[ tm ]-> q';; tape0.
Proof with constructor; assumption.
  introv E.
  destruct d.
  - rewrite <- move_left_tape0 at 2...
  - rewrite <- move_right_tape0 at 2...
Qed.

Local Hint Resolve zero_step : core.

(** [zvisits] corresponds to what the Turing machine actually does *)
Proposition zvisits_steps : forall tm q qs,
  zvisits tm q qs ->
  exists q', q;; tape0 -[ tm ]->> length qs / q';; tape0 /\ ReachedNZ tm q'.
Proof.
  introv H. induction H.
  - eauto.
  - destruct IHzvisits as [q'' [IH1 IH2]].
    simpl. eauto.
Qed.

Fixpoint find_zvisits (tm : TM) (q : Q) (n : nat) : option (list Q) :=
  match n with
  | 0 => None
  | S n =>
    match tm (q, s0) with
    | Some (s, d, q') =>
      if eqb_sym s s0 then
        match find_zvisits tm q' n with
        | Some qs => Some (q' :: qs)
        | None => None
        end
      else
        Some []
    | None => Some []
    end
  end.

Proposition find_zvisits_some : forall tm q qs n,
  zvisits tm q qs ->
  length qs < n ->
  find_zvisits tm q n = Some qs.
Proof.
  introv H. generalize dependent n.
  induction H; introv Hlen;
    destruct n; try lia.
  - simpl. inverts H as H; rewrite H; auto.
    destruct (eqb_sym s s0); [contradiction | reflexivity].
  - simpl. rewrite H.
    destruct (eqb_sym s0 s0); try congruence.
    simpl in Hlen.
    rewrite IHzvisits; auto. lia.
Qed.

Corollary find_zvisits_some' : forall tm q qs,
  zvisits tm q qs ->
  find_zvisits tm q (length all_qs) = Some qs.
Proof.
  introv H.
  apply find_zvisits_some; eauto using zvisits_bound.
Qed.

Fixpoint max_zvisits (tm : TM) (qs : list Q) : nat :=
  match qs with
  | [] => 0
  | q :: qs =>
    match find_zvisits tm q (length all_qs) with
    | None => max_zvisits tm qs
    | Some xs => max (length xs) (max_zvisits tm qs)
    end
  end.

Lemma max_zvisits_le : forall tm q qs,
  max_zvisits tm qs <= max_zvisits tm (q :: qs).
Proof.
  introv. simpl.
  destruct (find_zvisits tm q (length all_qs)); lia.
Qed.

Lemma max_zvisits_spec : forall tm qs q qs',
  zvisits tm q qs' ->
  In q qs ->
  length qs' <= max_zvisits tm qs.
Proof.
  induction qs; introv Hvisits Hin.
  - destruct Hin.
  - destruct Hin as [Hin | Hin].
    + subst a.
      apply find_zvisits_some' in Hvisits.
      simpl. rewrite Hvisits. lia.
    + transitivity (max_zvisits tm qs); eauto using max_zvisits_le.
Qed.

(** Structure of the enumeration tree *)
Definition is_child_of (tm tm' : TM) :=
  forall qs, tm' qs = None \/ tm qs = tm' qs.

Lemma child_trans : forall tm tm' tm'',
  is_child_of tm  tm'  ->
  is_child_of tm' tm'' ->
  is_child_of tm  tm''.
Proof.
  introv H1 H2.
  intro qs.
  destruct (H2 qs). { auto. }
  destruct (H1 qs); constructor; congruence.
Qed.

Lemma child_step : forall tm tm' c c',
  is_child_of tm tm' ->
  c -[ tm' ]-> c' ->
  c -[ tm  ]-> c'.
Proof.
  introv Hchild Hstep.
  inverts Hstep;
    destruct (Hchild (q, s));
    constructor; congruence.
Qed.

Local Hint Resolve child_step : core.

Lemma child_multistep : forall tm tm' c c' n,
  is_child_of tm tm' ->
  c -[ tm' ]->> n / c' ->
  c -[ tm  ]->> n / c'.
Proof.
  introv Hchild Hsteps.
  induction Hsteps; eauto.
Qed.

Lemma child_evstep : forall tm tm' c c',
  is_child_of tm tm' ->
  c -[ tm' ]->* c' ->
  c -[ tm  ]->* c'.
Proof.
  introv Hchild Hsteps.
  induction Hsteps; eauto.
Qed.

Lemma parent_step : forall tm tm' c c',
  is_child_of tm tm' ->
  c -[ tm  ]-> c' ->
  c -[ tm' ]-> c' \/ halted tm' c.
Proof.
  introv Hchild Hstep.
  inverts Hstep;
    destruct (Hchild (q, s)); auto;
    left; constructor; congruence.
Qed.

Lemma parent_multistep : forall tm tm' c c' n,
  is_child_of tm tm' ->
  c -[ tm  ]->> n / c' ->
  c -[ tm' ]->> n / c' \/ halts tm' c.
Proof.
  introv Hchild Hsteps.
  induction Hsteps.
  - auto.
  - eapply parent_step in H. 2: eassumption.
    destruct H; auto.
    destruct IHHsteps; eauto.
Qed.

Lemma parent_halted : forall tm tm' c,
  is_child_of tm tm' ->
  halted tm c ->
  halted tm' c.
Proof.
  introv Hchild Hhalted.
  destruct c as [q [[l s] r]]. simpl in *.
  destruct (Hchild (q, s)); congruence.
Qed.

Local Hint Resolve parent_halted : core.

Lemma child_nonhalt : forall tm tm' c,
  is_child_of tm tm' ->
  ~ halts tm' c ->
  ~ halts tm  c.
Proof.
  introv Hchild Hnonhalt Hhalt.
  destruct Hhalt as [n [ch [Hsteps Hhalted]]].
  eapply parent_multistep in Hsteps. 2: eassumption.
  destruct Hsteps; eauto 8.
Qed.
