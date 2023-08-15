(** * TM: Definition of Turing Machines *)

From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
From BusyCoq Require Export Helper.
Set Default Goal Selector "!".

(** The direction a Turing machine can step in. *)
Inductive dir : Type := L | R.

(** We parametrize over... *)
Module Type Ctx.
  (** the type of states [Q]; *)
  Parameter Q : Type.
  (** the type of tape symbols [Sym]; *)
  Parameter Sym : Type.
  (** the starting state [q0]; *)
  Parameter q0 : Q.
  (** and the blank symbol [s0]. *)
  Parameter s0 : Sym.

  (** Moreover we want decidable equality for [Q] and [Sym]. *)
  Parameter eqb_q : Q -> Q -> bool.
  Parameter eqb_q_spec : forall a b, reflect (a = b) (eqb_q a b).
  Parameter eqb_sym : Sym -> Sym -> bool.
  Parameter eqb_sym_spec : forall a b, reflect (a = b) (eqb_sym a b).

  (** It is also useful, in some situations, to be able to enumerate
      all the symbols and states. *)
  Parameter all_qs : list Q.
  Parameter all_qs_spec : forall a, In a all_qs.
  Parameter all_syms : list Sym.
  Parameter all_syms_spec : forall a, In a all_syms.
End Ctx.

Module TM (Ctx : Ctx).
  Export Ctx.

Lemma eqb_q_refl : forall q, eqb_q q q = true.
Proof. introv. destruct (eqb_q_spec q q); congruence. Qed.

Lemma eqb_sym_refl : forall s, eqb_sym s s = true.
Proof. introv. destruct (eqb_sym_spec s s); congruence. Qed.

#[export] Hint Resolve all_qs_spec all_syms_spec : core.

(** A Turing machine is a function mapping each [(state, symbol)] pair
    to one of

    - [None], in which case the machine halts;
    - [Some (s, d, q)], in which case the machine writes [s] on the tape,
      moves in the direction specified by [d], and transitions to state [q].

*)
Definition TM : Type := Q * Sym -> option (Sym * dir * Q).

Notation side := (Stream Sym).

(** The state of the tape is represented abstractly as a tuple [(l, s, r)],
    where [v] is the symbol under the head, while [l] and [r] are infinite
    streams of symbols on the left and right side of the head, respectively. *)
Notation tape := (side * Sym * side)%type.

(** We define a notation for tapes, evocative of a turing machine's head
    hovering over a particular symbol. **)
Notation "l {{ s }} r" := (l, s, r)
  (at level 30, only parsing).

(** Moreover the streams could use some more natural notation, to have
    the element at the start of the stream be on the right side, as necessary. *)
Notation "s >> r" := (Cons s r) (at level 25, right associativity).
Notation "l << s" := (Cons s l) (at level 24, left associativity).

Local Example tape_ex (a b c d e : Sym) : tape :=
  const s0 << a << b {{c}} d >> e >> const s0.

(** Helper functions for moving the tape head: *)
Definition move_left (t : tape) : tape :=
  match t with
  | l {{s}} r => tl l {{hd l}} s >> r
  end.

Definition move_right (t : tape) : tape :=
  match t with
  | l {{s}} r => l << s {{hd r}} tl r
  end.

(** Notation for the configuration of a machine. Note that the position
    of the head within the tape is implicit, since the tape is centered
    at the head. *)
Notation "q ;; t" := (q, t) (at level 35, only parsing).

(** The small-step semantics of Turing machines: *)
Reserved Notation "c -[ tm ]-> c'" (at level 40).

Inductive step (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | step_left q q' s s' l r :
    tm (q, s) = Some (s', L, q') ->
    q;; l {{s}} r -[ tm ]-> q';; (move_left (l {{s'}} r))
  | step_right q q' s s' l r :
    tm (q, s) = Some (s', R, q') ->
    q;; l {{s}} r -[ tm ]-> q';; (move_right (l {{s'}} r))

  where "c -[ tm ]-> c'" := (step tm c c').

#[export] Hint Constructors step : core.

(** If we have an assumption of the form [tm (q, s) = Some (s', d, q')],
   perform case analysis on [d]. *)
Ltac destruct_dir tm q s :=
  lazymatch goal with
  | H: tm (q, s) = Some (?s', ?d, ?q') |- _ =>
    lazymatch d with
    | L => fail
    | R => fail
    | _ => destruct d
    end
  end.

#[export] Hint Extern 1 =>
  match goal with
  | |- context [?q;; _ {{?s}} _ -[ ?tm ]-> _] => destruct_dir tm q s
  end : core.

(** Executing a specified number of steps: *)
Reserved Notation "c -[ tm ]->> n / c'" (at level 40, n at next level).

Inductive multistep (tm : TM) : nat -> Q * tape -> Q * tape -> Prop :=
  | multistep_0 c : c -[ tm ]->> 0 / c
  | multistep_S n c c' c'' :
    c  -[ tm ]->  c' ->
    c' -[ tm ]->> n / c'' ->
    c  -[ tm ]->> S n / c''

  where "c -[ tm ]->> n / c'" := (multistep tm n c c').

#[export] Hint Constructors multistep : core.

#[export] Hint Extern 1 =>
  lazymatch goal with
  | H: _ -[ _ ]->> _ / _ |- _ => inverts H
  end : core.

(** Executing an unspecified number of steps (the "eventually
    reaches" relation): *)
Reserved Notation "c -[ tm ]->* c'" (at level 40).

Inductive evstep (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | evstep_refl c : c -[ tm ]->* c
  | evstep_step c c' c'' :
    c  -[ tm ]->  c'  ->
    c' -[ tm ]->* c'' ->
    c  -[ tm ]->* c''

  where "c -[ tm ]->* c'" := (evstep tm c c').

#[export] Hint Constructors evstep : core.

(** Executing an unspecified, but non-zero number of steps: *)
Reserved Notation "c -[ tm ]->+ c'" (at level 40).

Inductive progress (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | progress_base c c' :
    c -[ tm ]->  c' ->
    c -[ tm ]->+ c'
  | progress_step c c' c'' :
    c  -[ tm ]->  c'  ->
    c' -[ tm ]->+ c'' ->
    c  -[ tm ]->+ c''

  where "c -[ tm ]->+ c'" := (progress tm c c').

#[export] Hint Constructors progress : core.

(** A halting configuration is one for which [tm (q, s)] returns [None]. *)
Definition halting (tm : TM) (c : Q * tape) : Prop :=
  match c with
  | (q, l {{s}} r) => tm (q, s) = None
  end.

(** The initial configuration of the machine *)
Definition c0 : Q * tape := q0;; const s0 {{s0}} const s0.

(** A Turing machine halts if it eventually reaches a halting configuration. *)
Definition halts_in (tm : TM) (c : Q * tape) (n : nat) :=
  exists ch, c -[ tm ]->> n / ch /\ halting tm ch.

Definition halts (tm : TM) (c0 : Q * tape) :=
  exists n, halts_in tm c0 n.

(** We prove that the "syntactic" notion of [halting] corresponds
    to the behavior of [step]. *)
Lemma halting_no_step :
  forall tm c c',
  halting tm c ->
  ~ c -[ tm ]-> c'.
Proof.
  introv Hhalting Hstep.
  inverts Hstep; congruence.
Qed.

Lemma no_halting_step :
  forall tm c,
  ~ halting tm c ->
  exists c',
  c -[ tm ]-> c'.
Proof.
  introv Hhalting.
  destruct c as [q [[l s] r]].
  destruct (tm (q, s)) as [[[s' d] q'] |] eqn:E.
  - (* tm (q, s) = Some (s', d, q') *)
    eauto 6.
  - (* tm (q, s) = None *)
    congruence.
Qed.

(** Other useful lemmas: *)
Lemma step_deterministic :
  forall tm c c' c'',
  c -[ tm ]-> c'  ->
  c -[ tm ]-> c'' ->
  c' = c''.
Proof.
  introv H1 H2.
  inverts H1; inverts H2; congruence.
Qed.

Ltac step_deterministic :=
  lazymatch goal with
  | H1: ?c -[ ?tm ]-> ?c',
    H2: ?c -[ ?tm ]-> ?c''
    |- _ =>
    pose proof (step_deterministic tm c c' c'' H1 H2); subst c''; clear H2
  end.

#[export] Hint Extern 1 => step_deterministic : core.

Lemma multistep_trans :
  forall tm n m c c' c'',
  c  -[ tm ]->> n / c' ->
  c' -[ tm ]->> m / c'' ->
  c  -[ tm ]->> (n + m) / c''.
Proof.
  introv H1 H2.
  induction H1; simpl; eauto.
Qed.

Lemma multistep_deterministic :
  forall tm n c c' c'',
  c -[ tm ]->> n / c'  ->
  c -[ tm ]->> n / c'' ->
  c' = c''.
Proof.
  introv H1 H2.
  induction H1; inverts H2; auto.
Qed.

Ltac multistep_deterministic :=
  lazymatch goal with
  | H1: ?c -[ ?tm ]->> ?n / ?c',
    H2: ?c -[ ?tm ]->> ?n / ?c''
    |- _ =>
    pose proof (multistep_deterministic tm n c c' c'' H1 H2); subst c''; clear H2
  end.

#[export] Hint Extern 1 => multistep_deterministic : core.

Ltac deterministic := repeat (step_deterministic || multistep_deterministic).

Lemma multistep_last :
  forall tm n c c'',
  c -[ tm ]->> S n / c'' ->
  exists c', c -[ tm ]->> n / c' /\ c' -[ tm ]-> c''.
Proof.
  induction n; introv H; inverts H as H1 H2.
  - eauto.
  - apply IHn in H2. destruct H2 as [cmid [H2 H3]].
    eauto.
Qed.

Lemma evstep_trans :
  forall tm c c' c'',
  c  -[ tm ]->* c'  ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->* c''.
Proof.
  introv H1 H2. induction H1; eauto.
Qed.

Lemma progress_trans :
  forall tm c c' c'',
  c  -[ tm ]->+ c'  ->
  c' -[ tm ]->+ c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. induction H1; eauto.
Qed.

Lemma multistep_progress :
  forall tm n c c',
  c -[ tm ]->> S n / c' ->
  c -[ tm ]->+ c'.
Proof.
  induction n; introv H; inverts H; eauto.
Qed.

#[export] Hint Immediate multistep_progress : core.

Lemma progress_multistep :
  forall tm c c',
  c -[ tm ]->+ c' ->
  exists n,
  c -[ tm ]->> S n / c'.
Proof.
  introv H. induction H.
  - eauto.
  - destruct IHprogress as [n IH].
    eauto.
Qed.

Lemma without_counter :
  forall tm n c c',
  c -[ tm ]->> n / c' ->
  c -[ tm ]->* c'.
Proof.
  introv H. induction H; eauto.
Qed.

Lemma with_counter :
  forall tm c c',
  c -[ tm ]->* c' ->
  exists n, c -[ tm ]->> n / c'.
Proof.
  introv H. induction H.
  - eauto.
  - destruct IHevstep as [n IH].
    eauto.
Qed.

Lemma evstep_progress :
  forall tm c c',
  c -[ tm ]->* c' ->
  c <> c' ->
  c -[ tm ]->+ c'.
Proof.
  introv Hrun Hneq.
  apply with_counter in Hrun.
  destruct Hrun as [[| n] Hrun].
  - inverts Hrun. contradiction.
  - eauto.
Qed.

Lemma evstep_progress_trans :
  forall tm c c' c'',
  c  -[ tm ]->* c'  ->
  c' -[ tm ]->+ c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. induction H1; eauto.
Qed.

Lemma progress_evstep_trans :
  forall tm c c' c'',
  c  -[ tm ]->+ c'  ->
  c' -[ tm ]->* c'' ->
  c  -[ tm ]->+ c''.
Proof.
  introv H1 H2. induction H1.
  - apply with_counter in H2.
    destruct H2 as [[| n] H2]; eauto.
  - eauto.
Qed.

Lemma rewind_split:
  forall tm n k c c'',
  c -[ tm ]->> (n + k) / c'' ->
  exists c', c -[ tm ]->> n / c' /\ c' -[ tm ]->> k / c''.
Proof.
  intros tm n k.
  induction n; intros c c'' H.
  - eauto.
  - inverts H as Hstep Hrest.
    apply IHn in Hrest. clear IHn.
    destruct Hrest as [cn [Hn Hk]].
    eauto.
Qed.

(** When using [rewind_split], it is often more convenient to have the arithmetic
    show up as a separate goal, to be easily discharged with [lia]. *)
Lemma rewind_split':
  forall k1 k2 tm n c c'',
  c -[ tm ]->> n / c'' ->
  n = k1 + k2 ->
  exists c', c -[ tm ]->> k1 / c' /\ c' -[ tm ]->> k2 / c''.
Proof.
  introv H E. subst n. apply rewind_split; assumption.
Qed.

Lemma halting_no_multistep:
  forall tm c c' n,
  n > 0 ->
  halting tm c ->
  ~ c -[ tm ]->> n / c'.
Proof.
  introv Hgt0 Hhalting Hrun.
  inverts Hrun as Hstep Hrest.
  - inverts Hgt0.
  - eapply halting_no_step in Hhalting. eauto.
Qed.

Lemma exceeds_halt : forall tm c c' n k,
  halts_in tm c k ->
  n > k ->
  c -[ tm ]->> n / c' ->
  False.
Proof.
  introv [ch [Hch Hhalting]] Hnk Hexec.
  eapply (rewind_split' k (n - k)) in Hexec; try lia.
  destruct Hexec as [ch' [H1 H2]].
  deterministic.
  eapply halting_no_multistep in Hhalting.
  - eauto.
  - lia.
Qed.

Corollary within_halt : forall tm c c' k n,
  halts_in tm c n ->
  c -[ tm ]->> k / c' ->
  k <= n.
Proof.
  introv Hhalts Hrun.
  destruct (Nat.leb_spec k n); try assumption.
  exfalso. eauto using exceeds_halt.
Qed.

Lemma preceeds_halt : forall tm c c' n k,
  halts_in tm c k ->
  c -[ tm ]->> n / c' ->
  n <= k ->
  halts_in tm c' (k - n).
Proof.
  introv Hhalt Hexec Hle.
  destruct Hhalt as [ch [Hrunch Hhalting]].
  apply (rewind_split' n (k - n)) in Hrunch; try lia.
  destruct Hrunch as [cm [H1 H2]].
  deterministic.
  exists ch. auto.
Qed.

Lemma skip_halts: forall tm c c' n,
  c -[ tm ]->> n / c' ->
  ~ halts tm c' ->
  ~ halts tm c.
Proof.
  introv Hexec Hnonhalt [k Hhalt].
  (* destruct Hhalt as [k [ch [Hrunch Hhalting]]]. *)
  destruct (Nat.ltb_spec k n).
  - eapply exceeds_halt; eassumption.
  - apply Hnonhalt.
    eexists. eapply preceeds_halt; eassumption.
Qed.

Lemma progress_nonhalt' : forall tm (P : Q * tape -> Prop),
  (forall c, P c -> exists c', P c' /\ c -[ tm ]->+ c') ->
  forall k c, P c -> ~ halts_in tm c k.
Proof.
  introv Hstep.
  induction k using strong_induction.
  introv H0 Hhalts.
  apply Hstep in H0. destruct H0 as [c' [HP Hrun]].
  apply progress_multistep in Hrun. destruct Hrun as [n Hrun].
  destruct (Nat.leb_spec (S n) k).
  - assert (Hhalts' : halts_in tm c' (k - S n)).
    { eapply preceeds_halt; eassumption. }
    assert (Hnhalts : ~ halts_in tm c' (k - S n)).
    { apply H; [lia | assumption]. }
    contradiction.
  - eapply exceeds_halt; eassumption.
Qed.

Lemma progress_nonhalt : forall tm (P : Q * tape -> Prop) c,
  (forall c, P c -> exists c', P c' /\ c -[ tm ]->+ c') ->
  P c ->
  ~ halts tm c.
Proof.
  introv Hstep H0 Hhalts.
  destruct Hhalts as [k Hhalts].
  assert (Hnhalts : ~ halts_in tm c k).
  { apply (progress_nonhalt' tm P); assumption. }
  contradiction.
Qed.

End TM.
