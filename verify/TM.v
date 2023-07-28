(** * TM: Definition of Turing Machines *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Export Lists.Streams.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
From BusyCoq Require Import Helper.
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
End Ctx.

Module TMs (Ctx : Ctx).
  Export Ctx.

(** A Turing machine is a function mapping each [(state, symbol)] pair
    to one of

    - [None], in which case the machine halts;
    - [Some (s, d, q)], in which case the machine writes [s] on the tape,
      moves in the direction specified by [d], and transitions to state [q].

*)
Definition TM : Type := Q * Sym -> option (Sym * dir * Q).

(** The state of the tape is represented abstractly as a tuple [(l, s, r)],
    where [v] is the symbol under the head, while [l] and [r] are infinite
    streams of symbols on the left and right side of the head, respectively. *)
Definition tape : Type := Stream Sym * Sym * Stream Sym.

(** We define a notation for tapes, evocative of a turing machine's head
    hovering over a particular symbol. **)
Notation "l {{ s }} r" := (l, s, r)
  (at level 30).

(** Moreover the streams could use some more natural notation, to have
    the element at the start of the stream be on the right side, as necessary. *)
Notation "s >> r" := (Cons s r) (at level 25, right associativity).
Notation "l << s" := (Cons s l) (at level 24, left associativity).

Local Example tape_ex (a b c d e : Sym) : tape :=
  const s0 << a << b {{c}} d >> e >> const s0.

(** Helper functions for moving the tape head: *)
Definition move_left (t : tape) : tape :=
  match t with
  | l << s' {{s}} r => l {{s'}} s >> r
  end.

Definition move_right (t : tape) : tape :=
  match t with
  | l {{s}} s' >> r => l << s {{s'}} r
  end.

(** Notation for the configuration of a machine. Note that the position
    of the head within the tape is implicit, since the tape is centered
    at the head. *)
Notation "q ; t" := (q, t) (at level 35).

(** The small-step semantics of Turing machines: *)
Reserved Notation "c -[ tm ]-> c'" (at level 40).

Inductive step (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | step_left q q' s s' l r :
    tm (q, s) = Some (s', L, q') ->
    q; l {{s}} r -[ tm ]-> q'; (move_left (l {{s'}} r))
  | step_right q q' s s' l r :
    tm (q, s) = Some (s', R, q') ->
    q; l {{s}} r -[ tm ]-> q'; (move_right (l {{s'}} r))

  where "c -[ tm ]-> c'" := (step tm c c').

(** And the indexed multistep relation: *)
Reserved Notation "c -[ tm ]->* n / c'" (at level 40, n at next level).

Inductive multistep (tm : TM) : nat -> Q * tape -> Q * tape -> Prop :=
  | multistep_0 c : c -[ tm ]->* 0 / c
  | multistep_S n c c' c'' :
    c  -[ tm ]->  c' ->
    c' -[ tm ]->* n / c'' ->
    c  -[ tm ]->* S n / c''

  where "c -[ tm ]->* n / c'" := (multistep tm n c c').

(** A halting configuration is one for which [tm (q, s)] returns [None]. *)
Definition halting (tm : TM) (c : Q * tape) : Prop :=
  match c with
  | (q, l {{s}} r) => tm (q, s) = None
  end.

(** The initial configuration of the machine *)
Definition c0 : Q * tape := q0; const s0 {{s0}} const s0.

(** A Turing machine halts if it eventually reaches a halting configuration. *)
Definition halts_in (tm : TM) (c : Q * tape) (n : nat) :=
  exists ch, c -[ tm ]->* n / ch /\ halting tm ch.

Definition halts (tm : TM) (c0 : Q * tape) :=
  exists n, halts_in tm c0 n.

(** We prove that this corresponds with [step]. *)
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
    destruct d; eexists.
    + (* L *) apply step_left. eassumption.
    + (* R *) apply step_right. eassumption.
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
  inverts H1 as E1; inverts H2 as E2; try congruence;
    rewrite E2 in E1; inverts E1; auto.
Qed.

Lemma multistep_trans :
  forall tm n m c c' c'',
  c  -[ tm ]->* n / c' ->
  c' -[ tm ]->* m / c'' ->
  c  -[ tm ]->* (n + m) / c''.
Proof.
  introv H1 H2.
  induction H1.
  - exact H2.
  - simpl. destruct c''. eapply multistep_S; eauto.
Qed.

Lemma multistep_deterministic :
  forall tm n c c' c'',
  c -[ tm ]->* n / c'  ->
  c -[ tm ]->* n / c'' ->
  c' = c''.
Proof.
  introv H1 H2.
  induction H1 as [| n c0 c1 c2 H01 H12 IH]; inverts H2 as H0a Hab.
  - reflexivity.
  - apply IH.
    rewrite (step_deterministic _ _ _ _ H01 H0a).
    assumption.
Qed.

Lemma rewind_split:
  forall tm n k c c'',
  c -[ tm ]->* (n + k) / c'' ->
  exists c', c -[ tm ]->* n / c' /\ c' -[ tm ]->* k / c''.
Proof.
  intros tm n k.
  induction n; intros c c'' H.
  - exists c. split.
    + apply multistep_0.
    + assumption.
  - inverts H as Hstep Hrest.
    apply IHn in Hrest. clear IHn.
    destruct Hrest as [cn [Hn Hk]].
    exists cn. split.
    + eapply multistep_S; eassumption.
    + exact Hk.
Qed.

Lemma halting_no_multistep:
  forall tm c c' n,
  n > 0 ->
  halting tm c ->
  ~ c -[ tm ]->* n / c'.
Proof.
  introv Hgt0 Hhalting Hrun.
  inverts Hrun as Hstep Hrest.
  - inverts Hgt0.
  - eapply halting_no_step in Hhalting.
    apply Hhalting. exact Hstep.
Qed.

Lemma skip_halts: forall tm c c' n,
  c -[ tm ]->* n / c' ->
  ~ halts tm c' ->
  ~ halts tm c.
Proof.
  introv Hexec Hnonhalt Hhalt.
  destruct Hhalt as [k [ch [Hrunch Hhalting]]].
  destruct (Nat.ltb_spec k n).
  - replace n with (k + (n - k)) in Hexec by lia.
    apply rewind_split in Hexec.
    destruct Hexec as [ch' [H1 H2]].
    replace ch' with ch in *
      by (eapply multistep_deterministic; eassumption).
    clear ch' H1.
    eapply halting_no_multistep in Hhalting.
    + apply Hhalting, H2.
    + lia.
  - replace k with (n + (k - n)) in Hrunch by lia.
    apply rewind_split in Hrunch.
    destruct Hrunch as [cm [H1 H2]].
    replace cm with c' in *
      by (eapply multistep_deterministic; eassumption).
    clear cm H1.
    apply Hnonhalt.
    exists (k - n), ch. auto.
Qed.

Lemma exceeds_halt : forall tm c c' n k,
  halts_in tm c k ->
  n > k ->
  c -[ tm ]->* n / c' ->
  False.
Proof.
  introv [ch [Hch Hhalting]] Hnk Hexec.
  replace n with (k + (n - k)) in Hexec by lia.
  eapply rewind_split in Hexec.
  destruct Hexec as [ch' [H1 H2]].
  replace ch' with ch in * by (eapply multistep_deterministic; eassumption).
  eapply halting_no_multistep in Hhalting.
  - apply Hhalting. eassumption.
  - lia.
Qed.

End TMs.
