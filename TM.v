(** * TM: Definition of Turing Machines *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lists.Streams.
From BusyCoq Require Import LibTactics.
Set Default Goal Selector "!".

Section TMs.
  (** The type of states. *)
  Variable Q : Type.

  (** The type of tape symbols. *)
  Variable Sym : Type.

  (** Initial state. *)
  Variable q0 : Q.

  (** The 0 symbol. *)
  Variable s0 : Sym.

(** The direction a Turing machine can step in. *)
Inductive dir : Type := L | R.

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
Notation "l [ [ s ] ] r" := (l, s, r)
  (at level 30, format "l  [ [ s ] ]  r").

Notation "q ; t" := (q, t) (at level 35).
Definition st0 : Q * tape := q0; const s0 [[s0]] const s0.

(** Moreover the streams could use some more natural notation, to have
    the element at the start of the stream be on the right side, as necessary. *)
Notation "s >> r" := (Cons s r) (at level 25, right associativity).
Notation "l << s" := (Cons s l) (at level 24, left associativity).

Example tape_ex (a b c d e : Sym) (l r : Stream Sym) : tape :=
  l << a << b [[c]] d >> e >> r.

(** Helper functions for moving the tape head: *)
Definition move_left (t : tape) : tape :=
  match t with
  | l << s' [[s]] r => l [[s']] s >> r
  end.

Definition move_right (t : tape) : tape :=
  match t with
  | l [[s]] s' >> r => l << s [[s']] r
  end.

(** The small-step semantics of Turing machines: *)
Reserved Notation "st -[ tm ]-> st'" (at level 40).

Inductive step (tm : TM) : Q * tape -> Q * tape -> Prop :=
  | step_left q q' s s' l r :
    tm (q, s) = Some (s', L, q') ->
    q; l [[s]] r -[ tm ]-> q'; (move_left (l [[s']] r))
  | step_right q q' s s' l r :
    tm (q, s) = Some (s', R, q') ->
    q; l [[s]] r -[ tm ]-> q'; (move_right (l [[s']] r))

  where "st -[ tm ]-> st'" := (step tm st st').

(** A halting configuration is one for which [tm (q, s)] returns [None]. *)
Definition halting (tm : TM) (st : Q * tape) : Prop :=
  match st with
  | (q, l [[s]] r) => tm (q, s) = None
  end.

(** We prove that this corresponds with [step]. *)
Lemma halting_no_step :
  forall tm q q' t t',
  halting tm (q, t) ->
  ~ q; t -[ tm ]-> q'; t'.
Proof.
  introv Hhalting Hstep.
  destruct t as [[l s] r].
  inverts Hstep; congruence.
Qed.

Lemma no_halting_step :
  forall tm q t,
  ~ halting tm (q, t) ->
  exists q' t',
  q; t -[ tm ]-> q'; t'.
Proof.
  introv Hhalting.
  destruct t as [[l s] r].
  destruct (tm (q, s)) as [[[s' d] q'] |] eqn:E.
  - (* tm (q, s) = Some (s', d, q') *)
    destruct d; repeat eexists.
    + (* L *) apply step_left. eassumption.
    + (* R *) apply step_right. eassumption.
  - (* tm (q, s) = None *)
    congruence.
Qed.

Theorem step_deterministic :
  forall tm st st' st'',
  st -[ tm ]-> st'  ->
  st -[ tm ]-> st'' ->
  st' = st''.
Proof.
  introv H1 H2.
  inverts H1 as E1; inverts H2 as E2; try congruence;
    rewrite E2 in E1; inverts E1; auto.
Qed.

(** We now need to define composition of more than one step. *)

Reserved Notation "st -[ tm ]->* n / st'" (at level 40, n at next level).

Inductive multistep (tm : TM) : nat -> Q * tape -> Q * tape -> Prop :=
  | multistep_0 q t : q; t -[ tm ]->* 0 / q; t
  | multistep_S n q t q' t' q'' t'' :
    q ; t  -[ tm ]-> q'; t'->
    q'; t' -[ tm ]->* n / q''; t'' ->
    q ; t  -[ tm ]->* S n / q''; t''

  where "st -[ tm ]->* n / st'" := (multistep tm n st st').

Lemma multistep_trans :
  forall tm n m q t q' t' q'' t'',
  q ; t  -[ tm ]->* n / q'; t' ->
  q'; t' -[ tm ]->* m / q''; t'' ->
  q ; t  -[ tm ]->* (n + m) / q''; t''.
Proof.
  introv H1 H2.
  induction H1.
  - exact H2.
  - simpl. eapply multistep_S; eauto.
Qed.

Definition halts (tm : TM) := exists n st,
  st0 -[ tm ]->* n / st /\ halting tm st.

End TMs.
