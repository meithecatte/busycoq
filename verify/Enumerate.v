(** * Enumerate: TNF enumeration *)

From Coq Require Import List. Import ListNotations.
From BusyCoq Require Export Permute.
Set Default Goal Selector "!".

Module Enumerate (Ctx : Ctx).
  Module Permute := Permute Ctx. Export Permute.

(** To justify only enumerating machines that start with 1RB, we need
    to prove that all the other machines won't take many steps to write
    their first 1 (or a non-zero symbol in the case of non-binary Turing
    machines). *)

(** [tm] visits the sequence of states [q :: qs] before writing its first
    non-zero symbol. *)
Inductive zvisits (tm : TM) : Q -> list Q -> Prop :=
  | zvisits_halt q :
    tm (q, s0) = None ->
    zvisits tm q []
  | zvisits_nz q s d q' :
    tm (q, s0) = Some (s, d, q') ->
    s <> s0 ->
    zvisits tm q []
  | zvisits_step q d q' qs :
    tm (q, s0) = Some (s0, d, q') ->
    zvisits tm q' qs ->
    zvisits tm q (q' :: qs).

(** This sequence is unique. *)

Lemma zvisits_unique : forall tm qs qs' q,
  zvisits tm q qs ->
  zvisits tm q qs' ->
  qs = qs'.
Proof.
  induction qs as [| a qs IH]; introv H1 H2;
    inverts H1; inverts H2; try congruence.
  assert (a = q'). { congruence. }
  subst. f_equal. eauto.
Qed.

(** Therefore, [q] cannot occur in [qs]. *)
Lemma zvisits_In_skip : forall tm qs q q',
  zvisits tm q qs ->
  In q' qs ->
  exists qs', zvisits tm q' qs' /\ qs <> qs'.
Proof.
  induction qs as [| a qs IH].
  - contradiction.
  - introv Hvisits Hin. inverts Hvisits as Etm Hvisits.
    destruct Hin as [E | Hin]; subst; eauto.
Qed.

Lemma zvisits_In : forall tm qs q,
  zvisits tm q qs ->
  ~ In q qs.
Proof.
  introv H1 Hin.
  apply 
  induction qs as [| a qs IH].
  - contradiction.
  - inverts H1 as Etm H1.
    * subst a.
  assert (H2: zvisits tm 
