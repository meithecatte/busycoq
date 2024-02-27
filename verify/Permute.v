(** * Permute: renaming the states *)

From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Module Permute (Ctx : Ctx).
  Module Flip := Flip Ctx. Export Flip.

(* [f q = q'], where [q] is a state in [tm] and [q'] is the equivalent state
   in [tm']. *)
Definition Perm (tm tm' : TM) (f : Q -> Q) :=
  (forall q s,
    tm (q, s) = None ->
    tm' (f q, s) = None) /\
  (forall q s s' d q',
    tm (q, s) = Some (s', d, q') ->
    tm' (f q, s) = Some (s', d, f q')).

Lemma perm_halted : forall tm tm' f q t,
  Perm tm tm' f ->
  halted tm (q;; t) ->
  halted tm' (f q;; t).
Proof.
  introv [Hnone Hsome] H.
  destruct t as [[l s] r].
  apply Hnone, H.
Qed.

Local Hint Resolve perm_halted : core.

Lemma perm_step : forall tm tm' f q t q' t',
  Perm tm tm' f ->
  q;; t -[ tm ]-> q';; t' ->
  f q;; t -[ tm' ]-> f q';; t'.
Proof.
  introv [Hnone Hsome] Hstep.
  inverts Hstep as Hstep; constructor; auto.
Qed.

Local Hint Resolve perm_step : core.

Lemma perm_multistep : forall tm tm' f,
  Perm tm tm' f -> forall n q t q' t',
  q;; t -[ tm ]->> n / q';; t' ->
  f q;; t -[ tm' ]->> n / f q';; t'.
Proof.
  introv HP.
  induction n; introv Hsteps; inverts Hsteps.
  - auto.
  - destruct c' as [qq tt]. eauto.
Qed.

Local Hint Resolve perm_multistep : core.

Lemma perm_halts_in : forall tm tm' f q t n,
  Perm tm tm' f ->
  halts_in tm (q;; t) n ->
  halts_in tm' (f q;; t) n.
Proof.
  introv HP Hhalt.
  unfold halts_in in *.
  destruct Hhalt as [[q' t'] [Hstep Hhalt]]. eauto.
Qed.

Local Hint Resolve perm_halts_in : core.

Lemma perm_halts : forall tm tm' f q t,
  Perm tm tm' f ->
  halts tm (q;; t) ->
  halts tm' (f q;; t).
Proof.
  introv HP Hhalts.
  unfold halts in *.
  destruct Hhalts as [n Hhalts]. eauto.
Qed.

Lemma perm_nonhalt : forall tm tm' f q t,
  Perm tm tm' f ->
  ~ halts tm' (f q;; t) ->
  ~ halts tm (q;; t).
Proof.
  introv HP H' H.
  eauto using perm_halts.
Qed.

End Permute.
