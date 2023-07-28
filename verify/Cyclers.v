(** * Cyclers *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Import Helper.
From BusyCoq Require Import TM.
From BusyCoq Require Import Compute.
Set Default Goal Selector "!".

Module Cyclers (Ctx : Ctx).
  Export Ctx.
  Local Module TMs := TMs Ctx. Export Ctx.
  Local Module Compute := Compute Ctx. Export Compute.

Definition verify_cycler (tm : TM) (n k : nat) : bool :=
  match cmultistep tm n starting with
  | Some c =>
    match cmultistep tm k c with
    | Some c' => (0 <? k) && eqb c c'
    | None => false
    end
  | None => false
  end.

Lemma cycle_chain :
  forall (tm : TM) c n k,
  c -[ tm ]->* k / c ->
  c -[ tm ]->* (n * k) / c.
Proof.
  introv H.
  induction n.
  - apply multistep_0.
  - simpl. eapply multistep_trans; eassumption.
Qed.

Lemma cycle_nonhalting :
  forall (tm : TM) c k,
  k > 0 ->
  c -[ tm ]->* k / c ->
  ~ halts tm c.
Proof.
  introv Hgt0 Hk [h Hhalts_in].
  destruct (eventually_exceeds k h Hgt0) as [r Hr].
  eapply cycle_chain in Hk.
  eapply exceeds_halt; eassumption.
Qed.

Theorem verify_cycler_correct : forall tm n k,
  verify_cycler tm n k = true -> ~ halts tm c0.
Proof.
  introv H. unfold verify_cycler in H.
  destruct (cmultistep tm n starting) as [c |] eqn:E; try discriminate.
  destruct (cmultistep tm k c) as [c' |] eqn:E'; try discriminate.
  destruct (Nat.ltb_spec 0 k) as [Hgt0 |]; try discriminate.
  destruct (eqb_spec c c') as [Elift |]; try discriminate.

  apply cmultistep_some in E, E'.
  rewrite lift_starting in E.
  rewrite <- Elift in E'.
  eapply skip_halts.
  - eassumption.
  - eapply cycle_nonhalting; eassumption.
Qed.

End Cyclers.
