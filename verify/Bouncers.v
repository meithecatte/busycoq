(** * Bouncers *)

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Program.Tactics.
From Coq Require Import Program.Wf.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Module Cyclers (Ctx : Ctx).
  Module Flip := Flip Ctx. Export Flip.

Inductive segment :=
  | Repeat (xs : list Sym)
  | Symbol (x : Sym).

Reserved Notation "s ~ t" (at level 70).

Inductive matches : list segment -> list Sym -> Prop :=
  | match_nil : [] ~ []
  | match_sym x s t : s ~ t -> Symbol x :: s ~ x :: t
  | match_skip xs s t : s ~ t -> Repeat xs :: s ~ t
  | match_repeat xs s t : Repeat xs :: s ~ t -> Repeat xs :: s ~ xs ++ t

  where "s ~ t" := (matches s t).

Local Hint Constructors matches : core.

Lemma match_repeatn : forall n xs s t,
  s ~ t -> Repeat xs :: s ~ concat (repeat xs n) ++ t.
Proof.
  induction n; introv H.
  - auto.
  - simpl. rewrite <- app_assoc. auto.
Qed.

Local Hint Resolve match_repeatn : core.

(** A greedy check is sufficient, as the decider will have provided us with
    an aligned tape. *)

Local Obligation Tactic := program_simplify; auto; simpl;
  autorewrite with list; try lia;
  try intuition congruence.

Program Fixpoint check_match (s : list segment) (t : list Sym)
    {measure (length s + length t)} : {s ~ t} + {True} :=
  match s, t with
  | Symbol x :: s', x' :: t' =>
    eqb_sym x x' && Reduce (check_match s' t')
  | Repeat [] :: s', t =>
    Reduce (check_match s' t)
  | Repeat xs :: s', t =>
    match (strip_prefix eqb_sym xs t) with
    | [|| t' ||] => Reduce (check_match (Repeat xs :: s') t')
    | !! => Reduce (check_match s' t)
    end
  | [], [] => Yes
  | _, _ => No
  end.

Obligation 8. lia.
