(** * Compute: executable Turing machine model *)

(**
 * The model in [TM] uses a step relation which isn't explicitly computable.
 * This is nice for abstract reasoning, but not directly usable for deciding
 * Turing machines.  Here, we'll introduce a computable model, and prove that
 * corresponds to the abstract one. *)

From Coq Require Import Bool.
From Coq Require Import Program.Tactics.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Lia.
From BusyCoq Require Export TM.
Set Default Goal Selector "!".

Module Compute (Ctx : Ctx).
  Module TM := TM Ctx. Export TM.

Definition eqb_side {d} : forall (xs ys : side d), {xs = ys} + {xs <> ys}.
Proof.
  decide equality. apply eqb_sym.
Qed.

Definition eqb_conf : forall (c c' : Q * tape), {c = c'} + {c <> c'}.
Proof.
  repeat decide equality; apply eqb_sym || apply eqb_q.
Qed.

Local Obligation Tactic := program_simplify;
  try constructor; eauto.

(** Computable semantics of Turing machines. *)
Program Definition cstep (tm : TM) (c : Q * tape)
    : {c' | c -[ tm ]-> c'} + {halted tm c} :=
  match c with
  | q;; l {{s}} r =>
    match tm (q, s) with
    | None => inright _
    | Some (s', L, q') => [|| q';; move_left  (l {{s'}} r) ||]
    | Some (s', R, q') => [|| q';; move_right (l {{s'}} r) ||]
    end
  end.

Program Fixpoint cmultistep (tm : TM) (n : nat) (c : Q * tape)
    : {c' | c -[ tm ]->> n / c'} + {halts tm c} :=
  match n with
  | 0 => [|| c ||]
  | S n' =>
    bind c' <-- cstep tm c;
    bind c'' <-- cmultistep tm n' c';
    [|| c'' ||]
  end.

End Compute.
