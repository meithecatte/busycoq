(** * Enumerate: TNF enumeration *)

From BusyCoq Require Export Permute.
Set Default Goal Selector "!".

Module Enumerate (Ctx : Ctx).
  Module Permute := Permute Ctx. Export Permute.

Inductive ReachesNZ (tm : TM) : Q -> nat -> Prop :=
  | Reaches_halt q :
    tm (q, s0) = None ->
    ReachesNZ tm q 0
  | Reaches_now q s d q' :
    tm (q, s0) = Some (s, d, q') ->
    s <> s0 ->
    ReachesNZ tm q 0
  | Reaches_later q d q' n :
    tm (q, s0) = Some (s0, d, q') ->
    ReachesNZ tm q' n ->
    ReachesNZ tm q (S n).
