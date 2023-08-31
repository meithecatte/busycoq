(** * Directed: the "head between tape cells" formulation *)

From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Module Directed (Ctx : Ctx).
  Module Flip := Flip Ctx. Export Flip.

Definition dtape : Type := dir * list Sym * list Sym.

Definition undir (d : dtape) : ctape :=
  match d with
  | (L, l, r) =>
    match l with
    | s :: l => l {{s}} r
    | [] => [] {{s0}} r
    end
  | (R, l, r) =>
    match r with
    | s :: r => l {{s}} r
    | [] => l {{s0}} []
    end
  end.

End Directed.
