(** * DirectedCompute: the "head between tape cells" formulation *)

From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Module DirectedCompute (Ctx : Ctx).
  Module Flip := Flip Ctx. Export Flip.

Definition dtape : Type := dir * list Sym * list Sym.

Definition undir (d : dtape) : tape :=
  match d with
  | (L, l, r) =>
    match l with
    | s :: l => to_dlist l {{s}} to_dlist r
    | [] => <[] {{s0}} to_dlist r
    end
  | (R, l, r) =>
    match r with
    | s :: r => to_dlist l {{s}} to_dlist r
    | [] => to_dlist l {{s0}} []>
    end
  end.

Lemma flip_undir : forall q d l r,
  flip_conf (q;; undir (d, l, r)) = q;; undir (flip_dir d, r, l).
Proof.
  introv.
  destruct d.
  - destruct l; simpl; repeat rewrite dflip_to_dlist; reflexivity.
  - destruct r; simpl; repeat rewrite dflip_to_dlist; reflexivity.
Qed.

Lemma undir_left_s0 : forall n r,
  undir (L, repeat s0 n, r) = (drepeat s0 (pred n), s0, to_dlist r).
Proof. introv. destruct n; simpl; try rewrite to_dlist_repeat; reflexivity. Qed.

Lemma undir_right_s0 : forall n l,
  undir (R, l, repeat s0 n) = (to_dlist l, s0, drepeat s0 (pred n)).
Proof. introv. destruct n; simpl; try rewrite to_dlist_repeat; reflexivity. Qed.

End DirectedCompute.
