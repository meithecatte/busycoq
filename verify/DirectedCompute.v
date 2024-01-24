(** * DirectedCompute: the "head between tape cells" formulation *)

From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Module DirectedCompute (Ctx : Ctx).
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

Lemma flip_undir : forall q d l r,
  flip_conf (lift (q, undir (d, l, r))) = lift (q, undir (flip_dir d, r, l)).
Proof.
  introv.
  destruct d.
  - destruct l; reflexivity.
  - destruct r; reflexivity.
Qed.

Lemma undir_left_s0 : forall n r,
  undir (L, repeat s0 n, r) = (repeat s0 (pred n), s0, r).
Proof. introv. destruct n; reflexivity. Qed.

Lemma undir_right_s0 : forall n l,
  undir (R, l, repeat s0 n) = (l, s0, repeat s0 (pred n)).
Proof. introv. destruct n; reflexivity. Qed.

End DirectedCompute.
