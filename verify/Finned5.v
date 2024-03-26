(** * Cubic-finned machine #5 (https://bbchallenge.org/11018487) *)

From BusyCoq Require Import Individual52.
From Coq Require Import Lia.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, A)
  | B, 0 => Some (0, L, C)  | B, 1 => Some (0, R, E)
  | C, 0 => None            | C, 1 => Some (1, L, D)
  | D, 0 => Some (1, L, A)  | D, 1 => Some (0, L, C)
  | E, 0 => Some (1, R, A)  | E, 1 => Some (1, R, E)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym.

Inductive I : Type :=
  | I0 (a b : nat) (H : 2*a = b) : I                 (* 1RB -> I1 *)
  | I1 (a b : nat) (H : 2*a + 1 = b) : I             (* 0LC -> I2 *)
  | I2 (a b d : nat) (H : 2*a = b + 2*d) : I         (* 1LD -> I3, I4 *)
  | I3 (a b d : nat) (H : 2*a = b + 2*d + 1) : I     (* 0LC -> I2 *)
  | I4 (a : nat) : I                                 (* 1LA -> I5, I6 *)
  | I5 (a b c d : nat) (H : 2*a + d + 1 = b + c) : I (* 1LA -> I5, I6 *)
  | I6 (a c d : nat) (H : 2*a + d + 1 = c) : I       (* 1RB -> I7 *)
  | I7 (a c d : nat) (H : 2*a + d + 1 = c) : I       (* 0RE -> I8 *)
  | I8 (a b c d : nat) (H : 2*a + d = b + c + 2) : I (* 1RE -> I8, I9 *)
  | I9 (a b d : nat) (H : 2*a + d = b + 1) : I       (* 1RA -> I0, I5 *)
  .

Open Scope sym.

Definition f (i : I) : Q * tape :=
  match i with
  | I0 a b _ => A;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I1 a b _ => B;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I2 a b d _ => C;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [0; 1]^^d *> const 0
  | I3 a b d _ => D;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} 1 >> [0; 1]^^d *> const 0
  | I4 a => D;;
    const 0 <* [1]^^a {{0}} 1 >> [0; 1]^^a *> const 0
  | I5 a b c d _ => A;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I6 a c d _ => A;;
    const 0 <* [1]^^a {{0}} 1 >> [1]^^c *> [0; 1]^^d *> const 0
  | I7 a c d _ => B;;
    const 0 <* [1]^^a << 1 {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I8 a b c d _ => E;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I9 a b d _ => E;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} [1; 0]^^d *> const 0
  end.

Ltac single := eapply progress_intro; [prove_step | simpl_tape; finish].
Ltac goto x := match type of x with
  | I => exists x
  | _ -> I => exists (x ltac:(lia))
  end; single.

Lemma align_d : forall d, [0; 1]^^d *> const 0 = 0 >> [1; 0]^^d *> const 0.
Proof.
  induction d; simpl.
  - rewrite <- const_unfold. reflexivity.
  - rewrite IHd. reflexivity.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  replace c0 with (A;; const 0 << 0 {{0}} const 0)
    by now rewrite <- const_unfold.
  apply progress_nonhalt_simple with (C := f) (i0 := I0 0 0 eq_refl).
  intros [].
  - (* I0 *) goto (I1 a (S b)).
  - (* I1 *)
    destruct b as [| b']. { lia. }
    goto (I2 a b' 0).
  - (* I2 *)
    destruct b as [| b'].
    + goto (I4 a).
    + goto (I3 a b' d).
  - (* I3 *)
    destruct b as [| b']. { lia. }
    goto (I2 a b' (S d)).
  - (* I4 *)
    destruct a as [| a'].
    + goto (I6 0 1 0).
    + goto (I5 0 a' 2 (S a')).
  - (* I5 *)
    destruct b as [| b'].
    + goto (I6 a c d).
    + goto (I5 a b' (S c) d).
  - (* I6 *)
    + goto (I7 a c d).
  - (* I7 *)
    destruct c as [| c']. { lia. }
    goto (I8 (S a) 0 c' d).
  - (* I8 *)
    destruct c as [| c'].
    + simpl f. rewrite align_d.
      goto (I9 a (S b) d).
    + goto (I8 a (S b) c' d).
  - (* I9 *)
    destruct d as [| d'].
    + goto (I0 a (S b)).
    + simpl f. rewrite <- align_d.
      goto (I5 a (S b) 0 d').
Qed.
