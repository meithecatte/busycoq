From Coq Require Import Lists.List.
From Coq Require Import ZArith.
From BusyCoq Require Import Individual52 Finned.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => None
  | B, 0 => Some (0, R, C)  | B, 1 => Some (1, L, B)
  | C, 0 => Some (1, R, D)  | C, 1 => Some (1, R, C)
  | D, 0 => Some (1, L, E)  | D, 1 => Some (1, L, D)
  | E, 0 => Some (0, R, A)  | E, 1 => Some (0, L, E)
  end.
Close Scope sym.

Definition lwfa : WNFA :=  [(0%nat, 0%nat, 0%sym, 0%Z);
                            (1%nat, 1%nat, 0%sym, 0%Z);
                            (1%nat, 1%nat, 1%sym, 0%Z);
                            (2%nat, 2%nat, 1%sym, 0%Z);
                            (2%nat, 3%nat, 0%sym, 1%Z);
                            (3%nat, 1%nat, 0%sym, 0%Z);
                            (3%nat, 2%nat, 1%sym, 0%Z);
                            (0%nat, 2%nat, 1%sym, 0%Z)].
 
Definition rwfa : WNFA :=  [(1%nat, 1%nat, 0%sym, 0%Z);
                            (1%nat, 1%nat, 1%sym, 0%Z);
                            (2%nat, 0%nat, 0%sym, (-1)%Z);
                            (2%nat, 2%nat, 1%sym, 0%Z);
                            (0%nat, 0%nat, 0%sym, 0%Z);
                            (0%nat, 2%nat, 1%sym, 0%Z)].

Open Scope nat.
Definition lnn : list nat := [0;1;2;3].
Definition lnp : list nat := [0].
Definition rnn : list nat := [1].
Definition rnp : list nat := [0;1;2].
Close Scope nat.

Definition aset : list AcceptTuple :=  [(A, 0%sym, 0%nat, 0%nat, Some 0%Z, Some 0%Z);
                                        (D, 0%sym, 2%nat, 0%nat, Some 1%Z, None);
                                        (B, 1%sym, 3%nat, 2%nat, Some 1%Z, None);
                                        (B, 1%sym, 2%nat, 2%nat, Some 1%Z, None);
                                        (C, 0%sym, 3%nat, 0%nat, Some 1%Z, None);
                                        (C, 1%sym, 2%nat, 2%nat, Some 1%Z, None);
                                        (E, 1%sym, 0%nat, 0%nat, Some 0%Z, Some 0%Z);
                                        (E, 0%sym, 0%nat, 0%nat, Some 0%Z, Some 0%Z);
                                        (B, 1%sym, 2%nat, 0%nat, Some 1%Z, None);
                                        (C, 0%sym, 2%nat, 2%nat, Some 2%Z, None);
                                        (C, 1%sym, 2%nat, 0%nat, Some 1%Z, None);
                                        (E, 1%sym, 2%nat, 0%nat, Some 0%Z, None);
                                        (D, 1%sym, 3%nat, 2%nat, Some 2%Z, None);
                                        (A, 0%sym, 3%nat, 2%nat, Some 1%Z, None);
                                        (B, 0%sym, 2%nat, 0%nat, Some 0%Z, None);
                                        (C, 1%sym, 3%nat, 0%nat, Some 1%Z, None);
                                        (C, 1%sym, 3%nat, 2%nat, Some 1%Z, None);
                                        (D, 1%sym, 2%nat, 0%nat, Some 2%Z, None);
                                        (E, 1%sym, 2%nat, 2%nat, Some 1%Z, None);
                                        (C, 0%sym, 3%nat, 2%nat, Some 2%Z, None);
                                        (D, 1%sym, 2%nat, 2%nat, Some 2%Z, None);
                                        (C, 0%sym, 2%nat, 0%nat, Some 1%Z, None);
                                        (E, 0%sym, 2%nat, 0%nat, Some (-1)%Z, None);
                                        (B, 0%sym, 2%nat, 2%nat, Some 0%Z, None);
                                        (D, 0%sym, 2%nat, 2%nat, Some 1%Z, None);
                                        (E, 1%sym, 3%nat, 2%nat, Some 1%Z, None);
                                        (E, 1%sym, 3%nat, 0%nat, Some 0%Z, None);
                                        (A, 0%sym, 3%nat, 0%nat, Some 0%Z, None)].

Definition certData := (lwfa, rwfa, lnn, lnp, rnn, rnp, aset).

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply check_MITMWFA_cert_correct with certData. reflexivity.
Qed.