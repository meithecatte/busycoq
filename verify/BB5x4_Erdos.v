(** * The BB(5,4) machine equivalent to Erdös' conjecture on powers of 2 *)

From Coq Require Import Lia PeanoNat Lists.List. Import ListNotations.
From Coq.micromega Require Import ZifyNat.
From BusyCoq Require Export Individual.
Set Default Goal Selector "!".

Lemma cases_mod3 : forall n,
  n mod 3 = 0 \/ n mod 3 = 1 \/ n mod 3 = 2.
Proof. lia. Qed.

(** Instantiate the development to BB(5, 4). We descriptive names tailored for
 * this specific machine. *)
Inductive state :=
  | mul2_F
  | mul2_G
  | find_2
  | rewind
  | check_halt.
Inductive sym := S0 | S1 | S2 | Sblank.

Module BB5x4 <: Ctx.
  Definition Q := state.
  Definition Sym := sym.
  Definition q0 := mul2_G. (* initial state *)
  Definition q1 := mul2_F. (* arbitrary other state *)
  Definition s0 := Sblank. (* blank symbol *)
  Definition s1 := S1.     (* arbitrary other symbol *)

  Lemma q0_neq_q1 : q0 <> q1.
  Proof. discriminate. Qed.

  Lemma s0_neq_s1 : s0 <> s1.
  Proof. discriminate. Qed.

  Definition eqb_q (a b : Q): {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition eqb_sym (a b : Sym): {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition all_qs := [mul2_F; mul2_G; find_2; rewind; check_halt].

  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.

  Definition all_syms := [S0; S1; S2; Sblank].

  Lemma all_syms_spec : forall a, In a all_syms.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.
End BB5x4.

Module Individual5x4 := Individual BB5x4.
Export Individual5x4.

Declare Scope sym_scope.
Bind Scope sym_scope with Sym.
Delimit Scope sym_scope with sym.
Open Scope sym.

Notation "0" := S0 : sym_scope.
Notation "1" := S1 : sym_scope.
Notation "2" := S2 : sym_scope.
Notation "#" := Sblank : sym_scope.

(** Ternary representations, in terms of the symbol type. *)

(* Helper function. Assumes that [n < 3], but we don't encode this in the
   typesystem. *)
Definition sym_of (n : nat) : sym :=
  match n with
  | 0%nat => 0
  | 1%nat => 1
  | _ => 2
  end.

Definition ternary : nat -> list sym :=
  Fix Wf_nat.lt_wf (fun _ => list sym) (fun n ternary =>
    if Nat.eq_dec n 0
      then []
      else sym_of (n mod 3) :: ternary (n / 3)
        (ltac:(apply Nat.div_lt; lia))).

Lemma ternary_unfold : forall n, ternary n =
  if Nat.eq_dec n 0
    then []
    else sym_of (n mod 3) :: ternary (n / 3).
Proof.
  intros.
  unfold ternary at 1.
  rewrite Fix_eq.
  - reflexivity.
  - introv H.
    destruct (Nat.eq_dec x 0); try rewrite H; reflexivity.
Qed.

Lemma sym_of_no_blank : forall n, # <> sym_of n.
Proof.
  intros [| [| n]]; discriminate.
Qed.

Lemma ternary_no_blank : forall n, ~ In # (ternary n).
Proof.
  induction n as [n IH] using strong_induction.
  rewrite ternary_unfold.
  destruct (Nat.eq_dec n 0).
  - apply in_nil.
  - apply not_in_cons. split.
    + apply sym_of_no_blank.
    + apply IH. lia.
Qed.

(** The conjecture and its corresponding Turing machine. *)
Definition ErdosConjecture : Prop :=
  forall n, n > 8 -> In 2 (ternary (2^n)).

(* We use IsCounterexample to later state that the TM halting gives
 * a constructive counterexample. *)
Definition IsCounterexample (n : nat) : Prop :=
  n > 8 /\ ~ In 2 (ternary (2^n)).

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | mul2_F, 0 => Some (0, R, mul2_F)
  | mul2_F, 1 => Some (2, R, mul2_F)
  | mul2_F, 2 => Some (1, R, mul2_G)
  | mul2_F, # => Some (#, L, find_2)

  | mul2_G, 0 => Some (1, R, mul2_F)
  | mul2_G, 1 => Some (0, R, mul2_G)
  | mul2_G, 2 => Some (2, R, mul2_G)
  | mul2_G, # => Some (1, R, mul2_F)

  | find_2, 0 => Some (0, L, find_2)
  | find_2, 1 => Some (1, L, find_2)
  | find_2, 2 => Some (2, L, rewind)
  | find_2, # => Some (#, L, check_halt)

  | rewind, 0 => Some (0, L, rewind)
  | rewind, 1 => Some (1, L, rewind)
  | rewind, 2 => Some (2, L, rewind)
  | rewind, # => Some (#, R, mul2_F)

  | check_halt, 0 => Some (1, R, rewind)
  | check_halt, 1 => Some (2, R, rewind)
  | check_halt, 2 => None
  | check_halt, # => Some (0, R, rewind)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** First, the behavior of the multiplication-by-2 FST *)

(* TM state for a particular value of carry-in *)
Definition stc (c : nat) : Q :=
  match c with
  | 0%nat => mul2_F
  | _ => mul2_G
  end.

(* Note that we could state a stronger lemma, with [-->] instead of [-->*],
   but that doesn't compose well with the tactics. *)
Lemma step_mul2 : forall n c l r,
  c < 2 ->
  l {{stc c}}> sym_of (n mod 3) >> r -->*
  l << sym_of ((c + 2*(n mod 3)) mod 3) {{stc ((c + 2*(n mod 3)) / 3)}}> r.
Proof.
  introv H.
  assert (H': (c = 0 \/ c = 1) % nat) by lia.
  destruct H' as [-> | ->];
    destruct (cases_mod3 n) as [E | [E | E]]; rewrite E in *;
    execute.
Qed.

(* Prove both the behavior of mul2_F and mul2_G at once, since we need mutual
   induction between them. *)
Lemma do_mul2' : forall n l c,
  c < 2 ->
  l {{stc c}}> ternary n *> const # -->+
  l <* rev (ternary (c + 2*n)) <{{find_2}} const #.
Proof.
  induction n as [n IH] using strong_induction.
  introv H.
  destruct (Nat.eq_dec n 0) as [-> | Hneq].
  - (* n = 0 *) simpl.
    assert (H': (c = 0 \/ c = 1) % nat) by lia.
    destruct H' as [-> | ->]; start_progress.
  - (* n <> 0 *)
    rewrite (ternary_unfold n).
    destruct (Nat.eq_dec n 0); [contradiction|].
    rewrite (ternary_unfold (c + 2*n)).
    destruct (Nat.eq_dec (c + 2*n) 0); [lia|].
    cbn[rev]. rewrite Str_app_assoc. cbn[Str_app].
    follow step_mul2.
    eapply progress_evstep_trans. { apply IH; lia. }
    finish.
Qed.

Corollary do_mul2 : forall n l,
  l {{mul2_F}}> ternary n *> const # -->+
  l <* rev (ternary (2*n)) <{{find_2}} const #.
Proof.
  introv.
  exact (do_mul2' n l 0 ltac:(lia)).
Qed.

(** Now, for the other subcomponents *)
Lemma step_rewind : forall l x r,
  x <> # ->
  l << x <{{rewind}} r -->*
  l <{{rewind}} x >> r.
Proof.
  introv H.
  destruct x; [execute.. | congruence].
Qed.

Lemma do_rewind : forall xs l r,
  ~ In # xs ->
  l << # <* xs <{{rewind}} r -->*
  l << # {{mul2_F}}> rev xs *> r.
Proof.
  induction xs as [| x xs IH]; introv H.
  - execute.
  - rewrite not_in_cons in H. destruct H as [Hneq Hnotin].
    cbn[Str_app]. follow step_rewind. follow IH.
    cbn[rev]. rewrite Str_app_assoc. finish.
Qed.

Lemma do_find2_found : forall xs l r,
  ~ In # xs ->
  In 2 xs ->
  l << # <* xs <{{find_2}} r -->*
  l << # {{mul2_F}}> rev xs *> r.
Proof.
  induction xs as [| x xs IH]; introv Hblank H2.
  - destruct H2.
  - rewrite not_in_cons in Hblank. destruct Hblank as [Hneq Hblank].
    destruct x. 4: congruence.
    3: { (* x = 2 *)
      clear H2. clear Hneq.
      step. follow do_rewind. finish. }
    all: destruct H2 as [|H2]; [congruence|].
    all: step; follow IH; finish.
Qed.

Lemma do_find2_notfound : forall xs l r,
  ~ In # xs ->
  ~ In 2 xs ->
  l << # <* xs <{{find_2}} r -->*
  l <{{check_halt}} # >> rev xs *> r.
Proof.
  induction xs as [| x xs IH]; introv Hblank H2.
  - execute.
  - rewrite not_in_cons in Hblank. destruct Hblank as [Hneq1 Hblank].
    rewrite not_in_cons in H2. destruct H2 as [Hneq2 H2].
    destruct x. 3, 4: congruence.
    all: step; follow IH; finish.
Qed.

(** Main loop of the TM *)
Definition C (x : sym) (n : nat) : Q * tape :=
  const # << x << # {{mul2_F}}> ternary n *> const #.

Definition next (x : sym) : option sym :=
  match x with
  | # => Some 0
  | 0 => Some 1
  | 1 => Some 2
  | 2 => None
  end.

Lemma mul2 : forall x n,
  In 2 (ternary (2*n)) ->
  C x n -->+ C x (2*n).
Proof.
  introv H.
  eapply progress_evstep_trans. { apply do_mul2. }
  follow do_find2_found.
    1, 2: rewrite <- In_rev.
    2: apply H. 1: apply ternary_no_blank.
  rewrite rev_involutive.
  finish.
Qed.

Corollary mul2' : forall x n,
  In 2 (ternary (2*n)) ->
  C x n -->* C x (2*n).
Proof.
  introv H. now apply progress_evstep, mul2.
Qed.

Corollary incr : forall x n,
  In 2 (ternary (2^S n)) ->
  C x (2^n) -->+ C x (2^(S n)).
Proof.
  introv H. rewrite Nat.pow_succ_r' in *. now apply mul2.
Qed.

Lemma found_counterexample' : forall n x,
  ~ In 2 (ternary (2*n)) ->
  C x n -->*
  const # << x <{{check_halt}} # >> ternary (2*n) *> const #.
Proof.
  introv H.
  eapply evstep_trans. { eapply progress_evstep, do_mul2. }
  follow do_find2_notfound.
    1, 2: rewrite <- In_rev.
    2: apply H. 1: apply ternary_no_blank.
  rewrite rev_involutive.
  finish.
Qed.

Lemma found_counterexample : forall n x x',
  ~ In 2 (ternary (2*n)) ->
  next x = Some x' ->
  C x n -->* C x' (2*n).
Proof.
  introv Hin Hnext.
  follow found_counterexample'.
  destruct x; inverts Hnext; execute.
Qed.

(** Executing through the known counterexamples *)
Ltac initialize :=
  lazymatch goal with
  | |- C ?x (2^?n) -->* _ =>
    destruct (In_dec eqb_sym 2 (ternary (2^S n))) as [H | H] eqn:E;
      cbv in E; try discriminate E;
    lazymatch type of E with
    | Yes = Yes => follow mul2';
      clear H E; rewrite <- Nat.pow_succ_r'
    | No = No =>
      let sx' := eval cbv in (next x) in
      lazymatch sx' with
      | Some ?x' =>
        follow (found_counterexample (2^n) x x');
        clear H E; rewrite <- Nat.pow_succ_r'
      end
    end
  end.

Lemma start :
  c0 -->* C 2 (2^8).
Proof.
  apply evstep_trans with (C 0 (2^0)).
  { do 6 step. finish. }
  do 8 initialize.
  finish.
Qed.

(** Overall behavior *)
Theorem halts_implies_counterexample :
  halts tm c0 -> exists n, IsCounterexample n.
Proof.
  introv H.
  pose proof start as H'. apply halts_evstep' in H'; [|exact H].
  apply progress_halts_cond with
    (C := fun n => C 2 (2^n))
    (P := fun n => n >= 8)
    (Z := fun n => ~ In 2 (ternary (2^S n)))
    in H'.
  3: lia.
  1: destruct H' as [n [H1 H2]]; exists (S n);
    unfold IsCounterexample; intuition lia.
  introv Hgeq.
  destruct (In_dec eqb_sym 2 (ternary (2^S i))) as [Hyes | Hno];
    eauto 7 using incr.
Qed.

Lemma halts_or_k : forall k, k >= 8 ->
  halts tm c0 \/ c0 -->* C 2 (2^k).
Proof.
  induction k. { lia. }
  introv Hgeq.
  destruct (Nat.eq_dec (S k) 8) as [-> | Hk].
  - right. apply start.
  - specialize (IHk ltac:(lia)).
    destruct IHk as [Hhalts | Hexec]; [auto|].
    destruct (In_dec eqb_sym 2 (ternary (2^S k))) as [Hyes | Hno].
    + right. follow Hexec. now apply progress_evstep, incr.
    + left. eapply halted_evstep_halts.
      { follow Hexec. follow found_counterexample'. finish. }
      reflexivity.
Qed.

Theorem counterexample_implies_halt : forall n,
  IsCounterexample n -> halts tm c0.
Proof.
  unfold IsCounterexample.
  introv [Hgeq Hno2].
  destruct n as [|n]; [lia|].
  destruct (halts_or_k n ltac:(lia)) as [|Hexec]; [assumption|].
  eapply halted_evstep_halts.
  { follow Hexec. follow found_counterexample'. finish. }
  reflexivity.
Qed.

(** And, the punchline: *)
Corollary counterexample_eqv_halt :
  halts tm c0 <-> exists n, IsCounterexample n.
Proof.
  split.
  - apply halts_implies_counterexample.
  - intros [n H]. eauto using counterexample_implies_halt.
Qed.

Theorem conjecture_eqv_nonhalt :
  ErdosConjecture <-> ~ halts tm c0.
Proof.
  rewrite counterexample_eqv_halt.
  unfold ErdosConjecture, IsCounterexample.
  split.
  - introv Hconj Hc. jauto.
  - introv Hnc Hgeq.
    destruct (In_dec eqb_sym 2 (ternary (2^n))) as [| H]; [assumption|].
    exfalso. apply Hnc. eauto.
Qed.
