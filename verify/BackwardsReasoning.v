(** * Backwards Reasoning *)

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.Streams.
From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Module BackwardsReasoning (Ctx : Ctx).
  Module Flip := Flip Ctx. Export Flip.

Definition all_qs := list_prod all_qs all_syms.

Lemma all_qs_spec : forall a, In a all_qs.
Proof. introv. destruct a. apply in_prod; auto. Qed.

Local Hint Resolve all_qs_spec : core.

Fixpoint side_matches {d} (xs : side d) (ys : side d) : Prop :=
  match ys with
  | dnil => True
  | dcons y ys => hd xs = y /\ side_matches (tl xs) ys
  end.

Lemma side_matches_nil : forall d (xs : side d), side_matches xs dnil.
Proof. split. Qed.

Lemma side_matches_cons : forall d (xs ys : side d),
  side_matches (tl xs) ys ->
  side_matches xs (dcons (hd xs) ys).
Proof.
  introv H. simpl in *. intuition.
Qed.

Local Hint Resolve side_matches_nil : core.
Local Hint Resolve side_matches_cons : core.

Definition stencil : Type := Q * tape.

Definition matches (t : Q * tape) (t' : stencil) : Prop :=
  match t, t' with
  | q;; l {{s}} r, q';; l' {{s'}} r' =>
    q = q' /\ s = s' /\ side_matches l l' /\ side_matches r r'
  end.

Local Hint Unfold matches : core.

Definition find_transitions (tm : TM) (f : option (Sym * dir * Q) -> bool)
    : list (Q * Sym) :=
  filter (fun a => f (tm a)) all_qs.

Lemma find_transitions_In : forall tm f q s,
  f (tm (q, s)) = true <->
  In (q, s) (find_transitions tm f).
Proof.
  introv.
  unfold find_transitions.
  rewrite filter_In.
  intuition.
Qed.

Definition halting_transitions (tm : TM) :=
  find_transitions tm (fun cmd =>
    match cmd with
    | Some _ => false
    | None => true
    end).

Definition haltings (tm : TM) : list stencil :=
  map (fun '(q, s) => q;; <[] {{s}} []>) (halting_transitions tm).

Lemma haltings_spec : forall tm c,
  halted tm c -> Exists (matches c) (haltings tm).
Proof.
  introv H. destruct c as [q [[l s] r]].
  unfold halted in H.
  assert (Hfound : In (q, s) (halting_transitions tm)).
  { unfold halting_transitions.
    rewrite <- find_transitions_In.
    rewrite H. reflexivity. }
  eapply in_map in Hfound.
  rewrite Exists_exists.
  eauto 7.
Qed.

(* Check if we could've had [s'] on the tape before moving
   in the direction [d]. *)
Definition symbol_ok (t : tape) (s' : Sym) (d : dir) :=
  match d, t with
  | L, _ {{_}} dnil        => true
  | L, _ {{_}} (dcons s _) => if eqb_sym s s' then true else false
  | R,        dnil {{_}} _ => true
  | R, (dcons s _) {{_}} _ => if eqb_sym s s' then true else false
  end.

(* If we took the [(q, s)] transition and ended up at [st], how did the
   tape look before? *)
Definition rewind (tm : TM) (st : stencil) (q : Q) (s : Sym) : option stencil :=
  let '(qfin, tfin) := st in
  match tm (q, s) with
  | None => None
  | Some (s', d, q') =>
    if eqb_q qfin q' then
      if symbol_ok tfin s' d then
        let '(l, _, r) :=
          match d with
          | L => move_right tfin
          | R => move_left tfin
          end
        in
        Some (q;; l {{s}} r)
      else
        None
    else
      None
  end.

Lemma rewind_spec : forall tm q l s r c' st,
  q;; l {{s}} r -[ tm ]-> c' ->
  matches c' st ->
  exists st0, rewind tm st q s = Some st0 /\ matches (q;; l {{s}} r) st0.
Proof.
  introv Hstep Hmatch.
  destruct c' as [q' [[l' s'] r']].
  destruct st as [q'' [[stl s''] str]].
  destruct Hmatch as [Eq [Es [Hl Hr]]]. subst q'' s''.
  inverts Hstep as Htm;
    unfold rewind;
    rewrite Htm; destruct (eqb_q q' q'); try congruence;
    lazymatch goal with
    | H: side_matches (dcons ?side ?s) ?st |- _ =>
      destruct st; [clear H | inverts H]
    end; simpl;
    lazymatch goal with
    | |- context [eqb_sym ?s ?s] => destruct (eqb_sym s s); try congruence
    | _ => idtac
    end;
    eexists; repeat split; auto.
Qed.

Fixpoint has_contra (tm : TM) (n : nat) (st : stencil) :=
  match n with
  | O => false
  | S n =>
    forallb (fun '(q, s) =>
      match rewind tm st q s with
      | Some st' => has_contra tm n st'
      | None => true
      end)
      all_qs
  end.

Theorem has_contra_spec : forall tm n c c' st,
  c -[ tm ]->> n / c' ->
  matches c' st ->
  has_contra tm n st = true ->
  False.
Proof.
  induction n; introv Hrun Hmatches Hcontra.
  - discriminate.
  - apply multistep_last in Hrun.
    destruct Hrun as [c'' [Hrun Hstep]].
    simpl in Hcontra. rewrite forallb_forall in Hcontra.
    destruct c'' as [q [[l s] r]].
    specialize (Hcontra (q, s) (all_qs_spec _)).
    simpl in Hcontra.
    apply rewind_spec with (st := st) in Hstep; try assumption.
    destruct Hstep as [st' [Erewind Hmatches']].
    rewrite Erewind in Hcontra.
    eauto.
Qed.

Definition verify_backwards (tm : TM) (n : nat) : bool :=
  if cmultistep tm n c0 then
    forallb (has_contra tm n) (haltings tm)
  else
    false.

Theorem verify_backwards_correct : forall tm n,
  verify_backwards tm n = true ->
  ~ halts tm c0.
Proof.
  introv H Hhalts. unfold verify_backwards in H.
  destruct (cmultistep tm n c0) as [[c' Hexec] |]; try discriminate.
  destruct Hhalts as [m Hhalts].
  assert (Hle : n <= m)
    by eauto using within_halt.

  destruct Hhalts as [ch [Hhaltrun Hhalting]].
  apply (rewind_split' (m - n) n) in Hhaltrun; try lia.
  destruct Hhaltrun as [c1 [Hrun1 Hrun2]].

  apply haltings_spec in Hhalting.
  rewrite Exists_exists in Hhalting.
  destruct Hhalting as [st [Hin Hmatches]].

  rewrite forallb_forall in H. apply H in Hin.
  eapply has_contra_spec; eassumption.
Qed.

End BackwardsReasoning.
