(** * Compute: executable Turing machine model *)

(** The model in [TM] uses coinductive, infinite streams, for which
    equality is undecidable, and a step relation, which isn't
    explicitly computable. This is nice for abstract reasoning,
    but not directly usable for deciding Turing machines.
    Here, we'll introduce a computable model, and prove
    that corresponds to the abstract one. *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lia.
From BusyCoq Require Export TM.
Set Default Goal Selector "!".

Module Compute (Ctx : Ctx).
  Local Module TM := TM Ctx. Export TM.

(** During computation, a tape is represented similarly to [tape], but
    with finite lists at each side, implicitly completed with [s0]. *)
Definition ctape : Type := list Sym * Sym * list Sym.

(** Lifting [ctape] into the corresponding [tape]. *)
Fixpoint lift_side (xs : list Sym) : Stream Sym :=
  match xs with
  | [] => const s0
  | x :: xs => Cons x (lift_side xs)
  end.

Definition lift_tape (t : ctape) : tape :=
  match t with (l, s, r) => (lift_side l, s, lift_side r) end.

Definition lift (c : Q * ctape) : Q * tape :=
  match c with (q, t) => (q, lift_tape t) end.

(** Deciding whether two [ctape]s correspond to the same [tape]. *)
Fixpoint empty_side (xs : list Sym) : bool :=
  match xs with
  | x :: xs => eqb_sym x s0 && empty_side xs
  | [] => true
  end.

Lemma empty_side_spec : forall xs,
  reflect (lift_side xs = const s0) (empty_side xs).
Proof.
  induction xs.
  - apply ReflectT. reflexivity.
  - simpl.
    destruct (eqb_sym_spec a s0) as [E | Hneq].
    + subst a.
      inverts IHxs as Elift Eempty.
      * apply ReflectT. rewrite Elift, <- const_unfold. reflexivity.
      * apply ReflectF. rewrite const_unfold. congruence.
    + apply ReflectF. rewrite const_unfold. congruence.
Qed.

Fixpoint eqb_side (xs ys : list Sym) : bool :=
  match xs with
  | x :: xs' =>
    match ys with
    | y :: ys' => eqb_sym x y && eqb_side xs' ys'
    | [] => empty_side xs
    end
  | [] => empty_side ys
  end.

Lemma eqb_side_spec : forall xs ys,
  reflect (lift_side xs = lift_side ys) (eqb_side xs ys).
Proof.
  induction xs; intros ys.
  - simpl. apply reflect_sym, empty_side_spec.
  - destruct ys as [| y ys].
    + apply empty_side_spec.
    + simpl.
      destruct (eqb_sym_spec a y) as [E | Hneq].
      * subst a. simpl.
        destruct (IHxs ys) as [E | Hneq]; constructor; congruence.
      * apply ReflectF. congruence.
Qed.

Definition eqb_tape (t t' : ctape) : bool :=
  match t, t' with
  | (l, s, r), (l', s', r') =>
    eqb_side l l' && eqb_sym s s' && eqb_side r r'
  end.

Lemma eqb_tape_spec : forall t t',
  reflect (lift_tape t = lift_tape t') (eqb_tape t t').
Proof.
  intros [[l s] r] [[l' s'] r']. simpl.
  apply iff_reflect.
  repeat rewrite andb_true_iff.
  rewrite <- (reflect_iff _ _ (eqb_side_spec l l')).
  rewrite <- (reflect_iff _ _ (eqb_sym_spec  s s')).
  rewrite <- (reflect_iff _ _ (eqb_side_spec r r')).
  repeat split; try (inverts H; auto).
  intros [[H1 H2] H3]. congruence.
Qed.

Definition eqb (c c' : Q * ctape) : bool :=
  match c, c' with
  | q;; t, q';; t' => eqb_q q q' && eqb_tape t t'
  end.

Lemma eqb_spec : forall c c',
  reflect (lift c = lift c') (eqb c c').
Proof.
  intros [q t] [q' t']. simpl.
  apply iff_reflect. rewrite andb_true_iff.
  rewrite <- (reflect_iff _ _ (eqb_q_spec q q')).
  rewrite <- (reflect_iff _ _ (eqb_tape_spec t t')).
  repeat split; try (inverts H; auto).
  intros [H1 H2]. congruence.
Qed.

(** Movement on [ctape]s. *)
Definition left (t : ctape) : ctape :=
  match t with
  | ([], s, r) => ([], s0, s :: r)
  | (s' :: l, s, r) => (l, s', s :: r)
  end.

Definition right (t : ctape) : ctape :=
  match t with
  | (l, s, []) => (s :: l, s0, [])
  | (l, s, s' :: r) => (s :: l, s', r)
  end.

Arguments left : simpl never.
Arguments right : simpl never.

Lemma lift_left : forall t, lift_tape (left t) = move_left (lift_tape t).
Proof.
  intros [[[| s' l] s] r]; reflexivity.
Qed.

Lemma lift_right : forall t, lift_tape (right t) = move_right (lift_tape t).
Proof.
  intros [[l s] [| s' r]]; reflexivity.
Qed.

(** Computable semantics of Turing machines. *)
Definition cstep (tm : TM) (c : Q * ctape) : option (Q * ctape) :=
  match c with
  | q;; l {{s}} r =>
    match tm (q, s) with
    | None => None
    | Some (s', L, q') => Some (q';; left  (l {{s'}} r))
    | Some (s', R, q') => Some (q';; right (l {{s'}} r))
    end
  end.

Lemma cstep_halting : forall tm c,
  cstep tm c = None -> halting tm (lift c).
Proof.
  introv H. destruct c as [q [[l s] r]]. unfold halting.
  simpl. simpl in H.
  destruct (tm (q;; s)) as [[[s' []] q'] |]; try discriminate.
  reflexivity.
Qed.

Lemma cstep_some : forall tm c c',
  cstep tm c = Some c' ->
  lift c -[ tm ]-> lift c'.
Proof.
  introv H. destruct c as [q [[l s] r]].
  simpl. simpl in H.
  destruct (tm (q;; s)) as [[[s' []] q1] |] eqn:E; inverts H as; simpl.
  - rewrite lift_left. apply step_left. assumption.
  - rewrite lift_right. apply step_right. assumption.
Qed.

Fixpoint cmultistep (tm : TM) (n : nat) (c : Q * ctape) : option (Q * ctape) :=
  match n with
  | 0 => Some c
  | S n' =>
    match cstep tm c with
    | Some c' => cmultistep tm n' c'
    | None => None
    end
  end.

Lemma cmultistep_some : forall tm n c c',
  cmultistep tm n c = Some c' ->
  lift c -[ tm ]->> n / lift c'.
Proof.
  induction n; introv H; simpl in H.
  - inverts H. apply multistep_0.
  - destruct (cstep tm c) as [c1 |] eqn:E.
    + apply IHn in H. apply cstep_some in E.
      eapply multistep_S; eassumption.
    + discriminate.
Qed.

Lemma cmultistep_halts_in : forall tm n c,
  cmultistep tm n c = None ->
  exists n', n' < n /\ halts_in tm (lift c) n'.
Proof.
  induction n; introv H.
  - discriminate.
  - simpl in H. destruct (cstep tm c) as [c1 |] eqn:E.
    + apply IHn in H. apply cstep_some in E.
      destruct H as [n' [Hlt [ch [Hrun Hhalting]]]].
      exists (S n'). split.
      * lia.
      * exists ch. split.
        ** eapply multistep_S; eassumption.
        ** assumption.
    + apply cstep_halting in E. exists 0. split.
      * lia.
      * exists (lift c). split.
        ** apply multistep_0.
        ** assumption.
Qed.

Corollary cmultistep_halts : forall tm n c,
  cmultistep tm n c = None ->
  halts tm (lift c).
Proof.
  introv H.
  apply cmultistep_halts_in in H.
  destruct H as [n' [_ H]].
  exists n'. exact H.
Qed.

(** The starting configuration. *)
Definition starting : Q * ctape := q0;; [] {{s0}} [].

Lemma lift_starting : lift starting = c0.
Proof. reflexivity. Qed.

End Compute.
