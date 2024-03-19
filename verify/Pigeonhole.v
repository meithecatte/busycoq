From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From BusyCoq Require Export LibTactics.
Set Default Goal Selector "!".

(** [repeats xs] if [xs] repeats an element. *)
Inductive repeats {X : Type} : list X -> Prop :=
  | repeats_head x xs : In x xs -> repeats (x :: xs)
  | repeats_cons x xs : repeats xs -> repeats (x :: xs).

Hint Constructors repeats : core.

Lemma in_split : forall (X : Type) (x : X) (l : list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  introv H. induction l as [| a l IH].
  - inverts H.
  - destruct H.
    + subst a. exists (@nil X), l. reflexivity.
    + specialize (IH H). destruct IH as [l1' [l2' IH]].
      subst l. exists (a :: l1'), l2'. reflexivity.
Qed.

Hint Extern 1 (In _ (_ :: _)) => left : core.
Hint Extern 1 (In _ (_ :: _)) => right : core.

(* See below for the motivation on this lemma. *)
Lemma insplit_decide : forall (X : Type) (x : X) (l1 l2a l2b : list X),
  Forall (fun y => In y (l2a ++ x :: l2b)) l1 ->
  In x l1 \/ Forall (fun y => In y (l2a ++ l2b)) l1.
Proof.
  introv Hsubset.
  induction l1 as [| a l1 IH].
  - auto.
  - inverts Hsubset as Ha Hsubset. specialize (IH Hsubset).
    (* Take care of the simple case where IH has already found x in l1. *)
    destruct IH as [IH | IH]. { auto. }
    apply in_app_or in Ha.
    destruct Ha as [Ha | [Ha | Ha]]; auto using in_or_app.
Qed.

Theorem pigeonhole_principle : forall (X : Type) (l1 l2 : list X),
  Forall (fun x => In x l2) l1 ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros X l1. induction l1 as [| x l1 IH]; introv Hsubset Hlonger.
  - inverts Hlonger.
  - (* Proof sketch: if [In x l1], we win – that's the element that repeats.
       Otherwise, remove x from l2, which lets us preserve [Hlonger]
       for the induction hypothesis.

       How do we decide if [In x l1], though?

       Answer: [Hsubset] implicitly encodes one position of [x] in [l2],
       as well as one position of each element of [l1] in [l2]. If the position
       of [x] is not referenced by any element of [l1], we can remove it and
       invoke the induction hypothesis. *)

    (* First, we locate at least one occurrence of [x] in [l2]: *)
    inverts Hsubset as Hx Hsubset.

    (* This is the occurrence we'll be trying to remove for our induction step: *)
    apply in_split in Hx.
    destruct Hx as [l2a [l2b El2]]. subst l2.

    (* Iterate over [l1] and see if [Hsubset] ever points at that [x]. If so,
       [In x l1]. Otherwise we have the precondition of [IH]. *)
    apply insplit_decide in Hsubset.
    destruct Hsubset as [Hx | Hsubset]. { auto. }
    specialize (IH _ Hsubset).

    autorewrite with list in Hlonger, IH. simpl length in Hlonger.
    apply repeats_cons, IH.
    lia.
Qed.
