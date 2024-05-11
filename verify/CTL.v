From BusyCoq Require Export Permute.

Module CTL (Ctx : Ctx).
  Module Permute := Permute Ctx. Export Permute.

Definition Language :Type := Q * tape -> Prop.

Definition closed (L : Language) (tm : TM) :=
    forall c c',
    c -[ tm ]-> c' ->
    L c ->
    L c'.

Definition non_halt (L : Language) (tm : TM) :=
    forall c,
    L c ->
    ~halted tm c.

Lemma closed_tape_language_nonhalt:
    forall (L : Language) (tm: TM) (c: Q*tape),
    closed L tm ->
    non_halt L tm ->
    L c ->
    ~ halts tm c.
Proof.
    introv HClosed HNonhalt HStart. 
    apply progress_nonhalt with (P:=L).
    -   introv Hc1.
        unfold non_halt in HNonhalt.
        pose proof Hc1 as Hnext.
        apply HNonhalt in Hnext.
        apply no_halted_step in Hnext.
        destruct Hnext as [c2 HStep].
        exists c2.
        split.
        +   unfold closed in HClosed.
            apply HClosed with (c := c1). assumption. assumption.
        +   apply progress_intro with (c' := c2). assumption. apply evstep_refl.
    -   assumption.
Qed.

End CTL.