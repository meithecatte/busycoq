From BusyCoq Require Export CTL.
From Coq Require Import Lists.List.
From Coq Require Import Lists.Streams.
From Coq Require Import ZArith.
From Coq Require Import Bool.Sumbool.
Local Open Scope Z_scope.


Module WNFA (Ctx : Ctx).
  Module CTL := CTL Ctx. Export CTL.

Fixpoint inP {A:Type} (P:A->bool) (l:list A) : bool :=
    match l with
    | [] => false
    | hd :: tl => orb (P hd) (inP P tl)
    end.

Lemma inP_exists :
    forall (A:Type) P (l:list A),
        inP P l = true
        <->
        exists a, In a l /\ P a = true.
Proof.
    introv. induction l as [|hd tl].
    -   split.
        +   intros H. discriminate.
        +   introv [a [H1 H2]]. destruct H1.
    -   simpl. destruct (P hd) eqn: Case.
        +   split; try reflexivity.
            intros _. exists hd. intuition.
        +   simpl. split.
            *   intros H. apply IHtl in H. destruct H as [a [HIn HPa]].
                exists a. intuition.
            *   intros [a [[H1|H2] HIn]].
                --  rewrite <- H1 in HIn. rewrite Case in HIn. discriminate.
                --  apply IHtl. exists a. intuition.
Qed.                

Definition inEqb {A:Type} P (a:A) (l: list A) :=
    inP (P a) l.

Lemma inEqb_In :
    forall A P a l,
        (forall (x y:A), P x y = true <-> x = y ) ->
        inEqb P a l = true <-> In a l.
Proof.
    introv Heq. unfold inEqb. split.
    -   intros. apply inP_exists in H. destruct H as [a' [HIna' Haa']].
        apply Heq in Haa'. rewrite Haa'. assumption.
    -   intros HIna. apply inP_exists.
        exists a. split; try assumption.
        apply Heq. reflexivity.
Qed.

Definition inb n l :=
    inEqb Nat.eqb n l.

Lemma inb_In : forall n l, 
    inb n l = true <-> In n l.
Proof.
    introv. apply inEqb_In. apply Nat.eqb_eq.
Qed.


Fixpoint allP {A:Type} (P:A->bool) (l:list A) : bool :=
    match l with
    | [] => true
    | hd :: tl => andb (P hd) (allP P tl)
    end.

Lemma allP_forall :
    forall (A:Type) P (l:list A),
        allP P l = true
        <->
        forall a, In a l -> P a = true.
Proof.
    introv. induction l.
    -   split.
        +   intros. destruct H0.
        +   reflexivity.
    -   simpl. split.
        +   intros. apply andb_prop in H. destruct H as [HPa HPtl].
            destruct H0.
            *   rewrite <- H. assumption.
            *   destruct IHl as [IHl _].
                apply IHl with a0 in HPtl; assumption.
        +   intros H. unfold andb. destruct (P a) eqn:Case.
            *   apply IHl. intros.
                apply H. right. assumption.
            *   specialize H with a. destruct H.
                --  left. reflexivity.
                --  rewrite Case. reflexivity.
Qed.               
        
Definition pos_or_zero x :=
    match x with
    |   None => Some 0
    |   Some y => if y <=? 0 then Some 0 else x
    end.

Definition neg_or_zero x :=
    match x with
    |   None => Some 0
    |   Some y => if y >=? 0 then Some 0 else x
    end.


Definition WEdge : Type := nat * nat * Sym * Z. 

Definition WNFA : Type :=  list WEdge.

Inductive wnfa_read_side : WNFA -> side -> nat -> Z -> Prop :=
    | wnfa_start :  forall wnfa, wnfa_read_side wnfa (const s0) 0 0
    | wnfa_step : forall wnfa s q w q' s' w',
                    In (q, q', s', w') wnfa ->
                    wnfa_read_side wnfa s q w ->
                    wnfa_read_side wnfa (s << s') q' (w + w').

Definition non_negative (wnfa : WNFA) (l : list nat) : Prop :=
    forall s q w,
    In q l ->
    wnfa_read_side wnfa s q w ->
    w >= 0.

Definition WEdge_pres_non_negative (l : list nat) (e : WEdge) :=
    match e with
    | (sq, eq, s, w) => if inb eq l
                        then    if inb sq l
                                then w >=? 0
                                else false
                        else    true
    end.

Fixpoint strong_non_negative (wnfa : WNFA) (l : list nat) :=
    match wnfa with
    |   []  =>  true
    |   e :: tl =>  andb (WEdge_pres_non_negative l e) (strong_non_negative tl l)
    end.

Lemma strong_non_negative_In :
    forall wnfa l e,
        In e wnfa ->
        strong_non_negative wnfa l = true ->
        WEdge_pres_non_negative l e = true.
Proof.
    introv HIn Hsnn.
    induction wnfa.
    -   destruct HIn.
    -   simpl in Hsnn.
        apply andb_prop in Hsnn. destruct Hsnn.
        inversion HIn.
        +   rewrite <- H1. assumption.
        +   apply IHwnfa; assumption.
Qed.   

Lemma strong_non_negative_sufficient :
    forall wnfa l,
        strong_non_negative wnfa l = true ->
        non_negative wnfa l.
Proof.
    introv Hsnn. unfold non_negative. introv HIn Hread.
    induction Hread.
    -   discriminate.
    -   assert (Hpres: WEdge_pres_non_negative l (q, q', s', w') = true).
        {   apply strong_non_negative_In with wnfa; assumption. }
        simpl in Hpres.
        apply inb_In in HIn.
        rewrite HIn in Hpres.
        apply Z.le_ge. apply Z.add_nonneg_nonneg.
        +   apply Z.ge_le. apply IHHread.
            *   assumption.
            *   destruct (inb q l) eqn: Hinq.
                --  apply inb_In. assumption.
                --  discriminate.
        +   destruct (inb q l) eqn: Hinq.
            *   apply Z.leb_le. rewrite <- Z.geb_leb. assumption.
            *   discriminate.
Qed.

Definition non_positive (wnfa : WNFA) (l : list nat) : Prop :=
    forall s q w,
    In q l ->
    wnfa_read_side wnfa s q w ->
    w <= 0.

Definition WEdge_pres_non_positive (l : list nat) (e : WEdge) :=
    match e with
    | (sq, eq, s, w) => if inb eq l
                        then    if inb sq l
                                then w <=? 0
                                else false
                        else    true
    end.

Fixpoint strong_non_positive (wnfa : WNFA) (l : list nat) :=
    match wnfa with
    |   []  =>  true
    |   e :: tl =>  andb (WEdge_pres_non_positive l e) (strong_non_positive tl l)
    end.

Lemma strong_non_positive_In :
    forall wnfa l e,
        In e wnfa ->
        strong_non_positive wnfa l = true ->
        WEdge_pres_non_positive l e = true.
Proof.
    introv HIn Hsnn.
    induction wnfa.
    -   destruct HIn.
    -   simpl in Hsnn.
        apply andb_prop in Hsnn. destruct Hsnn.
        inversion HIn.
        +   rewrite <- H1. assumption.
        +   apply IHwnfa; assumption.
Qed.   

Lemma strong_non_positive_sufficient :
    forall wnfa l,
        strong_non_positive wnfa l = true ->
        non_positive wnfa l.
Proof.
    introv Hsnn. unfold non_positive. introv HIn Hread.
    induction Hread.
    -   discriminate.
    -   assert (Hpres: WEdge_pres_non_positive l (q, q', s', w') = true).
        {   apply strong_non_positive_In with wnfa; assumption. }
        simpl in Hpres.
        apply inb_In in HIn.
        rewrite HIn in Hpres.
        apply Z.add_nonpos_nonpos.
        +   apply IHHread.
            *   assumption.
            *   destruct (inb q l) eqn: Hinq.
                --  apply inb_In. assumption.
                --  discriminate.
        +   destruct (inb q l) eqn: Hinq.
            *   apply Z.leb_le. assumption.
            *   discriminate.
Qed.

Definition Reduced_Config : Type := Q * Sym * nat * nat * Z. 

Definition Config_mod_WNFAs (leftWFA rightWFA : WNFA) (c : Q * tape) (c' : Reduced_Config) :=
    match c, c' with
    | (q, (l, s, r)), (q', s', lq, rq, w) => 
                    q = q'
                /\  s = s'
                /\  exists lw rw, lw + rw = w
                            /\  wnfa_read_side leftWFA l lq lw
                            /\  wnfa_read_side rightWFA r rq rw
    end.

Definition AcceptTuple : Type :=  Q * Sym * nat * nat * option Z * option Z.

Inductive AcceptTuple_accept : AcceptTuple -> Reduced_Config -> Prop :=
    | AcceptTuple_accept_bounded :
        forall q s lq rq w lb ub,
            lb <= w ->
            w <= ub -> 
            AcceptTuple_accept (q, s, lq, rq, (Some lb), (Some ub)) (q, s, lq, rq, w)
    | AcceptTuple_accept_upper_bound :
        forall q s lq rq w ub,
            w <= ub -> 
            AcceptTuple_accept (q, s, lq, rq, None, (Some ub)) (q, s, lq, rq, w)
    | AcceptTuple_accept_lower_bound :
        forall q s lq rq w lb,
            lb <= w -> 
            AcceptTuple_accept (q, s, lq, rq, (Some lb), None) (q, s, lq, rq, w)
    | AcceptTuple_accept_unbounded :
    forall q s lq rq w,
            AcceptTuple_accept (q, s, lq, rq, None, None) (q, s, lq, rq, w).

Definition AcceptTuple_covers leftWFA rightWFA a b : Prop :=
    forall c c',
        Config_mod_WNFAs leftWFA rightWFA c c' ->
        AcceptTuple_accept a c' ->
        AcceptTuple_accept b c'.

Definition strong_impossible_config_neg leftNN rightNN (c':Reduced_Config) :=
    match c' with
    |   (q,s,lq,rq,w) =>    if andb (inb lq leftNN) (inb rq rightNN)
                                then (w < 0)
                                else False
    end.

Definition strong_impossible_config_pos leftNP rightNP (c':Reduced_Config) :=
    match c' with
    |   (q,s,lq,rq,w) =>    if andb (inb lq leftNP) (inb rq rightNP)
                                then (w > 0)
                                else False
    end.

Definition strong_impossible_config leftNN leftNP rightNN rightNP c' :=
    strong_impossible_config_neg leftNN rightNN c' \/ strong_impossible_config_pos leftNP rightNP c'.

Definition impossible_config leftWFA rightWFA c' :=
    forall c, ~Config_mod_WNFAs leftWFA rightWFA c c'.

Lemma strong_impossible_config_sufficient:
    forall leftWFA rightWFA leftNN leftNP rightNN rightNP c',
    non_negative leftWFA leftNN ->
    non_positive leftWFA leftNP ->
    non_negative rightWFA rightNN ->
    non_positive rightWFA rightNP ->
    strong_impossible_config leftNN leftNP rightNN rightNP c' ->
    impossible_config leftWFA rightWFA c'.
Proof.
    unfold impossible_config. introv Hlnn Hlnp Hrnn Hrnp HImpossible.
    intros c Hmod. destruct c as [q [[l s]r]]. destruct c' as [[[[q' s'] lq'] rq'] w'].
    destruct Hmod as [Hq [Hs [lw [rw [Hsum [HreadLeft HreadRight]]]]]].
    destruct HImpossible.
    -   unfold strong_impossible_config_neg in H.
        destruct (inb lq' leftNN && inb rq' rightNN)%bool eqn: HCase; try assumption.
        apply andb_prop in HCase as [HinLeft HinRight].
        apply inb_In in HinLeft. apply inb_In in HinRight.
        rewrite <- Hsum in H.   
        apply Hlnn in HreadLeft; try assumption.
        apply Hrnn in HreadRight; try assumption.
        assert (H': 0 <= lw + rw).
        {   apply Ztac.add_le; apply Z.ge_le; assumption. }
        assert (Hcontra: 0<0).
        {   apply Z.le_lt_trans with (lw+rw); assumption. }
        discriminate.
    -   unfold strong_impossible_config_pos in H.
        destruct (inb lq' leftNP && inb rq' rightNP)%bool eqn: HCase; try assumption.
        apply andb_prop in HCase as [HinLeft HinRight].
        apply inb_In in HinLeft. apply inb_In in HinRight.
        rewrite <- Hsum in H.   
        apply Hlnp in HreadLeft; try assumption.
        apply Hrnp in HreadRight; try assumption.
        assert (H': lw + rw <= 0).
        {   apply Z.add_nonpos_nonpos; assumption. }
        assert (Hcontra: 0<0).
        {   apply Z.gt_lt in H. apply Z.lt_le_trans with (lw+rw); assumption. }
        discriminate.
Qed.

Definition AcceptTuple_strong_covers leftNN leftNP rightNN rightNP a b: Prop :=
    forall c',
        AcceptTuple_accept a c' ->
        AcceptTuple_accept b c' \/ strong_impossible_config leftNN leftNP rightNN rightNP c'.

Lemma AcceptTuple_strong_covers_sufficient:
    forall leftWFA rightWFA leftNN leftNP rightNN rightNP a b,
    AcceptTuple_strong_covers leftNN leftNP rightNN rightNP a b ->
    non_negative leftWFA leftNN ->
    non_positive leftWFA leftNP ->
    non_negative rightWFA rightNN ->
    non_positive rightWFA rightNP ->
    AcceptTuple_covers leftWFA rightWFA a b.
Proof.
    introv Hstrong. unfold AcceptTuple_covers. introv Hlnn Hlnp Hrnn Hrnp Hmod Hacc.

    apply Hstrong in Hacc. destruct Hacc. assumption. exfalso.
    apply strong_impossible_config_sufficient
        with (leftWFA := leftWFA) (rightWFA := rightWFA) in H; try assumption.
    apply H in Hmod. assumption.
Qed.

Lemma AcceptTuple_covers_trans:
    forall leftWFA rightWFA a b c,
        AcceptTuple_covers leftWFA rightWFA a b ->
        AcceptTuple_covers leftWFA rightWFA b c ->
        AcceptTuple_covers leftWFA rightWFA a c.
Proof.
    unfold AcceptTuple_covers.
    introv Hab Hbc.
    intros co co' Hmod Ha.
    apply Hbc with co; try assumption.
    apply Hab with co; try assumption.
Qed.

Lemma AcceptTuple_strong_covers_trans :
    forall leftNN leftNP rightNN rightNP a b c,
        AcceptTuple_strong_covers leftNN leftNP rightNN rightNP a b ->
        AcceptTuple_strong_covers leftNN leftNP rightNN rightNP b c ->
        AcceptTuple_strong_covers leftNN leftNP rightNN rightNP a c.
Proof.
    unfold AcceptTuple_strong_covers.
    introv Hab Hbc.
    intros co' Ha.
    apply Hab in Ha. destruct Ha.
    -   apply Hbc. assumption.
    -   right. assumption.
Qed.

Lemma AcceptTuple_strong_covers_lb_le : forall leftNN leftNP rightNN rightNP q s lq rq lb lb' ub,
    lb' <= lb ->
    AcceptTuple_strong_covers leftNN leftNP rightNN rightNP (q,s,lq,rq,Some lb,ub) (q,s,lq,rq,Some lb',ub).
Proof.
    introv Hle. unfold AcceptTuple_strong_covers. introv HAcc. left.
    destruct ub.
    -   inversion HAcc.
        apply AcceptTuple_accept_bounded; try assumption.
        apply Z.le_trans with lb; assumption.
    -   inversion HAcc.
        apply AcceptTuple_accept_lower_bound.
        apply Z.le_trans with lb; assumption.
Qed.

Lemma AcceptTuple_strong_covers_lb_none : forall leftNN leftNP rightNN rightNP q s lq rq lb ub,
    AcceptTuple_strong_covers leftNN leftNP rightNN rightNP (q,s,lq,rq,Some lb,ub) (q,s,lq,rq,None,ub).
Proof.
    introv. unfold AcceptTuple_strong_covers. intros c' HAcc. left.
    destruct ub.
    -   inversion HAcc. apply AcceptTuple_accept_upper_bound. assumption.
    -   inversion HAcc. apply AcceptTuple_accept_unbounded.
Qed.

Lemma AcceptTuple_strong_covers_ub_ge : forall leftNN leftNP rightNN rightNP q s lq rq lb ub ub',
    ub <= ub' ->
    AcceptTuple_strong_covers leftNN leftNP rightNN rightNP (q,s,lq,rq,lb,Some ub) (q,s,lq,rq,lb,Some ub').
Proof.
    introv Hle. unfold AcceptTuple_strong_covers. introv HAcc. left.
    destruct lb.
    -   inversion HAcc.
        apply AcceptTuple_accept_bounded; try assumption.
        apply Z.le_trans with ub; assumption.
    -   inversion HAcc.
        apply AcceptTuple_accept_upper_bound.
        apply Z.le_trans with ub; assumption.
Qed.

Lemma AcceptTuple_strong_covers_ub_none : forall leftNN leftNP rightNN rightNP q s lq rq lb ub,
    AcceptTuple_strong_covers leftNN leftNP rightNN rightNP (q,s,lq,rq,lb,Some ub) (q,s,lq,rq,lb,None).
Proof.
    introv. unfold AcceptTuple_strong_covers. intros c' HAcc. left.
    destruct lb.
    -   inversion HAcc. apply AcceptTuple_accept_lower_bound. assumption.
    -   inversion HAcc. apply AcceptTuple_accept_unbounded.
Qed.


Definition AcceptTuple_apply_NonNeg (leftNN rightNN : list nat) (a : AcceptTuple) : AcceptTuple :=
    match a with
    |   (q,s,lq,rq,lb,ub) =>    if andb (inb lq leftNN) (inb rq rightNN)
                                then (q,s,lq,rq,pos_or_zero lb,ub)
                                else a
    end.

Lemma AcceptTuple_apply_NonNeg_strong_covers:
    forall leftWFA rightWFA leftNN leftNP rightNN rightNP a a',
        non_negative leftWFA leftNN ->
        non_positive leftWFA leftNP ->
        non_negative rightWFA rightNN ->
        non_positive rightWFA rightNP ->
        AcceptTuple_apply_NonNeg leftNN rightNN a = a' ->
        AcceptTuple_strong_covers leftNN leftNP rightNN rightNP a a'.
Proof.
    introv Hlnn Hlnp Hrnn Hrnp Happly. unfold AcceptTuple_strong_covers. introv Hacc.
    destruct a as [[[[[q s] lq] rq] lb] ub]. destruct a' as [[[[[q' s'] lq'] rq'] lb'] ub']. 
    unfold AcceptTuple_apply_NonNeg in Happly.
    destruct (inb lq leftNN && inb rq rightNN)%bool eqn: HCase.   
    -   destruct c' as [r w''].
        assert (Hr: r = (q, s, lq, rq)).
        {   inversion Hacc; reflexivity. }
        rewrite Hr. rewrite Hr in Hacc.
        destruct (w''<?0) eqn: Hw.
        +   right. apply Z.ltb_lt in Hw.
            unfold strong_impossible_config. left.
            unfold strong_impossible_config_neg. rewrite HCase. assumption.
        +   left. rewrite <- Happly.
            unfold pos_or_zero. destruct (lb). destruct (z <=? 0).   
            *   destruct ub eqn: Hub.
                --  apply AcceptTuple_accept_bounded.
                    ++  apply Z.ltb_ge. assumption.
                    ++  inversion Hacc. assumption.
                --  apply AcceptTuple_accept_lower_bound.
                    apply Z.ltb_ge. assumption.
            *   assumption.   
            *   destruct ub eqn: Hub.
                --  apply AcceptTuple_accept_bounded.
                    ++  apply Z.ltb_ge. assumption.
                    ++  inversion Hacc. assumption.
                --  apply AcceptTuple_accept_lower_bound.
                    apply Z.ltb_ge. assumption.
    -   left. rewrite <- Happly. assumption.
Qed.      

Definition AcceptTuple_apply_NonPos (leftNP rightNP : list nat) (a : AcceptTuple) : AcceptTuple :=
    match a with
    |   (q,s,lq,rq,lb,ub) =>    if andb (inb lq leftNP) (inb rq rightNP)
                                then (q,s,lq,rq,lb,neg_or_zero ub)
                                else a
    end.

Lemma AcceptTuple_apply_NonPos_strong_covers:
    forall leftWFA rightWFA leftNN leftNP rightNN rightNP a a',
        non_negative leftWFA leftNN ->
        non_positive leftWFA leftNP ->
        non_negative rightWFA rightNN ->
        non_positive rightWFA rightNP ->
        AcceptTuple_apply_NonPos leftNP rightNP a = a' ->
        AcceptTuple_strong_covers leftNN leftNP rightNN rightNP a a'.
Proof.
    introv Hlnn Hlnp Hrnn Hrnp Happly. unfold AcceptTuple_strong_covers. introv Hacc.
    destruct a as [[[[[q s] lq] rq] lb] ub]. destruct a' as [[[[[q' s'] lq'] rq'] lb'] ub'].
    unfold AcceptTuple_apply_NonPos in Happly.
    destruct (inb lq leftNP && inb rq rightNP)%bool eqn: HCase.
    -   destruct c' as [r w''].
        assert (Hr: r = (q, s, lq, rq)).
        {   inversion Hacc; reflexivity. }
        rewrite Hr. rewrite Hr in Hacc.
        destruct (w''>?0) eqn: Hw.
        +   right. apply Z.gtb_gt in Hw.
            unfold strong_impossible_config. right.
            unfold strong_impossible_config_pos. rewrite HCase. assumption.
        +   left. rewrite <- Happly.
            unfold neg_or_zero. destruct (ub). destruct (z >=? 0).
            *   destruct lb eqn: Hlb.
                --  apply AcceptTuple_accept_bounded.
                    ++  inversion Hacc. assumption.
                    ++  apply Z.ltb_ge. rewrite <- Z.gtb_ltb. assumption.
                --  apply AcceptTuple_accept_upper_bound.
                    apply Z.ltb_ge. rewrite <- Z.gtb_ltb. assumption.
            *   assumption.
            *   destruct lb eqn: Hlb.
                --  apply AcceptTuple_accept_bounded.
                    ++  inversion Hacc. assumption.
                    ++  apply Z.ltb_ge. rewrite <- Z.gtb_ltb. assumption.
                --  apply AcceptTuple_accept_upper_bound.
                    apply Z.ltb_ge. rewrite <- Z.gtb_ltb. assumption.
    -   left. rewrite <- Happly. assumption.
Qed.

Definition AcceptTuple_apply_SpecialSets leftNN leftNP rightNN rightNP a :=
    AcceptTuple_apply_NonNeg leftNN rightNN (AcceptTuple_apply_NonPos leftNP rightNP a).

Lemma AcceptTuple_apply_SpecialSets_strong_covers leftWFA rightWFA:
    forall leftNN leftNP rightNN rightNP a a',
        non_negative leftWFA leftNN ->
        non_positive leftWFA leftNP ->
        non_negative rightWFA rightNN ->
        non_positive rightWFA rightNP ->
        AcceptTuple_apply_SpecialSets leftNN leftNP rightNN rightNP a = a' ->
        AcceptTuple_strong_covers leftNN leftNP rightNN rightNP a a'.
Proof.
    introv Hnnl Hnpl Hnnr Hnpr Happ.
    unfold AcceptTuple_apply_SpecialSets in Happ.
    apply AcceptTuple_strong_covers_trans with (AcceptTuple_apply_NonPos leftNP rightNP a).
    -   apply AcceptTuple_apply_NonPos_strong_covers with leftWFA rightWFA; intuition.
    -   rewrite <- Happ.
        apply AcceptTuple_apply_NonNeg_strong_covers with leftWFA rightWFA; intuition.
Qed.

Fixpoint AcceptSet_nonhalt (tm:TM) (aset: list AcceptTuple) : bool :=
    match aset with
    |   [] => true
    |   (q,s,_,_,_,_) :: tl =>  match tm (q,s) with
                                | None => false
                                | Some _ => AcceptSet_nonhalt tm tl
                                end
    end.

Lemma AcceptSet_nonhalt_In_Some:
    forall tm aset q s lq rq lb ub,
        AcceptSet_nonhalt tm aset = true ->
        In (q, s, lq, rq, lb, ub) aset ->
        ~ tm (q,s) = None.
Proof.
    introv Hasnh HIn.
    induction aset.
    -   destruct HIn.
    -   destruct HIn.
        +   rewrite H in Hasnh. simpl in Hasnh.
            intros Htmqs. rewrite Htmqs in Hasnh. discriminate.
        +   apply IHaset; try assumption.
            destruct a as [[[[[qa sa]lqa]rqa]lba]uba].
            simpl in Hasnh; destruct (tm (qa,sa)).
            *   assumption.
            *   discriminate.
Qed.

Lemma AcceptSet_nonhalt_accepted_config_not_halted:
    forall tm leftWFA rightWFA aset a c c',
        Config_mod_WNFAs leftWFA rightWFA c c' ->
        AcceptSet_nonhalt tm aset = true ->
        In a aset ->
        AcceptTuple_accept a c' ->
        ~halted tm c.
Proof.
    introv Hmod Hasetnh HIn HAcc.
    destruct c as [q [[l s] r]].
    destruct (tm (q, s)) eqn: HCase.
    -   unfold halted. rewrite HCase. discriminate.
    -   destruct c' as [[[[q' s']lq]rq]w] .
        simpl in Hmod. destruct Hmod as [Hqq' [Hss' _]].
        destruct a as [[[[[qa sa]lqa]rqa]lb]ub].
        assert (Hqqa: qa = q').
        {   inversion HAcc; reflexivity. }
        assert (Hssa: sa = s').
        {   inversion HAcc; reflexivity. }
        rewrite Hqq' in HCase. rewrite <- Hqqa in HCase.
        rewrite Hss' in HCase. rewrite <- Hssa in HCase.
        assert (HContra: ~ tm (qa, sa) = None).
        {   apply AcceptSet_nonhalt_In_Some with aset lqa rqa lb ub; assumption. }
        apply HContra in HCase. destruct HCase.
Qed.

Definition MITMWFAR_Cert : Type :=
    TM * (WNFA * WNFA * list nat * list nat * list nat * list nat * list AcceptTuple).

Definition L_from_Cert (cert:MITMWFAR_Cert) (c: Q * tape) : Prop :=
    match cert with
    |   (_, (leftWFA, rightWFA, _, _, _, _, accept)) 
        => exists a c',
                Config_mod_WNFAs leftWFA rightWFA c c'
            /\  In a accept
            /\  AcceptTuple_accept a c'
    end. 

Definition L_from_Cert_nonhalt (cert : MITMWFAR_Cert) :=
    match cert with
    | (tm,(_,_,_,_,_,_,aset)) => AcceptSet_nonhalt tm aset
    end.

Lemma L_from_Cert_nonhalt_correct:
    forall tm c,
        L_from_Cert_nonhalt (tm, c) = true ->
        non_halt (L_from_Cert (tm, c)) tm.
Proof.
    introv Hnonhalt.
    destruct c as [[[[[[lwfa rwfa]lnn]lnp]rnn]rnp] aset].
    inversion Hnonhalt as [Hasnh].
    unfold non_halt. introv HLAcc.
    inversion HLAcc as [a [c' [ Hmod [HIn HAcc ]]]].
    apply AcceptSet_nonhalt_accepted_config_not_halted
        with lwfa rwfa aset a c'; try assumption.
Qed.

Definition AcceptSet_step_closed tm leftWFA rightWFA aset :=
    forall c0 c0' a0 c1,
        Config_mod_WNFAs leftWFA rightWFA c0 c0' ->
        In a0 aset ->
        AcceptTuple_accept a0 c0' ->
        c0 -[ tm ]-> c1 ->
        exists a1 c1',            
                Config_mod_WNFAs leftWFA rightWFA c1 c1'
            /\  In a1 aset
            /\  AcceptTuple_accept a1 c1'.

Lemma AcceptSet_step_closed_sufficient:
    forall tm leftWFA rightWFA lnn lnp rnn rnp aset,
        AcceptSet_step_closed tm leftWFA rightWFA aset ->
        closed (L_from_Cert (tm, (leftWFA, rightWFA, lnn, lnp, rnn, rnp, aset))) tm.
Proof.
    introv HstepClosed. unfold closed. intros c0 c1 Hstep HLc.
    simpl in HLc. destruct HLc as [a0 [c0' [Hmod0 [HIna HAcc]]]].
    unfold L_from_Cert. apply HstepClosed with c0 c0' a0; assumption.
Qed.

Definition eqbb_sym s s' :=
    if eqb_sym s s'
    then true
    else false.

Fixpoint wnfa_succ (wnfa:WNFA) (q:nat) (s:Sym) : list (nat*Z):=
    match wnfa with
    |   [] => []
    |   (sq, eq, s', w) :: tl =>    if andb (Nat.eqb q sq) (eqbb_sym s s')
                                    then (eq, w) :: wnfa_succ tl q s
                                    else wnfa_succ tl q s
    end.

Lemma wnfa_succ_In:
    forall wnfa q s q' w,
        In (q', w) (wnfa_succ wnfa q s)
        <->
        In (q, q', s, w) wnfa.
Proof.
    introv. induction wnfa.
    -   split; intros HIn; destruct HIn.
    -   destruct a as [[[sqa eqa]sa]wa].
        split.
        +   simpl. intros HIn.
            destruct ((q =? sqa)%nat && eqbb_sym s sa)%bool eqn: HCase.
            *   destruct HIn.
                --  left. inversion H.  
                    apply andb_prop in HCase.
                    destruct HCase. apply Nat.eqb_eq in H0. rewrite H0.
                    unfold eqbb_sym in H3. destruct (eqb_sym s sa).
                    ++  rewrite e. reflexivity.
                    ++  discriminate.
                -- right. apply IHwnfa. assumption.
            *   right. apply IHwnfa. assumption.               
        +   intros HIn. simpl in HIn. destruct HIn as [Heqa|HIn].
            *   rewrite Heqa. simpl.
                assert (HObvs: ((q =? q)%nat && eqbb_sym s s)%bool = true).
                {   apply Bool.andb_true_iff. split.
                    -   apply Nat.eqb_refl.
                    -   unfold eqbb_sym.
                        destruct (eqb_sym s s).
                        +   reflexivity.
                        +   destruct n. reflexivity. }
                rewrite HObvs. simpl. left. reflexivity.
            *   apply IHwnfa in HIn.  simpl.
                destruct ((q =? sqa)%nat && eqbb_sym s sa)%bool; try assumption.
                simpl. right. assumption.
Qed.

Fixpoint wnfa_pred (wnfa:WNFA) (q:nat) : list (nat*Sym*Z) :=
    match wnfa with
    |   [] => []
    |   (sq, eq, s, w) :: tl => if Nat.eqb q eq
                                then (sq, s, w) :: wnfa_pred tl q
                                else wnfa_pred tl q
    end.

Lemma wnfa_pred_In:
    forall wnfa q s q' w,
        In (q', s, w) (wnfa_pred wnfa q)
        <->
        In (q', q, s, w) wnfa.
Proof.
    introv. induction wnfa.
    -   split; intros HIn; destruct HIn.
    -   destruct a as [[[sqa eqa]sa]wa].
        split.
        +   simpl. intros HIn.
            destruct (q =? eqa)%nat eqn: HCase.
            *   destruct HIn.
                --  left. inversion H.
                    apply Nat.eqb_eq in HCase. rewrite HCase. reflexivity.
                -- right. apply IHwnfa. assumption.
            *   right. apply IHwnfa. assumption.               
        +   intros HIn. simpl in HIn. destruct HIn as [Heqa|HIn].
            *   rewrite Heqa. simpl.
                assert (HObvs: (q =? q)%nat = true).
                {   apply Nat.eqb_eq. reflexivity. }
                rewrite HObvs. simpl. left. reflexivity.
            *   apply IHwnfa in HIn.  simpl.
                destruct (q =? eqa)%nat; try assumption.
                simpl. right. assumption.
Qed.

Definition impossible_mod_config leftWFA rightWFA c' :=
    forall c,
        ~ Config_mod_WNFAs leftWFA rightWFA c c'.

Definition AcceptSet_modStepLeft_closed (tm:TM) leftWFA rightWFA aset :=
    forall c a q0 s0 lq0 rq0 w q1 s1 lq1 ls lw,
        In a aset ->
        AcceptTuple_accept a c ->
        c = (q0, s0, lq0, rq0, w) ->
        tm (q0, s0) = Some (s1, L, q1) ->
        In (lq1, ls, lw) (wnfa_pred leftWFA lq0) ->
        exists rq1 rw b,
                In (rq1, rw) (wnfa_succ rightWFA rq0 s1)
            /\  ((In b aset
                    /\  AcceptTuple_accept b (q1, ls, lq1, rq1, w-lw+rw))
                \/  impossible_mod_config leftWFA rightWFA (q1, ls, lq1, rq1, w-lw+rw)).

Definition AcceptSet_modStepRight_closed (tm:TM) leftWFA rightWFA aset :=
    forall c a q0 s0 lq0 rq0 w q1 s1 rq1 rs rw,
        In a aset ->
        AcceptTuple_accept a c ->
        c = (q0, s0, lq0, rq0, w) ->
        tm (q0, s0) = Some (s1, R, q1) ->
        In (rq1, rs, rw) (wnfa_pred rightWFA rq0) ->
        exists lq1 lw b,
                In (lq1, lw) (wnfa_succ leftWFA lq0 s1)
            /\  ((In b aset
                    /\  AcceptTuple_accept b (q1, rs, lq1, rq1, w + lw - rw))
                \/  impossible_mod_config leftWFA rightWFA (q1, rs, lq1, rq1, w + lw - rw)).

Lemma ModStep_pred_possible :
    forall wfa s1 tl q0' w,
        In (0%nat, 0%nat, s0, 0) wfa ->
        wnfa_read_side wfa (s1 >> tl) q0' w ->
        exists q1' dw,
                In (q1', s1, dw) (wnfa_pred wfa q0')
            /\  wnfa_read_side wfa tl q1' (w-dw).
Proof.
    introv Hstart Hread. inversion Hread.
    -   exists 0%nat 0.
        rewrite const_unfold in H1. inversion H1. split.
        +   apply wnfa_pred_In. assumption.   
        +   apply wnfa_start.
    -   exists q w'. split.
        +   apply wnfa_pred_In. assumption.
        +   assert (Hobvs: w0 + w' - w' = w0).
            {   ring. }
            rewrite Hobvs. assumption.
Qed.       

Lemma AcceptSet_modStepLeftRight_closed_sufficient:
    forall tm leftWFA rightWFA aset,
        In (0%nat, 0%nat, s0, 0) leftWFA ->
        In (0%nat, 0%nat, s0, 0) rightWFA ->
        AcceptSet_modStepLeft_closed tm leftWFA rightWFA aset ->
        AcceptSet_modStepRight_closed tm leftWFA rightWFA aset ->
        AcceptSet_step_closed tm leftWFA rightWFA aset.
Proof.
    introv HInStartLeft HInStartRight HleftClosed HrightClosed.
    unfold AcceptSet_step_closed. introv Hmod HIna0 HAcc Hstep.
    destruct a0 as [[[[[q0 s0]lq0]rq0]lb0]ub0] eqn: Ha0.
    invert Hstep; introv Htm Hc1 Hc2.
    -   unfold AcceptSet_modStepLeft_closed in HleftClosed.
        rewrite <- Hc1 in Hmod. destruct c0' as [[[[q0' s0']lq0']rq0']w0'] eqn: Hc0'. 
        destruct l0 eqn: Hl0.
        simpl in Hmod. destruct Hmod as [Hqq0 [Hss0 [lw0 [rw0 [Hwsum [HreadLeft0 HreadRight0]]]]]].
        assert (HpredExist: exists lq1' lw1',
                In (lq1', s2, lw1') (wnfa_pred leftWFA lq0')
            /\  wnfa_read_side leftWFA s3 lq1' (lw0-lw1')).
        {   apply ModStep_pred_possible; assumption. }
        destruct HpredExist as [lq1' [lw1' [HInPred HrlPred]]].
        specialize HleftClosed with c0' a0 q0' s0' lq0' rq0' w0' q' s' lq1' s2 lw1'.
        assert (HexistSucc: exists (rq1 : nat) (rw0 : Z) (b : AcceptTuple),
            In (rq1, rw0) (wnfa_succ rightWFA rq0' s')
            /\ ((In b aset
                    /\ AcceptTuple_accept b (q', s2, lq1', rq1, w0' - lw1' + rw0))
                \/ impossible_mod_config leftWFA rightWFA (q', s2, lq1', rq1, w0' - lw1' + rw0))).
        {   apply HleftClosed; try assumption.
            -   rewrite Ha0. assumption.
            -   rewrite Ha0. rewrite Hc0'. assumption.
            -   rewrite <- Htm. rewrite Hqq0. rewrite Hss0. reflexivity. }
        destruct HexistSucc as [rq1 [rw [b [HInSucc [[HInb HAccn]|HImpossible]]]]].
        +   exists b (q', s2, lq1', rq1, w0' - lw1' + rw).
            split.
            *   split. reflexivity. split. reflexivity.
                exists (lw0-lw1') (rw0+rw).
                split. rewrite <- Hwsum. ring.
                split. simpl. assumption.
                apply wnfa_step with rq0'; try assumption.
                apply wnfa_succ_In. assumption.
            *   split; try assumption.
        +   exfalso.
            unfold impossible_mod_config in HImpossible. 
            specialize HImpossible with c2. apply HImpossible.
            destruct c2 as [q2 [[l2 s2']r2]]. unfold Config_mod_WNFAs.
            inversion Hc2. split. reflexivity. split. reflexivity.
            exists (lw0-lw1') (rw0+rw).
            split; try split.
            *   rewrite <- Hwsum. ring.
            *   rewrite <- H1. assumption.
            *   apply wnfa_step with rq0'; try assumption.
                apply wnfa_succ_In. assumption.
    -   unfold AcceptSet_modStepRight_closed in HrightClosed.
        rewrite <- Hc1 in Hmod. destruct c0' as [[[[q0' s0']lq0']rq0']w0'] eqn: Hc0'. 
        destruct r eqn: Hr.
        simpl in Hmod. destruct Hmod as [Hqq0 [Hss0 [lw0 [rw0 [Hwsum [HreadLeft0 HreadRight0]]]]]].
        assert (HpredExist: exists rq1' rw1',
                In (rq1', s2, rw1') (wnfa_pred rightWFA rq0')
            /\  wnfa_read_side rightWFA s3 rq1' (rw0-rw1')).
        {   apply ModStep_pred_possible; assumption. }
        destruct HpredExist as [rq1' [rw1' [HInPred HrrPred]]].
        specialize HrightClosed with c0' a0 q0' s0' lq0' rq0' w0' q' s' rq1' s2 rw1'.
        assert (HexistSucc: exists (lq1 : nat) (lw0 : Z) (b : AcceptTuple),
            In (lq1, lw0) (wnfa_succ leftWFA lq0' s')
            /\ (( In b aset 
                    /\ AcceptTuple_accept b (q', s2, lq1, rq1', w0' + lw0 - rw1'))
                \/ (impossible_mod_config leftWFA rightWFA (q', s2, lq1, rq1', w0' + lw0 - rw1')) )).
        {   apply HrightClosed; try assumption.
            -   rewrite Ha0. assumption.
            -   rewrite Ha0. rewrite Hc0'. assumption.
            -   rewrite <- Htm. rewrite Hqq0. rewrite Hss0. reflexivity. }
        destruct HexistSucc as [lq1 [lw [b [HInSucc [[HInb HAccn]|HImpossible]]]]].
        +   exists b (q', s2, lq1, rq1', w0' + lw - rw1').
            split.
            *   split. reflexivity. split. reflexivity.
                exists (lw0+lw) (rw0-rw1').
                split. rewrite <- Hwsum. ring.
                split. apply wnfa_step with lq0'; try assumption.
                apply wnfa_succ_In. assumption.
                simpl. assumption.
            *   split; try assumption.
        +   exfalso.
            unfold impossible_mod_config in HImpossible. 
            specialize HImpossible with c2. apply HImpossible.
            destruct c2 as [q2 [[l2 s2']r2]]. unfold Config_mod_WNFAs.
            inversion Hc2. split. reflexivity. split. reflexivity.
            exists (lw0+lw) (rw0 - rw1').
            split; try split.
            *   rewrite <- Hwsum. ring.
            *   apply wnfa_step with lq0'; try assumption.
                apply wnfa_succ_In. assumption.
            *   rewrite <- H3. assumption.
Qed.

Definition opt_add z d :=
    match z with
    |   None => None
    |   Some w => Some (w+d)
    end.

Definition impossible_acceptTuple a :=
    forall c, ~AcceptTuple_accept a c.

Definition AcceptSet_strong_modStepRight_closed (tm:TM) leftWFA rightWFA leftNN leftNP rightNN rightNP aset :=
    forall a q0 s0 lq0 rq0 lb0 ub0 s1 q1 rq1 rs rw,
        In a aset ->
        a = (q0, s0, lq0, rq0, lb0, ub0) ->
        tm (q0, s0) = Some (s1, R, q1) ->
        In (rq1, rs, rw) (wnfa_pred rightWFA rq0) ->
        exists lq1 lw b,
                In (lq1, lw) (wnfa_succ leftWFA lq0 s1)
            /\  let bmin := AcceptTuple_apply_SpecialSets leftNN leftNP rightNN rightNP (q1, rs, lq1, rq1, opt_add lb0 (lw-rw), opt_add ub0 (lw-rw)) in
                ((In b aset
                    /\  AcceptTuple_strong_covers leftNN leftNP rightNN rightNP bmin b)
                \/ impossible_acceptTuple bmin).

Lemma AcceptSet_strong_modStepRight_closed_sufficient:
    forall tm leftWFA rightWFA leftNN leftNP rightNN rightNP aset,
    non_negative leftWFA leftNN ->
    non_positive leftWFA leftNP ->
    non_negative rightWFA rightNN ->
    non_positive rightWFA rightNP ->
    AcceptSet_strong_modStepRight_closed tm leftWFA rightWFA leftNN leftNP rightNN rightNP aset ->
    AcceptSet_modStepRight_closed tm leftWFA rightWFA aset.
Proof.
    introv Hlnn Hlnp Hrnn Hrnp. unfold AcceptSet_strong_modStepRight_closed. unfold AcceptSet_modStepRight_closed.
    introv Hclosed Hina Hacc Hc Htm Hpred.
    destruct a as [[r lb0]ub0] eqn:Ha.
    specialize Hclosed with a q2 s2 lq0 rq0 lb0 ub0 s3 q3 rq1 rs rw.
    rewrite <- Ha in Hina. apply Hclosed in Hina.
    -   destruct Hina as [lq1 [lw [b [Hsucc Hor]]]].
        exists lq1 lw b.
        assert (HAccminb: AcceptTuple_accept
                    (q3, rs, lq1, rq1, opt_add lb0 (lw - rw), opt_add ub0 (lw - rw)) 
                    (q3, rs, lq1, rq1, w + lw - rw)).
        {
            rewrite Hc in Hacc. destruct lb0; destruct ub0.
            *   simpl. apply AcceptTuple_accept_bounded.
                --  inversion Hacc.
                    assert (HObvs: w+lw-rw=w+(lw-rw)). { ring. }
                    rewrite HObvs. apply Zplus_le_compat_r. assumption.
                --  inversion Hacc.
                    assert (HObvs: w+lw-rw=w+(lw-rw)). { ring. }
                    rewrite HObvs. apply Zplus_le_compat_r. assumption.
            *   apply AcceptTuple_accept_lower_bound.
                --  inversion Hacc.
                    assert (HObvs: w+lw-rw=w+(lw-rw)). { ring. }
                    rewrite HObvs. apply Zplus_le_compat_r. assumption.
            *   apply AcceptTuple_accept_upper_bound.
                --  inversion Hacc.
                    assert (HObvs: w+lw-rw=w+(lw-rw)). { ring. }
                    rewrite HObvs. apply Zplus_le_compat_r. assumption.
            *   apply AcceptTuple_accept_unbounded.
        }
        split;try assumption.
        pose proof AcceptTuple_apply_SpecialSets_strong_covers leftWFA rightWFA leftNN leftNP rightNN rightNP
            (q3, rs, lq1, rq1, opt_add lb0 (lw - rw), opt_add ub0 (lw - rw))
            (AcceptTuple_apply_SpecialSets leftNN leftNP rightNN rightNP
                (q3, rs, lq1, rq1, opt_add lb0 (lw - rw), opt_add ub0 (lw - rw))).
        pose proof Hlnn as HlnnCopy.
        apply H in Hlnn; try assumption; try reflexivity.
        destruct Hor as [[Hinb Hcover]|HImpossible].
        +   unfold AcceptTuple_strong_covers in Hcover.
            specialize Hcover with (q3, rs, lq1, rq1, w + lw - rw).
            apply Hlnn in HAccminb. destruct HAccminb as [HAccepted|HstrImpossible].
            *   apply Hcover in HAccepted. destruct HAccepted as [Haccepted'|HstrImpossible].
                --  left. split; assumption.
                --  right. apply strong_impossible_config_sufficient with leftNN leftNP rightNN rightNP; try assumption.
            *   right. apply strong_impossible_config_sufficient with leftNN leftNP rightNN rightNP; try assumption.
        +   right. unfold impossible_mod_config. introv.
            unfold impossible_acceptTuple in HImpossible.
            specialize HImpossible with (q3, rs, lq1, rq1, w + lw - rw).
            unfold AcceptTuple_strong_covers in Hlnn. specialize Hlnn with (q3, rs, lq1, rq1, w + lw - rw).
            apply Hlnn in HAccminb. destruct HAccminb as [HAccminb|HstrImpossible].
            *   apply HImpossible in HAccminb. destruct HAccminb.
            *   apply strong_impossible_config_sufficient with (leftWFA := leftWFA) (rightWFA := rightWFA)
                    in HstrImpossible; try assumption.
                unfold impossible_config in HstrImpossible. apply HstrImpossible.   
    -   rewrite Ha. assert (Hr: r = (q2, s2, lq0, rq0)).
        {   rewrite Hc in Hacc. inversion Hacc; reflexivity.     }
        rewrite Hr. reflexivity.
    -   assumption.
    -   assumption.
Qed.

Definition AcceptSet_strong_modStepLeft_closed (tm:TM) leftWFA rightWFA leftNN leftNP rightNN rightNP aset :=
    forall a q0 s0 lq0 rq0 lb0 ub0 s1 q1 lq1 ls lw,
        In a aset ->
        a = (q0, s0, lq0, rq0, lb0, ub0) ->
        tm (q0, s0) = Some (s1, L, q1) ->
        In (lq1, ls, lw) (wnfa_pred leftWFA lq0) ->
        exists rq1 rw b,
                In (rq1, rw) (wnfa_succ rightWFA rq0 s1)
            /\  let bmin := AcceptTuple_apply_SpecialSets leftNN leftNP rightNN rightNP (q1, ls, lq1, rq1, opt_add lb0 (rw-lw), opt_add ub0 (rw-lw)) in
                ((In b aset
                    /\  AcceptTuple_strong_covers leftNN leftNP rightNN rightNP bmin b)
                \/ impossible_acceptTuple bmin).

Lemma AcceptSet_strong_modStepLeft_closed_sufficient:
    forall tm leftWFA rightWFA leftNN leftNP rightNN rightNP aset,
    non_negative leftWFA leftNN ->
    non_positive leftWFA leftNP ->
    non_negative rightWFA rightNN ->
    non_positive rightWFA rightNP ->
    AcceptSet_strong_modStepLeft_closed tm leftWFA rightWFA leftNN leftNP rightNN rightNP aset ->
    AcceptSet_modStepLeft_closed tm leftWFA rightWFA aset.
Proof.
    introv Hlnn Hlnp Hrnn Hrnp. unfold AcceptSet_strong_modStepLeft_closed. unfold AcceptSet_modStepLeft_closed.
    introv Hclosed Hina Hacc Hc Htm Hpred.
    destruct a as [[r lb0]ub0] eqn:Ha.
    specialize Hclosed with a q2 s2 lq0 rq0 lb0 ub0 s3 q3 lq1 ls lw.
    rewrite <- Ha in Hina. apply Hclosed in Hina.
    -   destruct Hina as [rq1 [rw [b [Hsucc Hor]]]].
        exists rq1 rw b.
        assert (HAccminb: AcceptTuple_accept
                    (q3, ls, lq1, rq1, opt_add lb0 (rw - lw), opt_add ub0 (rw - lw)) 
                    (q3, ls, lq1, rq1, w - lw + rw)).
        {
            rewrite Hc in Hacc. destruct lb0; destruct ub0.
            *   simpl. apply AcceptTuple_accept_bounded.
                --  inversion Hacc.
                    assert (HObvs: w-lw+rw=w+(rw-lw)). { ring. }
                    rewrite HObvs. apply Zplus_le_compat_r. assumption.
                --  inversion Hacc.
                    assert (HObvs: w-lw+rw=w+(rw-lw)). { ring. }
                    rewrite HObvs. apply Zplus_le_compat_r. assumption.
            *   apply AcceptTuple_accept_lower_bound.
                --  inversion Hacc.
                    assert (HObvs: w-lw+rw=w+(rw-lw)). { ring. }
                    rewrite HObvs. apply Zplus_le_compat_r. assumption.
            *   apply AcceptTuple_accept_upper_bound.
                --  inversion Hacc.
                    assert (HObvs: w-lw+rw=w+(rw-lw)). { ring. }
                    rewrite HObvs. apply Zplus_le_compat_r. assumption.
            *   apply AcceptTuple_accept_unbounded.
        }
        split;try assumption.
        pose proof AcceptTuple_apply_SpecialSets_strong_covers leftWFA rightWFA leftNN leftNP rightNN rightNP
            (q3, ls, lq1, rq1, opt_add lb0 (rw - lw), opt_add ub0 (rw - lw))
            (AcceptTuple_apply_SpecialSets leftNN leftNP rightNN rightNP
                (q3, ls, lq1, rq1, opt_add lb0 (rw - lw), opt_add ub0 (rw - lw))).
        pose proof Hlnn as HlnnCopy.
        apply H in Hlnn; try assumption; try reflexivity.
        destruct Hor as [[Hinb Hcover]|HImpossible].
        +   unfold AcceptTuple_strong_covers in Hcover.
            specialize Hcover with (q3, ls, lq1, rq1, w + rw - lw).
            apply Hlnn in HAccminb. destruct HAccminb as [HAccepted|HstrImpossible].
            *   rewrite Z.add_sub_swap in Hcover. apply Hcover in HAccepted. destruct HAccepted as [Haccepted'|HstrImpossible].
                --  left. split; assumption.
                --  right. apply strong_impossible_config_sufficient with leftNN leftNP rightNN rightNP; try assumption.
            *   right. apply strong_impossible_config_sufficient with leftNN leftNP rightNN rightNP; try assumption.
        +   right. unfold impossible_mod_config. introv.
            unfold impossible_acceptTuple in HImpossible.
            specialize HImpossible with (q3, ls, lq1, rq1, w - lw + rw).
            unfold AcceptTuple_strong_covers in Hlnn. specialize Hlnn with (q3, ls, lq1, rq1, w - lw + rw).
            apply Hlnn in HAccminb. destruct HAccminb as [HAccminb|HstrImpossible].
            *   apply HImpossible in HAccminb. destruct HAccminb.
            *   apply strong_impossible_config_sufficient with (leftWFA := leftWFA) (rightWFA := rightWFA)
                    in HstrImpossible; try assumption.
                unfold impossible_config in HstrImpossible. apply HstrImpossible.   
    -   rewrite Ha. assert (Hr: r = (q2, s2, lq0, rq0)).
        {   rewrite Hc in Hacc. inversion Hacc; reflexivity.     }
        rewrite Hr. reflexivity.
    -   assumption.
    -   assumption.
Qed.

Definition eqbb_q q q' :=
    if eqb_q q q' then true else false.

Lemma eqbb_q_eq:
    forall a b, eqbb_q a b = true <-> a = b.
Proof.
    introv. unfold eqbb_q. destruct (eqb_q a b).
    -   intuition.
    -   intuition. discriminate.
Qed.   

Lemma eqbb_q_refl:
    forall s, eqbb_q s s = true.
Proof.
    intros. unfold eqbb_q. destruct (eqb_q s s).
    -   reflexivity.
    -   destruct n. reflexivity.
Qed.

Lemma eqbb_sym_eq:
    forall a b, eqbb_sym a b = true <-> a = b.
Proof.
    introv. unfold eqbb_sym. destruct (eqb_sym a b).
    -   intuition.
    -   intuition. discriminate.
Qed.   

Lemma eqbb_sym_refl:
    forall s, eqbb_sym s s = true.
Proof.
    intros. unfold eqbb_sym. destruct (eqb_sym s s).
    -   reflexivity.
    -   destruct n. reflexivity.
Qed.

Definition eqb_edge (a b:WEdge) :bool:=
    match a, b with
    |   (sqa, eqa, sa, wa), (sqb, eqb, sb, wb) =>
            ((Nat.eqb sqa sqb) && (Nat.eqb eqa eqb) && (eqbb_sym sa sb) && (Z.eqb wa wb))
    end.


Lemma eqb_edge_eq:
    forall a b, eqb_edge a b = true <-> a = b.
Proof.
    introv. destruct a as [[[sqa eqa] sa] wa]. destruct b as [[[sqb eqb] sb] wb].
    unfold eqb_edge. split; intros H.
    -   repeat (apply andb_prop in H; destruct H).
        apply Nat.eqb_eq in H.
        apply Nat.eqb_eq in H2.
        apply eqbb_sym_eq in H1.
        apply Z.eqb_eq in H0.
        subst. reflexivity.
    -   inversion H.
        rewrite Nat.eqb_refl with sqb.
        rewrite Nat.eqb_refl with eqb.
        rewrite eqbb_sym_refl with sb.
        rewrite Z.eqb_refl with wb.
        reflexivity.
Qed.

Definition StartInb (wnfa:WNFA) :bool :=
    inEqb eqb_edge (0%nat, 0%nat, s0, 0) wnfa.

Lemma StartInb_correct:
    forall wnfa, StartInb wnfa = true <-> In (0%nat, 0%nat, s0, 0) wnfa.
Proof.
    introv. apply inEqb_In. apply eqb_edge_eq.
Qed.

Definition AcceptTuple_trivial_ub_coversb (a b:AcceptTuple) :=
    match a, b with
    |   _,(_,None) => true
    |   (_,Some uba),(_,Some ubb) => uba <=? ubb
    |   _,_ => false
    end.

Definition AcceptTuple_trivial_lb_coversb (a b:AcceptTuple) :=
    match a, b with
    |   _,(_,None,_) => true
    |   (_,Some lba,_),(_,Some lbb,_) => lba >=? lbb
    |   _,_ => false
    end.

Definition AcceptTuple_for_same_shortconfigb (a b:AcceptTuple) :=
    match a, b with
    |   (qa, sa, lqa, rqa, _, _), (qb, sb, lqb, rqb, _, _) =>
        ((eqbb_q qa qb) && (eqbb_sym sa sb) && (Nat.eqb lqa lqb) && (Nat.eqb rqa rqb))%bool
    end.

Lemma AcceptTuple_for_same_shortconfigb_correct:
    forall ra lba uba rb lbb ubb,
        AcceptTuple_for_same_shortconfigb (ra, lba, uba) (rb, lbb, ubb) = true <->
        ra = rb.
Proof.
    introv. destruct ra as [[[qa sa] lqa] rqa]. destruct rb as [[[qb sb] lqb] rqb].
    unfold AcceptTuple_for_same_shortconfigb. split; intros H.
    -   repeat (apply andb_prop in H; destruct H).
        apply eqbb_q_eq in H.
        apply eqbb_sym_eq in H2.
        apply Nat.eqb_eq in H1.
        apply Nat.eqb_eq in H0.
        subst. reflexivity.
    -   inversion H.
        rewrite eqbb_q_refl with qb.
        rewrite eqbb_sym_refl with sb.
        rewrite Nat.eqb_refl with lqb.
        rewrite Nat.eqb_refl with rqb.
        reflexivity.
Qed.

Definition AcceptTuple_trivial_coversb (a b:AcceptTuple) :=
    ((AcceptTuple_for_same_shortconfigb a b) &&
    (AcceptTuple_trivial_ub_coversb a b) &&
    (AcceptTuple_trivial_lb_coversb a b))%bool.

Lemma AcceptTuple_trivial_coversb_sufficient:
    forall a b lnn lnp rnn rnp,
        AcceptTuple_trivial_coversb a b = true ->
        AcceptTuple_strong_covers lnn lnp rnn rnp a b.
Proof.
    introv.
    destruct a as [[ra lba] uba]. 
    destruct b as [[rb lbb] ubb].
    unfold AcceptTuple_trivial_coversb. intros H.
    repeat (apply andb_prop in H; destruct H).
    apply AcceptTuple_for_same_shortconfigb_correct in H. subst.
    destruct rb as [[[q s] lq] rq].
    apply AcceptTuple_strong_covers_trans with (q, s, lq, rq, lba, ubb).
    -   destruct ubb as [ubb'|]; destruct uba as [uba'|].
        +   apply AcceptTuple_strong_covers_ub_ge. apply Z.leb_le in H1. assumption.
        +   discriminate.
        +   apply AcceptTuple_strong_covers_ub_none.
        +   constructor. assumption.
    -   destruct lbb as [lbb'|]; destruct lba as [lba'|].
        +   apply AcceptTuple_strong_covers_lb_le. apply Z.geb_ge in H0. apply Z.ge_le. assumption.
        +   discriminate.
        +   apply AcceptTuple_strong_covers_lb_none.
        +   constructor. assumption.
Qed.

Definition AcceptTuple_trivial_covered aset a :=
    inP (AcceptTuple_trivial_coversb a) aset.

Definition AcceptTuple_trivial_impossible (a:AcceptTuple) :=
    match a with
    | (_,Some lb, Some ub) => ub <? lb
    | _ => false
    end.

Lemma AcceptTuple_trivial_impossible_sufficient:
    forall a, AcceptTuple_trivial_impossible a = true -> impossible_acceptTuple a.
Proof.
    introv H. unfold impossible_acceptTuple. introv HAcc.
    revert H. unfold AcceptTuple_trivial_impossible.
    inversion HAcc; try discriminate.
    assert (Hle: lb <= ub). {   apply Z.le_trans with w; assumption. }
    rewrite Z.ltb_lt. intro Hlt.
    assert (contra: ub < ub). { apply Z.lt_le_trans with lb; assumption. }
    apply Z.lt_irrefl with ub. assumption.
Qed.   

Definition AcceptTuple_fine lnn lnp rnn rnp aset a :=
    let a' := AcceptTuple_apply_SpecialSets lnn lnp rnn rnp a in
    orb (AcceptTuple_trivial_impossible a')
        (AcceptTuple_trivial_covered aset a').

Lemma AcceptTuple_fine_sufficient:
    forall lnn lnp rnn rnp aset a,
        AcceptTuple_fine lnn lnp rnn rnp aset a = true ->
        exists b,
        let bmin := AcceptTuple_apply_SpecialSets lnn lnp rnn rnp a in
            ((In b aset
                /\  AcceptTuple_strong_covers lnn lnp rnn rnp bmin b)
            \/ impossible_acceptTuple bmin).
Proof.
    unfold AcceptTuple_fine. introv H. 
    apply Bool.orb_true_iff in H. destruct H.
    -   exists a. right. apply AcceptTuple_trivial_impossible_sufficient. assumption.
    -   apply inP_exists in H. destruct H as [b [HbIn HtrCov]]. exists b.
        left. split; try assumption.
        apply AcceptTuple_trivial_coversb_sufficient. assumption.
Qed.

Definition eqb_succ a b :=
    match a, b with
    |   (qa, wa), (qb, wb) =>
            ((Nat.eqb qa qb) && Z.eqb wa wb)%bool
    end.

Lemma eqb_succ_eq:
    forall a b, eqb_succ a b = true <-> a = b.
Proof.
    introv. destruct a as [qa  wa]. destruct b as [qb  wb].
    unfold eqb_succ. split; intros H.
    -   repeat (apply andb_prop in H; destruct H).
        apply Nat.eqb_eq in H.
        apply Z.eqb_eq in H0.
        subst. reflexivity.
    -   inversion H.
        rewrite Nat.eqb_refl with qb.
        rewrite Z.eqb_refl with wb.
        reflexivity.
Qed.

Definition eqb_pred a b :=
    match a, b with
    |   (qa, sa, wa), (qb, sb, wb) =>
            ((Nat.eqb qa qb)&&(eqbb_sym sa sb) && Z.eqb wa wb)%bool
    end.

Lemma eqb_pred_eq:
    forall a b, eqb_pred a b = true <-> a = b.
Proof.
    introv. destruct a as [[qa sa] wa]. destruct b as [[qb sb] wb].
    unfold eqb_pred. split; intros H.
    -   repeat (apply andb_prop in H; destruct H).
        apply Nat.eqb_eq in H.
        apply eqbb_sym_eq in H1.
        apply Z.eqb_eq in H0.
        subst. reflexivity.
    -   inversion H.
        rewrite Nat.eqb_refl with qb.
        rewrite eqbb_sym_refl with sb.
        rewrite Z.eqb_refl with wb.
        reflexivity.
Qed.

Definition succ_leftStep_fine lnn lnp rnn rnp aset q' s' lq' lb ub lw succ :=
    match succ with
    | (rq', rw) => AcceptTuple_fine lnn lnp rnn rnp aset (q', s', lq', rq', opt_add lb (rw-lw), opt_add ub (rw-lw))
    end.

Definition exists_succ_leftStep_fine rwfa lnn lnp rnn rnp aset q' s' lq' lb ub lw rq s :=
    inP (succ_leftStep_fine lnn lnp rnn rnp aset q' s' lq' lb ub lw) (wnfa_succ rwfa rq s).

Definition pred_leftStep_fine rwfa lnn lnp rnn rnp aset q' lb ub rq s pred :=
    match pred with
    | (lq', s', lw) => exists_succ_leftStep_fine rwfa lnn lnp rnn rnp aset q' s' lq' lb ub lw rq s
    end.

Definition all_pred_leftStep_fine lwfa rwfa lnn lnp rnn rnp aset q' lb ub lq rq s :=
    allP (pred_leftStep_fine rwfa lnn lnp rnn rnp aset q' lb ub rq s) (wnfa_pred lwfa lq).


Definition AcceptTuple_leftStep_fine (tm:TM) lwfa rwfa lnn lnp rnn rnp aset a :=
    match a with
    |   (q, s, lq, rq, lb, ub) => 
        match tm (q, s) with
        |   Some (s', L, q') => all_pred_leftStep_fine lwfa rwfa lnn lnp rnn rnp aset q' lb ub lq rq s'
        |   _ => true
        end
    end.

Definition AcceptSet_leftStep_fine tm lwfa rwfa lnn lnp rnn rnp aset :=
    allP (AcceptTuple_leftStep_fine tm lwfa rwfa lnn lnp rnn rnp aset) aset.

Lemma AcceptSet_leftStep_fine_sufficient:
    forall tm lwfa rwfa lnn lnp rnn rnp aset,
        AcceptSet_leftStep_fine tm lwfa rwfa lnn lnp rnn rnp aset = true ->
        AcceptSet_strong_modStepLeft_closed tm lwfa rwfa lnn lnp rnn rnp aset.
Proof.
    introv H. unfold AcceptSet_strong_modStepLeft_closed. introv Hina Ha Htm Hinpred.
    unfold AcceptSet_leftStep_fine in H. rewrite allP_forall in H. apply H in Hina. clear H.
    rewrite Ha in Hina. unfold AcceptTuple_leftStep_fine in Hina. rewrite Htm in Hina.
    unfold all_pred_leftStep_fine in Hina. rewrite allP_forall in Hina. apply Hina in Hinpred. clear Hina.
    unfold pred_leftStep_fine in Hinpred. unfold exists_succ_leftStep_fine in Hinpred.
    rewrite inP_exists in Hinpred. destruct Hinpred as [[rq1 rw] [Hinsucc Hsuccfine]].
    unfold succ_leftStep_fine in Hsuccfine. apply AcceptTuple_fine_sufficient in Hsuccfine.
    destruct Hsuccfine as [b H].
    exists rq1 rw b. intuition.
Qed.

Definition succ_rightStep_fine lnn lnp rnn rnp aset q' s' rq' lb ub rw succ :=
    match succ with
    | (lq', lw) => AcceptTuple_fine lnn lnp rnn rnp aset (q', s', lq', rq', opt_add lb (lw-rw), opt_add ub (lw-rw))
    end.

Definition exists_succ_rightStep_fine lwfa lnn lnp rnn rnp aset q' s' rq' lb ub rw lq s :=
    inP (succ_rightStep_fine lnn lnp rnn rnp aset q' s' rq' lb ub rw) (wnfa_succ lwfa lq s).

Definition pred_rightStep_fine lwfa lnn lnp rnn rnp aset q' lb ub lq s pred :=
    match pred with
    | (rq', s', rw) => exists_succ_rightStep_fine lwfa lnn lnp rnn rnp aset q' s' rq' lb ub rw lq s
    end.

Definition all_pred_rightStep_fine lwfa rwfa lnn lnp rnn rnp aset q' lb ub lq rq s :=
    allP (pred_rightStep_fine lwfa lnn lnp rnn rnp aset q' lb ub lq s) (wnfa_pred rwfa rq).


Definition AcceptTuple_rightStep_fine (tm:TM) lwfa rwfa lnn lnp rnn rnp aset a :=
    match a with
    |   (q, s, lq, rq, lb, ub) => 
        match tm (q, s) with
        |   Some (s', R, q') => all_pred_rightStep_fine lwfa rwfa lnn lnp rnn rnp aset q' lb ub lq rq s'
        |   _ => true
        end
    end.

Definition AcceptSet_rightStep_fine tm lwfa rwfa lnn lnp rnn rnp aset :=
    allP (AcceptTuple_rightStep_fine tm lwfa rwfa lnn lnp rnn rnp aset) aset.

Lemma AcceptSet_rightStep_fine_sufficient:
    forall tm lwfa rwfa lnn lnp rnn rnp aset,
        AcceptSet_rightStep_fine tm lwfa rwfa lnn lnp rnn rnp aset = true ->
        AcceptSet_strong_modStepRight_closed tm lwfa rwfa lnn lnp rnn rnp aset.
Proof.
    introv H. unfold AcceptSet_strong_modStepRight_closed. introv Hina Ha Htm Hinpred.
    unfold AcceptSet_rightStep_fine in H. rewrite allP_forall in H. apply H in Hina. clear H.
    rewrite Ha in Hina. unfold AcceptTuple_rightStep_fine in Hina. rewrite Htm in Hina.
    unfold all_pred_rightStep_fine in Hina. rewrite allP_forall in Hina. apply Hina in Hinpred. clear Hina.
    unfold pred_rightStep_fine in Hinpred. unfold exists_succ_rightStep_fine in Hinpred.
    rewrite inP_exists in Hinpred. destruct Hinpred as [[lq1 lw] [Hinsucc Hsuccfine]].
    unfold succ_rightStep_fine in Hsuccfine. apply AcceptTuple_fine_sufficient in Hsuccfine.
    destruct Hsuccfine as [b H].
    exists lq1 lw b. intuition.
Qed.

Definition Lstartb aset :=
    AcceptTuple_trivial_covered aset (q0, s0, 0%nat, 0%nat, Some 0, Some 0).

Lemma Lstartb_sufficient:
    forall tm lwfa rwfa lnn lnp rnn rnp aset,
        Lstartb aset = true ->
        L_from_Cert (tm, (lwfa, rwfa, lnn, lnp, rnn, rnp, aset)) c0.
Proof.
    introv H. unfold Lstartb in H. unfold AcceptTuple_trivial_covered in H.
    apply inP_exists in H. destruct H as [a [Hina Hcovers]].
    unfold L_from_Cert. exists a (q0, s0, 0%nat, 0%nat, 0). split; intuition.
    -   simpl. intuition. exists 0 0. intuition; constructor.
    -   apply AcceptTuple_trivial_coversb_sufficient with (lnn:=lnn) (lnp:=lnp) (rnn:=rnn) (rnp:=rnp) in Hcovers.
        unfold AcceptTuple_strong_covers in Hcovers. specialize Hcovers with (q0, s0, 0%nat, 0%nat, 0).
        assert (H: AcceptTuple_accept (q0, s0, 0%nat, 0%nat, Some 0, Some 0) (q0, s0, 0%nat, 0%nat, 0)).
        {   constructor; apply Z.le_refl. }
        apply Hcovers in H. destruct H.
        +   assumption.
        +   exfalso. unfold strong_impossible_config in H. destruct H.
            *   simpl in H. destruct (inb 0 lnn && inb 0 rnn)%bool. discriminate. destruct H.
            *   simpl in H. destruct (inb 0 lnp && inb 0 rnp)%bool. discriminate. destruct H.
Qed.

Definition check_MITMWFA_cert (cert:MITMWFAR_Cert):bool :=
    match cert with
    |   (tm, (lwfa, rwfa, lnn, lnp, rnn, rnp, aset)) =>
        (   StartInb lwfa  
        &&  StartInb rwfa
        &&  strong_non_negative lwfa lnn
        &&  strong_non_positive lwfa lnp
        &&  strong_non_negative rwfa rnn
        &&  strong_non_positive rwfa rnp
        &&  L_from_Cert_nonhalt cert
        &&  AcceptSet_rightStep_fine tm lwfa rwfa lnn lnp rnn rnp aset
        &&  AcceptSet_leftStep_fine tm lwfa rwfa lnn lnp rnn rnp aset
        &&  Lstartb aset
        )%bool
    end.

Theorem check_MITMWFA_cert_correct:
    forall tm c,
        check_MITMWFA_cert (tm, c) = true ->
        ~halts tm c0.
Proof.
    introv. set (L:=L_from_Cert (tm,c)).
    destruct c as [[[[[[lwfa rwfa]lnn]lnp]rnn]rnp]aset]. unfold check_MITMWFA_cert. intros H. 
    repeat (apply andb_prop in H; destruct H).
    apply strong_non_negative_sufficient in H7. apply strong_non_positive_sufficient in H6.
    apply strong_non_negative_sufficient in H5. apply strong_non_positive_sufficient in H4.
    apply StartInb_correct in H. apply StartInb_correct in H8.
    apply L_from_Cert_nonhalt_correct in H3.
    apply Lstartb_sufficient with tm lwfa rwfa lnn lnp rnn rnp aset in H0.
    apply AcceptSet_rightStep_fine_sufficient in H2.
    apply AcceptSet_leftStep_fine_sufficient in H1.
    apply closed_tape_language_nonhalt with L; try assumption.
    apply AcceptSet_step_closed_sufficient.
    apply AcceptSet_modStepLeftRight_closed_sufficient; try assumption.
    -   apply AcceptSet_strong_modStepLeft_closed_sufficient with lnn lnp rnn rnp; try assumption.
    -   apply AcceptSet_strong_modStepRight_closed_sufficient with lnn lnp rnn rnp; try assumption.
Qed.

End WNFA.