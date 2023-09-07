(** * Bouncers *)

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Lists.Streams.
From Coq Require Import Program.Tactics.
From Coq Require Import Program.Wf.
From BusyCoq Require Export Subtape.
Set Default Goal Selector "!".

Module Bouncers (Ctx : Ctx).
  Module Subtape := Subtape Ctx. Export Subtape.

(** A tape [segment] is either a single [Symbol], or a sequence of symbols
    [Repeat]ed at least one time. *)
Inductive segment :=
  | Repeat (xs : list Sym)
  | Symbol (x : Sym).

(** Repeat [xs], [S n] times. *)
Fixpoint repeated (n : nat) (xs : list Sym) : list Sym :=
  match n with
  | 0 => xs
  | S n => xs ++ repeated n xs
  end.

Lemma repeated_nil : forall n,
  repeated n [] = [].
Proof. induction n; auto. Qed.

Local Hint Rewrite repeated_nil : list.

Lemma repeated_eq_nil : forall xs n,
  repeated n xs = [] -> xs = [].
Proof.
  introv H. destruct n.
  - auto.
  - simpl in H.
    apply app_eq_nil in H.
    intuition.
Qed.

Lemma repeated_shift : forall xs n,
  xs ++ repeated n xs = repeated n xs ++ xs.
Proof.
  induction n.
  - auto.
  - simpl. rewrite IHn at 1.
    rewrite app_assoc. reflexivity.
Qed.

Reserved Notation "s ~ t" (at level 70).

Inductive matches : list segment -> list Sym -> Prop :=
  | match_nil :
    [] ~ []
  | match_sym x s t :
    s ~ t ->
    Symbol x :: s ~ x :: t
  | match_repeat n xs s t :
    s ~ t ->
    Repeat xs :: s ~ repeated n xs ++ t

  where "s ~ t" := (matches s t).

Local Hint Constructors matches : core.

(** ** Splitting the initial concrete tape into a symbolic tape: *)
Lemma match_map_app : forall xs s t,
  s ~ t ->
  map Symbol xs ++ s ~ xs ++ t.
Proof. induction xs; simpl; auto. Qed.

Local Hint Resolve match_map_app : core.

Lemma match_map : forall t, map Symbol t ~ t.
Proof. induction t; simpl; auto. Qed.

Lemma match_map_firstn : forall n s' t,
  s' ~ skipn n t ->
  map Symbol (firstn n t) ++ s' ~ t.
Proof.
  induction n.
  - auto.
  - destruct t; simpl; auto.
Qed.

Lemma match_map_destruct : forall xs s t,
  map Symbol xs ++ s ~ t ->
  exists t', t = xs ++ t' /\ s ~ t'.
Proof.
  induction xs; introv H; simpl in *.
  - eauto.
  - inverts H as H. apply IHxs in H. destruct H as [t' [E H]].
    subst. eauto.
Qed.

Local Ltac match_map_destruct H :=
  lazymatch type of H with
  | map Symbol ?xs ++ ?s ~ ?t =>
    let E := fresh in
    let t' := fresh in
    apply match_map_destruct in H;
    destruct H as [t' [E H]];
    subst t; rename t' into t
  end.

Local Hint Extern 1 =>
  lazymatch goal with
  | H: map Symbol _ ++ _ ~ _ |- _ => match_map_destruct H
  end : core.

Lemma match_repeat_firstn : forall n s' t,
  s' ~ skipn n t ->
  Repeat (firstn n t) :: s' ~ t.
Proof.
  introv H.
  assert (E : firstn n t ++ skipn n t = t)
    by apply firstn_skipn.
  rewrite <- E at 2.
  apply (match_repeat 0).
  exact H.
Qed.

Lemma match_repeat_more : forall xs s t,
  Repeat xs :: s ~ t ->
  Repeat xs :: s ~ xs ++ t.
Proof.
  introv H. inverts H as H.
  rewrite app_assoc.
  apply (match_repeat (S n)).
  auto.
Qed.

Local Hint Resolve match_map match_map_firstn match_repeat_firstn
  match_repeat_more : core.

Program Fixpoint split_tape (xs : list (nat * nat)) (t : list Sym)
    : {s | s ~ t} :=
  match xs with
  | [] => [: map Symbol t :]
  | (nt, nr) :: xs =>
    let tail := firstn nt t in
    let t' := skipn nt t in

    let repeat := firstn nr t' in
    let t'' := skipn nr t' in

    [: map Symbol tail ++ Repeat repeat :: split_tape xs t'' :]
  end.

(** ** Alignment: *)

Lemma shift_repeated : forall x r n,
  repeated n (x :: r) ++ [x] = x :: repeated n (r ++ [x]).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    repeat rewrite <- app_assoc.
    rewrite IHn. reflexivity.
Qed.

Lemma shift_repeat : forall x r s t,
  Repeat (x :: r) :: Symbol x :: s ~ t ->
  Symbol x :: Repeat (r ++ [x]) :: s ~ t.
Proof.
  introv H. inverts H as H. inverts H as H.
  replace (repeated n (x :: r) ++ x :: t)
    with ((repeated n (x :: r) ++ [x]) ++ t)
    by (rewrite <- app_assoc; reflexivity).
  rewrite shift_repeated. simpl. auto.
Qed.

Definition Cycle :=
  { '(xs, ys) : list Sym * list Sym | ys <> [] /\ exists k, xs = skipn k ys }.

Definition cycle (xs : list Sym) {H: xs <> []} : Cycle.
  refine (exist _ (xs, xs) _).
  intuition. exists 0. reflexivity.
Defined.

Local Obligation Tactic :=
  program_simpl; match goal with
  | cyc: Cycle |- _ => destruct cyc; simpl in *; subst
  end; jauto.

Program Definition cyc_hd (cyc : Cycle) : Sym :=
  match cyc with
  | (x :: _, _) => x
  | ([], x :: _) => x
  | ([], []) => False_rect _ _
  end.

Program Definition cyc_get (cyc : Cycle) : list Sym :=
  match cyc with
  | (xs, ys) => firstn (length ys) (xs ++ ys)
  end.

Lemma firstn_app_exact : forall A (l1 l2 : list A),
  firstn (length l1) (l1 ++ l2) = l1.
Proof.
  introv. rewrite <- (Nat.add_0_r (length l1)).
  autorewrite with list. reflexivity.
Qed.

#[export] Hint Rewrite firstn_app_exact : list.

Lemma cyc_get_cycle : forall xs (H: xs <> []),
  cyc_get (@cycle xs H) = xs.
Proof.
  introv. unfold cycle. unfold cyc_get. simpl.
  apply firstn_app_exact.
Qed.

Lemma cyc_hd_cyc_get : forall cyc,
  cyc_get cyc = cyc_hd cyc :: tl (cyc_get cyc).
Proof.
  intros [[xs ys] [Hcons Hinv]].
  unfold cyc_get, cyc_hd.
  destruct xs, ys; intuition.
Qed.

Lemma skipn_cons_1 : forall A (x : A) xs, xs = skipn 1 (x :: xs).
Proof. reflexivity. Qed.

Lemma skipn_succ : forall A (x : A) xs ys k,
  x :: xs = skipn k ys ->
  xs = skipn (S k) ys.
Proof.
  intros. replace (S k) with (k + 1) by lia.
  rewrite skipn_add, <- H. reflexivity.
Qed.

Local Hint Immediate skipn_cons_1 skipn_succ : core.

Program Definition cyc_next (cyc : Cycle) : Cycle :=
  match cyc with
  | ([], x :: ys) => [: (ys, x :: ys) :]
  | ([], []) => False_rect _ _
  | (x :: xs, ys) => [: (xs, ys) :]
  end.

Arguments firstn _ !n !l.

Lemma skipn_cons_length : forall A n xs (y : A) ys,
  skipn n xs = y :: ys ->
  n < length xs.
Proof.
  introv H.
  destruct (le_lt_dec (length xs) n); auto.
  replace n with (length xs + (n - length xs)) in H by lia.
  rewrite skipn_add in H.
  autorewrite with list in H. discriminate.
Qed.

Lemma firstn_shift : forall ys n (x : Sym) xs,
  x :: xs = skipn n ys ->
  firstn (S (length ys)) (skipn n ys ++ ys) =
    firstn (length ys) (skipn n ys ++ ys) ++ [x].
Proof.
  introv H.
  assert (Hlt : n < length ys)
    by eauto using skipn_cons_length.
  repeat rewrite firstn_app, skipn_length.
  repeat rewrite (firstn_all2 (skipn n ys))
    by (rewrite skipn_length; lia).
  rewrite <- app_assoc. f_equal.
  replace (S (length ys) - (length ys - n)) with (S n) by lia.
  replace (length ys - (length ys - n)) with n by lia.
  rewrite <- (firstn_skipn n ys) at 1.
  rewrite firstn_app, firstn_length.
  replace (S n - Nat.min n (length ys)) with 1 by lia.
  rewrite <- H. f_equal.
  rewrite firstn_firstn.
  f_equal. lia.
Qed.

Lemma cyc_next_spec : forall cyc x xs,
  cyc_get cyc = x :: xs ->
  cyc_get (cyc_next cyc) = xs ++ [x].
Proof.
  introv H. destruct cyc as [[ys zs] Hinv].
  destruct zs; try discriminate.
  destruct ys; unfold cyc_next, cyc_get in *; simpl in *.
  - rewrite firstn_all in H. inverts H.
    rewrite app_cons_r.
    replace (S (length xs)) with (length (xs ++ [x]))
      by (autorewrite with list; simpl; lia).
    apply firstn_app_exact.
  - inverts H. destruct Hinv as [_ [k Eskip]].
    pose proof Eskip as H.
    apply firstn_shift in H. rewrite <- Eskip in H. simpl in H.
    inverts H. reflexivity.
Qed.

(** Return an aligned equivalent of [Repeat (cyc_get cyc) :: s]. *)
Fixpoint align' (cyc : Cycle) (s : list segment) :=
  match s with
  | Symbol x :: s' =>
    if eqb_sym x (cyc_hd cyc) then
      Symbol x :: align' (cyc_next cyc) s'
    else
      Repeat (cyc_get cyc) :: s
  | _ => Repeat (cyc_get cyc) :: s
  end.

Lemma repeat_empty : forall s t,
  s ~ t -> Repeat [] :: s ~ t.
Proof. apply (match_repeat 0 []). Qed.

Local Hint Resolve repeat_empty : core.

Lemma repeat_empty_destruct : forall s t,
  Repeat [] :: s ~ t -> s ~ t.
Proof.
  introv H. inverts H. rewrite repeated_nil. auto.
Qed.

Local Hint Immediate repeat_empty_destruct : core.

Lemma repeat_cyc_next : forall cyc s t,
  Repeat (cyc_get cyc) :: Symbol (cyc_hd cyc) :: s ~ t ->
  Symbol (cyc_hd cyc) :: Repeat (cyc_get (cyc_next cyc)) :: s ~ t.
Proof.
  introv H.
  rewrite cyc_hd_cyc_get in H.
  apply shift_repeat in H.
  erewrite cyc_next_spec by apply cyc_hd_cyc_get.
  exact H.
Qed.

Lemma align'_correct : forall s t cyc,
  Repeat (cyc_get cyc) :: s ~ t ->
  align' cyc s ~ t.
Proof.
  induction s as [| x s IH]; introv H; auto.
  destruct x; auto.
  simpl align'.
  destruct (eqb_sym x (cyc_hd cyc)) as [Ex |]; auto. subst x.
  apply repeat_cyc_next in H.
  inverts H. auto.
Qed.

Program Definition align (xs : list Sym) (s : list segment) :=
  match xs with
  | [] => s
  | _ => align' (@cycle xs _) s
  end.

Lemma align_correct : forall s t xs,
  Repeat xs :: s ~ t ->
  align xs s ~ t.
Proof.
  introv H. destruct xs; auto.
  simpl.
  apply align'_correct.
  rewrite cyc_get_cycle.
  assumption.
Qed.

Local Hint Resolve align_correct : core.

Obligation Tactic := program_simpl.

(** We now have to relate the configuration expressed using symbolic tapes
    to the concrete configurations the machine can be in. *)
Notation stape := (dir * list segment * list segment)%type.

Definition stape_matches (sc : stape) (c : dtape) : Prop :=
  let '(d, l, r) := sc in
  let '(d', l', r') := c in
  d = d' /\ l ~ l' /\ r ~ r'.

Notation "sc ~~ c" := (stape_matches sc c) (at level 70).

Local Hint Unfold stape_matches : core.

Definition simple_step (tm : TM) (q : Q) (s : Sym) (l r : list segment)
    : option (Q * stape) :=
  match tm (q, s) with
  | Some (s', L, q') => Some (q', (L, l, Symbol s' :: r))
  | Some (s', R, q') => Some (q', (R, Symbol s' :: l, r))
  | None => None
  end.

Lemma simple_step_some : forall tm q s l r q' st' lt rt,
  simple_step tm q s l r = Some (q', st') ->
  l ~ lt ->
  r ~ rt ->
  exists t', st' ~~ t' /\
    lift (q;; lt {{s}} rt) -[ tm ]->+ lift (q';; undir t').
Proof.
  introv Hstep Hl Hr.
  unfold simple_step in Hstep.
  destruct (tm (q, s)) as [[[s' []] q0] |] eqn:Etm;
    inverts Hstep.
  - (* L *)
    destruct lt as [| ls lt]; eexists (_, _, _);
      intuition eauto; exact (progress_base (step_left Etm)).
  - (* R *)
    destruct rt as [| rs rt]; eexists (_, _, _);
      intuition eauto; exact (progress_base (step_right Etm)).
Qed.

Program Fixpoint grab_tail (s : list segment) (k : nat)
    : { '(tail, rest) | map Symbol tail ++ rest = s } + {True} :=
  match k with
  | 0 => [|| ([], s) ||]
  | S k =>
    match s with
    | Symbol x :: s =>
      bind (tail', rest) <-- grab_tail s k;
      [|| (x :: tail', rest) ||]
    | _ => !!
    end
  end.

Lemma shiftrule_left_exec : forall tm q s s' tail k,
  submultistep tm (S k) (q, (L, s, tail)) = Some (q, (L, [], tail ++ s')) ->
  forall n l r,
  lift (q;; undir (L, repeated n s ++ l, tail ++ r)) -[ tm ]->+
    lift (q;; undir (L, l, tail ++ repeated n s' ++ r)).
Proof.
  introv H. induction n; introv;
    eapply submultistep_some in H; simpl sublift in H;
    rewrite <- app_assoc in H.
  - eauto.
  - simpl repeated. rewrite (repeated_shift s').
    repeat rewrite <- app_assoc.
    eapply progress_trans; [| apply IHn].
    eauto.
Qed.

Lemma shiftrule_left : forall tm q l s tail rest n s' t,
  submultistep tm (S n) (q, (L, s, tail)) = Some (q, (L, [], tail ++ s')) ->
  (L, Repeat s :: l, map Symbol tail ++ rest) ~~ t ->
  exists t', (L, l, map Symbol tail ++ Repeat s' :: rest) ~~ t' /\
    lift (q;; undir t) -[ tm ]->+ lift (q;; undir t').
Proof.
  introv Hstep Hmatch.
  destruct t as [[d lt] rt]. destruct Hmatch as [E [Hl Hr]]. subst d.
  match_map_destruct Hr. inverts Hl as Hl.
  eexists (L, _, _). split; [| eapply shiftrule_left_exec, Hstep].
  auto 6.
Qed.

(** Try applying a shift rule that has a tail of length [k] and
    takes [n] base steps to prove. *)
Definition try_shift_rule (tm : TM) (q : Q) (s : list Sym) (l r : list segment)
    (n k : nat) : option (list segment) :=
  match grab_tail r k with
  | [|| (tail, rest) ||] =>
    match submultistep tm n (q, (L, s, tail)) with
    | Some (q', (L, [], r')) =>
      if eqb_q q q' then
        match strip_prefix eqb_sym tail r' with
        | [|| s' ||] =>
          match n with
          | 0 => None
          | S _ => Some (map Symbol tail ++ align s' rest)
          end
        | !! => None
        end
      else
        None
    | _ => None
    end
  | !! => None
  end.

Lemma try_shift_rule_some : forall tm q s l r r' n k t,
  try_shift_rule tm q s l r n k = Some r' ->
  (L, Repeat s :: l, r) ~~ t ->
  exists t', (L, l, r') ~~ t' /\
    lift (q;; undir t) -[ tm ]->+ lift (q;; undir t').
Proof.
  introv H Hmatch. unfold try_shift_rule in H.
  destruct (grab_tail r k) as [[[tail rest] Hgrab] |]; try discriminate.
  simpl in Hgrab. subst r.

  destruct (submultistep tm n (q, (L, s, tail)))
    as [[q'' [[[] []] r'']] |] eqn:Hstep; try discriminate.
  destruct (eqb_q q q'') as [E |]; try discriminate. subst q''.
  destruct (strip_prefix eqb_sym tail r'') as [[s' E] |]; try discriminate.
  subst r''. destruct n; inverts H.

  eapply shiftrule_left in Hstep; try eassumption.
  destruct Hstep as [[[d l'] r'] [[E [Hl Hr]] Hrun]]. subst d.
  match_map_destruct Hr.
  exists (L, l', tail ++ r'). eauto 7.
Qed.

Definition step (tm : TM) (q : Q) (st : stape) (shifts : list (nat * nat))
    : option (Q * stape) * list (nat * nat) :=
  match st with
  | (L, Repeat s :: l, r) =>
    match shifts with
    | (n, k) :: shifts =>
      match try_shift_rule tm q s l r n k with
      | Some r => (Some (q, (L, l, r)), shifts)
      | None => (None, shifts)
      end
    | [] => (None, [])
    end
  | (L, Symbol s :: l, r) => (simple_step tm q s l r, shifts)
  | (L, [], r) => (simple_step tm q s0 [] r, shifts)
  | (R, l, Repeat s :: r) =>
    match shifts with
    | (n, k) :: shifts =>
      match try_shift_rule (flip tm) q s r l n k with
      | Some l => (Some (q, (R, l, r)), shifts)
      | None => (None, shifts)
      end
    | [] => (None, [])
    end
  | (R, l, Symbol s :: r) => (simple_step tm q s l r, shifts)
  | (R, l, []) => (simple_step tm q s0 l [], shifts)
  end.

Lemma step_some : forall tm q q' st st' shifts shifts' t,
  step tm q st shifts = (Some (q', st'), shifts') ->
  st ~~ t ->
  exists t', st' ~~ t' /\
    lift (q;; undir t) -[ tm ]->+ lift (q';; undir t').
Proof.
  introv H Hmatch.
  destruct st as [[[] l] r]; simpl in H.
  - (* L *)
    destruct l as [| [s | s] l].
    + (* [] *)
      destruct t as [[d lt] rt]; destruct Hmatch as [E [Hl Hr]]; subst d.
      inverts H as H. inverts Hl.
      eapply simple_step_some in H; eauto.
    + (* Repeat s *)
      destruct shifts as [| [n k] shifts]; try discriminate.
      destruct (try_shift_rule tm q s l r n k) as [r' |] eqn:E; inverts H.
      eapply try_shift_rule_some in E; eassumption.
    + (* Symbol s *)
      destruct t as [[d lt] rt]; destruct Hmatch as [E [Hl Hr]]; subst d.
      inverts H as H. inverts Hl as Hl.
      eapply simple_step_some in H; eauto.
  - (* R *)
    destruct r as [| [s | s] r]; destruct t as [[d lt] rt].
    + (* [] *)
      destruct Hmatch as [E [Hl Hr]]; subst d.
      inverts H as H. inverts Hr.
      eapply simple_step_some in H; eauto.
    + (* Repeat s *)
      destruct shifts as [| [n k] shifts]; try discriminate.
      destruct (try_shift_rule (flip tm) q s r l n k) eqn:E; inverts H.
      destruct Hmatch as [Hmatch [Hl Hr]]. subst d.
      eapply try_shift_rule_some with (t := (L, rt, lt)) in E; auto.
      destruct E as [[[d rt'] lt'] [[Ed [Hr' Hl']] Hrun]]. subst d.
      apply unflip_progress in Hrun.
      repeat rewrite flip_undir in Hrun. simpl flip_dir in Hrun.
      exists (R, lt', rt'). auto.
    + (* Symbol s *)
      destruct Hmatch as [E [Hl Hr]]; subst d.
      inverts H as H. inverts Hr as Hr.
      eapply simple_step_some in H; eauto.
Qed.

Fixpoint steps (tm : TM) (n : nat) (q : Q) (t : stape)
    (shifts : list (nat * nat)) : option (Q * stape) :=
  match n with
  | 0 => Some (q, t)
  | S n =>
    match step tm q t shifts with
    | (Some (q, t), shifts) => steps tm n q t shifts
    | (None, _) => None
    end
  end.

Lemma steps_some : forall tm n q q' st st' t shifts,
  steps tm (S n) q st shifts = Some (q', st') ->
  st ~~ t ->
  exists t', st' ~~ t' /\
    lift (q;; undir t) -[ tm ]->+ lift (q';; undir t').
Proof.
  induction n; introv E Hmatch; simpl in E;
    destruct (step tm q st shifts) as [[[qq tt] |] shifts'] eqn:E1;
      try discriminate;
      eapply step_some in E1; try eassumption.
  - inverts E. assumption.
  - destruct E1 as [t' [Htt Hstep]].
    eapply IHn in E; try eassumption.
    destruct E as [t'' [Hst' Hsteps]].
    eauto using progress_trans.
Qed.

Program Fixpoint strip_sym_prefix (s : list Sym) (u : list segment)
    : {u' | u = map Symbol s ++ u'} + {True} :=
  match s with
  | [] => [|| u ||]
  | x :: s =>
    match u with
    | Symbol x' :: u =>
      if eqb_sym x x' then
        bind u' <-- strip_sym_prefix s u;
        [|| u' ||]
      else
        !!
    | _ => !!
    end
  end.

Lemma transfer_repeat : forall s t u xs,
  (forall xs', t ~ xs' -> u ~ xs') ->
  Repeat s :: t ~ xs ->
  Repeat s :: u ~ xs.
Proof.
  introv Htu Hr.
  remember (Repeat s :: t) as t' eqn:Et'.
  induction Hr; inverts Et'; auto.
Qed.

Lemma transfer_symbol : forall x t u xs,
  (forall xs', t ~ xs' -> u ~ xs') ->
  Symbol x :: t ~ xs ->
  Symbol x :: u ~ xs.
Proof.
  introv Htu Hx. inverts Hx. auto.
Qed.

Local Hint Immediate transfer_repeat transfer_symbol : core.

Lemma length_gt0_if_not_nil : forall A (xs : list A),
  [] <> xs -> length xs <> 0.
Proof. introv H Hlen. apply length_zero_iff_nil in Hlen. auto. Qed.

Local Ltac Zify.zify_pre_hook ::=
  lazymatch goal with
  | H: [] <> _ |- _ => apply length_gt0_if_not_nil in H
  | H: [] = _ -> False |- _ => apply length_gt0_if_not_nil in H
  | _ => idtac
  end.

Local Obligation Tactic := program_simplify; eauto; simpl;
  autorewrite with list; intuition;
  try congruence.

(** Check whether [t] is a special case of [u]. Assumes that both tapes
    are aligned, which allows using a greedy algorithm. *)
Program Fixpoint subsumes (t : list segment) (u : list segment)
    {measure (length t + length u)} : {forall xs, t ~ xs -> u ~ xs} + {True} :=
  match t, u with
  | [], [] => Yes
  | [], Repeat s :: u => No
  | [], Symbol x :: u => No
  | Repeat s :: t, Repeat s' :: u =>
    list_eq_dec eqb_sym s s' && Reduce (subsumes t u)
  | _, Repeat s :: u =>
    match s with
    | [] => Reduce (subsumes t u)
    | _ =>
      bind t' <- strip_sym_prefix s t;
      Reduce (subsumes t' (Repeat s :: u))
    end
  | Symbol x :: t, Symbol x' :: u =>
    eqb_sym x x' && Reduce (subsumes t u)
  | _, _ => No
  end.

Definition verify_bouncer_l (tm : TM) (n0 n1 : nat)
    (split : list (nat * nat)) (shifts : list (nat * nat)) : bool :=
  match cmultistep tm n0 starting with
  | [|| q;; [] {{s}} r ||] =>
    if eqb_sym s s0 then
      let '[: t0 :] := split_tape split r in
      match steps tm n1 q (L, [], t0) shifts with
      | Some (q', (L, [], t1)) =>
        if eqb_q q q' then
          if subsumes t1 t0 then
            match n1 with
            | 0 => false
            | S _ => true
            end
          else
            false
        else false
      | _ => false
      end
    else
      false
  | _ => false
  end.

Definition verify_bouncer (tm : TM) (d : dir) (n0 n1 : nat)
    (split : list (nat * nat)) (shifts : list (nat * nat)) : bool :=
  match d with
  | L => verify_bouncer_l tm n0 n1 split shifts
  | R => verify_bouncer_l (flip tm) n0 n1 split shifts
  end.

Lemma verify_bouncer_l_correct : forall tm n0 n1 split shifts,
  verify_bouncer_l tm n0 n1 split shifts = true ->
  ~ halts tm c0.
Proof.
  introv H. unfold verify_bouncer_l in H.
  destruct (cmultistep tm n0 starting) as [[c' Hc'] |]; try discriminate.
  destruct c' as [q [[[] s] r]]; try discriminate.
  destruct (eqb_sym s s0); try discriminate. subst s.
  destruct (split_tape split r) as [t0 Ht0].
  destruct (steps tm n1 q (L, [], t0) shifts) as [[q' [[[] []] t1]] |] eqn:E;
    try discriminate.
  destruct (eqb_q q q'); try discriminate. subst q'.
  destruct (subsumes t1 t0) as [Ht1 |]; try discriminate.
  destruct n1; inverts H.

  eapply skip_halts with (n := n0); try eassumption.
  apply progress_nonhalt with
    (P := fun c => exists r, c = lift (q;; undir (L, [], r)) /\ t0 ~ r).
  - introv H1. destruct H1 as [r' [Ec Hr']]. subst c.
    apply steps_some with (t := (L, [], r')) in E; auto.
    destruct E as [[[d l] r''] [[E [Hl Hr]] Hrun]]. subst d. inverts Hl.
    eauto 6.
  - exists r. auto.
Qed.

Theorem verify_bouncer_correct : forall tm d n0 n1 split shifts,
  verify_bouncer tm d n0 n1 split shifts = true ->
  ~ halts tm c0.
Proof.
  introv H.
  destruct d; apply verify_bouncer_l_correct in H; auto.
Qed.

End Bouncers.
