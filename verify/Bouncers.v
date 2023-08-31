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

Inductive segment :=
  | Repeat (xs : list Sym)
  | Symbol (x : Sym).

Reserved Notation "s ~ t" (at level 70).

Inductive matches : list segment -> list Sym -> Prop :=
  | match_zeros n : [] ~ repeat s0 n
  | match_sym x s t : s ~ t -> Symbol x :: s ~ x :: t
  | match_skip xs s t : s ~ t -> Repeat xs :: s ~ t
  | match_repeat xs s t : Repeat xs :: s ~ t -> Repeat xs :: s ~ xs ++ t

  where "s ~ t" := (matches s t).

Local Hint Constructors matches : core.

Lemma match_nil : [] ~ [].
Proof. exact (match_zeros 0). Qed.

Local Hint Immediate match_nil : core.

(** XXX: perhaps unnecessary *)
Lemma match_repeatn : forall n xs s t,
  s ~ t -> Repeat xs :: s ~ concat (repeat xs n) ++ t.
Proof.
  induction n; introv H.
  - auto.
  - simpl. rewrite <- app_assoc. auto.
Qed.

Lemma length_gt0_if_not_nil : forall A (xs : list A),
  [] <> xs -> length xs <> 0.
Proof. introv H Hlen. apply length_zero_iff_nil in Hlen. auto. Qed.

Local Ltac Zify.zify_pre_hook ::=
  try lazymatch goal with
  | H: [] <> _ |- _ => apply length_gt0_if_not_nil in H
  | H: [] = _ -> False |- _ => apply length_gt0_if_not_nil in H
  end.

Local Obligation Tactic := program_simplify; auto; simpl;
  autorewrite with list; intuition;
  try (lia || congruence).

(** Check whether a symbolic tape [s] matches a concrete tape [t].
    Assumes that [s] is aligned, which allows using a greedy algorithm. *)
Program Fixpoint check_match (s : list segment) (t : list Sym)
    {measure (length s + length t)} : {s ~ t} + {True} :=
  match s, t with
  | Symbol x :: s', x' :: t' =>
    eqb_sym x x' && Reduce (check_match s' t')
  | Repeat xs :: s', t =>
    match xs with
    | [] => Reduce (check_match s' t)
    | _ =>
      match (strip_prefix eqb_sym xs t) with
      | [|| t' ||] => Reduce (check_match (Repeat xs :: s') t')
      | !! => Reduce (check_match s' t)
      end
    end
  | [], [] => Yes
  | _, _ => No
  end.


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

Ltac match_map_destruct H :=
  lazymatch type of H with
  | map Symbol ?xs ++ ?s ~ ?t =>
    let E := fresh in
    let t' := fresh in
    apply match_map_destruct in H;
    destruct H as [t' [E H]];
    subst t; rename t' into t
  end.

Lemma match_repeat_firstn : forall n s' t,
  s' ~ skipn n t ->
  Repeat (firstn n t) :: s' ~ t.
Proof.
  introv H.
  assert (E : firstn n t ++ skipn n t = t)
    by apply firstn_skipn.
  rewrite <- E at 2.
  auto.
Qed.

Local Hint Resolve match_map match_map_firstn match_repeat_firstn : core.

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

Lemma shift_repeat : forall x r s t,
  Repeat (x :: r) :: Symbol x :: s ~ t ->
  Symbol x :: Repeat (r ++ [x]) :: s ~ t.
Proof.
  introv H.
  remember (Repeat (x :: r) :: Symbol x :: s) as s' eqn:Es'.
  induction H; try discriminate.
  - (* match_skip *)
    inverts Es'. inverts H. auto.
  - (* match_repeat *)
    specialize (IHmatches Es'). inverts Es'.
    inverts IHmatches as IH.
    simpl. apply match_sym.
    rewrite (app_cons_r r x t0).
    auto.
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
  Repeat [] :: s ~ t -> s ~ t.
Proof.
  introv H.
  remember (Repeat [] :: s) as s' eqn:Es'.
  induction H; try discriminate; inverts Es'; auto.
Qed.

Local Hint Immediate repeat_empty : core.

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

Lemma match_s0 : forall s, s ~ [] -> s ~ [s0].
Proof.
  introv H.
  remember [] as t eqn:Et.
  induction H.
  - (* match_zeros *)
    inverts Et as E. rewrite E.
    apply (match_zeros 1).
  - (* match_sym *) inverts Et.
  - (* match_skip *) auto.
  - (* match_repeat *)
    apply app_eq_nil in Et. destruct Et. subst.
    auto.
Qed.

Local Hint Resolve match_s0 : core.

Lemma simple_step_some : forall tm q s l r q' st' lt rt,
  simple_step tm q s l r = Some (q', st') ->
  l ~ lt ->
  r ~ rt ->
  exists t', st' ~~ t' /\
    lift (q;; lt {{s}} rt) -[ tm ]->* lift (q';; undir t').
Proof.
  introv Hstep Hl Hr.
  unfold simple_step in Hstep.
  destruct (tm (q, s)) as [[[s' []] q0] |] eqn:Etm;
    inverts Hstep; unfold "~~".
  - (* L *)
    destruct lt as [| ls lt]; eexists (_, _, _);
      intuition eauto; exact (evstep_one (step_left Etm)).
  - (* R *)
    destruct rt as [| rs rt]; eexists (_, _, _);
      intuition eauto; exact (evstep_one (step_right Etm)).
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

(** To prove the shift rule lemma, we need to strengthen the hypothesis,
    by allowing for some occurences of [s'] on the right-hand side. *)
Lemma shiftrule_left' : forall tm q l s tail rest n s' t,
  submultistep tm n (q, (L, s, tail)) = Some (q, (L, [], tail ++ s')) ->
  (L, Repeat s :: l, map Symbol tail ++ Repeat s' :: rest) ~~ t ->
  exists t', (L, l, map Symbol tail ++ Repeat s' :: rest) ~~ t' /\
    lift (q;; undir t) -[ tm ]->* lift (q;; undir t').
Proof.
  introv Hstep Hmatch.
  destruct t as [[d lt ] rt]. destruct Hmatch as [Hd [Hl Hr]]. subst d.
  remember (Repeat s :: l) as l' eqn:El'.
  generalize dependent rt.
  induction Hl as [| | tail' l' lt Hl IH | tail' l' lt Hl IH];
    inverts El'; introv Hr;
    match_map_destruct Hr.
  - (* match_skip *)
    exists (L, lt, tail ++ rt).
    auto 7.
  - (* match_repeat *)
    specialize (IH eq_refl (tail ++ s' ++ rt) ltac:(solve [auto])).
    destruct IH as [t [Hmatch IH]]. exists t.
    split; [exact Hmatch|].
    eapply submultistep_some in Hstep. simpl sublift in Hstep.
    eapply evstep_trans. { apply Hstep. }
    rewrite <- app_assoc. apply IH.
Qed.

Lemma shiftrule_left : forall tm q l s tail rest n s' t,
  submultistep tm n (q, (L, s, tail)) = Some (q, (L, [], tail ++ s')) ->
  (L, Repeat s :: l, map Symbol tail ++ rest) ~~ t ->
  exists t', (L, l, map Symbol tail ++ Repeat s' :: rest) ~~ t' /\
    lift (q;; undir t) -[ tm ]->* lift (q;; undir t').
Proof.
  introv Hstep Hmatch.
  destruct t as [[d lt] rt]. destruct Hmatch as [E [Hl Hr]]. subst d.
  match_map_destruct Hr.
  eapply shiftrule_left'; eauto 6.
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
        | [|| s' ||] => Some (map Symbol tail ++ Repeat s' :: rest)
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
    lift (q;; undir t) -[ tm ]->* lift (q;; undir t').
Proof.
  introv H Hmatch. unfold try_shift_rule in H.
  destruct (grab_tail r k) as [[[tail rest] Hgrab] |]; try discriminate.
  simpl in Hgrab. subst r.

  destruct (submultistep tm n (q, (L, s, tail)))
    as [[q'' [[[] []] r'']] |] eqn:Hstep; try discriminate.
  destruct (eqb_q q q'') as [E |]; try discriminate. subst q''.
  destruct (strip_prefix eqb_sym tail r'') as [[s' E] |]; try discriminate.
  subst r''. inverts H.

  eapply shiftrule_left; eassumption.
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

Lemma undir_left_s0 : forall n r,
  undir (L, repeat s0 n, r) = (repeat s0 (pred n), s0, r).
Proof. introv. destruct n; reflexivity. Qed.

Lemma undir_right_s0 : forall n l,
  undir (R, l, repeat s0 n) = (l, s0, repeat s0 (pred n)).
Proof. introv. destruct n; reflexivity. Qed.

Lemma step_some : forall tm q q' st st' shifts shifts' t,
  step tm q st shifts = (Some (q', st'), shifts') ->
  st ~~ t ->
  exists t', st' ~~ t' /\
    lift (q;; undir t) -[ tm ]->* lift (q';; undir t').
Proof.
  introv H Hmatch.
  destruct st as [[[] l] r]; simpl in H.
  - (* L *)
    destruct l as [| [s | s] l].
    + (* [] *)
      destruct t as [[d lt] rt]; destruct Hmatch as [E [Hl Hr]]; subst d.
      inverts H as H. inverts Hl.
      rewrite undir_left_s0.
      eapply simple_step_some in H; eauto.
    + (* Repeat s *)
      destruct shifts as [| [n k] shifts]; try discriminate.
      destruct (try_shift_rule tm q s l r n k) as [r' |] eqn:E; inverts H.
      eapply try_shift_rule_some in E; try eassumption.
    + (* Symbol s *)
      destruct t as [[d lt] rt]; destruct Hmatch as [E [Hl Hr]]; subst d.
      inverts H as H. inverts Hl as Hl.
      eapply simple_step_some in H; eauto.
  - (* R *)
    destruct r as [| [s | s] r].
    + (* [] *)
      destruct t as [[d lt] rt]; destruct Hmatch as [E [Hl Hr]]; subst d.
      inverts H as H. inverts Hr.
      rewrite undir_right_s0.
      eapply simple_step_some in H; eauto.
    + (* Repeat s *)
      destruct shifts as [| [n k] shifts]; try discriminate.
      admit.
    + (* Symbol s *)
      destruct t as [[d lt] rt]; destruct Hmatch as [E [Hl Hr]]; subst d.
      inverts H as H. inverts Hr as Hr.
      eapply simple_step_some in H; eauto.
Admitted.
