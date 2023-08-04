(** * Skelet #1 *)

(** Following https://www.sligocki.com/2023/03/13/skelet-1-infinite.html *)

Set Warnings "-notation-overriden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import PeanoNat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
From BusyCoq Require Import Individual.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, R, D)
  | B, 0 => Some (1, L, C)  | B, 1 => Some (0, R, C)
  | C, 0 => Some (1, R, A)  | C, 1 => Some (1, L, D)
  | D, 0 => Some (0, R, E)  | D, 1 => Some (0, L, B)
  | E, 0 => None            | E, 1 => Some (1, R, C)
  end.

Fixpoint repeat {A} (n : nat) (f : A -> A) (a : A) : A :=
  match n with
  | O => a
  | S n => f (repeat n f a)
  end.

Lemma repeat_shift : forall A n f (a : A),
  f (repeat n f a) = repeat n f (f a).
Proof.
  induction n; introv.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma repeat_add : forall A n m f (a : A),
  repeat (n + m) f a = repeat n f (repeat m f a).
Proof.
  introv. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation "f :> t" := (f t)  (at level 25, right associativity, only parsing).
Notation "t <: f" := (f t)  (at level 24, left associativity, only parsing).
Notation "l <| r" := (l <{{C}} 1 >> 0 >> r)  (at level 30).
Notation "l |> r" := (l {{A}}> r)  (at level 30).

Fixpoint run (n : nat) (t : side) : side :=
  match n with
  | O => t << 0
  | S n => run n t << 1
  end.

Definition x  (t : side) := t <: run 2 <: run 2.
Definition Dl (t : side) := t <: run 2 <: run 1.
Definition Dr (t : side) := run 2 :> run 1 :> t.
Definition C0 (t : side) := t <: run 2 <: run 3 <: run 2.
Definition C1 (t : side) := t <: run 2 <: run 0 <: run 1.
Definition C2 (t : side) := t <: run 4 <: run 2.
Definition C3 (t : side) := t <: run 1 <: run 1.
Notation C := C3.
Definition R := const 0.
Definition L := const 0.
Definition P  (t : side) := t <: run 2.
Definition F0 (t : side) := t <: run 4 <: run 3 <: run 2.
Definition F1 (t : side) := t <: run 4 <: run 0 <: run 1.
Definition F2 (t : side) := t <: run 6 <: run 2.
Definition F3 (t : side) := t <: run 3 <: run 1.
Definition G0 (t : side) := t <: run 2 <: run 3 <: run 3 <: run 2.
Definition G1 (t : side) := t <: run 2 <: run 3 <: run 0 <: run 1.
Definition G2 (t : side) := t <: run 2 <: run 5 <: run 2.

Lemma rule_x_left  : forall l r,       l <: x <| r -->* l <| x :> r.
Proof. triv. Qed.
Lemma rule_D_left  : forall l r,      l <: Dl <| r -->* l <| Dr :> r.
Proof. triv. Qed.
Lemma rule_C_left  : forall l r,       l <: C <| r -->* l <| C :> r.
Proof. triv. Qed.
Lemma rule_x_right : forall l r,       l |> x :> r -->* l <: x |> r.
Proof. triv. Qed.
Lemma rule_D_right : forall l r,      l |> Dr :> r -->* l <: Dl |> r.
Proof. triv. Qed.
Lemma rule_xR      : forall l,         l <: x |> R -->* l <| C :> x :> P :> R.
Proof. unfold R, C, x, P. triv. Qed.
Lemma rule_DR      : forall l,        l <: Dl |> R -->* l <| x :> R.
Proof. unfold R, x. triv. Qed.
Lemma rule_L       : forall r,    L <| C :> x :> r -->* L <: C1 <: Dl |> P :> r.
Proof. unfold L, C1, Dl, C. triv. Qed.
Lemma rule_C30     : forall l r,  l <: x |> C :> r -->* l <: C0 |> r.
Proof. triv. Qed.
Lemma rule_C01     : forall l r,      l <: C0 <| r -->* l <: C1 <: x |> r.
Proof. triv. Qed.
Lemma rule_C12     : forall l r,      l <: C1 <| r -->* l <: C2 |> r.
Proof. triv. Qed.
Lemma rule_C23     : forall l r,      l <: C2 <| r -->* l <: C <: x |> r.
Proof. triv. Qed.
Lemma rule_DC      : forall l r, l <: Dl |> C :> r -->* l <: P <: x |> r.
Proof. triv. Qed.
Lemma rule_C20     : forall l r, l <: C2 |> C :> r -->* l <: F0 |> r.
Proof. triv. Qed.
Lemma rule_F0      : forall l r,      l <: F0 <| r -->* l <: F1 <: x |> r.
Proof. triv. Qed.
Lemma rule_F1      : forall l r,      l <: F1 <| r -->* l <: F2 |> r.
Proof. triv. Qed.
Lemma rule_F2      : forall l r,      l <: F2 <| r -->* l <: F3 <: x |> r.
Proof. triv. Qed.
Lemma rule_F3      : forall l r, l <: x <: F3 <| r -->* l <: P <: C1 <: Dl |> r.
Proof. triv. Qed.
Lemma rule_C03     : forall l r, l <: C0 |> C :> r -->* l <: G0 |> r.
Proof. triv. Qed.
Lemma rule_G0      : forall l r,      l <: G0 <| r -->* l <: G1 <: x |> r.
Proof. triv. Qed.
Lemma rule_G1      : forall l r,      l <: G1 <| r -->* l <: G2 |> r.
Proof. triv. Qed.
Lemma rule_G2      : forall l r,      l <: G2 <| r -->* l <: P <: Dl <: x |> r.
Proof. triv. Qed.
Lemma rule_P_left  : forall l r,       l <: P <| r -->* l <| P :> r.
Proof. triv. Qed.
Lemma rule_P_P     : forall l r,  l |> P :> P :> r -->* l <: x |> r.
Proof. triv. Qed.
Lemma rule_P_x     : forall l r,  l |> P :> x :> r -->* l <: x |> P :> r.
Proof. triv. Qed.
Lemma rule_P_R     : forall l,         l |> P :> R -->* l <| P :> R.
Proof. unfold P, R. triv. Qed.
Lemma rule_P_Dx    : forall l r,
  l |> P :> Dr :> x :> r -->* l <: C1 <: Dl |> P :> r.
Proof. triv. Qed.
Lemma rule_P_Cx    : forall l r,
  l |> P :> C :> x :> r -->* l <| P :> Dr :> P :> r.
Proof. triv. Qed.
Lemma rule_P_DP    : forall l r,
  l |> P :> Dr :> P :> r -->* l <: C1 <: Dl |> r.
Proof. triv. Qed.
Lemma rule_P_DDx   : forall l r,
  l |> P :> Dr :> Dr :> x :> r -->* l <: C2 <: C1 <: Dl |> r.
Proof. triv. Qed.
Lemma rule_P_DCx   : forall l r,
  l |> P :> Dr :> C :> x :> r -->* l <: G1 <: Dl |> P :> r.
Proof. triv. Qed.

Lemma rule_xn_left : forall n l r,
  l <: repeat n x <| r -->* l <| repeat n x :> r.
Proof. induction n; triv. rewrite repeat_shift. finish. Qed.

Lemma rule_xn_right : forall n l r,
  l |> repeat n x :> r -->* l <: repeat n x |> r.
Proof. induction n; triv. rewrite repeat_shift. finish. Qed.

Lemma rule_P_xn    : forall n l r,
  l |> P :> repeat n x :> r -->* l <: repeat n x |> P :> r.
Proof. induction n.
  - triv.
  - introv.
    simpl. follow rule_P_x. follow IHn.
    rewrite repeat_shift.
    finish.
Qed.

(*
Inductive strider : nat -> side -> Prop :=
  | strider_R n : strider n R
  | strider_x n t : strider n t -> strider n (x :> t)
  | strider_D n t : strider n t -> strider n (Dr :> t)
  | strider_C n t : strider (4 * n) t -> strider n (repeat n x :> C :> t).

Fixpoint stride_result (n : nat) (t : side) (s : strider (S n) t) :
  {t' : side | strider n t'} :=
  match s return {t' : side | strider n t'}%type with
  | strider_R _ => exist _ R (strider_R n)
  | _ => exist _ R (strider_R n)
  end.
*)

Inductive lsym :=
  | l_xs (n : positive)
  | l_D
  | l_P
  | l_C0 | l_C1 | l_C2 | l_C3
  | l_F0 | l_F1 | l_F2 | l_F3
  | l_G0 | l_G1 | l_G2.

Inductive rsym :=
  | r_xs (n : positive)
  | r_D
  | r_C
  | r_P.

Notation ltape := (list lsym).
Notation rtape := (list rsym).

Inductive direction := left | right.

Notation conf := (direction * ltape * rtape)%type.

Fixpoint lift_right (t : rtape) : side :=
  match t with
  | [] => R
  | r_xs n :: t => repeat (Pos.to_nat n) x :> lift_right t
  | r_D :: t => Dr :> lift_right t
  | r_C :: t => C :> lift_right t
  | r_P :: t => P :> lift_right t
  end.

Fixpoint lift_left (t : ltape) : side :=
  match t with
  | [] => L
  | l_xs n :: t => lift_left t <: repeat (Pos.to_nat n) x
  | l_D :: t => lift_left t <: Dl
  | l_P :: t => lift_left t <: P
  | l_C0 :: t => lift_left t <: C0
  | l_C1 :: t => lift_left t <: C1
  | l_C2 :: t => lift_left t <: C2
  | l_C3 :: t => lift_left t <: C3
  | l_F0 :: t => lift_left t <: F0
  | l_F1 :: t => lift_left t <: F1
  | l_F2 :: t => lift_left t <: F2
  | l_F3 :: t => lift_left t <: F3
  | l_G0 :: t => lift_left t <: G0
  | l_G1 :: t => lift_left t <: G1
  | l_G2 :: t => lift_left t <: G2
  end.

Fixpoint lift (c : conf) : Q * tape :=
  match c with
  | (left,  l, r) => lift_left l <| lift_right r
  | (right, l, r) => lift_left l |> lift_right r
  end.

Definition decr (n : positive) : N :=
  N.pred (N.pos n).

Lemma decr_nat : forall n, N.to_nat (decr (Pos.of_succ_nat n)) = n.
Proof. unfold decr. lia. Qed.

Definition lxs (n : N) (l : ltape) : ltape :=
  match n with
  | N0 => l
  | Npos n =>
    match l with
    | l_xs m :: l =>
      l_xs (n + m) :: l
    | _ => l_xs n :: l
    end
  end.

Definition rxs (n : N) (r : rtape) : rtape :=
  match n with
  | N0 => r
  | Npos n =>
    match r with
    | r_xs m :: r =>
      r_xs (n + m) :: r
    | _ => r_xs n :: r
    end
  end.

Lemma lift_lxs : forall n l,
  lift_left (lxs n l) = lift_left l <: repeat (N.to_nat n) x.
Proof.
  introv. destruct n; try reflexivity.
  destruct l as [| [] l]; try reflexivity.
  simpl. rewrite Pos2Nat.inj_add.
  rewrite repeat_add. reflexivity.
Qed.

Lemma lift_rxs : forall n r,
  lift_right (rxs n r) = repeat (N.to_nat n) x :> lift_right r.
Proof.
  introv. destruct n; try reflexivity.
  destruct r as [| [] r]; try reflexivity.
  simpl. rewrite Pos2Nat.inj_add.
  rewrite repeat_add. reflexivity.
Qed.

Arguments lxs _ _ : simpl never.
Arguments rxs _ _ : simpl never.

(*
Lemma decr_some : forall n m,
  decr n = Some m ->
  n = Pos.succ m.
Proof. introv H; destruct n; inverts H; lia. Qed.

Ltac match_decr :=
  match goal with
  | H: match decr ?n with | Some _ => _ | None => _ end = _ |- _ =>
    let E := fresh in
    let n' := fresh n in
    destruct (decr n) as [n' |] eqn:E;
      [apply decr_some in E; subst n |];
    try discriminate
  end.
  *)

Ltac pos_nat p :=
  let p' := fresh p in
  let E := fresh in
  destruct (Pos2Nat.is_succ p) as [p' E];
  rewrite E in *;
  apply SuccNat2Pos.inv in E; subst p;
  rename p' into p.

Ltac handle_decr :=
  match goal with
  | |- context G [decr ?p] => pos_nat p
  end.

Ltac simp :=
  simpl;
  try rewrite lift_lxs;
  try rewrite lift_rxs;
  try rewrite Pos2Nat.inj_succ;
  try handle_decr;
  try rewrite decr_nat;
  simpl.

Definition step (c : conf) : option conf :=
  match c with
  | (right, l, r) =>
    match r with
    | [] =>
      match l with
      (* x > R  -->  < C x P R *)
      | l_xs n :: l =>
        Some (left, lxs (decr n) l, [r_C; r_xs 1; r_P])
      (* D > R  -->  < x R *)
      | l_D :: l =>
        Some (left, l, [r_xs 1])
      | _ => None
      end
    (* > x^n  -->  x^n > *)
    | r_xs n :: r =>
    Some (right, lxs (N.pos n) l, r)
    (* > D    -->  D > *)
    | r_D :: r =>
      Some (right, l_D :: l, r)
    | r_C :: r =>
      match l with
      (* x > C  -->  C0 > *)
      | l_xs n :: l =>
        Some (right, l_C0 :: lxs (decr n) l, r)
      (* D > C  -->  P x > *)
      | l_D :: l =>
        Some (right, l_xs 1 :: l_P :: l, r)
      (* C0 > C --> G0 > *)
      | l_C0 :: l =>
        Some (right, l_G0 :: l, r)
      | _ => None
      end
    (* > P R    --> < P R *)
    | [r_P] =>
      Some (left, l, [r_P])
    (* > P x^n  --> x^n > P *)
    | r_P :: r_xs n :: r =>
      Some (right, lxs (N.pos n) l, r_P :: r)
    (* > P D x  --> C1 D > P *)
    | r_P :: r_D :: r_xs n :: r =>
      Some (right, l_D :: l_C1 :: l, r_P :: rxs (decr n) r)
    (* > P DDx  --> C2 C1 D > *)
    | r_P :: r_D :: r_D :: r_xs n :: r =>
      Some (right, l_D :: l_C1 :: l_C2 :: l, rxs (decr n) r)
    (* > P DCx  --> G1 D > P *)
    | r_P :: r_D :: r_C :: r_xs n :: r =>
      Some (right, l_D :: l_G1 :: l, r_P :: rxs (decr n) r)
    (* > P D P  --> C1 D > *)
    | r_P :: r_D :: r_P :: r =>
      Some (right, l_D :: l_C1 :: l, r)
    (* > P C x  --> < P D P *)
    | r_P :: r_C :: r_xs n :: r =>
      Some (left, l, r_P :: r_D :: r_P :: rxs (decr n) r)
    (* > P P    --> x > *)
    | r_P :: r_P :: r =>
      Some (right, lxs 1 l, r)
    | _ => None
    end
  | (left, l, r) =>
    match l with
    (* L < C x --> L C1 D > P *)
    | [] =>
      match r with
      | r_C :: r_xs n :: r =>
        Some (right, [l_D; l_C1], r_P :: rxs (decr n) r)
      | _ => None
      end
    (* x^n <  --> < x^n *)
    | l_xs n :: l =>
      Some (left, l, rxs (N.pos n) r)
    (* D <   --> < D *)
    | l_D :: l =>
      Some (left, l, r_D :: r)
    (* P <   --> < P *)
    | l_P :: l =>
      Some (left, l, r_P :: r)
    (* C0 <  -->  C1 x > *)
    | l_C0 :: l =>
      Some (right, l_xs 1 :: l_C1 :: l, r)
    (* C1 <  -->  C2 > *)
    | l_C1 :: l =>
      Some (right, l_C2 :: l, r)
    (* C2 <  -->  C3 x > *)
    | l_C2 :: l =>
      Some (right, l_xs 1 :: l_C3 :: l, r)
    (* C <  -->  < C *)
    | l_C3 :: l =>
      Some (left, l, r_C :: r)
    (* G0 < -->  G1 x > *)
    | l_G0 :: l =>
      Some (right, l_xs 1 :: l_G1 :: l, r)
    (* G1 < -->  G2 > *)
    | l_G1 :: l =>
      Some (right, l_G2 :: l, r)
    (* G2 < -->  P D x > *)
    | l_G2 :: l =>
      Some (right, l_xs 1 :: l_D :: l_P :: l, r)
    | _ => None
    end
  end.

Lemma step_spec : forall c c',
  step c = Some c' ->
  lift c -->* lift c'.
Proof.
  introv H.
  destruct c as [[[] l] r]; simpl in H.
  - (* left *)
    destruct l as [| [] l]; inverts H as H; simp.
    + (* L < C x --> L C1 D > P *)
      destruct r as [| [] [| [] r]]; inverts H; simp.
      apply rule_L.
    + (* x^n < --> < x^n *)
      apply rule_xn_left.
    + (* D <   --> < D *)
      apply rule_D_left.
    + (* P <   --> < P *)
      apply rule_P_left.
    + (* C0 <  --> C1 x > *)
      apply rule_C01.
    + (* C1 <  --> C2 > *)
      apply rule_C12.
    + (* C2 <  --> C3 x > *)
      apply rule_C23.
    + (* C <   --> < C *)
      apply rule_C_left.
    + (* G0 <  --> G1 x > *)
      apply rule_G0.
    + (* G1 <  --> G2 > *)
      apply rule_G1.
    + (* G2 <  --> P D x > *)
      apply rule_G2.
  - (* right *)
    destruct r as [| [] r]; inverts H as H; simp.
    + destruct l as [| [] l]; inverts H; simp.
      * (* x > R  -->  < C x P R *)
        apply rule_xR.
      * (* D > R  -->  < x R *)
        apply rule_DR.
    + (* > x^n  -->  x^n > *)
      apply rule_xn_right.
    + (* > D    -->  D > *)
      apply rule_D_right.
    + destruct l as [| [] l]; inverts H; simp.
      * (* x > C  -->  C0 > *)
        apply rule_C30.
      * (* D > C  -->  P x *)
        apply rule_DC.
      * (* C0 > C -->  G0 > *)
        apply rule_C03.
    + destruct r as [| [] r]; inverts H as H; simp.
      * (* > P R   --> < P R *)
        apply rule_P_R.
      * (* > P x^n --> x^n > P *)
        apply rule_P_xn.
      * destruct r as [| [] r]; inverts H as H; simp.
        ** (* > P D x --> C1 D > P *)
          apply rule_P_Dx.
        ** (* > P DDx --> C2 C1 D > *)
          destruct r as [| [] r]; inverts H as H; simp.
          apply rule_P_DDx.
        ** (* > P DCx --> G1 D > P *)
          destruct r as [| [] r]; inverts H as H; simp.
          apply rule_P_DCx.
        ** (* > P D P --> C1 D *)
          apply rule_P_DP.
      * destruct r as [| [] r]; inverts H as H; simp.
        (* > P C x --> < P D P *)
        apply rule_P_Cx.
      * (* > P P --> x > *)
        apply rule_P_P.
Qed.

Lemma init : c0 -->* L <: C1 |> P :> R.
Proof. unfold L, C1, R. execute. Qed.

Definition initial: conf := (right, [l_C1], [r_P]).

Lemma init' : c0 -->* lift initial.
Proof. exact init. Qed.

Fixpoint steps (n : nat) (c : conf) : option conf :=
  match n with
  | O => Some c
  | S n =>
    match step c with
    | Some c' => steps n c'
    | None => None
    end
  end.

Compute steps 13367 initial.
