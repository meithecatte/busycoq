(** * Skelet #1 *)

(** Following https://www.sligocki.com/2023/03/13/skelet-1-infinite.html *)

Set Warnings "-abstract-large-number".
From Coq Require Import PeanoNat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
From Coq Require Import Program.Tactics.
From Coq Require Import ZifyBool.
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

Lemma repeat_S : forall {A} n f (a : A),
  repeat (S n) f a = f (repeat n f a).
Proof. reflexivity. Qed.

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

Definition Fl (t : side) := t <: C2 <: repeat 7640 x <: Dl <: repeat 10344 x.
Definition Gl (t : side) :=
  t <: repeat 300 x <: Dl <: repeat 30826 x <: Dl <: repeat 72142 x <: Dl <:
  repeat 3076 x <: Dl <: repeat 1538 x <: Dl.
Definition Gr (t : side) :=
  repeat 300 x :> Dr :> repeat 30826 x :> Dr :> repeat 72142 x :> Dr :>
  repeat 3076 x :> Dr :> repeat 1538 x :> Dr :> t.
Definition Hl (t : side) :=
  t <: C1 <: Dl <: repeat 299 x <: C1 <: Dl <: repeat 30825 x
  <: C1 <: Dl <: repeat 72141 x <: C1 <: Dl <: repeat 3075 x
  <: C1 <: Dl <: repeat 1537 x.

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
Lemma rule_C2_C    : forall l r, l <: C2 |> C :> r -->* l <: F0 |> r.
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
Proof.
  induction n.
  - triv.
  - introv.
    simpl. follow rule_P_x. follow IHn.
    rewrite repeat_shift.
    finish.
Qed.

Lemma rule_P_DG    : forall l r,
  l |> P :> Dr :> Gr :> r  -->*  l <: Hl |> P :> Dr :> r.
Proof.
  introv. unfold Gr.
  rewrite (repeat_S 299).
  follow rule_P_Dx. follow rule_P_xn.
  rewrite (repeat_S 30825).
  follow rule_P_Dx. follow rule_P_xn.
  rewrite (repeat_S 72141).
  follow rule_P_Dx. follow rule_P_xn.
  rewrite (repeat_S 3075).
  follow rule_P_Dx. follow rule_P_xn.
  rewrite (repeat_S 1537).
  follow rule_P_Dx. follow rule_P_xn.
  finish.
Qed.

Lemma rule_P_DGn   : forall n l r,
  l |> P :> Dr :> repeat n Gr :> r  -->*  l <: repeat n Hl |> P :> Dr :> r.
Proof.
  induction n; introv.
  - finish.
  - simpl repeat. follow rule_P_DG. follow IHn.
    rewrite repeat_shift. finish.
Qed.

Lemma rule_G_right : forall l r, l |> Gr :> r -->* l <: Gl |> r.
Proof.
  introv. unfold Gl, Gr.
  repeat (follow rule_xn_right; follow rule_D_right).
  finish.
Qed.

Lemma rule_Gn_right : forall n l r,
  l |> repeat n Gr :> r -->* l <: repeat n Gl |> r.
Proof.
  induction n; introv.
  - finish.
  - simpl repeat. follow rule_G_right.
    follow IHn. rewrite repeat_shift.
    finish.
Qed.

Lemma rule_G_left : forall l r, l <: Gl <| r -->* l <| Gr :> r.
Proof.
  introv. unfold Gl, Gr.
  repeat (follow rule_D_left; follow rule_xn_left).
  finish.
Qed.

Lemma rule_Gn_left : forall n l r,
  l <: repeat n Gl <| r -->* l <| repeat n Gr :> r.
Proof.
  induction n; introv.
  - finish.
  - simpl repeat. follow rule_G_left.
    follow IHn. rewrite repeat_shift.
    finish.
Qed.

Inductive lsym :=
  | l_xs (n : positive)
  | l_D
  | l_P
  | l_C0 | l_C1 | l_C2 | l_C3
  | l_F0 | l_F1 | l_F2 | l_F3
  | l_G0 | l_G1 | l_G2
  | l_Fs (n : positive)
  | l_Gs (n : positive)
  | l_Hs (n : positive).

Inductive rsym :=
  | r_xs (n : positive)
  | r_D
  | r_C
  | r_P
  | r_Gs (n : positive).

Notation ltape := (list lsym).
Notation rtape := (list rsym).

Definition F := [l_xs 10344; l_D; l_xs 7640; l_C2].
Definition G := [r_xs 300; r_D; r_xs 30826; r_D; r_xs 72142; r_D;
              r_xs 3076; r_D; r_xs 1538; r_D].
Definition J := [l_D; l_C2; l_xs 95; l_C0;
                 l_xs 7713; l_D; l_D; l_xs 1866; l_C1;
                 l_xs 13231; l_D; l_xs 6197; l_C3;
                 l_xs 11066; l_D; l_xs 7279; l_C0;
                 l_xs 10524; l_D; l_xs 7550; l_C2;
                 l_xs 10389; l_D; l_xs 7618; l_C1;
                 l_xs 10355; l_D; l_xs 7635; l_C3;
                 l_xs 10347; l_D; l_xs 7639; l_C3;
                 l_xs 10345; l_D; l_xs 7640; l_C1].
Definition K : rtape :=
  [r_xs 7639; r_D; r_xs 10347; r_C;
   r_xs 7635; r_D; r_xs 10355; r_C;
   r_xs 7619; r_D; r_xs 10387; r_C;
   r_xs 7555; r_D; r_xs 10515; r_C;
   r_xs 7299; r_D; r_xs 11027; r_C;
   r_xs 6275; r_D; r_xs 13075; r_C;
   r_xs 2179; r_D; r_D; r_xs 7088; r_C;
   r_xs 1; r_C; r_xs 3849; r_P].

Definition uni_P : positive := 53946.
Definition uni_T : positive := 4 * uni_P - 5.

Definition eqb_l (a b : lsym) : {a = b} + {a <> b}.
  decide equality; apply Pos.eq_dec.
Defined.

Definition eqb_r (a b : rsym) : {a = b} + {a <> b}.
  decide equality; apply Pos.eq_dec.
Defined.

Definition eqb_rtape (xs ys : rtape) : {xs = ys} + {xs <> ys}.
  decide equality; apply eqb_r.
Defined.

Notation left := TM.L.
Notation right := TM.R.

Notation conf := (dir * ltape * rtape)%type.

Fixpoint lift_right (t : rtape) : side :=
  match t with
  | [] => R
  | r_xs n :: t => repeat (Pos.to_nat n) x :> lift_right t
  | r_D :: t => Dr :> lift_right t
  | r_C :: t => C :> lift_right t
  | r_P :: t => P :> lift_right t
  | r_Gs n :: t => repeat (Pos.to_nat n) Gr :> lift_right t
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
  | l_Fs n :: t => lift_left t <: repeat (Pos.to_nat n) Fl
  | l_Gs n :: t => lift_left t <: repeat (Pos.to_nat n) Gl
  | l_Hs n :: t => lift_left t <: repeat (Pos.to_nat n) Hl
  end.

Definition lift (c : conf) : Q * tape :=
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
    | l_xs m :: l => l_xs (n + m) :: l
    | _ => l_xs n :: l
    end
  end.

Definition rxs (n : N) (r : rtape) : rtape :=
  match n with
  | N0 => r
  | Npos n =>
    match r with
    | r_xs m :: r => r_xs (n + m) :: r
    | _ => r_xs n :: r
    end
  end.

Definition Fls (n : N) (l : ltape) : ltape :=
  match n with
  | N0 => l
  | Npos n =>
    match l with
    | l_Fs m :: l => l_Fs (n + m) :: l
    | _ => l_Fs n :: l
    end
  end.

Definition Gls (n : N) (l : ltape) : ltape :=
  match n with
  | N0 => l
  | Npos n =>
    match l with
    | l_Gs m :: l => l_Gs (n + m) :: l
    | _ => l_Gs n :: l
    end
  end.

Definition Grs (n : N) (r : rtape) : rtape :=
  match n with
  | N0 => r
  | Npos n =>
    match r with
    | r_Gs m :: r => r_Gs (n + m) :: r
    | _ => r_Gs n :: r
    end
  end.

Definition Hls (n : N) (l : ltape) : ltape :=
  match n with
  | N0 => l
  | Npos n =>
    match l with
    | l_Hs m :: l => l_Hs (n + m) :: l
    | _ => l_Hs n :: l
    end
  end.

Ltac prove_liftrule :=
  intros n t; destruct n; try reflexivity;
  destruct t as [| [] t]; try reflexivity;
  simpl; rewrite Pos2Nat.inj_add;
  rewrite repeat_add; reflexivity.

Lemma lift_lxs : forall n l,
  lift_left (lxs n l) = lift_left l <: repeat (N.to_nat n) x.
Proof. prove_liftrule. Qed.

Lemma lift_rxs : forall n r,
  lift_right (rxs n r) = repeat (N.to_nat n) x :> lift_right r.
Proof. prove_liftrule. Qed.

Lemma lift_Fls : forall n l,
  lift_left (Fls n l) = lift_left l <: repeat (N.to_nat n) Fl.
Proof. prove_liftrule. Qed.

Lemma lift_Gls : forall n l,
  lift_left (Gls n l) = lift_left l <: repeat (N.to_nat n) Gl.
Proof. prove_liftrule. Qed.

Lemma lift_Grs : forall n r,
  lift_right (Grs n r) = repeat (N.to_nat n) Gr :> lift_right r.
Proof. prove_liftrule. Qed.

Lemma lift_Hls : forall n l,
  lift_left (Hls n l) = lift_left l <: repeat (N.to_nat n) Hl.
Proof. prove_liftrule. Qed.

Ltac pos_nat p :=
  let p' := fresh p in
  let E := fresh in
  destruct (Pos2Nat.is_succ p) as [p' E];
  try rewrite E in *;
  apply SuccNat2Pos.inv in E; subst p;
  rename p' into p.

Ltac handle_decr :=
  lazymatch goal with
  | |- context [decr ?p] => pos_nat p; try rewrite decr_nat
  end.

Ltac simp :=
  simpl;
  try rewrite lift_lxs;
  try rewrite lift_rxs;
  try rewrite lift_Fls;
  try rewrite lift_Gls;
  try rewrite lift_Grs;
  try rewrite lift_Hls;
  try rewrite Pos2Nat.inj_succ;
  try handle_decr;
  simpl.

Definition unrxs (r : rtape) : option rtape :=
  match r with
  | r_xs n :: r => Some (rxs (decr n) r)
  | r_Gs n :: r =>
    Some (r_xs 299 :: r_D :: r_xs 30826 :: r_D :: r_xs 72142 :: r_D ::
              r_xs 3076 :: r_D :: r_xs 1538 :: r_D :: Grs (decr n) r)
  | _ => None
  end.

Lemma unrxs_spec : forall r r',
  unrxs r = Some r' ->
  lift_right r = x :> lift_right r'.
Proof.
  introv H.
  destruct r as [| [] r]; try discriminate; inverts H.
  - simp. reflexivity.
  - cbn[lift_right].
    rewrite lift_Grs.
    handle_decr.
    reflexivity.
Qed.

Arguments unrxs _ : simpl never.

Definition simple_step (c : conf) : option conf :=
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
      (* C2 > C --> F0 > *)
      | l_C2 :: l =>
        Some (right, l_F0 :: l, r)
      | _ => None
      end
    (* > P R    --> < P R *)
    | [r_P] =>
      Some (left, l, [r_P])
    (* > P x^n  --> x^n > P *)
    | r_P :: r_xs n :: r =>
      Some (right, lxs (N.pos n) l, r_P :: r)
    (* > P D x  --> C1 D > P *)
    (* Note: this rule doesn't use unrxs to let a more specialized rule
       trigger on > P D G^n. *)
    | r_P :: r_D :: r_xs n :: r =>
      Some (right, l_D :: l_C1 :: l, r_P :: rxs (decr n) r)
    (* > P DDx  --> C2 C1 D > *)
    | r_P :: r_D :: r_D :: r =>
      match unrxs r with
      | Some r => Some (right, l_D :: l_C1 :: l_C2 :: l, r)
      | None => None
      end
    (* > P DCx  --> G1 D > P *)
    | r_P :: r_D :: r_C :: r =>
      match unrxs r with
      | Some r => Some (right, l_D :: l_G1 :: l, r_P :: r)
      | None => None
      end
    (* > P D P  --> C1 D > *)
    | r_P :: r_D :: r_P :: r =>
      Some (right, l_D :: l_C1 :: l, r)
    (* > P D G^n --> H^n > P D *)
    | r_P :: r_D :: r_Gs n :: r =>
      Some (right, Hls (N.pos n) l, r_P :: r_D :: r)
    (* > P C x  --> < P D P *)
    | r_P :: r_C :: r =>
      match unrxs r with
      | Some r => Some (left, l, r_P :: r_D :: r_P :: r)
      | None => None
      end
    (* > P P    --> x > *)
    | r_P :: r_P :: r =>
      Some (right, lxs 1 l, r)
    (* > G^n    --> G^n > *)
    | r_Gs n :: r =>
      Some (right, Gls (N.pos n) l, r)
    | _ => None
    end
  | (left, l, r) =>
    match l with
    (* L < C x --> L C1 D > P *)
    | [] =>
      match r with
      | r_C :: r =>
        match unrxs r with
        | Some r => Some (right, [l_D; l_C1], r_P :: r)
        | None => None
        end
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
    (* F0 < -->  F1 x > *)
    | l_F0 :: l =>
      Some (right, l_xs 1 :: l_F1 :: l, r)
    (* F1 < -->  F2 > *)
    | l_F1 :: l =>
      Some (right, l_F2 :: l, r)
    (* F2 < --> F3 x > *)
    | l_F2 :: l =>
      Some (right, l_xs 1 :: l_F3 :: l, r)
    (* x F3 < --> P C1 D > *)
    | l_F3 :: l_xs n :: l =>
      Some (right, l_D :: l_C1 :: l_P :: lxs (decr n) l, r)
    (* G0 < -->  G1 x > *)
    | l_G0 :: l =>
      Some (right, l_xs 1 :: l_G1 :: l, r)
    (* G1 < -->  G2 > *)
    | l_G1 :: l =>
      Some (right, l_G2 :: l, r)
    (* G2 < -->  P D x > *)
    | l_G2 :: l =>
      Some (right, l_xs 1 :: l_D :: l_P :: l, r)
    (* G^n < --> < G^n *)
    | l_Gs n :: l =>
      Some (left, l, Grs (N.pos n) r)
    | _ => None
    end
  end.

Arguments lxs _ _ : simpl never.
Arguments rxs _ _ : simpl never.
Arguments Fls _ _ : simpl never.
Arguments Gls _ _ : simpl never.
Arguments Grs _ _ : simpl never.
Arguments Hls _ _ : simpl never.

Ltac unrxs :=
  lazymatch goal with
  | H: context [unrxs ?r] |- _ =>
    let E := fresh "E" in
    let r' := fresh "r'" in
    destruct (unrxs r) as [r' |] eqn:E; try discriminate;
    inverts H as H;
    apply unrxs_spec in E; simp; simpl in E; try rewrite E
  end.

Lemma simple_step_spec : forall c c',
  simple_step c = Some c' ->
  lift c -->* lift c'.
Proof.
  introv H.
  destruct c as [[[] l] r]; simpl in H.
  - (* left *)
    destruct l as [| [] l]; inverts H as H; simp.
    + (* L < C x --> L C1 D > P *)
      destruct r as [| [] r]; try discriminate; unrxs.
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
    + (* F0 <  --> F1 x > *)
      apply rule_F0.
    + (* F1 <  --> F2 > *)
      apply rule_F1.
    + (* F2 <  --> F3 x > *)
      apply rule_F2.
    + (* x F3 < --> P C1 D > *)
      destruct l as [| [] l]; inverts H; simp.
      apply rule_F3.
    + (* G0 <  --> G1 x > *)
      apply rule_G0.
    + (* G1 <  --> G2 > *)
      apply rule_G1.
    + (* G2 <  --> P D x > *)
      apply rule_G2.
    + (* G^n < --> < G^n *)
      apply rule_Gn_left.
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
      * (* C2 > C -->  F0 > *)
        apply rule_C2_C.
    + destruct r as [| [] r]; inverts H as H; simp.
      * (* > P R   --> < P R *)
        apply rule_P_R.
      * (* > P x^n --> x^n > P *)
        apply rule_P_xn.
      * destruct r as [| [] r]; (unrxs || inverts H; simp).
        ** (* > P Dx --> C1 D > P *)
          apply rule_P_Dx.
        ** (* > P DDx --> C2 C1 D > *)
          apply rule_P_DDx.
        ** (* > P DCx --> G1 D > P *)
          apply rule_P_DCx.
        ** (* > P DP --> C1 D *)
          apply rule_P_DP.
        ** (* > P DG^n --> H^n P D *)
          apply rule_P_DGn.
      * (* > P C x --> < P D P *)
        unrxs. apply rule_P_Cx.
      * (* > P P --> x > *)
        apply rule_P_P.
    + (* > G^n --> G^n > *)
      apply rule_Gn_right.
Qed.

(** [max_stride] returns the maximum number of times the stride rule can
    be applied to a tape before it becomes no longer possible. If [None]
    is returned, that means the rule can be applied an arbitrarily high
    amount of times – that happens for the very tail of the tape, without
    any [r_C] symbols.

    You'll note that [max_stride] is not critical for correctness in any way,
    since if it returns a value that's too large, the acceleration will simply
    not be applied. As such, we don't really prove anything about [max_stride].
    *)
Fixpoint max_stride (xs : N) (t : rtape) : option N :=
  match t with
  | [r_P] => None
  | r_P :: _ => Some 0%N
  | [] => Some 0%N
  | r_xs xs' :: t => max_stride (xs + N.pos xs') t
  | r_D :: t => max_stride 0 t
  | r_C :: t =>
    match max_stride 0 t with
    | Some n' => Some (N.min xs (N.shiftr n' 2))
    | None => Some xs
    end
  | r_Gs _ :: t => max_stride 0 t
  end.

Fixpoint stride (xs : N) (n : positive) (t : rtape) : option rtape :=
  match t with
  | [r_P] => Some (rxs xs [r_P])
  | r_P :: _ => None
  | [] => None
  | r_xs xs' :: t => stride (xs + N.pos xs') n t
  | r_D :: t =>
    match stride 0 n t with
    | Some t => Some (rxs xs (r_D :: t))
    | None => None
    end
  | r_C :: t =>
    if (N.pos n <=? xs)%N then
      match stride 0 n~0~0 t with
      | Some t => Some (rxs (xs - N.pos n) (r_C :: rxs (N.pos n~0) t))
      | None => None
      end
    else
      None
  | r_Gs gs :: t =>
    match stride 0 n t with
    | Some t => Some (rxs xs (Grs (N.pos gs) t))
    | None => None
    end
  end.

Lemma stride_rxs : forall t xs xs' n,
  stride xs n (rxs xs' t) = stride (xs + xs') n t.
Proof.
  introv.
  destruct xs'.
  - rewrite N.add_0_r. reflexivity.
  - destruct t as [| [] t]; try reflexivity.
    simpl. f_equal. lia.
Qed.

Lemma rxs_rxs : forall n m t,
  rxs n (rxs m t) = rxs (n + m) t.
Proof.
  introv.
  destruct n, m; try reflexivity.
  destruct t as [| [] t]; try reflexivity.
  unfold rxs. simpl.
  repeat (lia || f_equal).
Qed.

Lemma Fls_Fls : forall n m t,
  Fls n (Fls m t) = Fls (n + m) t.
Proof.
  introv.
  destruct n, m; try reflexivity.
  destruct t as [| [] t]; try reflexivity.
  unfold Fls. simpl.
  repeat (lia || f_equal).
Qed.

Lemma Grs_Grs : forall n m t,
  Grs n (Grs m t) = Grs (n + m) t.
Proof.
  introv.
  destruct n, m; try reflexivity.
  destruct t as [| [] t]; try reflexivity.
  unfold Grs. simpl.
  repeat (lia || f_equal).
Qed.

(** A "tail recursive" implementation of [stride] that hopefully, perhaps,
    possibly, might be better performance-wise when evaluating within Coq.
    Actual tail recursion would be a huge pain with smart constructors like
    [rxs], so let's try explicit continuations first. *)
Fixpoint stride' (xs : N) (n :positive) (t : rtape)
    (k : rtape -> rtape) : option rtape :=
  match t with
  | [r_P] => Some (k (rxs xs [r_P]))
  | r_P :: _ => None
  | [] => None
  | r_xs xs' :: t => stride' (xs + N.pos xs') n t k
  | r_D :: t => stride' 0 n t (fun t => k (rxs xs (r_D :: t)))
  | r_C :: t =>
    if (N.pos n <=? xs)%N then
      stride' 0 n~0~0 t (fun t => k (rxs (xs - N.pos n)
        (r_C :: rxs (N.pos n~0) t)))
    else
      None
  | r_Gs gs :: t =>
    stride' 0 n t (fun t => k (rxs xs (Grs (N.pos gs) t)))
  end.

Lemma stride'_spec : forall t xs n k,
  stride' xs n t k = option_map k (stride xs n t).
Proof.
  induction t as [| [xs | | | | gs] t IH]; introv.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH.
    destruct (stride 0 n t); reflexivity.
  - simpl.
    destruct (N.pos n <=? xs)%N; try reflexivity.
    rewrite IH. simpl.
    destruct (stride 0 n~0~0 t); reflexivity.
  - destruct t; reflexivity.
  - simpl. rewrite IH.
    destruct (stride 0 n t); reflexivity.
Qed.

Lemma stride_more : forall t t' xs xs' n,
  stride xs' n t = Some t' ->
  stride (xs + xs') n t = Some (rxs xs t').
Proof.
  induction t as [| [xs'' | | | | gs] t IH]; introv H; simpl; simpl in H.
  - (* [] *) discriminate.
  (* simpl. rewrite rxs_rxs. reflexivity. *)
  - (* r_xs xs'' :: t *)
    simpl in H.
    eapply IH in H.
    rewrite <- N.add_assoc.
    apply H.
  - (* r_D :: t *)
    simpl in H.
    destruct (stride 0 n t) as [t1 |] eqn:E; inverts H.
    rewrite rxs_rxs. reflexivity.
  - (* r_C :: t *)
    destruct (N.leb_spec (N.pos n) xs') as [Hle |]; try discriminate.
    destruct (N.leb_spec (N.pos n) (xs + xs')) as [Hle' |]; try lia.
    destruct (stride 0 n~0~0 t) as [t1 |] eqn:E; inverts H.
    rewrite rxs_rxs.
    repeat (lia || f_equal).
  - (* r_P :: t *)
    destruct t; inverts H.
    rewrite rxs_rxs. reflexivity.
  - (* r_Gs gs :: t *)
    simpl in H.
    destruct (stride 0 n t) as [t1 |] eqn:E; inverts H.
    rewrite rxs_rxs. reflexivity.
Qed.

Lemma stride_Grs : forall t t' xs gs n,
  stride 0 n t = Some t' ->
  stride xs n (Grs gs t) = Some (rxs xs (Grs gs t')).
Proof.
  introv H.
  destruct gs.
  - eapply stride_more in H. rewrite N.add_0_r in H. exact H.
  - destruct t as [| [] t]; try discriminate;
    try (unfold Grs at 1; simpl; simpl in H; rewrite H; reflexivity).
    simpl. simpl in H. unfold rxs in H.
    destruct (stride 0 n t) as [t1|]; inverts H.
    rewrite Grs_Grs.
    repeat (lia || f_equal).
Qed.

Lemma stride_add : forall t t2 xs n m,
  stride xs (n + m) t = Some t2 ->
  exists t1, stride xs n t = Some t1 /\ stride 0 m t1 = Some t2.
Proof.
  induction t as [| [xs' | | | | gs] t IH]; introv H.
  - (* [] *) discriminate.
  - (* r_xs xs' :: t *)
    simpl in H.
    apply IH in H. destruct H as [t1 [H1 H2]].
    exists t1. intuition.
  - (* r_D :: t *)
    simpl in H.
    destruct (stride 0 (n + m) t) as [t2' |] eqn:E; inverts H.
    apply IH in E. destruct E as [t1 [H1 H2]].
    exists (rxs xs (r_D :: t1)).
    simpl. rewrite H1.
    repeat split.
    rewrite stride_rxs. simpl.
    rewrite H2. reflexivity.
  - (* r_C :: t *)
    simpl in H. simpl.
    destruct (N.leb_spec (N.pos (n + m)) xs) as [Hle |]; try discriminate.
    destruct (stride 0 (n + m)~0~0 t) as [t2' |] eqn:E; inverts H.
    destruct (N.leb_spec (N.pos n) xs) as [Hle' |]; try lia.
    replace (n + m)~0~0%positive with (n~0~0 + m~0~0)%positive in E by lia.
    apply IH in E. destruct E as [t1 [H1 H2]].
    rewrite H1.
    eexists. repeat split.
    rewrite stride_rxs. simpl.
    destruct (N.leb_spec (N.pos m) (xs - N.pos n)) as [Hle'' |]; try lia.
    rewrite stride_rxs. simpl.
    eapply stride_more in H2.
    rewrite N.add_0_r in H2. rewrite H2.
    rewrite rxs_rxs.
    repeat (lia || f_equal).
  - (* r_P :: t *)
    simpl in H.
    destruct t; inverts H.
    eexists. repeat split.
    rewrite stride_rxs. reflexivity.
  - (* r_Gs gs :: t *)
    simpl in H.
    destruct (stride 0 (n + m) t) as [t2' |] eqn:E; inverts H.
    apply IH in E. destruct E as [t1 [H1 H2]].
    exists (rxs xs (Grs (N.pos gs) t1)).
    simpl. rewrite H1.
    repeat split.
    rewrite stride_rxs.
    eapply stride_Grs in H2. rewrite H2.
    reflexivity.
Qed.

Fixpoint stride_level (t : rtape) : nat :=
  match t with
  | [] => 0
  | r_C :: t => S (stride_level t)
  | _ :: t => stride_level t
  end.

Lemma stride_level_rxs : forall xs t,
  stride_level (rxs xs t) = stride_level t.
Proof.
  introv. destruct xs; try reflexivity.
  destruct t as [| [] t]; reflexivity.
Qed.

Lemma stride_level_Grs : forall xs t,
  stride_level (Grs xs t) = stride_level t.
Proof.
  introv. destruct xs; try reflexivity.
  destruct t as [| [] t]; reflexivity.
Qed.

Lemma stride_same_level : forall t t' xs n,
  stride xs n t = Some t' ->
  stride_level t = stride_level t'. 
Proof.
  induction t as [| [] t IH]; introv H.
  - (* [] *) discriminate.
  - (* r_xs n :: t *)
    eapply IH, H.
  - (* r_D :: t *)
    simpl in H.
    destruct (stride 0 n t) as [t1 |] eqn:E; inverts H.
    rewrite stride_level_rxs. simpl.
    eapply IH, E.
  - (* r_C :: t *)
    simpl in H.
    destruct (N.leb_spec (N.pos n) xs) as [Hle |]; try discriminate.
    destruct (stride 0 n~0~0 t) as [t1 |] eqn:E; inverts H.
    repeat (rewrite stride_level_rxs; simpl).
    f_equal.
    eapply IH, E.
  - (* r_P :: t *)
    simpl in H.
    destruct t; inverts H.
    rewrite stride_level_rxs.
    reflexivity.
  - (* r_Gs n :: t *)
    simpl in H.
    destruct (stride 0 n0 t) as [t1 |] eqn:E; inverts H.
    simpl.
    rewrite stride_level_rxs, stride_level_Grs.
    eapply IH, E.
Qed.

Theorem stride_correct' : forall k t t' xs l,
  stride_level t = k ->
  stride xs 1 t = Some t' ->
  l <: repeat (N.to_nat xs) x |> lift_right t -->* l <| lift_right t'.
Proof.
  (* We do induction on k, and then on t. This duplicates most of the cases,
     so we hoist them here manually. *)
  assert (case_xs : forall t t' xs xs' l,
    (forall t' xs l, stride xs 1 t = Some t' ->
      l <: repeat (N.to_nat xs) x |> lift_right t -->* l <| lift_right t') ->
    stride xs 1 (r_xs xs' :: t) = Some t' ->
    l <: repeat (N.to_nat xs) x |> lift_right (r_xs xs' :: t)
      -->* l <| lift_right t').
  { introv IH H.
    simpl in H. eapply IH in H.
    simpl. follow rule_xn_right.
    rewrite <- repeat_add.
    follow H. finish. }

  assert (case_D : forall t t' xs l,
    (forall t' xs l, stride xs 1 t = Some t' ->
      l <: repeat (N.to_nat xs) x |> lift_right t -->* l <| lift_right t') ->
    stride xs 1 (r_D :: t) = Some t' ->
    l <: repeat (N.to_nat xs) x |> lift_right (r_D :: t)
      -->* l <| lift_right t').
  { introv IH H.
    simpl in H.
    destruct (stride 0 1 t) as [t1 |] eqn:E; inverts H.
    eapply IH in E.
    simpl lift_right. follow rule_D_right.
    simpl repeat in E. follow E.
    follow rule_D_left.
    follow rule_xn_left.
    simp. finish. }

  assert (case_Gs : forall t t' gs xs l,
    (forall t' xs l, stride xs 1 t = Some t' ->
      l <: repeat (N.to_nat xs) x |> lift_right t -->* l <| lift_right t') ->
    stride xs 1 (r_Gs gs :: t) = Some t' ->
    l <: repeat (N.to_nat xs) x |> lift_right (r_Gs gs :: t)
      -->* l <| lift_right t').
  { introv IH H.
    simpl in H.
    destruct (stride 0 1 t) as [t1 |] eqn:E; inverts H.
    eapply IH in E.
    simpl lift_right. follow rule_Gn_right.
    simpl repeat in E. follow E.
    follow rule_Gn_left.
    follow rule_xn_left.
    simp. finish. }

  assert (case_P : forall t t' xs l,
    stride xs 1 (r_P :: t) = Some t' ->
    l <: repeat (N.to_nat xs) x |> lift_right (r_P :: t)
      -->* l <| lift_right t').
  { introv H. destruct t; inverts H.
    follow rule_P_R. follow rule_xn_left.
    simp. finish. }

  induction k; induction t as [| [xs' | | | | gs] t IHt]; introv Hlevel H;
    try discriminate;
    try (apply case_xs; intuition);
    try (apply case_D; intuition);
    try (apply case_P; intuition);
    try (apply case_Gs; intuition);
    clear case_xs case_D case_P case_Gs.

  (* r_C :: t *)
  clear IHt. inverts Hlevel.
  simpl in H.
  destruct (N.leb_spec 1 xs) as [Hle |]; try discriminate.
  destruct (stride 0 4 t) as [tfin |] eqn:E; inverts H.
  destruct (N.to_nat xs) as [| u] eqn:Eu; try lia.
  simpl repeat. simpl lift_right.
  follow rule_C30.
  
  change 4%positive with (1 + 3)%positive in E. apply stride_add in E.
  destruct E as [t1 [H1 E]].
  pose proof H1 as Hlevel1. apply stride_same_level in Hlevel1.
  eapply IHk in H1; try reflexivity.
  simpl in H1. follow H1. clear H1.
  follow rule_C01.

  change 3%positive with (1 + 2)%positive in E. apply stride_add in E.
  destruct E as [t2 [H1 E]].
  pose proof H1 as Hlevel2. apply stride_same_level in Hlevel2.
  eapply IHk in H1; try congruence.
  simpl in H1. follow H1. clear H1.
  follow rule_x_left. follow rule_C12. follow rule_x_right.

  change 2%positive with (1 + 1)%positive in E. apply stride_add in E.
  destruct E as [t3 [H1 E]].
  pose proof H1 as Hlevel3. apply stride_same_level in Hlevel3.
  eapply IHk in H1; try congruence.
  simpl in H1. follow H1. clear H1.
  follow rule_x_left. follow rule_C23. follow rule_x_right.

  eapply IHk in E; try congruence.
  simpl in E. follow E. clear E.

  repeat follow rule_x_left.
  follow rule_C_left.
  follow rule_xn_left.
  repeat simp.
  finish.
Qed.

Corollary stride_correct : forall t t' xs l,
  stride xs 1 t = Some t' ->
  l <: repeat (N.to_nat xs) x |> lift_right t -->* l <| lift_right t'.
Proof.
  introv. eapply stride_correct'; intuition.
Qed.

Corollary stride_correct_0 : forall t t' l,
  stride 0 1 t = Some t' ->
  l |> lift_right t -->* l <| lift_right t'.
Proof.
  introv H. eapply stride_correct in H. apply H.
Qed.

Definition try_stride (c : conf) : option conf :=
  match c with
  | (left, l, r) => None
  | (right, l, r) =>
    match stride 0 1 r with
    | Some r => Some (left, l, r)
    | None => None
    end
  end.

Definition step (c : conf) : option conf :=
  match try_stride c with
  | Some c' => Some c'
  | None => simple_step c
  end.

Lemma try_stride_spec : forall c c',
  try_stride c = Some c' ->
  lift c -->* lift c'.
Proof.
  introv H.
  destruct c as [[[] l] r]; try discriminate.
  simpl in H.
  destruct (stride 0 1 r) as [r' |] eqn:E; inverts H.
  apply stride_correct_0, E.
Qed.

Lemma step_spec : forall c c',
  step c = Some c' ->
  lift c -->* lift c'.
Proof.
  introv H.
  unfold step in H.
  destruct (try_stride c) as [c0 |] eqn:E.
  - inverts H. apply try_stride_spec, E.
  - apply simple_step_spec, H.
Qed.

Arguments lxs _ _ /.
Arguments rxs _ _ /.

Lemma prepare_apply_stride : forall n1 n2 xs {n} {t} {t'},
  stride 0 n t = Some t' ->
  (n1 + n2 = n)%positive ->
  exists t1, (forall k, stride' xs n1 t k = Some (k (rxs xs t1)))
    /\ stride 0 n2 t1 = Some t'.
Proof.
  introv H En. subst n.
  apply stride_add in H.
  destruct H as [t1 [H1 H2]].
  eapply stride_more in H1.
  rewrite N.add_0_r in H1.
  exists t1. intuition.
  rewrite stride'_spec, H1.
  reflexivity.
Qed.

Lemma use_stride' : forall t t' l,
  stride' 0 1 t id = Some t' ->
  lift (right, l, t) -->* lift (left, l, t').
Proof.
  introv H.
  rewrite stride'_spec in H.
  destruct (stride 0 1 t) as [t1 |] eqn:E; inverts H.
  eapply stride_correct in E.
  apply E.
Qed.

Lemma decr_rearrange : forall xs k,
  k <> 1%positive ->
  N.pos (xs :+ Pos.pred k) = decr (xs :+ k).
Proof.
  introv H.
  destruct xs; unfold decr; lia.
Qed.

Lemma le_het_add : forall a b c,
  (a <=? N.pos c)%N = true ->
  true = (a <=? N.pos (b :+ c))%N.
Proof. lia. Qed.

Lemma het_add_sub : forall b c d,
  (d <? c)%positive = true ->
  N.pos (b :+ (c - d)) = (0 + N.pos (b :+ c) - N.pos d)%N.
Proof. lia. Qed.

Ltac apply_stride_at H N R R' l r r' Hr :=
  lazymatch r' with
  | if ?cond then ?THEN else _ =>
    let cond' := eval cbn in cond in
    lazymatch cond' with
    | (?a <=? N.pos (?b :+ ?c))%N =>
      replace cond with true in Hr
        by exact (le_het_add a b c eq_refl);
      let then' := eval hnf in THEN in
      change (stride' 0 1 r id = then') in Hr;
      apply_stride_at H N R R' l r then' Hr
    end
  | context G [ (0 + N.pos (?b :+ ?c) - ?d)%N ] =>
    lazymatch d with
    | Npos ?d' =>
      let a := eval vm_compute in (c - d')%positive in
      replace (0 + N.pos (b :+ c) - d)%N
        with (N.pos (b :+ a)) in Hr
        by exact (het_add_sub b c d' eq_refl);
      let r' := context G [ N.pos (b :+ a) ] in
      apply_stride_at H N R R' l r r' Hr
    end
  | stride' ?xs ?n R ?k =>
    let N' := eval vm_compute in (N - n)%positive in
    destruct (prepare_apply_stride n N' xs H eq_refl) as [t1 [H1 H2]];
    clear H; rename H2 into H;
    let rfin := eval cbn in (k t1) in
    assert (H2 : stride' 0 1 r id = Some rfin)
      by (transitivity r'; [exact Hr | exact (H1 k)]);
      clear H1;
    unfold id in H2;
    eapply evstep_trans; [apply use_stride', H2 |];
    clear Hr;
    clear H2; clear R; rename t1 into R
  end.

Ltac apply_stride :=
  lazymatch goal with
  | H: stride 0 ?N ?R = Some ?R' |- lift (right, ?l, ?r) -->* _ =>
    let r' := eval hnf in (stride' 0 1 r id) in
    let Hr := fresh in
    assert (Hr : stride' 0 1 r id = r') by reflexivity;
    apply_stride_at H N R R' l r r' Hr
  end.

Ltac apply_simple :=
  lazymatch goal with
  | |- lift ?c -->* _ =>
    let c' := eval hnf in (simple_step c) in
    lazymatch c' with
    | Some ?c' =>
      assert (H0: simple_step c = Some c') by reflexivity;
      lazymatch c' with
      | context [decr (?a :+ ?b)] =>
        let b' := eval vm_compute in (Pos.pred b) in
        replace (decr (a :+ b)) with (N.pos (a :+ Pos.pred b)) in H0
          by (apply decr_rearrange; discriminate);
        change (Pos.pred b) with b' in H0
      | _ => idtac
      end;
      let c'' := eval cbn in c' in
      change c' with c'' in H0;
      apply simple_step_spec in H0;
      follow H0; clear H0
    end
  end.

(** Avoid running [reflexivity] on [lift c = lift c'] directly, as that will
    unfold all the compression. *)
Ltac maybe_finish :=
  lazymatch goal with
  | |- lift ?c -->* lift ?c' =>
    replace c with c' by reflexivity;
    apply evstep_refl
  end.

Ltac apply_step := apply_stride || apply_simple.

Theorem uni_cycle : forall l r r' xs,
  stride 0 uni_T r = Some r' ->
  lift (right, l_D :: l_C1 :: l_xs (xs :+ (uni_P + 1)) :: J ++ l, r) -->*
    lift (right, l_D :: l_C1 :: l_xs (xs :+ 1) :: J ++ F ++ l, G ++ r').
Proof.
  unfold uni_T, uni_P.
  introv H.
  Time repeat apply_step.
  assert (H': forall l, lift (right, l, r) -->* lift (left, l, r')).
  { introv. eapply stride_correct in H. apply H. }
  follow H'. clear H H'.
  repeat (maybe_finish || apply_simple).
Time Qed.

Lemma lift_eq : forall d l l' r r',
  lift_left l = lift_left l' ->
  lift_right r = lift_right r' ->
  lift (d, l, r) = lift (d, l', r').
Proof.
  introv H1 H2. unfold lift. rewrite H1, H2. reflexivity.
Qed.

Lemma lift_left_cons : forall a xs ys,
  lift_left xs = lift_left ys ->
  lift_left (a :: xs) = lift_left (a :: ys).
Proof. introv H. simpl. rewrite H. reflexivity. Qed.

Corollary uni_cycle' : forall l r r' xs,
  stride 0 uni_T r = Some r' ->
  lift (right, l_D :: l_C1 :: l_xs (xs :+ (uni_P + 1)) :: J ++ l, r) -->*
    lift (right, l_D :: l_C1 :: l_xs (xs :+ 1) :: J ++ Fls 1 l, Grs 1 r').
Proof.
  introv H.
  follow uni_cycle.
  finish.
  apply lift_eq.
  - repeat apply lift_left_cons.
    rewrite lift_Fls. reflexivity.
  - rewrite lift_Grs. reflexivity.
Qed.

Opaque J.

Corollary uni_cycles : forall n xs l r r',
  stride 0 (n * uni_T) r = Some r' ->
  lift (right, l_D :: l_C1 :: l_xs (xs :+ (n * uni_P + 1)) :: J ++ l, r) -->*
    lift (right, l_D :: l_C1 :: l_xs (xs :+ 1) :: J ++ Fls (N.pos n) l,
      Grs (N.pos n) r').
Proof.
  induction n using Pos.peano_ind; introv H.
  - apply uni_cycle', H.
  - replace (xs :+ (Pos.succ n * uni_P + 1))
      with ((xs + N.pos uni_P) :+ (n * uni_P + 1))
      by lia.
    replace (Pos.succ n * uni_T)%positive
      with (n * uni_T + uni_T)%positive in H by lia.
    apply stride_add in H. destruct H as [t1 [H1 H2]].
    follow IHn. clear H1.
    replace ((xs + N.pos uni_P) :+ 1)
      with (xs :+ (uni_P + 1))
      by lia.
    follow uni_cycle'. { apply stride_Grs. eassumption. }
    unfold rxs. rewrite Grs_Grs.
    rewrite Fls_Fls.
    finish.
Qed.

Definition uni_cycle_count (xs : positive) (r : rtape) : N :=
  let xs_limit := (N.pred (N.pos xs) / N.pos uni_P)%N in
  match xs_limit with
  | N0 => 0
  | Npos _ =>
    match max_stride 0 r with
    | Some strides => N.min xs_limit (strides / N.pos uni_T)%N
    | None => xs_limit
    end
  end.

Lemma uni_cycle_count_spec : forall xs r,
  (uni_cycle_count xs r * N.pos uni_P < N.pos xs)%N.
Proof.
  introv. unfold uni_cycle_count.
  destruct (N.pred (N.pos xs) / N.pos uni_P)%N eqn:E; try lia.
  enough (N.pos p * N.pos uni_P < N.pos xs)%N.
  { destruct (max_stride 0 r); nia. }
  pose proof (N.mul_div_le (N.pred (N.pos xs)) (N.pos uni_P)).
  nia.
Qed.

Definition try_uni_cycle (c : conf) : option conf :=
  match c with
  | (right, l_D :: l_C1 :: l_xs xs :: l, r) =>
    match strip_prefix eqb_l J l with
    | [|| l ||] =>
      match uni_cycle_count xs r with
      | N0 => None
      | Npos n =>
        match stride 0 (n * uni_T) r with
        | Some r' =>
          Some (right, l_D :: l_C1 :: l_xs (xs - n * uni_P) ::
            J ++ Fls (N.pos n) l, Grs (N.pos n) r')
        | None => None
        end
      end
    | !! => None
    end
  | _ => None
  end.

Lemma try_uni_cycle_spec : forall c c',
  try_uni_cycle c = Some c' ->
  lift c -->* lift c'.
Proof.
  introv H.
  destruct c as [[[] l] r]; simpl in H; try discriminate.
  destruct l as [| [] l]; try discriminate.
  destruct l as [| [] l]; try discriminate.
  destruct l as [| [] l]; try discriminate. rename n into xs.
  destruct (strip_prefix eqb_l J l) as [[l' El'] |]; try discriminate.
  subst l. rename l' into l.
  destruct (uni_cycle_count xs r) as [| n] eqn:Ecount; try discriminate.
  destruct (stride 0 (n * uni_T) r) as [r' |] eqn:Estride; inverts H.

  assert (H: (N.pos n * N.pos uni_P < N.pos xs)%N).
  { rewrite <- Ecount. apply uni_cycle_count_spec. }
  pose (N.pred (N.pos xs - N.pos (n * uni_P))) as u.
  follow (uni_cycles n u l r r'). finish.
Qed.

Definition fullstep (c : conf) : option conf :=
  match try_uni_cycle c with
  | Some c' => Some c'
  | None => step c
  end.

Lemma fullstep_spec : forall c c',
  fullstep c = Some c' ->
  lift c -->* lift c'.
Proof.
  introv H. unfold fullstep in H.
  destruct (try_uni_cycle c) as [c1 |] eqn:E.
  - inverts H. apply try_uni_cycle_spec, E.
  - apply step_spec, H.
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
    match fullstep c with
    | Some c' => steps n c'
    | None => None
    end
  end.

Lemma steps_spec : forall n c c',
  steps n c = Some c' ->
  lift c -->* lift c'.
Proof.
  induction n; introv H.
  - inverts H. finish.
  - simpl in H.
    destruct (fullstep c) as [c1 |] eqn:E; try discriminate.
    apply fullstep_spec in E. follow E.
    apply IHn, H.
Qed.

Lemma infinite_cycle : forall l,
  lift (right, l_C0 :: l, K) -->+ lift (right, l_C0 :: F ++ l, K).
Proof.
  introv.
  eapply progress_evstep_trans.
  - apply evstep_progress.
    + (* use a point where the head is pointing the other way for
         a maximally easy proof of distinctness. not that it matters
         in the end *)
      apply (steps_spec 30).
      reflexivity.
    + discriminate.
  - apply (steps_spec 952).
    reflexivity.
Qed.

Lemma cycle_nonhalt : forall l,
  ~ halts tm (lift (right, l_C0 :: l, K)).
Proof.
  introv.
  apply progress_nonhalt with
    (P := fun c => exists l, c = lift (right, l_C0 :: l, K)).
  - introv H. destruct H as [l1 H]. subst c.
    repeat eexists. apply infinite_cycle.
  - eauto.
Qed.

Local Hint Immediate cycle_nonhalt : core.

Obligation Tactic := intros; subst; auto; discriminate.
    
Program Definition is_cycling (c : conf) : {~ halts tm (lift c)} + {True} :=
  match c with
  | (right, l_C0 :: l, r) =>
    Reduce (eqb_rtape K r)
  | _ => No
  end.

From Coq Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.

Extraction "skelet1.ml" int_of_pos initial fullstep is_cycling.
