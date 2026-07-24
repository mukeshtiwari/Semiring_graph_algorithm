From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat QArith.
From Semiring Require Import Mat  Definitions
  Listprop.
Import ListNotations.

Local Open Scope Q_scope.

(* ========================================================================= *)
(*  VITERBI SEMIRING: (Q, max, *, 0, 1)  —  most reliable path               *)
(*                                                                           *)
(*  The Viterbi semiring computes the path with maximum probability in a     *)
(*  network where edge weights are probabilities (rationals in [0,1]).       *)
(*                                                                           *)
(*    + = Qmax   : the best (most probable) of two alternative paths          *)
(*    * = Qmult  : the combined probability of two sequential edges           *)
(*    0 = 0%Q    : additive identity, also multiplicative annihilator         *)
(*    1 = 1%Q    : multiplicative identity                                    *)
(*                                                                           *)
(*  IMPORTANT: All semiring laws involving zero as identity require the      *)
(*  values to be non-negative (0 <= x). This is natural for probabilities.   *)
(*  Lemmas that need this include it as an explicit hypothesis.              *)
(*                                                                           *)
(*  Qmax is not in Stdlib QArith — we define it locally with its lemmas.     *)
(* ========================================================================= *)

Section Comp.

  (* ----------------------------------------------------------------------- *)
  (* Qmax: rational maximum (not in Stdlib QArith)                            *)
  (* ----------------------------------------------------------------------- *)

  Definition Qmax (x y : Q) : Q := if Qle_bool x y then y else x.

  Lemma Qmax_comm : forall x y, Qmax x y == Qmax y x.
  Proof.
    intros x y. unfold Qmax.
    case_eq (Qle_bool x y); intros Hxy;
    case_eq (Qle_bool y x); intros Hyx; cbn.
    - apply Qle_bool_imp_le in Hxy, Hyx. apply Qle_antisym; assumption.
    - reflexivity.
    - reflexivity.
    - (* both false: impossible by totality of Qle *)
      destruct (Qlt_le_dec x y) as [Hlt | Hle].
      + apply Qlt_le_weak in Hlt. apply Qle_bool_iff in Hlt. rewrite Hlt in Hxy. discriminate.
      + apply Qle_bool_iff in Hle. rewrite Hle in Hyx. discriminate.
  Qed.


  Lemma Qmax_assoc : forall x y z, Qmax x (Qmax y z) == Qmax (Qmax x y) z.
  Proof.
    intros x y z. unfold Qmax.
    case_eq (Qle_bool x y); intros Hxy;
    case_eq (Qle_bool y z); intros Hyz;
    case_eq (Qle_bool x z); intros Hxz; cbn;
    rewrite ?Hxy, ?Hyz, ?Hxz; cbn; try apply Qeq_refl.
    - (* Case 2: x<=y, y<=z, x>z — impossible *)
      apply Qle_bool_imp_le in Hxy, Hyz.
      assert (Hxz' : x <= z) by (eapply Qle_trans; eassumption).
      apply Qle_bool_iff in Hxz'. rewrite Hxz' in Hxz. discriminate.
    - (* Case 7: x>y, y>z, x<=z — impossible *)
      apply Qle_bool_imp_le in Hxz.
      assert (z_lt_y : z < y).
      { apply Qnot_le_lt. intro Hle. apply Qle_bool_iff in Hle. rewrite Hle in Hyz. discriminate. }
      assert (y_lt_x : y < x).
      { apply Qnot_le_lt. intro Hle. apply Qle_bool_iff in Hle. rewrite Hle in Hxy. discriminate. }
      assert (z_lt_x : z < x) by (eapply Qlt_trans; eassumption).
      apply Qlt_not_le in z_lt_x. exfalso. apply z_lt_x. exact Hxz.
  Qed.


  Lemma Qmax_idem : forall x, Qmax x x == x.
  Proof.
    intros x. unfold Qmax. destruct (Qle_bool x x); reflexivity.
  Qed.

  Lemma Qmax_0_l : forall x, 0 <= x -> Qmax 0 x == x.
  Proof.
    intros x Hle. unfold Qmax.
    apply Qle_bool_iff in Hle. rewrite Hle. apply Qeq_refl.
  Qed.

  Lemma Qmax_0_r : forall x, 0 <= x -> Qmax x 0 == x.
  Proof.
    intros x Hle. unfold Qmax.
    case_eq (Qle_bool x 0); intros Hx0; cbn.
    - apply Qle_bool_imp_le in Hx0. apply Qle_antisym; assumption.
    - apply Qeq_refl.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* Qmult distributes over Qmax (for non-negative multiplier)                *)
  (* ----------------------------------------------------------------------- *)

  (* ----------------------------------------------------------------------- *)
  (* Qmult preserves <= on the left (derived from Qmult_le_compat_r + comm)   *)
  (* ----------------------------------------------------------------------- *)

  Lemma Qmult_le_compat_l : forall x y z, x <= y -> 0 <= z -> z * x <= z * y.
  Proof.
    intros. rewrite (Qmult_comm z x), (Qmult_comm z y). apply Qmult_le_compat_r; assumption.
  Qed.

  Lemma Qmult_Qmax_distr_l : forall a b c, 0 <= a ->
    a * Qmax b c == Qmax (a * b) (a * c).
  Proof.
    intros a b c Ha. unfold Qmax.
    case_eq (Qle_bool b c); intros Hbc; cbn;
    case_eq (Qle_bool (a*b) (a*c)); intros Hac; cbn; try apply Qeq_refl.
    - (* b<=c, Qle_bool(a*b)(a*c)=false: impossible *)
      apply Qle_bool_imp_le in Hbc.
      assert (Hle : a * b <= a * c) by (apply Qmult_le_compat_l; assumption).
      assert (Hfalse : ~ a * b <= a * c).
      { intro H. apply Qle_bool_iff in H. rewrite H in Hac. discriminate. }
      contradiction.
    - (* b>c, Qle_bool(a*b)(a*c)=true: a*b == a*c *)
      apply Qle_bool_imp_le in Hac.
      assert (Hle : a * c <= a * b).
      { apply Qmult_le_compat_l; [| exact Ha].
        apply Qlt_le_weak. apply Qnot_le_lt. intro H.
        apply Qle_bool_iff in H. rewrite H in Hbc. discriminate. }
      apply Qle_antisym; assumption.
  Qed.

  Lemma Qmult_Qmax_distr_r : forall a b c, 0 <= c ->
    (Qmax a b) * c == Qmax (a * c) (b * c).
  Proof.
    intros a b c Hc. unfold Qmax.
    case_eq (Qle_bool a b); intros Hab; cbn;
    case_eq (Qle_bool (a*c) (b*c)); intros Hac; cbn; try apply Qeq_refl.
    - (* a<=b, Qle_bool(a*c)(b*c)=false: impossible *)
      apply Qle_bool_imp_le in Hab.
      assert (Hle : a * c <= b * c) by (apply Qmult_le_compat_r; assumption).
      assert (Hfalse : ~ a * c <= b * c).
      { intro H. apply Qle_bool_iff in H. rewrite H in Hac. discriminate. }
      contradiction.
    - (* a>b, Qle_bool(a*c)(b*c)=true: a*c == b*c *)
      apply Qle_bool_imp_le in Hac.
      assert (Hle : b * c <= a * c).
      { apply Qmult_le_compat_r; [| exact Hc].
        apply Qlt_le_weak. apply Qnot_le_lt. intro H.
        apply Qle_bool_iff in H. rewrite H in Hab. discriminate. }
      apply Qle_antisym; assumption.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* Candidate nodes and semiring definitions                                 *)
  (* ----------------------------------------------------------------------- *)

  Inductive Node := A | B | C.

  Definition eqN (x y : Node) : bool :=
  match x, y with
  | A, A => true
  | B, B => true
  | C, C => true
  | _, _ => false
  end.

  (* Carrier: rational numbers Q (intended as probabilities in [0,1]).
     Proofs assume non-negativity (0 <= x) where needed. *)
  Definition R := Q.

  Definition eqR (u v : R) : bool := Qeq_bool u v.

  Definition plusR (u v : R) : R := Qmax u v.

  Definition mulR (u v : R) : R := Qmult u v.

  Definition zeroR : R := 0%Q.
  Definition oneR  : R := 1%Q.

  Definition finN : list Node := [A; B; C].

  Definition vit_solver (m : Path.Matrix Node R) : Path.Matrix Node R :=
   matrix_exp_binary_eff_fun Node eqN finN R zeroR oneR plusR mulR m 2%N.

End Comp.

Section Proofs.

  (* ----------------------------------------------------------------------- *)
  (* Node proofs                                                              *)
  (* ----------------------------------------------------------------------- *)

  Theorem refN : brel_reflexive Node eqN.
  Proof.
    unfold brel_reflexive; intros [| | ]; simpl; reflexivity.
  Qed.

  Theorem symN : brel_symmetric Node eqN.
  Proof.
    unfold brel_symmetric; intros [| | ] [| | ]; simpl;
    try reflexivity; try congruence.
  Qed.

  Theorem trnN : brel_transitive Node eqN.
  Proof.
    unfold brel_transitive; intros [| | ] [| | ] [| | ];
    simpl; intros Ha Hb; try firstorder.
  Qed.

  Theorem dunN : no_dup Node eqN finN = true.
  Proof. reflexivity. Qed.

  Theorem lenN : (2 <= List.length finN)%nat.
  Proof. cbn; nia. Qed.

  Theorem memN : forall x : Node, in_list eqN finN x = true.
  Proof. intros [| | ]; cbn; reflexivity. Qed.

  (* ----------------------------------------------------------------------- *)
  (* R (Q) equality proofs — unconditional                                    *)
  (* ----------------------------------------------------------------------- *)

  Theorem refR : brel_reflexive R eqR.
  Proof.
    unfold brel_reflexive, eqR. intro x. apply Qeq_bool_refl.
  Qed.

  Theorem symR : brel_symmetric R eqR.
  Proof.
    unfold brel_symmetric, eqR. intros x y H.
    apply Qeq_bool_eq in H. apply Qeq_bool_iff. rewrite H. apply Qeq_refl.
  Qed.

  Theorem trnR : brel_transitive R eqR.
  Proof.
    unfold brel_transitive, eqR. intros x y z H1 H2.
    apply Qeq_bool_eq in H1, H2.
    apply Qeq_bool_iff. rewrite H1, H2. reflexivity.
  Qed.

  Declare Scope Mat_scope.
  Delimit Scope Mat_scope with R.
  Bind Scope Mat_scope with R.
  Local Open Scope Mat_scope.

  Local Notation "0" := zeroR : Mat_scope.
  Local Notation "1" := oneR : Mat_scope.
  Local Infix "+" := plusR : Mat_scope.
  Local Infix "*" := mulR : Mat_scope.
  Local Infix "=r=" := eqR (at level 70) : Mat_scope.

  (* ----------------------------------------------------------------------- *)
  (* Semiring proofs                                                          *)
  (*   - Unconditional lemmas: +-assoc/comm/idem, *-assoc/comm, 1-identities, *)
  (*     0-annihilation, ring-based lemmas.                                   *)
  (*   - Conditional lemmas: 0-identities (need 0 <= x), distributivity       *)
  (*     (need non-negative multiplier).                                      *)
  (* ----------------------------------------------------------------------- *)

  Theorem zero_left_identity_plus  : forall r : R, 0 <= r -> 0 + r =r= r = true.
  Proof.
    unfold plusR, zeroR, eqR. intros r Hr. apply Qeq_bool_iff. apply Qmax_0_l. exact Hr.
  Qed.

  Theorem zero_right_identity_plus : forall r : R, 0 <= r -> r + 0 =r= r = true.
  Proof.
    unfold plusR, zeroR, eqR. intros r Hr. apply Qeq_bool_iff. apply Qmax_0_r. exact Hr.
  Qed.

  Theorem plus_associative : forall a b c : R, a + (b + c) =r= (a + b) + c = true.
  Proof.
    unfold plusR, eqR. intros a b c. apply Qeq_bool_iff. apply Qmax_assoc.
  Qed.

  Theorem plus_commutative  : forall a b : R, a + b =r= b + a = true.
  Proof.
    unfold plusR, eqR. intros a b. apply Qeq_bool_iff. apply Qmax_comm.
  Qed.

  Theorem one_left_identity_mul  : forall r : R, 1 * r =r= r = true.
  Proof.
    unfold mulR, oneR, eqR. intro r. apply Qeq_bool_iff. ring.
  Qed.

  Theorem one_right_identity_mul : forall r : R, r * 1 =r= r = true.
  Proof.
    unfold mulR, oneR, eqR. intro r. apply Qeq_bool_iff. ring.
  Qed.

  Theorem mul_associative : forall a b c : R, a * (b * c) =r= (a * b) * c = true.
  Proof.
    unfold mulR, eqR. intros a b c. apply Qeq_bool_iff. ring.
  Qed.

  Theorem mul_commutative : forall a b : R, a * b =r= b * a = true.
  Proof.
    unfold mulR, eqR. intros a b. apply Qeq_bool_iff. ring.
  Qed.

  Theorem left_distributive_mul_over_plus : forall a b c : R, 0 <= a ->
    a * (b + c) =r= a * b + a * c = true.
  Proof.
    unfold plusR, mulR, eqR. intros a b c Ha.
    apply Qeq_bool_iff. apply Qmult_Qmax_distr_l. exact Ha.
  Qed.

  Theorem right_distributive_mul_over_plus : forall a b c : R, 0 <= c ->
    (a + b) * c =r= a * c + b * c = true.
  Proof.
    unfold plusR, mulR, eqR. intros a b c Hc.
    apply Qeq_bool_iff. apply Qmult_Qmax_distr_r. exact Hc.
  Qed.

  Theorem zero_left_anhilator_mul : forall a : R, 0 * a =r= 0 = true.
  Proof.
    unfold mulR, zeroR, eqR. intro a. apply Qeq_bool_iff. ring.
  Qed.

  Theorem zero_right_anhilator_mul : forall a : R, a * 0 =r= 0 = true.
  Proof.
    unfold mulR, zeroR, eqR. intro a. apply Qeq_bool_iff. ring.
  Qed.

  (* NOTE: zero_stable (1 + a = 1) holds only for min-plus (where 1=0).
     For Viterbi, 1 + a = max(1,a) which equals a when a >= 1. *)

  Theorem plus_idempotence : forall a : R, a + a =r= a = true.
  Proof.
    unfold plusR, eqR. intro a. apply Qeq_bool_iff. apply Qmax_idem.
  Qed.

End Proofs.
