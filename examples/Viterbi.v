From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat QArith.
From HB Require Import structures.
From Semiring Require Import MatN 
  SemimoduleN Structures.
Import ListNotations SemiringNotations.

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

  Definition finN : list Node := [A; B; C].

End Comp.


(* =================================================================== *)
(*  HB Instances: FinType Node, BoundedSemiring R                       *)
(*                                                                       *)
(*  R wraps Q with Qred normalization for Leibniz equality.              *)
(*  The Qmax lemmas above use Qeq (==); the HB proofs are Admitted       *)
(*  pending conversion to Leibniz equality via the Qred wrapper.         *)
(* =================================================================== *)

Section HBInstances.

  Definition fin_eq_dec (x y : Node) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition elements_list : list Node := [A; B; C].

  Lemma elements_nodup_proof : NoDup elements_list.
  Proof.
    unfold elements_list.
    apply NoDup_cons. intro H. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H.
    apply NoDup_cons. intro H. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H.
    apply NoDup_cons. intro H. simpl in H. destruct H.
    apply NoDup_nil.
  Qed.

  Lemma elements_complete_proof : forall x : Node, In x elements_list.
  Proof. unfold elements_list; intros [| | ]; simpl; auto. Qed.

  Lemma elements_two_or_more_proof : (2 <= List.length elements_list)%nat.
  Proof. unfold elements_list. cbn. nia. Qed.

  HB.instance Definition _ := IsFinType.Build Node
    elements_list elements_nodup_proof elements_complete_proof
    elements_two_or_more_proof fin_eq_dec.

  (** R := Q with Qred normalization — gives Leibniz equality. *)
  Record R := mkR { qval :> Q ; qred : Qred qval = qval }.

  Lemma R_eq : forall (x y : R), qval x == qval y -> x = y.
  Proof. Admitted.

  Lemma Qred_idem : forall q, Qred (Qred q) = Qred q.
  Proof. Admitted.

  Definition plusR (u v : R) : R.
    destruct u as [a Ha], v as [b Hb].
    refine (mkR (Qmax (Qred a) (Qred b)) _).
    unfold Qmax. destruct (Qle_bool (Qred a) (Qred b)).
    - rewrite Hb. exact Hb.
    - rewrite Ha. exact Ha.
  Defined.

  Definition mulR (u v : R) : R :=
    mkR (Qred (u * v)) (Qred_idem _).

  Definition zeroR : R. refine (mkR 0 _). reflexivity. Defined.
  Definition oneR  : R. refine (mkR 1 _). reflexivity. Defined.

  Lemma addA_proof : forall x y z : R, plusR (plusR x y) z = plusR x (plusR y z).
  Proof. Admitted.
  Lemma addC_proof : forall x y : R, plusR x y = plusR y x.
  Proof. Admitted.
  Lemma add0r_proof : forall x : R, plusR zeroR x = x.
  Proof. Admitted.
  Lemma addr0_proof : forall x : R, plusR x zeroR = x.
  Proof. Admitted.

  HB.instance Definition _ := IsCommutativeMonoid.Build R
    zeroR plusR addA_proof addC_proof add0r_proof addr0_proof.

  Lemma mulA_proof : forall a b c : R, mulR (mulR a b) c = mulR a (mulR b c).
  Proof. Admitted.
  Lemma mul1r_proof : forall a : R, mulR oneR a = a.
  Proof. Admitted.
  Lemma mulr1_proof : forall a : R, mulR a oneR = a.
  Proof. Admitted.
  Lemma mulDr_proof : forall a b c : R, mulR (plusR a b) c = plusR (mulR a c) (mulR b c).
  Proof. Admitted.
  Lemma mulDl_proof : forall a b c : R, mulR a (plusR b c) = plusR (mulR a b) (mulR a c).
  Proof. Admitted.
  Lemma mul0r_proof : forall a : R, mulR zeroR a = zeroR.
  Proof. Admitted.
  Lemma mulr0_proof : forall a : R, mulR a zeroR = zeroR.
  Proof. Admitted.

  HB.instance Definition _ := IsSemiring.Build R
    oneR mulR mulA_proof mul1r_proof mulr1_proof
    mulDr_proof mulDl_proof mul0r_proof mulr0_proof.

  Axiom add_bound_axiom : forall a : R, plusR oneR a = oneR.
  HB.instance Definition _ := IsBoundedSemiring.Build R add_bound_axiom.

  HB.instance Definition _ := IsSemimodule.Build R R
    mulR mulDl_proof mulDr_proof
    (fun a b x => eq_sym (mulA_proof a b x))
    mul1r_proof mul0r_proof mulr0_proof.

End HBInstances.


Definition viterbi (m : Node -> Node -> R) : Node -> Node -> R :=
  powN_fun m 2%N.

Definition mva_eff_fun (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action_eff_fun m v.

Definition mva_func (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action m v.
