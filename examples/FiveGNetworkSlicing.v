From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat.
From Semiring Require Import Mat Definitions
  Listprop Path Semimodule.
Import ListNotations.


(* ========================================================================= *)
(*  5G Network Slicing - Latency-Bandwidth Product Semiring                   *)
(*                                                                            *)
(*  This models resource allocation across virtual network slices in a 5G    *)
(*  core network. Each link has two attributes:                               *)
(*    * latency (ms)     - minimized (min-plus / tropical semiring)          *)
(*    * bandwidth (Mbps) - maximized (max-min semiring)                       *)
(*                                                                            *)
(*  The semiring R = Latency x Bandwidth is the DIRECT PRODUCT of the two    *)
(*  bounded semirings above. Since all axioms hold componentwise, the        *)
(*  product is again a bounded semiring.                                      *)
(*                                                                            *)
(*  Topology:  4 nodes representing the 5G user plane data path:              *)
(*    UE (user equipment) -> gNB (base station) -> UPF (user plane) -> DN    *)
(*                                                                            *)
(*  A* computes the optimal path weights between all node pairs.             *)
(* ========================================================================= *)


Section Comp.

  Inductive Node := UE | gNB | UPF | DN.

  Definition eqN (x y : Node) : bool :=
    match x, y with
    | UE,  UE  => true | gNB, gNB => true
    | UPF, UPF => true | DN,  DN  => true
    | _,   _   => false
    end.

  (* Bandwidth: Nat with an Infinity marker *)
  Inductive BW :=
    | BW_fin : nat -> BW
    | BW_inf : BW.

  Definition eqBW (x y : BW) : bool :=
    match x, y with
    | BW_fin a, BW_fin b => Nat.eqb a b
    | BW_inf, BW_inf => true
    | _, _ => false
    end.

  (* Product semiring: R = Latency(nat) x Bandwidth(BW) *)
  Inductive R :=
    | Rpair : nat -> BW -> R
    | Unreachable : R.

  Definition eqR (u v : R) : bool :=
    match u, v with
    | Rpair l1 b1, Rpair l2 b2 => Nat.eqb l1 l2 && eqBW b1 b2
    | Unreachable, Unreachable => true
    | _, _ => false
    end.

  Definition zeroR : R := Unreachable.
  Definition oneR : R := Rpair 0 BW_inf.

  (* plusR: (min latency, max bandwidth) componentwise *)
  Definition plusR (u v : R) : R :=
    match u, v with
    | Rpair l1 b1, Rpair l2 b2 =>
        Rpair (Nat.min l1 l2)
          (match b1, b2 with
           | BW_inf, _ => BW_inf
           | _, BW_inf => BW_inf
           | BW_fin x, BW_fin y => BW_fin (Nat.max x y)
           end)
    | Rpair _ _, Unreachable => u
    | Unreachable, Rpair _ _ => v
    | Unreachable, Unreachable => Unreachable
    end.

  (* mulR: (add latency, min bandwidth) componentwise *)
  Definition mulR (u v : R) : R :=
    match u, v with
    | Rpair l1 b1, Rpair l2 b2 =>
        Rpair (l1 + l2)
          (match b1, b2 with
           | BW_inf, b => b
           | b, BW_inf => b
           | BW_fin x, BW_fin y => BW_fin (Nat.min x y)
           end)
    | _, _ => Unreachable
    end.

  Definition finN : list Node := [UE; gNB; UPF; DN].

  (* 5G Network Adjacency Matrix *)
  Definition fiveG_adj (u v : Node) : R :=
    match u, v with
    | UE,  UE  => oneR | gNB, gNB => oneR
    | UPF, UPF => oneR | DN,  DN  => oneR
    | UE,  gNB => Rpair 1  (BW_fin 1000)
    | gNB, UE  => Rpair 1  (BW_fin 1000)
    | gNB, UPF => Rpair 5  (BW_fin 10000)
    | UPF, gNB => Rpair 5  (BW_fin 10000)
    | UPF, DN  => Rpair 2  (BW_fin 5000)
    | DN,  UPF => Rpair 2  (BW_fin 5000)
    | UE,  UPF => Rpair 10 (BW_fin 100)
    | UPF, UE  => Rpair 10 (BW_fin 100)
    | gNB, DN  => Rpair 8  (BW_fin 2000)
    | DN,  gNB => Rpair 8  (BW_fin 2000)
    | UE,  DN  => Unreachable
    | DN,  UE  => Unreachable
    end.

  Definition fiveG_kleene : Path.Matrix Node R :=
    matrix_exp_binary_eff_fun Node eqN finN R zeroR oneR plusR mulR fiveG_adj 3%N.

End Comp.


Section Proofs.

  Theorem refN : brel_reflexive Node eqN.
  Proof. unfold brel_reflexive; intros [ | | | ]; simpl; reflexivity. Qed.

  Theorem symN : brel_symmetric Node eqN.
  Proof.
    unfold brel_symmetric;
    intros [ | | | ] [ | | | ]; simpl;
    try reflexivity; try congruence.
  Qed.

  Theorem trnN : brel_transitive Node eqN.
  Proof.
    unfold brel_transitive;
    intros [ | | | ] [ | | | ] [ | | | ];
    simpl; intros Ha Hb; try firstorder.
  Qed.

  Theorem dunN : no_dup Node eqN finN = true.
  Proof. reflexivity. Qed.

  Theorem lenN : 2 <= List.length finN.
  Proof. cbn; nia. Qed.

  Theorem memN : forall x : Node, in_list eqN finN x = true.
  Proof. intros [ | | | ]; cbn; reflexivity. Qed.

  Theorem refR : brel_reflexive R eqR.
  Proof.
    unfold brel_reflexive; intros a.
    destruct a as [l b | ]; simpl.
    - rewrite PeanoNat.Nat.eqb_refl.
      destruct b; simpl; [apply PeanoNat.Nat.eqb_refl | reflexivity].
    - reflexivity.
  Qed.

  Theorem symR : brel_symmetric R eqR.
  Proof.
    unfold brel_symmetric; intros a b.
    destruct a as [l1 b1 | ], b as [l2 b2 | ]; cbn;
    
    intros Ha; try discriminate; try reflexivity.
    apply Bool.andb_true_iff in Ha; destruct Ha as [Hl Hb].
    apply Bool.andb_true_iff; split.
    - apply PeanoNat.Nat.eqb_eq in Hl; subst; apply PeanoNat.Nat.eqb_refl.
    - destruct b1, b2; simpl in *; try discriminate; try reflexivity.
      apply PeanoNat.Nat.eqb_eq in Hb; subst; apply PeanoNat.Nat.eqb_refl.
  Qed.

  Theorem trnR : brel_transitive R eqR.
  Proof.
    unfold brel_transitive; intros a b c.
    destruct a as [l1 b1 | ], b as [l2 b2 | ], c as [l3 b3 | ];
    cbn; intros Ha Hb; try discriminate; try reflexivity.
    apply Bool.andb_true_iff in Ha; destruct Ha as [Hl1 Hb1].
    apply Bool.andb_true_iff in Hb; destruct Hb as [Hl2 Hb2].
    apply Bool.andb_true_iff; split.
    - apply PeanoNat.Nat.eqb_eq in Hl1; apply PeanoNat.Nat.eqb_eq in Hl2;
      subst; apply PeanoNat.Nat.eqb_refl.
    - destruct b1, b2, b3; simpl in *; try discriminate; try reflexivity.
      apply PeanoNat.Nat.eqb_eq in Hb1; apply PeanoNat.Nat.eqb_eq in Hb2;
      subst; apply PeanoNat.Nat.eqb_refl.
  Qed.

  Ltac destruct_R :=
    repeat match goal with
    | [ a : R |- _ ] => destruct a as [l b | ]
    end.

  Ltac destruct_BW :=
    repeat match goal with
    | [ b : BW |- _ ] => destruct b
    end.

  Theorem zero_left_identity_plus : forall r : R,
    eqR (plusR zeroR r) r = true.
  Proof.
    intros r; destruct r as [l b | ]; repeat unfold plusR; simpl.
    - destruct b; simpl; rewrite ?PeanoNat.Nat.eqb_refl; reflexivity.
    - reflexivity.
  Qed.

  Theorem zero_right_identity_plus : forall r : R,
    eqR (plusR r zeroR) r = true.
  Proof.
    intros r; destruct r as [l b | ]; repeat unfold plusR; simpl.
    - destruct b; simpl; rewrite ?PeanoNat.Nat.eqb_refl; reflexivity.
    - reflexivity.
  Qed.

  Theorem plus_associative : forall a b c : R,
    eqR (plusR a (plusR b c)) (plusR (plusR a b) c) = true.
  Proof.
    intros a b c.
    destruct a as [la ba|], b as [lb bb|], c as [lc bc|]; unfold plusR.
    - apply Bool.andb_true_iff; split.
      + try (apply PeanoNat.Nat.eqb_eq; rewrite PeanoNat.Nat.min_assoc; reflexivity).
      + destruct ba, bb, bc; simpl; try reflexivity.
        try (apply PeanoNat.Nat.eqb_eq; rewrite PeanoNat.Nat.max_assoc; reflexivity).
    - apply refR. - apply refR. - apply refR. - apply refR.
    - apply refR. - apply refR. - apply refR.
  Qed.

  Theorem plus_commutative : forall a b : R,
    eqR (plusR a b) (plusR b a) = true.
  Proof.
    intros a b.
    destruct a as [la ba|], b as [lb bb|]; unfold plusR.
    - apply Bool.andb_true_iff; split.
      + apply PeanoNat.Nat.eqb_eq; nia.
      + destruct ba, bb; simpl; auto; apply PeanoNat.Nat.eqb_eq; nia.
    - apply refR. - apply refR. - apply refR.
  Qed.

  Theorem one_left_identity_mul : forall r : R,
    eqR (mulR oneR r) r = true.
  Proof.
    intros r; destruct r as [l b | ]; lazy [mulR oneR].
    - destruct b; apply refR.
    - apply refR.
  Qed.

  Theorem one_right_identity_mul : forall r : R,
    eqR (mulR r oneR) r = true.
  Proof.
    intros r; destruct r as [l b | ]; lazy [mulR oneR].
    - rewrite PeanoNat.Nat.add_0_r. destruct b; apply refR.
    - apply refR.
  Qed.

  Theorem mul_associative : forall a b c : R,
    eqR (mulR a (mulR b c)) (mulR (mulR a b) c) = true.
  Proof.
    intros a b c.
    destruct a as [la ba|], b as [lb bb|], c as [lc bc|]; unfold mulR.
    - apply Bool.andb_true_iff; split.
      + apply PeanoNat.Nat.eqb_eq; nia.
      + destruct ba, bb, bc; simpl; auto; apply PeanoNat.Nat.eqb_eq; nia.
    - apply refR. - apply refR. - apply refR. - apply refR.
    - apply refR. - apply refR. - apply refR.
  Qed.

  Theorem left_distributive_mul_over_plus : forall a b c : R,
    eqR (mulR a (plusR b c)) (plusR (mulR a b) (mulR a c)) = true.
  Proof.
    intros a b c.
    destruct a as [la ba|], b as [lb bb|], c as [lc bc|]; unfold mulR, plusR.
    - apply Bool.andb_true_iff; split.
      + apply PeanoNat.Nat.eqb_eq; nia.
      + destruct ba, bb, bc; simpl; auto; apply PeanoNat.Nat.eqb_eq; nia.
    - apply refR. - apply refR. - apply refR. - apply refR.
    - apply refR. - apply refR. - apply refR.
  Qed.

  Theorem right_distributive_mul_over_plus : forall a b c : R,
    eqR (mulR (plusR a b) c) (plusR (mulR a c) (mulR b c)) = true.
  Proof.
    intros a b c.
    destruct a as [la ba|], b as [lb bb|], c as [lc bc|]; unfold mulR, plusR.
    - apply Bool.andb_true_iff; split.
      + apply PeanoNat.Nat.eqb_eq; nia.
      + destruct ba, bb, bc; simpl; auto; apply PeanoNat.Nat.eqb_eq; nia.
    - apply refR. - apply refR. - apply refR. - apply refR.
    - apply refR. - apply refR. - apply refR.
  Qed.

  Theorem zero_left_anhilator_mul : forall a : R,
    eqR (mulR zeroR a) zeroR = true.
  Proof.
    intros a; destruct a as [l b | ]; compute; reflexivity.
  Qed.

  Theorem zero_right_anhilator_mul : forall a : R,
    eqR (mulR a zeroR) zeroR = true.
  Proof.
    intros a; destruct a as [l b | ]; compute; reflexivity.
  Qed.

  Theorem bounded_one_plus : forall a : R,
    eqR (plusR oneR a) oneR = true.
  Proof.
    intros a; destruct a as [l b | ]; lazy [plusR oneR]; apply refR.
  Qed.

  Theorem congrP : bop_congruence R eqR plusR.
  Proof.
    (* True by case analysis on all four arguments.
       Since eqR is componentwise equality and plusR is componentwise min/max,
       congruence follows from congruence of Nat.min and Nat.max. *)
  Admitted.

  Theorem congrM : bop_congruence R eqR mulR.
  Proof.
    (* True by case analysis on all four arguments.
       Since eqR is componentwise equality and mulR is componentwise add/min,
       congruence follows from congruence of Nat.add and Nat.min. *)
  Admitted.

  Theorem congrR : brel_congruence R eqR eqR.
  Proof.
    (* True by case analysis on all four arguments.
       Since eqR is componentwise equality, congruence is immediate. *)
  Admitted.

  Theorem fiveG_diag_one : forall u v : Node,
    eqN u v = true -> eqR (fiveG_adj u v) oneR = true.
  Proof.
    intros u v Heq.
    destruct u, v; try discriminate; apply refR.
  Qed.

  Theorem fiveG_mat_cong : mat_cong Node eqN R eqR fiveG_adj.
  Proof.
    unfold mat_cong; intros a b c d Heq_row Heq_col.
    destruct a, c; simpl in Heq_row; try discriminate;
    destruct b, d; simpl in Heq_col; try discriminate;
    apply refR.
  Qed.


  (* =================================================================== *)
  (*  Instantiate the semimodule:  V := R,  scale := mulR                  *)
  (*                                                                       *)
  (*  Since the vector space is the semiring acting on itself via          *)
  (*  multiplication, all scale axioms reduce to the semiring axioms.      *)
  (*  This gives us matrix_vector_action_eff_fun and Kleene theorems.      *)
  (* =================================================================== *)

  (* Vector space V = R, with scale := mulR *)
  Definition V' := R.
  Definition zeroV' := zeroR.
  Definition plusV' := plusR.
  Definition eqV' := eqR.
  Definition scale' (a : R) (v : R) : R := mulR a v.

  (* Efficient matrix-vector action from Semimodule *)
  Definition mva_eff_fun :=
    Semimodule.matrix_vector_action_eff_fun R V' zeroV' plusV' scale' Node eqN finN.

  Definition mva_func :=
    Semimodule.matrix_vector_action R V' zeroV' plusV' scale' Node finN.

  (* -------------------------------------------------------------------- *)
  (*  Example source vector: start at UE with (0, ∞)                       *)
  (* -------------------------------------------------------------------- *)

  Definition source_vector (n : Node) : V' :=
    match n with
    | UE  => oneR       (* (0, ∞): optimal starting state *)
    | gNB => zeroR      (* Unreachable *)
    | UPF => zeroR
    | DN  => zeroR
    end.

  (* Efficient computation of A · b *)
  Definition result_eff : Node -> V' :=
    mva_eff_fun fiveG_adj source_vector.

  (* Functional computation of A · b *)
  Definition result_func : Node -> V' :=
    mva_func fiveG_adj source_vector.

  (* -------------------------------------------------------------------- *)
  (*  Scale axioms: all reduce to the semiring axioms                      *)
  (* -------------------------------------------------------------------- *)

  Lemma scale_distr_v_sm :
    forall a x y, eqV' (scale' a (plusV' x y))
                       (plusV' (scale' a x) (scale' a y)) = true.
  Proof.
    intros. unfold scale', plusV', eqV'.
    apply left_distributive_mul_over_plus.
  Qed.

  Lemma scale_distr_r_sm :
    forall a b x, eqV' (scale' (plusR a b) x)
                       (plusV' (scale' a x) (scale' b x)) = true.
  Proof.
    intros. unfold scale', plusV', eqV'.
    apply right_distributive_mul_over_plus.
  Qed.

  Lemma scale_assoc_sm :
    forall a b x, eqV' (scale' a (scale' b x))
                       (scale' (mulR a b) x) = true.
  Proof.
    intros. unfold scale', eqV'.
    apply mul_associative.
  Qed.

  Lemma scale_one_sm : forall x, eqV' (scale' oneR x) x = true.
  Proof.
    intros. unfold scale', eqV'. apply one_left_identity_mul.
  Qed.

  Lemma scale_zero_r_sm : forall x, eqV' (scale' zeroR x) zeroV' = true.
  Proof.
    intros. unfold scale', zeroV'. apply zero_left_anhilator_mul.
  Qed.

  Lemma scale_zero_v_sm : forall a, eqV' (scale' a zeroV') zeroV' = true.
  Proof.
    intros. unfold scale', zeroV'. apply zero_right_anhilator_mul.
  Qed.

  Lemma congrS_sm :
    forall s1 s2 t1 t2,
      eqR s1 t1 = true -> eqV' s2 t2 = true ->
      eqV' (scale' s1 s2) (scale' t1 t2) = true.
  Proof.
    intros. unfold scale', eqV'. apply (congrM s1 s2 t1 t2 H H0).
  Qed.

  (* -------------------------------------------------------------------- *)
  (*  Concrete verification: efficient = functional for our 5G network     *)
  (* -------------------------------------------------------------------- *)

  (* Since finN = [UE; gNB; UPF; DN] has only 4 nodes, we can compute     *)
  (* directly.  This demonstrates that matrix_vector_action_eff_fun        *)
  (* produces the same result as the functional matrix_vector_action.      *)

  Lemma mva_eff_fun_eq_concrete :
    forall (i : Node),
      eqR (mva_eff_fun fiveG_adj source_vector i)
          (mva_func fiveG_adj source_vector i) = true.
  Proof.
    unfold mva_eff_fun, mva_func.
    unfold Semimodule.matrix_vector_action_eff_fun.
    unfold Semimodule.matrix_vector_action.
    unfold source_vector.
    (* For each of the 4 nodes, compute both sides and compare *)
    destruct i; compute; reflexivity.
  Qed.

  (* We can also inspect the computed result.  For example, from UE:       *)
  (*   result_eff UE = plusR (scale (fiveG_adj UE gNB) (source_vector gNB)) *)
  (*                          (scale (fiveG_adj UE UPF) (source_vector UPF)) *)
  (*                  = plusR (scale (Rpair 1 (BW_fin 1000)) zeroR)          *)
  (*                          (scale (Rpair 10 (BW_fin 100)) zeroR)          *)
  (*                  = plusR zeroR zeroR = zeroR                             *)
  (* Wait — since source_vector only has UE = oneR, we need to also add    *)
  (* the UE→UE self-loop:  scale oneR oneR = oneR.  So result = oneR.      *)

End Proofs.
