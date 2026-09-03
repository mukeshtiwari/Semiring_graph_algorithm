From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat. 
From HB Require Import structures.
From Semiring Require Import MatN
  SemimoduleN Structures.
Import ListNotations SemiringNotations.


(** min_+ alegebra *)
Section Comp. 

  (** Define Candidates *)
  Inductive Node := A | B | C. 
  

   (** Nat extended with Infinity *)
  Inductive R := 
  | Left : nat -> R 
  | Infinity : R.

  Definition plusR (u v : R) : R :=
  match u, v with 
  | Left x, Left y => Left (Nat.min x y)
  | Left x, Infinity => Left x 
  | Infinity, Left x => Left x 
  | _, _ => Infinity  
  end. 


  Definition mulR (u v : R) : R :=
  match u, v with 
  | Left x, Left y => Left (Nat.add x y)
  | _, _ => Infinity 
  end.

  (** zeroR *)
  Definition zeroR : R := Infinity.

  (** oneR *)
  Definition oneR : R := Left 0.  

  Definition finN : list Node := [A; B; C].

End Comp.

(** * HB Instances: FinType Node, BoundedSemiring R (min-plus/tropical) *)

Section HBInstances.

  (** * Node as a Finite Type  (A | B | C) *)

  Definition fin_eq_dec (x y : Node) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition elements_list : list Node := [A; B; C].

  Lemma elements_nodup_proof : NoDup elements_list.
  Proof.
    unfold elements_list.
    apply NoDup_cons.
    intro H. simpl in H. destruct H as [Heq|H]; [inversion Heq|].
    simpl in H. destruct H as [Heq|H]; [inversion Heq|].
    simpl in H. destruct H.
    apply NoDup_cons.
    intro H. simpl in H. destruct H as [Heq|H]; [inversion Heq|].
    simpl in H. destruct H.
    apply NoDup_cons.
    intro H. simpl in H. destruct H.
    apply NoDup_nil.
  Qed.

  Lemma elements_complete_proof : forall x : Node, In x elements_list.
  Proof.
    unfold elements_list; intros [| | ]; simpl; auto.
  Qed.

  Lemma elements_two_or_more_proof : (2 <= List.length elements_list)%nat.
  Proof.
    unfold elements_list. cbn. nia.
  Qed.

  HB.instance Definition _ := IsFinType.Build Node
    elements_list
    elements_nodup_proof
    elements_complete_proof
    elements_two_or_more_proof
    fin_eq_dec.

  (** * R as a Commutative Monoid  (min–semilattice with Infinity) *)

  Lemma addA_proof : forall x y z : R, plusR (plusR x y) z = plusR x (plusR y z).
  Proof.
    intros [x|] [y|] [z|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.min_assoc. reflexivity.
  Qed.

  Lemma addC_proof : forall x y : R, plusR x y = plusR y x.
  Proof.
    intros [x|] [y|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.min_comm. reflexivity.
  Qed.

  Lemma add0r_proof : forall x : R, plusR zeroR x = x.
  Proof.
    intro x. destruct x as [n|]; cbv [zeroR plusR]; reflexivity.
  Qed.

  Lemma addr0_proof : forall x : R, plusR x zeroR = x.
  Proof.
    intro x. destruct x as [n|]; cbv [zeroR plusR]; reflexivity.
  Qed.

  HB.instance Definition _ := IsCommutativeMonoid.Build R
    zeroR plusR addA_proof addC_proof add0r_proof addr0_proof.

  (** * R as a Semiring  (addition distributes over min) *)

  Lemma mulA_proof : forall a b c : R, mulR (mulR a b) c = mulR a (mulR b c).
  Proof.
    intros [a|] [b|] [c|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.add_assoc. reflexivity.
  Qed.

  Lemma mul1r_proof : forall a : R, mulR oneR a = a.
  Proof.
    intros [a|]; cbn; try reflexivity.
  Qed.

  Lemma mulr1_proof : forall a : R, mulR a oneR = a.
  Proof.
    intros [a|]; cbn; try reflexivity.
    f_equal. lia.
  Qed.

  Lemma mulDr_proof : forall a b c : R,
    mulR (plusR a b) c = plusR (mulR a c) (mulR b c).
  Proof.
    intros [a|] [b|] [c|]; cbn; try reflexivity; f_equal; lia.
  Qed.

  Lemma mulDl_proof : forall a b c : R,
    mulR a (plusR b c) = plusR (mulR a b) (mulR a c).
  Proof.
    intros [a|] [b|] [c|]; cbn; try reflexivity; f_equal; lia.
  Qed.

  Lemma mul0r_proof : forall a : R, mulR zeroR a = zeroR.
  Proof.
    intros [a|]; cbn; reflexivity.
  Qed.

  Lemma mulr0_proof : forall a : R, mulR a zeroR = zeroR.
  Proof.
    intros [a|]; cbn; reflexivity.
  Qed.

  HB.instance Definition _ := IsSemiring.Build R
    oneR mulR mulA_proof mul1r_proof mulr1_proof
    mulDr_proof mulDl_proof mul0r_proof mulr0_proof.

  (** * R as a Bounded Semiring  (0 is the minimum, absorbing in min) *)

  Lemma add_bound_proof : forall a : R, plusR oneR a = oneR.
  Proof.
    intros [a|]; cbv [plusR oneR]; try reflexivity.
  Qed.

  HB.instance Definition _ := IsBoundedSemiring.Build R add_bound_proof.

  (** * R as a Semimodule over itself  (scale := mulR = addition) *)

  HB.instance Definition _ := IsSemimodule.Build R R
    mulR
    mulDl_proof   (* scale a (x + y) = scale a x + scale a y *)
    mulDr_proof   (* scale (a + b) x = scale a x + scale b x *)
    (fun a b x => eq_sym (mulA_proof a b x))  (* scale a (scale b x) = scale (a * b) x *)
    mul1r_proof   (* scale 1 x = x *)
    mul0r_proof   (* scale 0 x = 0 *)
    mulr0_proof.  (* scale a 0 = 0 *)

End HBInstances.

(** Shortest-path computation: [m²] in the min-plus semiring.
    Raising the adjacency matrix to the second power yields the
    shortest path of up to two hops between all node pairs. *)
Definition shortestpath (m : Node -> Node -> R) : Node -> Node -> R :=
  powN_fun m 2%N.

(** Efficient matrix-vector action for the min-plus semimodule. *)
Definition mva_eff_fun (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action_eff_fun m v.

(** Functional matrix-vector action: [(A·v) i = minⱼ (A i j + v j)]. *)
Definition mva_func (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action m v.