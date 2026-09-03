From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat.
From HB Require Import structures.
From Semiring Require Import MatN 
  SemimoduleN Structures.
Import ListNotations SemiringNotations.


(** * 5G Network Slicing - Latency-Bandwidth Product Semiring

    This models resource allocation across virtual network slices in a 5G
    core network. Each link has two attributes:
      * latency (ms)     - minimized (min-plus / tropical semiring)
      * bandwidth (Mbps) - maximized (max-min semiring)

    The semiring R = Latency x Bandwidth is the DIRECT PRODUCT of the two
    bounded semirings above. Since all axioms hold componentwise, the
    product is again a bounded semiring.

    Topology:  4 nodes representing the 5G user plane data path:
      UE (user equipment) -> gNB (base station) -> UPF (user plane) -> DN

    A* computes the optimal path weights between all node pairs. *)


Section Comp.

  Inductive Node := UE | gNB | UPF | DN.

  (** Bandwidth: Nat with an Infinity marker *)
  Inductive BW :=
    | BW_fin : nat -> BW
    | BW_inf : BW.

 
  (** Product semiring: R = Latency(nat) x Bandwidth(BW) *)
  Inductive R :=
    | Rpair : nat -> BW -> R
    | Unreachable : R.

  Definition zeroR : R := Unreachable.
  Definition oneR : R := Rpair 0 BW_inf.

  (** plusR: (min latency, max bandwidth) componentwise *)
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

  (** mulR: (add latency, min bandwidth) componentwise *)
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

End Comp.


(** * HB Instances: FinType Node, BoundedSemiring R

    R = Latency(nat) x Bandwidth(BW) is the product of two bounded
    semirings: min-plus (latency) x max-min (bandwidth). *)

Section HBInstances.

  Definition fin_eq_dec (x y : Node) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition elements_list : list Node := [UE; gNB; UPF; DN].

  Lemma elements_nodup_proof : NoDup elements_list.
  Proof.
    unfold elements_list.
    apply NoDup_cons. intro H. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H.
    apply NoDup_cons. intro H. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H.
    apply NoDup_cons. intro H. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H.
    apply NoDup_cons. intro H. simpl in H. destruct H.
    apply NoDup_nil.
  Qed.

  Lemma elements_complete_proof : forall x : Node, In x elements_list.
  Proof. unfold elements_list; intros [ | | | ]; simpl; auto. Qed.

  Lemma elements_two_or_more_proof : (2 <= List.length elements_list)%nat.
  Proof. unfold elements_list. cbn. nia. Qed.

  HB.instance Definition _ := IsFinType.Build Node
    elements_list elements_nodup_proof elements_complete_proof
    elements_two_or_more_proof fin_eq_dec.

  Lemma addA_proof : forall x y z : R, plusR (plusR x y) z = plusR x (plusR y z).
  Proof.
    intros [l1 b1|] [l2 b2|] [l3 b3|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.min_assoc.
    destruct b1, b2, b3; cbn; try reflexivity.
    rewrite PeanoNat.Nat.max_assoc. reflexivity.
  Qed.

  Lemma addC_proof : forall x y : R, plusR x y = plusR y x.
  Proof.
    intros [l1 b1|] [l2 b2|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.min_comm.
    destruct b1, b2; cbn; try reflexivity.
    rewrite PeanoNat.Nat.max_comm. reflexivity.
  Qed.

  Lemma add0r_proof : forall x : R, plusR zeroR x = x.
  Proof. intros [l b|]; cbn; reflexivity. Qed.

  Lemma addr0_proof : forall x : R, plusR x zeroR = x.
  Proof. intros [l b|]; cbn; reflexivity. Qed.

  HB.instance Definition _ := IsCommutativeMonoid.Build R
    zeroR plusR addA_proof addC_proof add0r_proof addr0_proof.

  Lemma mulA_proof : forall a b c : R, mulR (mulR a b) c = mulR a (mulR b c).
  Proof.
    intros [l1 b1|] [l2 b2|] [l3 b3|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.add_assoc.
    destruct b1, b2, b3; cbn; try reflexivity.
    rewrite PeanoNat.Nat.min_assoc. reflexivity.
  Qed.

  Lemma mul1r_proof : forall a : R, mulR oneR a = a.
  Proof.
    intros [l b|]; cbn.
    - destruct b; cbn; f_equal; try lia; try reflexivity.
    - reflexivity.
  Qed.

  Lemma mulr1_proof : forall a : R, mulR a oneR = a.
  Proof.
    intros [l b|]; cbn.
    - destruct b; cbn; f_equal; try lia; try reflexivity.
    - reflexivity.
  Qed.

  Lemma mulDr_proof : forall a b c : R,
    mulR (plusR a b) c = plusR (mulR a c) (mulR b c).
  Proof.
    intros [l1 b1|] [l2 b2|] [l3 b3|]; cbn; try reflexivity;
      f_equal; try nia.
    (** bandwidth component: max-min distributivity *)
    destruct b1, b2, b3; cbn; try reflexivity; f_equal; nia.
  Qed.

  Lemma mulDl_proof : forall a b c : R,
    mulR a (plusR b c) = plusR (mulR a b) (mulR a c).
  Proof.
    intros [l1 b1|] [l2 b2|] [l3 b3|]; cbn; try reflexivity;
      f_equal; try nia.
    destruct b1, b2, b3; cbn; try reflexivity; f_equal; nia.
  Qed.

  Lemma mul0r_proof : forall a : R, mulR zeroR a = zeroR.
  Proof. intros [l b|]; cbn; reflexivity. Qed.

  Lemma mulr0_proof : forall a : R, mulR a zeroR = zeroR.
  Proof. intros [l b|]; cbn; reflexivity. Qed.

  HB.instance Definition _ := IsSemiring.Build R
    oneR mulR mulA_proof mul1r_proof mulr1_proof
    mulDr_proof mulDl_proof mul0r_proof mulr0_proof.

  Lemma add_bound_proof : forall a : R, plusR oneR a = oneR.
  Proof.
    intros [l b|]; cbn; try reflexivity.
  Qed.

  HB.instance Definition _ := IsBoundedSemiring.Build R add_bound_proof.

  HB.instance Definition _ := IsSemimodule.Build R R
    mulR mulDl_proof mulDr_proof
    (fun a b x => eq_sym (mulA_proof a b x))
    mul1r_proof mul0r_proof mulr0_proof.

End HBInstances.

(** Kleene star of the 5G adjacency matrix: [A* = A³].
    Computes optimal path weights between all node pairs. *)
Definition fiveG_kleene (m : Node -> Node -> R) : Node -> Node -> R :=
  powN_fun m 3%N.

Definition mva_eff_fun (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action_eff_fun m v.

Definition mva_func (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action m v.
