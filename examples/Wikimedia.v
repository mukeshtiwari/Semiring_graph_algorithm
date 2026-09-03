From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat Lia.
From HB Require Import structures.
From Semiring Require Import MatN 
  SemimoduleN Structures.

Import ListNotations SemiringNotations. 

Section Comp. 

    
    (* Inductive Node := A | B | C | D | E.  *)
    
    Inductive Node :=
    | TC
    | SK
    | KW
    | MR
    | LG
    | CB
    | HC
    | JSR
    | PL
    | JG
    | JF
    | FSS
    | GM
    | MP
    | EZ
    | WHD
    | UW
    | TM.
  
  (**
   https://en.wikipedia.org/wiki/Schulze_method
     Number of voters 	Order of preference
     5 	ACBED
     5 	ADECB
     8 	BEDAC
     3 	CABED
     7 	CAEBD
     2 	CBADE
     7 	DCEBA
     8 	EBADC  
 
   *)
    (* 
    Definition eqN (x y : Node) : bool := 
      match x, y with 
      | A, A => true 
      | B, B => true
      | C, C => true
      | D, D => true
      | E, E => true
      | _, _ => false
      end.
    *)
     
   
    


    Inductive R :=
    | Left : nat -> R
    | Infinity : R.


    Definition zeroR : R := Left 0.

    Definition oneR : R := Infinity.

    Definition plusR (u v : R) : R :=
      match u, v with 
      | Left x, Left y => Left (Nat.max x y) 
      | _, _ => Infinity
      end.

    Definition mulR (u v : R) : R :=
      match u, v with 
      | Left x, Left y => Left (Nat.min x y)
      | Left x, Infinity => Left x 
      | Infinity, Left y => Left y 
      | _, _ => Infinity 
      end.
    
    (* 
    Definition finN : list Node :=
      [A; B; C; D; E].
    *)
     
    Definition finN : list Node :=
    [TC; SK; KW; MR; LG; CB; HC; JSR; PL; JG; JF; FSS; GM; MP; EZ; WHD; UW; TM].
    

End Comp.


(** * HB Instances: FinType Node, BoundedSemiring R (max-min semiring) *)

Section HBInstances.

  Definition fin_eq_dec (x y : Node) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition elements_list : list Node :=
    [TC; SK; KW; MR; LG; CB; HC; JSR; PL; JG; JF; FSS; GM; MP; EZ; WHD; UW; TM].

  Lemma elements_nodup_proof : NoDup elements_list.
  Proof.
    unfold elements_list.
    repeat match goal with
           | |- NoDup [] => apply NoDup_nil
           | |- NoDup (_ :: _) =>
               apply NoDup_cons; [ intros H; simpl in H; firstorder discriminate | ]
           end.
  Qed.

  Lemma elements_complete_proof : forall x : Node, In x elements_list.
  Proof.
    unfold elements_list.
    intros [| | | | | | | | | | | | | | | | |].
    all: simpl; firstorder congruence.
  Qed.

  Lemma elements_two_or_more_proof : (2 <= List.length elements_list)%nat.
  Proof.
    unfold elements_list. cbn. nia.
  Qed.

  HB.instance Definition _ := IsFinType.Build Node
    elements_list elements_nodup_proof elements_complete_proof
    elements_two_or_more_proof fin_eq_dec.

  Lemma addA_proof : forall x y z : R, plusR (plusR x y) z = plusR x (plusR y z).
  Proof.
    intros [x|] [y|] [z|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.max_assoc. reflexivity.
  Qed.

  Lemma addC_proof : forall x y : R, plusR x y = plusR y x.
  Proof.
    intros [x|] [y|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.max_comm. reflexivity.
  Qed.

  Lemma add0r_proof : forall x : R, plusR zeroR x = x.
  Proof.
    intro x. destruct x as [n|]; cbv [zeroR plusR].
    f_equal. reflexivity.
  Qed.

  Lemma addr0_proof : forall x : R, plusR x zeroR = x.
  Proof.
    intro x. destruct x as [n|]; cbv [zeroR plusR].
    f_equal. nia. reflexivity.
  Qed.

  HB.instance Definition _ := IsCommutativeMonoid.Build R
    zeroR plusR addA_proof addC_proof add0r_proof addr0_proof.

  Lemma mulA_proof : forall a b c : R, mulR (mulR a b) c = mulR a (mulR b c).
  Proof.
    intros [a|] [b|] [c|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.min_assoc. reflexivity.
  Qed.

  Lemma mul1r_proof : forall a : R, mulR oneR a = a.
  Proof. intros [a|]; cbn; reflexivity. Qed.

  Lemma mulr1_proof : forall a : R, mulR a oneR = a.
  Proof. intros [a|]; cbn; reflexivity. Qed.

  Lemma mulDr_proof : forall a b c : R,
    mulR (plusR a b) c = plusR (mulR a c) (mulR b c).
  Proof.
    intros [a|] [b|] [c|]; cbn; try reflexivity; f_equal; nia.
  Qed.

  Lemma mulDl_proof : forall a b c : R,
    mulR a (plusR b c) = plusR (mulR a b) (mulR a c).
  Proof.
    intros [a|] [b|] [c|]; cbn; try reflexivity; f_equal; nia.
  Qed.

  Lemma mul0r_proof : forall a : R, mulR zeroR a = zeroR.
  Proof. intros [a|]; cbn; reflexivity. Qed.

  Lemma mulr0_proof : forall a : R, mulR a zeroR = zeroR.
  Proof. intros [a|]; cbn; try reflexivity.
    rewrite PeanoNat.Nat.min_0_r. reflexivity.
  Qed.

  HB.instance Definition _ := IsSemiring.Build R
    oneR mulR mulA_proof mul1r_proof mulr1_proof
    mulDr_proof mulDl_proof mul0r_proof mulr0_proof.

  Lemma add_bound_proof : forall a : R, plusR oneR a = oneR.
  Proof. intros [a|]; cbn; reflexivity. Qed.

  HB.instance Definition _ := IsBoundedSemiring.Build R add_bound_proof.

  HB.instance Definition _ := IsSemimodule.Build R R
    mulR mulDl_proof mulDr_proof
    (fun a b x => eq_sym (mulA_proof a b x))
    mul1r_proof mul0r_proof mulr0_proof.

End HBInstances.

Definition wikimedia (m : Node -> Node -> R) : Node -> Node -> R :=
  powN_fun m 17%N.

Definition mva_eff_fun (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action_eff_fun m v.

Definition mva_func (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action m v.