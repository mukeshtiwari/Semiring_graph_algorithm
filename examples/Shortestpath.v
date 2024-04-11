Require Import Semiring.Mat List BinNatDef
  Semiring.Definitions Semiring.Listprop
  Psatz Utf8 Coq.Arith.EqNat.
Import ListNotations.


(* min_+ alegebra *)
Section Comp. 

  (* Define Candidates *)
  Inductive Node := A | B | C. 
  
  (* Equality on Candidate *)
  Definition eqN (x y : Node) : bool :=
  match x, y with 
  | A, A => true 
  | B, B => true 
  | C, C => true 
  | _, _ => false
  end. 

   (* Nat extended with Infinity *)
  Inductive R := 
  | Left : nat -> R 
  | Infinity : R.

  Definition eqR (u v : R) : bool :=
  match u, v with 
  | Left x, Left y => Nat.eqb x y 
  | Infinity, Infinity => true 
  | _, _ => false 
  end. 

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

  (* zeroR *)
  Definition zeroR : R := Infinity.

  (* oneR *)
  Definition oneR : R := Left 0.  

  Definition finN : list Node := [A; B; C].

  (* Now, configure the matrix *)
  Definition shortestpath (m : Path.Matrix Node R) : Path.Matrix Node R :=
    matrix_exp_binary Node eqN finN R zeroR oneR plusR mulR m 2%N.

End Comp.

Section Proofs.


  (* Establish Proofs *)
  Theorem refN : brel_reflexive Node eqN. 
  Proof.
    unfold brel_reflexive;
    intros [| | ]; simpl;
    reflexivity.
  Qed.

  Theorem symN : brel_symmetric Node eqN.
  Proof.
    unfold brel_symmetric;
    intros [| | ] [| | ]; simpl;
    try reflexivity; try congruence.
  Qed.

  Theorem trnN : brel_transitive Node eqN.
  Proof.
    unfold brel_transitive;
    intros [| | ] [| | ] [| | ];
    simpl; intros Ha Hb;
    try firstorder. 
  Qed. 


  Theorem dunN : no_dup Node eqN finN = true. 
  Proof.
    reflexivity.
  Qed.

  Theorem lenN : 2 <= List.length finN. 
  Proof.
    cbn; nia. 
  Qed. 

  Theorem memN : ∀ x : Node, in_list eqN finN x = true. 
  Proof.
    intros [| | ];
    cbn; reflexivity.
  Qed.

  Theorem refR : brel_reflexive R eqR.
  Proof.
    unfold brel_reflexive;
    intros [x | ]; cbn;
    [eapply PeanoNat.Nat.eqb_refl | reflexivity].
  Qed. 
  
  Theorem symR : brel_symmetric R eqR.
  Proof.
    unfold brel_symmetric;
    intros [x | ] [y | ]; cbn;
    intros Ha; try reflexivity; 
    try congruence.
    eapply PeanoNat.Nat.eqb_eq in Ha.
    eapply PeanoNat.Nat.eqb_eq. 
    eapply eq_sym; assumption. 
  Qed. 

  Theorem trnR : brel_transitive R eqR.
  Proof.
    unfold brel_transitive;
    intros [x | ] [y | ] [z |]; cbn;
    intros Ha Hb;
    try reflexivity;
    try congruence.
    eapply PeanoNat.Nat.eqb_eq in Ha, Hb.
    eapply PeanoNat.Nat.eqb_eq.
    eapply eq_trans with y;
    try assumption.
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
  Local Infix "=n=" := eqN (at level 70) : Mat_scope.

  Theorem zero_left_identity_plus  : forall r : R, 0 + r =r= r = true.
  Proof.
    intros [x |]; cbn;
    [eapply PeanoNat.Nat.eqb_refl | reflexivity].
  Qed.

  Theorem zero_right_identity_plus : forall r : R, r + 0 =r= r = true.
  Proof.
    intros [x |]; cbn; try reflexivity.
    eapply PeanoNat.Nat.eqb_refl.
  Qed.

  Theorem plus_associative : forall a b c : R, a + (b + c) =r= 
    (a + b) + c = true.
  Proof.
    intros [x | ] [y | ] [z |]; cbn;
    try (eapply PeanoNat.Nat.eqb_refl);
    try reflexivity;
    now rewrite PeanoNat.Nat.min_assoc, 
    PeanoNat.Nat.eqb_refl.
  Qed.


  Theorem plus_commutative  : forall a b : R, a + b =r= b + a = true.
  Proof.
    intros [x | ] [y | ]; simpl;
    try (eapply PeanoNat.Nat.eqb_refl);
    try reflexivity.
    now rewrite PeanoNat.Nat.min_comm, 
    PeanoNat.Nat.eqb_refl.
  Qed.


  Theorem one_left_identity_mul  : forall r : R, 1 * r =r= r = true.
  Proof.
    intros [x |]; simpl;
    [eapply PeanoNat.Nat.eqb_refl | reflexivity].
  Qed.


  Theorem one_right_identity_mul : forall r : R, r * 1 =r= r = true.
  Proof.
    intros [x |]; simpl; 
    [rewrite PeanoNat.Nat.add_0_r; eapply PeanoNat.Nat.eqb_refl 
    | reflexivity].
  Qed.

  Theorem mul_associative : forall a b c : R, a * (b * c) =r= 
    (a * b) * c = true.
  Proof.
    intros [x | ] [y | ] [z |]; simpl;
    try reflexivity;
    try (eapply PeanoNat.Nat.eqb_refl).
    now rewrite PeanoNat.Nat.add_assoc, 
    PeanoNat.Nat.eqb_refl.
  Qed.


  
  Theorem left_distributive_mul_over_plus : forall a b c : R, 
    a * (b + c) =r= a * b + a * c = true.
  Proof.
    intros [x | ] [y | ] [z |]; simpl;
    try (eapply PeanoNat.Nat.eqb_refl);
    try reflexivity.
    +
      now rewrite PeanoNat.Nat.add_min_distr_l,
      PeanoNat.Nat.eqb_refl.
  Qed. 


  Theorem right_distributive_mul_over_plus : forall a b c : R, 
    (a + b) * c =r= a * c + b * c = true.
  Proof.
    intros [x | ] [y | ] [z |]; simpl;
    try (eapply PeanoNat.Nat.eqb_refl);
    try reflexivity.
    +
      now rewrite PeanoNat.Nat.add_min_distr_r,
      PeanoNat.Nat.eqb_refl.
  Qed. 


  Theorem zero_left_anhilator_mul : 
    forall a : R, 0 * a =r= 0 = true.
  Proof.
    intros [x | ]; simpl;
    reflexivity.
  Qed.

  Theorem zero_right_anhilator_mul : 
    forall a : R, a * 0 =r= 0 = true.
  Proof.
    intros [x | ]; simpl;
    try reflexivity.
  Qed.


  Theorem zero_stable : forall a : R, 1 + a =r= 1 = true.
  Proof.
    intros [x |]; simpl;
    reflexivity.
  Qed. 

  Theorem plus_idempotence : forall a : R, a + a =r= a = true.
  Proof.
    intros [x |]; simpl;
    try reflexivity.
    now rewrite PeanoNat.Nat.min_id,
    PeanoNat.Nat.eqb_refl.
  Qed.

End Proofs.



      