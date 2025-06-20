From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat. 
From Semiring Require Import Mat  Definitions
  Listprop.
Import ListNotations.

(* Take from Schulze's paper https://link.springer.com/content/pdf/10.1007/s00355-010-0475-4.pdf *)
Section Comp.

  (* 
  8 voters a ≻v c ≻v d ≻v b
  2 voters b ≻v a ≻v d ≻v c
  4 voters c ≻v d ≻v b ≻v a
  4 voters d ≻v b ≻v a ≻v c
  3 voters d ≻v c ≻v b ≻v a
  
  *)
  (* Define Candidates *)
  Inductive Node := A | B | C | D.
  
  (* Equality on Candidate *)
  Definition eqN (x y : Node) : bool :=
  match x, y with 
  | A, A => true 
  | B, B => true 
  | C, C => true 
  | D, D => true
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

  (* zeroR *)
  Definition zeroR : R := Left 0.

  (* oneR *)
  Definition oneR : R := Infinity. 

  (* plusR *)
  Definition plusR (u v : R) : R :=
  match u, v with 
  | Left x, Left y => Left (Nat.max x y) 
  | _, _ => Infinity
  end.

  (* mulR *)
  Definition mulR (u v : R) : R :=
  match u, v with 
  | Left x, Left y => Left (Nat.min x y)
  | Left x, Infinity => Left x 
  | Infinity, Left y => Left y 
  | _, _ => Infinity 
  end. 

 
  Definition finN : list Node := [A; B; C; D].

  (* Now, configure the matrix *)
  Definition schulze (m : Path.Matrix Node R) : Path.Matrix Node R :=
    matrix_exp_binary Node eqN finN R zeroR oneR plusR mulR m 3%N.

 

End Comp.


(* We establish in this section that we all the requirements of 
an idempotent and bounded semiring *)
Section Proofs. 

  (* Establish Proofs *)
  Theorem refN : brel_reflexive Node eqN. 
  Proof.
    unfold brel_reflexive;
    intros [| | | ]; simpl;
    reflexivity.
  Qed.

  Theorem symN : brel_symmetric Node eqN.
  Proof.
    unfold brel_symmetric;
    intros [| | | ] [| | | ]; simpl;
    try reflexivity; try congruence.
  Qed.

  Theorem trnN : brel_transitive Node eqN.
  Proof.
    unfold brel_transitive;
    intros [| | | ] [| | | ] [| | |];
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
    intros [| | |];
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
    now rewrite PeanoNat.Nat.max_0_r,
    PeanoNat.Nat.eqb_refl.
  Qed.
  

  Theorem plus_associative : forall a b c : R, a + (b + c) =r= 
    (a + b) + c = true.
  Proof.
    intros [x | ] [y | ] [z |]; cbn;
    try reflexivity.
    now rewrite PeanoNat.Nat.max_assoc, 
    PeanoNat.Nat.eqb_refl.
  Qed.


  Theorem plus_commutative  : forall a b : R, a + b =r= b + a = true.
  Proof.
    intros [x | ] [y | ]; simpl;
    try reflexivity.
    now rewrite PeanoNat.Nat.max_comm, 
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
    [eapply PeanoNat.Nat.eqb_refl | reflexivity].
  Qed.

  Theorem mul_associative : forall a b c : R, a * (b * c) =r= 
    (a * b) * c = true.
  Proof.
    intros [x | ] [y | ] [z |]; simpl;
    try reflexivity;
    try (eapply PeanoNat.Nat.eqb_refl).
    now rewrite PeanoNat.Nat.min_assoc, 
    PeanoNat.Nat.eqb_refl.
  Qed.

  (* Not in library! *)
  Theorem max_min_interaction : 
    forall (x y : nat), (Nat.max (Nat.min x y) x) = x.
  Proof.
    intros *. nia.
  Qed.
  

  (* It is indeed pain to discharge all these axioms *)
  Theorem left_distributive_mul_over_plus : forall a b c : R, 
    a * (b + c) =r= a * b + a * c = true.
  Proof.
    intros [x | ] [y | ] [z |]; simpl;
    try reflexivity.
    +
      now rewrite PeanoNat.Nat.min_max_distr,
      PeanoNat.Nat.eqb_refl.
    +
      now rewrite max_min_interaction,
      PeanoNat.Nat.eqb_refl.
    +
      now rewrite PeanoNat.Nat.max_comm,
      max_min_interaction,
      PeanoNat.Nat.eqb_refl.
    +
      now rewrite PeanoNat.Nat.max_id,
      PeanoNat.Nat.eqb_refl.
    +
      eapply PeanoNat.Nat.eqb_refl.
  Qed.


  Theorem right_distributive_mul_over_plus : forall a b c : R, 
    (a + b) * c =r= a * c + b * c = true.
  Proof.
    intros [x | ] [y | ] [z |]; simpl;
    try reflexivity.
    +
      (* Nat.eqb (Nat.min x (Nat.max y z)) 
        (Nat.max (Nat.min x y) (Nat.min x z)) = true*)
      rewrite PeanoNat.Nat.min_comm.
      replace (Nat.min x z) with (Nat.min z x);
      replace (Nat.min y z) with (Nat.min z y);
      try (eapply PeanoNat.Nat.min_comm).
      now rewrite PeanoNat.Nat.min_max_distr,
      PeanoNat.Nat.eqb_refl.
    +
      eapply PeanoNat.Nat.eqb_refl.
    +
      replace (Nat.min x z) with (Nat.min z x);
      try (eapply PeanoNat.Nat.min_comm).
      now rewrite max_min_interaction,
      PeanoNat.Nat.eqb_refl.
    +
      replace (Nat.max z (Nat.min y z)) with 
      (Nat.max (Nat.min y z) z);
      try (eapply PeanoNat.Nat.max_comm).
      replace (Nat.min y z) with (Nat.min z y);
      try (eapply PeanoNat.Nat.min_comm).
      now rewrite max_min_interaction,
      PeanoNat.Nat.eqb_refl.
    +
      now rewrite PeanoNat.Nat.max_id,
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
    now rewrite PeanoNat.Nat.min_0_r,
    PeanoNat.Nat.eqb_refl.
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
    now rewrite PeanoNat.Nat.max_id,
    PeanoNat.Nat.eqb_refl.
  Qed.


End Proofs.

