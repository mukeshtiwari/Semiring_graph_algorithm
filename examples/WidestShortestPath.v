Require Import Semiring.Mat List BinNatDef
  Semiring.Definitions Semiring.Listprop
  Psatz Utf8 Coq.Arith.EqNat.
Import ListNotations.



(* It should be shortest widest path *)
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

   Section min_plus.

    (* min_plus algebra + = min, * = +, 
      zero = Infinity, and one = Left 0 *)

    Definition zerof : R := Infinity. 
    Definition onef : R := Left 0. 
  
    Definition plusf (u v : R) : R :=
    match u, v with 
    | Left x, Left y => Left (Nat.min x y)
    | Left x, Infinity => Left x
    | Infinity, Left x => Left x 
    | _, _ => Infinity
    end. 

    Definition mulf (u v : R) : R :=
    match u, v with 
    | Left x, Left y => Left (Nat.add x y)
    | _, _ => Infinity
    end. 

  End min_plus.

  Section max_min.

    (* + = max, * = min, zero = 0, one = Infinity *)
    Definition zeros : R := Left 0.
    Definition ones : R := Infinity.

    Definition pluss (u v : R) : R :=
    match u, v with 
    | Left x, Left y => Left (Nat.max x y)
    | _, _ => Infinity 
    end. 

  
    Definition muls (u v : R) : R :=
    match u, v with 
    | Left x, Left y => Left (Nat.min x y)
    | Left x, Infinity => Left x 
    | Infinity, Left x => Left x 
    | _, _ => Infinity 
    end.


   
  End max_min.

 

  (* all good upto here *)

  (* This definition does appear to be correct in 
  the paper. *)
  Definition ltR (u v : R) : bool :=
  match u, v with 
  | Left x, Left y => Nat.ltb x y 
  | Left x, Infinity => true 
  | Infinity, Left _ => false 
  | _, _ => false
  end.

  (* pair *)
  Definition RR : Type := R * R. 
  (* zero *)
  Definition zeroRR : RR := (zerof, zeros). 
  (* one *)
  Definition oneRR : RR := (onef, ones).

  Definition eqRR (x y : RR) : bool :=
  match x, y with 
  |(xa, xb), (ya, yb) => eqR xa ya && eqR xb yb 
  end.


  (* Lexicographic product *)
  Definition lex_plusRR (u v : RR) : RR :=
  match u, v with 
  | (au, bu), (av, bv) => 
    match orb (ltR au av) (andb (eqR au av) (ltR bv bu)) with 
    | true => (au, bu)
    | _ => (av, bv)
    end 
  end. 

 
  (* Direct product *)
  Definition direct_mulRR (u v : RR) : RR :=
  match u, v with 
  | (au, bu), (av, bv) => (mulf au av,  muls bu bv)
  end.  


  Definition finN : list Node := [A; B; C].

  (* Now, configure the matrix *)
  Definition widest_shortest_path (m : Path.Matrix Node RR) : Path.Matrix Node RR :=
    matrix_exp_binary Node eqN finN RR zeroRR oneRR lex_plusRR direct_mulRR m 2%N.

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



  Local Notation "0" := zeroRR : Mat_scope.
  Local Notation "1" := oneRR : Mat_scope.
  Local Infix "+" := lex_plusRR : Mat_scope.
  Local Infix "*" := direct_mulRR : Mat_scope.
  Local Infix "=r=" := eqRR (at level 70) : Mat_scope.

  Theorem zero_left_identity_plus  : forall r : RR, 0 + r =r= r = true.
  Proof.
    intros ([ x | ], [y |]); cbn;
    try (repeat rewrite PeanoNat.Nat.eqb_refl);
    reflexivity.
  Qed.

  Theorem zero_right_identity_plus : forall r : RR, r + 0 =r= r = true.
  Proof.
    intros ([ x | ], [[ | y] |]); cbn;
    try (repeat rewrite PeanoNat.Nat.eqb_refl);
    reflexivity.
  Qed.

  Theorem ltr_transitive : forall (x y z : R), 
    ltR x y = true -> ltR y z = true -> ltR x z = true. 
  Proof.
    unfold ltR.
    intros [x |] [y |] [z|] Ha Hb; 
    try reflexivity; 
    try congruence.
    rewrite PeanoNat.Nat.ltb_lt in Ha, Hb |- *.
    nia.
  Qed.  

  Theorem ltr_total : forall (xa xb : R), ltR xa xb = false -> 
    eqR xa xb = true ∨ ltR xb xa = true. 
  Proof. 
    unfold ltR.
    intros [xa|] [xb|];
    intros Ha; try congruence.
    +
      rewrite PeanoNat.Nat.ltb_ge in Ha.
      simpl.
      rewrite PeanoNat.Nat.eqb_eq, 
      PeanoNat.Nat.ltb_lt.
      nia.
    +
      right; reflexivity.
    +
      left; reflexivity.
  Qed.

  Theorem eqr_reflexive : forall x : R, eqR x x = true. 
  Proof.
    intros [x|]; cbn;
    [now rewrite PeanoNat.Nat.eqb_refl |reflexivity].
  Qed.

  Theorem eqr_symmetric : forall x y : R, eqR x y = true -> eqR y x = true. 
  Proof.
    intros [x | ] [y | ]; 
    simpl; try reflexivity; 
    try congruence.
    intro Ha. 
    rewrite PeanoNat.Nat.eqb_eq in Ha |- *.
    auto.
  Qed.

  Theorem eqr_transitive : forall x y z : R, eqR x y = true -> 
    eqR y z = true -> eqR x z = true. 
  Proof. 
    intros [x | ] [y | ] [z |] Ha Hb; 
    simpl in Ha, Hb |- *; try reflexivity;
    try congruence.
    rewrite PeanoNat.Nat.eqb_eq in Ha, Hb |- *.
    nia.
  Qed.

  Theorem ltr_eqr_false : forall xb xc : R, eqR xb xc = true -> ltR xb xc = false.
  Proof.
    intros [x | ] [y | ]; simpl;
    try reflexivity; try congruence.
    intro Ha.
    rewrite PeanoNat.Nat.eqb_eq in Ha.
    rewrite PeanoNat.Nat.ltb_ge.
    nia.
  Qed.

    
  

  Theorem plus_associative : forall a b c : RR, a + (b + c) =r= 
    (a + b) + c = true.
  Proof.
    intros (xa, ya) (xb, yb) (xc, yc); cbn.
    case (ltR xb xc) eqn:Ha; cbn;
    case (ltR xa xb) eqn:Hb; cbn.
    +
      rewrite (ltr_transitive _ _ _ Hb Ha); cbn.
      now (repeat rewrite eqr_reflexive).
    +
      case (eqR xa xb) eqn:Hc;
      case (ltR yb ya) eqn:Hd;
      cbn.
      ++
        case (ltR xa xc) eqn:He; cbn.
        +++
          now (repeat rewrite eqr_reflexive).
        +++
          case (eqR xa xc) eqn:Hf;
          case (ltR yc ya) eqn:Hg;
          simpl.
          *
            now (repeat rewrite eqr_reflexive).
          *
            rewrite Hf.
            eapply ltr_total in Hg.
            destruct Hg as [Hg | Hg].
            **  
              eapply eqr_symmetric in Hg.
              now rewrite Hg.
            **
              eapply eqr_symmetric in Hc.
              pose proof eqr_transitive _ _ _ Hc Hf as Hi.
              (* contradiction *)
              pose proof ltr_eqr_false _ _ Hi as Hj.
              rewrite Hj in Ha.
              congruence.
          *
  Admitted.  
          










    
    



End Proofs.
  

