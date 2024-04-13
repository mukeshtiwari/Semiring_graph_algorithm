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

    
  Theorem eqrr_reflexive : forall xa ya : R, 
    ((xa, ya) =r= (xa, ya)) = true.
  Proof.
    intros [xa | ] [ya | ];
    simpl;
    try (repeat rewrite PeanoNat.Nat.eqb_refl);
    simpl; reflexivity.
  Qed.
  
  Theorem ltr_false : forall x y : R, ltR x y = true -> ltR y x = false.
  Proof.
    intros [x | ] [y | ]; 
    simpl; intros Ha;
    try reflexivity; 
    try congruence.
    rewrite PeanoNat.Nat.ltb_lt in Ha.
    rewrite PeanoNat.Nat.ltb_ge.
    nia.
  Qed.


  Theorem ltr_eqr_gen : forall (ya yb yc yd : R) (b : bool) , 
    eqR yc yb = true -> eqR ya yd = true -> ltR yc ya = b -> ltR yb yd = b.
  Proof. 
    intros [ya | ] [yb | ] [yc | ] [yd | ] [|]; 
    simpl; intros Ha Hb Hc;
    try congruence.
    +
      eapply PeanoNat.Nat.eqb_eq in Ha, Hb.
      rewrite PeanoNat.Nat.ltb_lt in Hc |- *.
      nia.
    +
      eapply PeanoNat.Nat.eqb_eq in Ha, Hb.
      rewrite PeanoNat.Nat.ltb_ge in Hc |- *.
      nia.
  Qed.
      

  Theorem ltr_eqr : forall (ya yb yc yd : R), 
    eqR yc yb = true -> eqR ya yd = true -> ltR yc ya = true -> ltR yb yd = true.
  Proof. 
    intros * Ha Hb Hc.
    eapply ltr_eqr_gen.
    exact Ha.
    exact Hb. 
    exact Hc.
  Qed.


  Theorem ltr_true_eqr_false : forall x y : R, 
    ltR x y = true -> eqR x y = false.
  Proof.
    intros [x | ] [y | ];
    simpl; try reflexivity;
    try congruence.
    intros Ha.
    rewrite PeanoNat.Nat.ltb_lt in Ha.
    rewrite PeanoNat.Nat.eqb_neq.
    nia.
  Qed.

  Theorem eqr_replace : forall xb xc xa : R, 
    eqR xb xc = true -> eqR xa xc = false -> 
    eqR xa xb = false.
  Proof.
    intros [xb | ] [xc | ] [xa | ] Ha Hb;
    simpl in Ha, Hb |- *;
    try reflexivity; 
    try congruence.
    rewrite PeanoNat.Nat.eqb_eq in Ha.
    rewrite PeanoNat.Nat.eqb_neq in Hb |- *.
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
            (* contradiction *)
            eapply ltr_total in He.
            destruct He as [He | He].
            **
              rewrite He in Hf; congruence.
            **
              pose proof ltr_transitive _ _ _ Ha He as Hh.
              eapply eqr_symmetric in Hc.
              now rewrite (ltr_eqr_false _ _ Hc) in Hh.
          *
            (* contracdiction *)
            eapply ltr_total in He.
            destruct He as [He | He].
            **
              rewrite He in Hf; congruence.
            **
              pose proof ltr_transitive _ _ _ Ha He as Hh.
              eapply eqr_symmetric in Hc.
              now rewrite (ltr_eqr_false _ _ Hc) in Hh.

      ++
        case (ltR xb xc) eqn:He; cbn.
        +++
          now (repeat rewrite eqr_reflexive).
        +++
          congruence.
      ++
        case (ltR xb xc) eqn:He; cbn.
        +++
          now (repeat rewrite eqr_reflexive).
        +++
          congruence.
      ++
        case (ltR xb xc) eqn:He; cbn.
        +++
          now (repeat rewrite eqr_reflexive).
        +++
          congruence.
    +
      case (eqR xb xc) eqn:Hc;
      case (ltR yc yb) eqn:Hd;
      simpl.
      ++
        rewrite Hb; simpl.
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
              pose proof eqr_transitive _ _ _ Hf Hc as Hi.
              (* contradiction *)
              pose proof ltr_eqr_false _ _ Hi as Hj.
              rewrite Hj in Hb.
              congruence.
          *
            (* contradiction *)
            eapply ltr_total in He.
            destruct He as [He | He].
            **
              rewrite He in Hf; congruence.
            **
              pose proof ltr_transitive _ _ _ He Hb as Hh.
              eapply eqr_symmetric in Hc.
              now rewrite (ltr_eqr_false _ _ Hc) in Hh.
          *
            (* contracdiction *)
            eapply ltr_total in He.
            destruct He as [He | He].
            **
              rewrite He in Hf; congruence.
            **
              pose proof ltr_transitive _ _ _ He Hb as Hh.
              eapply eqr_symmetric in Hc.
              now rewrite (ltr_eqr_false _ _ Hc) in Hh.
        ++
          case (ltR xa xc) eqn:He; cbn.
          +++
            now (repeat rewrite eqr_reflexive).
          +++
            destruct ((eqR xa xc && ltR yc ya))%bool.
            *
              eapply eqrr_reflexive.
            *
              eapply eqrr_reflexive.
        ++
          destruct (ltR xa xc || eqR xa xc && ltR yc ya)%bool;
          eapply eqrr_reflexive.
        ++
          destruct (ltR xa xc || eqR xa xc && ltR yc ya)%bool;
          eapply eqrr_reflexive.
    +
      case (eqR xb xc) eqn:Hc;
      case (ltR yc yb) eqn:Hd;
      simpl.
      ++
        rewrite Hb; simpl.
        case (eqR xa xb) eqn:He;
        case (ltR yb ya) eqn:Hf;
        simpl.
        +++
          rewrite (eqr_transitive _ _ _ He Hc).
          rewrite (ltr_transitive _ _ _ Hd Hf).
          simpl.
          rewrite Bool.orb_true_r.
          now (repeat rewrite eqr_reflexive).
        +++
          rewrite Ha, Hc, Hd. simpl.
          now (repeat rewrite eqr_reflexive).
        +++
          rewrite Ha, Hc, Hd; simpl.
          now (repeat rewrite eqr_reflexive).
        +++
          rewrite Ha, Hc, Hd; simpl.
          now (repeat rewrite eqr_reflexive).
      ++
        case (ltR xa xc) eqn:He;
        simpl.
        +++
          eapply ltr_total in Ha, Hb. 
          destruct Ha as [Ha | Ha];
          destruct Hb as [Hb | Hb].
          *
            (* contradiction *)
            pose proof (eqr_transitive _ _ _ Hb Ha) as Hi.
            rewrite (ltr_eqr_false _ _ Hi) in He.
            congruence.
          *
            pose proof (ltr_transitive _ _ _ Hb He) as Hi.
            rewrite (ltr_eqr_false _ _ Hc) in Hi.
            congruence.
          *
            pose proof (eqr_transitive _ _ _ Hb Hc) as Hi.
            rewrite (ltr_eqr_false _ _ Hi) in He.
            congruence.
          *
            eapply eqr_symmetric in Hc.
            eapply ltr_eqr_false in Hc.
            rewrite Hc in Ha.
            congruence.
        +++
          case (eqR xa xc) eqn:Hf;
          case (ltR yc ya) eqn:Hg;
          simpl.
          *
            eapply eqr_symmetric in Hc.
            rewrite (eqr_transitive _ _ _ Hf Hc); simpl.
            eapply ltr_total in Hd.
            destruct Hd as [Hd | Hd].
            **
              rewrite (ltr_eqr ya yb yc ya Hd (eqr_reflexive ya) Hg); simpl.
              rewrite He, Hf, Hg; simpl.
              now (repeat rewrite eqr_reflexive).
            **
              rewrite (ltr_transitive _ _ _ Hd Hg); simpl.
              rewrite He, Hf, Hg; simpl.
              now (repeat rewrite eqr_reflexive).
          *
            eapply eqr_symmetric in Hc.
            rewrite (eqr_transitive _ _ _ Hf Hc).
            simpl.
            case (ltR yb ya) eqn:Hh; simpl.
            **
              rewrite He, Hf, Hg; simpl.
              now (repeat rewrite eqr_reflexive).
            **
              eapply eqr_symmetric in Hc.
              rewrite Ha, Hc, Hd; simpl.
              now (repeat rewrite eqr_reflexive).
          *
            rewrite (eqr_replace _ _ _ Hc Hf).
            simpl.
            rewrite Ha, Hc, Hd; simpl.
            now (repeat rewrite eqr_reflexive).
          *
            rewrite (eqr_replace _ _ _ Hc Hf).
            simpl.
            rewrite Ha, Hc, Hd; simpl.
            now (repeat rewrite eqr_reflexive).
      ++
        case (ltR xa xc) eqn:He;
        simpl.
        +++
          case (eqR xa xb) eqn:Hf;
          case (ltR yb ya) eqn:Hi;
          simpl.
          *
            rewrite He; simpl.
            now (repeat rewrite eqr_reflexive).
          *
            rewrite Ha, Hc; simpl.
            (* contradiction *)
            eapply ltr_total in Ha, Hb.
            destruct Ha as [Ha | Ha];
            destruct Hb as [Hb | Hb].
            **
              pose proof (eqr_transitive _ _ _ Hb Ha) as Hh.
              eapply ltr_eqr_false in Hh.
              rewrite Hh in He.
              congruence.
            **
              rewrite Hc in Ha; congruence.
            **
              assert (Hj : ltR xc xa = true).
              eapply ltr_eqr.
              eapply eqr_reflexive.
              eapply eqr_symmetric.
              exact Hb.
              exact Ha.
              eapply ltr_false in Hj.
              rewrite Hj in He.
              congruence.
            **
              pose proof (ltr_transitive _ _ _ Ha Hb) as Hh.
              eapply ltr_false in Hh.
              rewrite He in Hh; congruence.
          *
            rewrite Ha, Hc, Hd; simpl.
            eapply ltr_total in Ha, Hb.
            destruct Ha as [Ha | Ha];
            destruct Hb as [Hb | Hb].
            **
              pose proof (eqr_transitive _ _ _ Hb Ha) as Hh.
              eapply ltr_eqr_false in Hh.
              rewrite Hh in He.
              congruence.
            **
              rewrite Hc in Ha; congruence.
            **
              assert (Hj : ltR xc xa = true).
              eapply ltr_eqr.
              eapply eqr_reflexive.
              eapply eqr_symmetric.
              exact Hb.
              exact Ha.
              eapply ltr_false in Hj.
              rewrite Hj in He.
              congruence.
            **
              pose proof (ltr_transitive _ _ _ Ha Hb) as Hh.
              eapply ltr_false in Hh.
              rewrite He in Hh; congruence.
          *
            eapply ltr_total in Ha, Hb.
            destruct Ha as [Ha | Ha];
            destruct Hb as [Hb | Hb].
            **
              pose proof (eqr_transitive _ _ _ Hb Ha) as Hh.
              eapply ltr_eqr_false in Hh.
              rewrite Hh in He.
              congruence.
            **
              rewrite Hc in Ha; congruence.
            **
              assert (Hj : ltR xc xa = true).
              eapply ltr_eqr.
              eapply eqr_reflexive.
              eapply eqr_symmetric.
              exact Hb.
              exact Ha.
              eapply ltr_false in Hj.
              rewrite Hj in He.
              congruence.
            **
              pose proof (ltr_transitive _ _ _ Ha Hb) as Hh.
              eapply ltr_false in Hh.
              rewrite He in Hh; congruence.
        +++
          case (eqR xa xc) eqn:Hf;
          case (ltR yc ya) eqn:Hg;
          simpl.
          *
            pose proof eqr_replace xa xc xb Hf Hc as Hi.
            case (eqR xa xb) eqn:Hj.
            eapply eqr_symmetric in Hj;
            rewrite Hj in Hi; congruence.
            simpl.
            rewrite Ha, Hc; simpl.
            (* contradiciton *)
            (* it was close! I though it was false :) *)
            eapply ltr_total in Ha, Hb.
            destruct Ha as [Ha | Ha];
            destruct Hb as [Hb | Hb];
            try (rewrite Hc in Ha; congruence);
            try (rewrite Hc in Ha; congruence).
            rewrite Hb in Hj; congruence.
            pose proof (ltr_transitive _ _ _ Ha Hb) as Hk.
            eapply eqr_symmetric in Hf.
            rewrite (ltr_eqr_false _ _ Hf) in Hk; 
            congruence.
          *
            pose proof eqr_replace _ _ _ Hf Hc as Hi.
            case (eqR xa xb) eqn:Hj.
            eapply eqr_symmetric in Hj;
            rewrite Hj in Hi; congruence.
            simpl.
            rewrite Ha, Hc; simpl.
            now (repeat rewrite eqr_reflexive).
          *
            eapply ltr_total in Ha, Hb.
            destruct Ha as [Ha | Ha];
            destruct Hb as [Hb | Hb].
            **
              pose proof (eqr_transitive _ _ _ Hb Ha) as Hh.
              eapply ltr_eqr_false in Hh.
              rewrite Hh in He.
              congruence.
            **
              rewrite Hc in Ha; congruence.
            **
              rewrite Hb; simpl.
              case (ltR yb ya) eqn:Hi; 
              simpl.
              ***
                rewrite He, Hf, Hg; simpl.
                now (repeat rewrite eqr_reflexive).
              ***
                eapply ltr_false  in Ha;
                rewrite Ha; simpl.
                rewrite Hc; simpl.
                now (repeat rewrite eqr_reflexive).
            **
                eapply ltr_true_eqr_false in Hb.
                case (eqR xa xb) eqn:Hi; 
                simpl. eapply eqr_symmetric in Hi;
                rewrite Hi in Hb; congruence.
                eapply ltr_false in Ha.
                rewrite Ha; simpl.
                rewrite Hc; simpl.
                now (repeat rewrite eqr_reflexive).
            *
              eapply ltr_total in Ha, Hb.
              destruct Ha as [Ha | Ha];
              destruct Hb as [Hb | Hb].
              **
                pose proof (eqr_transitive _ _ _ Hb Ha) as Hh.
                eapply ltr_eqr_false in Hh.
                rewrite Hh in He.
                congruence.
              **
                rewrite Hc in Ha; congruence.
              **
                rewrite Hb; simpl.
                case (ltR yb ya) eqn:Hi; 
                simpl.
                ***
                  rewrite He, Hf, Hg; simpl.
                  now (repeat rewrite eqr_reflexive).
                ***
                  eapply ltr_false  in Ha;
                  rewrite Ha; simpl.
                  rewrite Hc; simpl.
                  now (repeat rewrite eqr_reflexive).
              **
                  eapply ltr_true_eqr_false in Hb.
                  case (eqR xa xb) eqn:Hi; 
                  simpl. eapply eqr_symmetric in Hi;
                  rewrite Hi in Hb; congruence.
                  eapply ltr_false in Ha.
                  rewrite Ha; simpl.
                  rewrite Hc; simpl.
                  now (repeat rewrite eqr_reflexive).
      ++
        eapply ltr_total in Ha, Hb.
        destruct Ha as [Ha | Ha];
        destruct Hb as [Hb | Hb].
        +++
          pose proof (eqr_transitive _ _ _ Hb Ha) as He.
          eapply ltr_eqr_false in He;
          rewrite He; simpl.
          rewrite (eqr_transitive _ _ _ Hb Ha); 
          simpl.
          case (ltR yc ya) eqn:Hf; simpl;
          rewrite Hb; simpl;
          eapply ltr_total in Hd;
          destruct Hd as [Hd | Hd].
          *
            assert (Hg : ltR yb ya = true).
            eapply  ltr_eqr.
            exact Hd.
            eapply eqr_reflexive.
            exact Hf.
            rewrite Hg; simpl.
            rewrite He; simpl.
            rewrite (eqr_transitive _ _ _ Hb Ha); simpl.
            rewrite Hf.
            now (repeat rewrite eqr_reflexive).
          *
            rewrite (ltr_transitive _ _ _ Hd Hf);
            simpl.
            rewrite He; simpl.
            rewrite (eqr_transitive _ _ _ Hb Ha); simpl.
            rewrite Hf.
            now (repeat rewrite eqr_reflexive).
          *
            rewrite (ltr_eqr_gen ya yb yc ya false Hd (eqr_reflexive ya) Hf).
            simpl. rewrite Hc; simpl. 
            assert (Hi : ltR xb xc = false).
            eapply ltr_eqr_gen.
            exact Hb.
            eapply eqr_reflexive.
            exact He.
            rewrite Hi; simpl.
            now (repeat rewrite eqr_reflexive).
          *
            case (ltR yb ya) eqn:Hg; 
            simpl.
            rewrite He; simpl.
            **
              rewrite (eqr_transitive _ _ _ Hb Ha); 
              simpl. rewrite Hf.
              now (repeat rewrite eqr_reflexive).
            **
              assert (Hi : ltR xb xc = false).
              eapply ltr_eqr_gen.
              exact Hb.
              eapply eqr_reflexive.
              exact He.
              rewrite Hi; simpl.
              rewrite Ha; simpl.
              eapply ltr_false in Hd.
              rewrite Hd.
              now (repeat rewrite eqr_reflexive).
        +++
          rewrite Hc in Ha; congruence.
        +++
          eapply ltr_false in Ha.
          assert (He : ltR xa xc = false).
          eapply ltr_eqr_gen.
          eapply eqr_symmetric in Hb.
          exact Hb.
          eapply eqr_reflexive.
          exact Ha.
          rewrite He; simpl.
          case (eqR xa xc) eqn:Hf.
          rewrite (eqr_transitive _ _ _  (eqr_symmetric _ _ Hb) Hf) in Hc;
          congruence.
          simpl.
          rewrite Hb; simpl.
          case (ltR yb ya) eqn:Hi; simpl.
          **
            rewrite He, Hf. simpl.
            now (repeat rewrite eqr_reflexive).
          **
            rewrite Ha, Hc; simpl.
            now (repeat rewrite eqr_reflexive).
        +++
          pose proof (ltr_transitive _ _ _ Ha Hb) as He.
          eapply ltr_false in He.
          rewrite He; simpl.
          pose proof (ltr_transitive _ _ _ Ha Hb) as Hf.
          eapply ltr_true_eqr_false in Hf.
          case (eqR xa xc) eqn:Hg.
          eapply eqr_symmetric in Hg;
          rewrite Hg in Hf; 
          congruence.
          simpl.
          eapply ltr_true_eqr_false in Hb.
          case (eqR xa xb) eqn:Hi.
          eapply eqr_symmetric in Hi;
          rewrite Hi in Hb; congruence.
          simpl.
          assert (Hj : ltR xb xc = false).
          eapply ltr_false in Ha;
          rewrite Ha; reflexivity.
          rewrite Hj; simpl.
          rewrite Hc; simpl.
          now (repeat rewrite eqr_reflexive).
  Qed.


  Theorem eqr_general : forall x y u v : R, eqR x u = true -> 
    eqR y v = true -> eqRR (x, y) (u, v) = true.
  Proof.
    intros [x | ] [y | ] [u | ] [v |]; 
    simpl; intros Ha Hb;
    try congruence;
    rewrite Ha; simpl;
    [assumption | reflexivity].
  Qed. 

  Theorem plus_commutative  : forall a b : RR, a + b =r= b + a = true.
  Proof.
    intros (xa, ya) (xb, yb); simpl.
    case (ltR xa xb) eqn:Ha; simpl.
    +
      assert (Hb : ltR xb xa = false).
      eapply ltr_false; exact Ha.
      rewrite Hb; simpl.
      eapply ltr_true_eqr_false in Ha.
      case (eqR xb xa) eqn:Hc.
      ++
        eapply eqr_symmetric in Hc;
        rewrite Hc in Ha;
        congruence.
      ++
        simpl; now (repeat rewrite eqr_reflexive).
    +
      eapply ltr_total in Ha.
      destruct Ha as [Ha | Ha].
      ++
        rewrite Ha; simpl.
        assert (Hb : ltR xb xa = false).
        eapply eqr_symmetric in Ha.
        eapply ltr_eqr_false in Ha.
        exact Ha.
        rewrite Hb; simpl.
        eapply eqr_symmetric in Ha;
        rewrite Ha; simpl.
        case (ltR yb ya) eqn:Hc.
        +++
          eapply ltr_false in Hc;
          rewrite Hc.
          eapply eqrr_reflexive.
        +++
          eapply ltr_total in Hc.
          destruct Hc as [Hc | Hc].
          *
            eapply eqr_symmetric in Hc.
            assert (Hd : ltR ya yb = false).
            eapply ltr_eqr_false in Hc.
            exact Hc. 
            rewrite Hd.
            eapply eqr_general;
            try assumption.
            eapply eqr_symmetric; 
            try assumption.
          *
            rewrite Hc.
            eapply eqrr_reflexive.
      ++
        assert (Hb : eqR xb xa = false).
        eapply ltr_true_eqr_false in Ha.
        exact Ha.
        assert (Hc : eqR xa xb = false).
        case (eqR xa xb) eqn:Hc.
        eapply eqr_symmetric in Hc.
        rewrite Hc in Hb; congruence.
        reflexivity.
        rewrite Hc; simpl.
        rewrite Ha, Hb. simpl.
        now (repeat rewrite eqr_reflexive).
  Qed.

  Theorem one_left_identity_mul  : forall r : RR, 1 * r =r= r = true.
  Proof.
    intros ([x |], [y |]); simpl;
    repeat rewrite PeanoNat.Nat.eqb_refl;
    reflexivity.
  Qed.

  Theorem one_right_identity_mul : forall r : RR, r * 1 =r= r = true.
  Proof.
    intros ([x |], [y |]); simpl;
    try rewrite PeanoNat.Nat.add_0_r;
    repeat rewrite PeanoNat.Nat.eqb_refl;
    reflexivity.
  Qed.
    




    
    



End Proofs.
  

