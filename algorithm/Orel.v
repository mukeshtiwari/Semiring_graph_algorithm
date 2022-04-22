
From Coq Require Import List Utf8
  Lia.
From CAS Require Import coq.common.compute
coq.eqv.properties coq.eqv.structures
coq.eqv.theory coq.sg.properties
coq.algorithm.Listprop.
Import ListNotations.

Section Def.

  Variables
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)
    (eqR  : brel R).

  Definition Orel (a b : R) : Prop := 
      eqR (plusR a b) a = true.

End Def.


Section Proofs.

  Variables
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR).

  Declare Scope Mat_scope.
  Delimit Scope Mat_scope with R.
  Bind Scope Mat_scope with R.
  Local Open Scope Mat_scope.


  Local Notation "0" := zeroR : Mat_scope.
  Local Notation "1" := oneR : Mat_scope.
  Local Infix "+" := plusR : Mat_scope.
  Local Infix "*" := mulR : Mat_scope.
  Local Infix "=r=" := eqR (at level 70) : Mat_scope.


  Variables 
    (* Semiring Axiom on R *)
    (zero_left_identity_plus  : forall r : R, 0 + r =r= r = true)
    (zero_right_identity_plus : forall r : R, r + 0 =r= r = true)
    (plus_associative : forall a b c : R, a + (b + c) =r= 
      (a + b) + c = true)
    (plus_commutative  : forall a b : R, a + b =r= b + a = true)
    (plus_idempotence : forall a, a + a =r= a = true)
    (zero_stable : forall a, 1 + a =r= 1 = true)
    (one_left_identity_mul  : forall r : R, 1 * r =r= r = true)
    (one_right_identity_mul : forall r : R, r * 1 =r= r = true)
    (mul_associative : forall a b c : R, a * (b * c) =r= 
      (a * b) * c = true)
    (left_distributive_mul_over_plus : forall a b c : R, 
      a * (b + c) =r= a * b + a * c = true)
    (right_distributive_mul_over_plus : forall a b c : R, 
      (a + b) * c =r= a * c + b * c = true)
    (zero_left_anhilator_mul  : forall a : R, 0 * a =r= 0 = true)
    (zero_right_anhilator_mul : forall a : R, a * 0 =r= 0 = true)
    (* end of axioms *)

    (* start of congruence relation *)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).
    (* end of congruence *)


  (* Orel is a partial order *)
  
  Lemma orel_refl : 
    forall a, Orel R plusR eqR a a.
  Proof using R eqR plusR plus_idempotence.
    unfold Orel; intros ?.
    apply plus_idempotence.
  Qed.

  Lemma orel_anti_sym : 
    forall a b : R, 
    Orel R plusR eqR a b -> 
    Orel R plusR eqR b a -> 
    a =r= b = true.
  Proof using R congrR eqR plusR 
  plus_commutative refR symR.
    unfold Orel; intros ? ? Hab Hba.
    assert (Ht : a =r= a + b = true).
    apply symR. exact Hab.
    rewrite <-Ht; clear Ht.
    apply congrR. apply refR.
    apply symR.
    rewrite <-Hba.
    apply congrR.
    apply plus_commutative.
    apply refR.
  Qed.

  Lemma orel_trans : 
    forall a b c : R, 
    Orel R plusR eqR a b -> 
    Orel R plusR eqR b c -> 
    Orel R plusR eqR a c.
  Proof using R congrP congrR 
  eqR plusR plus_associative refR symR.
    unfold Orel; intros ? ? ? Hab Hbc.
    assert (Ht : a + c =r= a + b + c = true).
    apply congrP. apply symR.
    exact Hab.
    apply refR.
    rewrite <-Ht; clear Ht.
    apply congrR. apply refR.
    apply symR.
    rewrite <-Hab.
    apply congrR.
    assert (Ht : a + b + c =r= a + (b + c) = true).
    apply symR. apply plus_associative.
    rewrite <-Ht; clear Ht.
    apply congrR. apply refR.
    apply congrP. apply refR.
    apply symR. exact Hbc.
    apply refR.
  Qed.

  (* end of Orel partial order proof *)
  

  Lemma neutral_abouve : 
    forall (a : R), Orel R plusR eqR  a 0.
  Proof using R eqR plusR zeroR 
    zero_right_identity_plus.
    intro a; unfold Orel.
    apply zero_right_identity_plus.
  Qed.


  Lemma a_b_a : 
    forall a b, Orel R plusR eqR  (a + b) a.
  Proof using R congrP congrR 
  eqR plusR plus_associative 
  plus_commutative plus_idempotence refR symR.
    unfold Orel; intros ? ?.
    assert (Ht : a + b + a =r= a + a + b = true).
    pose proof (plus_commutative (a + b) a) as Hw.
    rewrite <-Hw; clear Hw.
    apply congrR. 
    apply refR.
    apply symR, plus_associative.
    rewrite <-Ht; clear Ht.
    apply congrR. 
    apply refR.
    apply congrP. 
    apply symR.
    apply plus_idempotence.
    apply refR.
  Qed.


  Lemma a_b_b : 
    forall a b, Orel R plusR eqR  (a + b) b.
  Proof using R congrP congrR eqR plusR 
  plus_associative plus_idempotence refR symR.
    unfold Orel; intros ? ?.
    assert (Ht : a + b + b =r= a + (b + b) = true).
    apply symR, plus_associative.
    rewrite <-Ht; clear Ht.
    apply congrR. apply refR.
    apply congrP. apply refR.
    apply symR.
    rewrite plus_idempotence with (a :=b).
    reflexivity.
  Qed.


  Lemma plus_a_b_c : 
    forall a b c, 
    Orel R plusR eqR a b -> 
    Orel R plusR eqR (a + c) (b + c).
  Proof using R congrP congrR eqR 
  plusR plus_associative plus_commutative
  plus_idempotence refR symR.
    unfold Orel; intros ? ? ? Ho.
    assert (Ht : a + c + (b + c) =r= 
      a + (c + (b + c)) = true).
    apply symR. apply plus_associative.
    rewrite <-Ht; clear Ht.
    apply congrR.
    apply refR.
    assert (Ht : a + c =r= a + b + c = true).
    apply congrP. apply symR. exact Ho.
    apply refR. rewrite <-Ht; clear Ht.
    apply congrR. apply refR.
    apply symR.
    assert (Ht : a + b + c =r= a + b + (c + c) = true).
    apply congrP. apply refR. 
    apply symR. apply plus_idempotence.
    rewrite <-Ht; clear Ht.
    apply congrR. apply refR.
    apply symR. 
    assert (Ht : a + b + (c + c) =r= a + (b + (c + c)) = true).
    apply symR. apply plus_associative.
    rewrite <-Ht; clear Ht.
    apply congrR. apply refR.
    apply congrP. apply refR.
    assert (Ht : c + (b + c) =r= b + c + c = true).
    apply plus_commutative.
    rewrite <-Ht; clear Ht.
    apply congrR. apply refR.
    apply plus_associative.
  Qed.      


  Lemma mul_a_b_c : 
    forall a b c : R, 
    Orel R plusR eqR a b -> 
    Orel R plusR eqR (a * c) (b * c).
  Proof using R congrM congrR eqR mulR plusR refR
  right_distributive_mul_over_plus symR.
    unfold Orel; intros ? ? ? Ho.
    assert (Ht : a * c + b * c =r= (a + b) * c = true).
    apply symR.
    apply right_distributive_mul_over_plus.
    rewrite <-Ht; clear Ht.
    apply congrR. 
    apply refR.
    apply congrM. 
    apply symR.
    exact Ho.
    apply refR.
  Qed.


  Lemma path_weight_rel : 
    forall a b c : R,
    Orel R plusR eqR (a * c) (a * b * c).
  Proof using R congrM congrP congrR eqR 
  left_distributive_mul_over_plus mulR
  mul_associative oneR one_left_identity_mul plusR refR
  right_distributive_mul_over_plus symR zero_stable.
    unfold Orel; intros ? ? ?.
    assert (Ht : a * c + a * b * c =r= 
      a * c + a * (b * c) = true).
    apply congrP. 
    apply refR.
    apply symR. 
    apply mul_associative.
    rewrite <-Ht; 
    clear Ht. 
    apply congrR.
    apply refR.
    apply symR.
    assert (Ht : a * c + a * (b * c) =r= 
      a * (c + b * c) = true).
    apply symR.
    apply left_distributive_mul_over_plus.
    rewrite <-Ht; clear Ht.
    apply congrR. 
    apply refR.
    apply symR. 
    apply congrM.
    apply refR.
    assert (Ht : (1 * c + b * c) =r= 
      (1 + b) * c = true).
    apply symR.
    apply right_distributive_mul_over_plus.
    rewrite <-Ht; clear Ht.
    apply congrR.
    apply congrP.
    apply symR.
    apply one_left_identity_mul.
    apply refR.
    (* Now, I need 0-stable  *)
    apply symR.
    assert (Ht : (1 + b) * c =r= 
      1 * c = true).
    apply congrM.
    apply zero_stable.
    apply refR.
    rewrite <-Ht; clear Ht.
    apply congrR. 
    apply refR.
    apply symR.
    apply one_left_identity_mul.
  Qed.

End Proofs.

  
     

  

