(* ========================================================================= *)
(*  Idempotent Semiring with Order                                           *)
(*                                                                           *)
(*  Typeclass-based version.  One `R : IdempotentSemiring.type` gives you    *)
(*  the carrier, operations, axioms, and the derived partial order Orel.     *)
(*  The order is the standard one: a ≤ b  :=  a + b = b.                     *)
(*                                                                           *)
(*  Unlike Orel.v (which uses boolean equality eqR), this file uses          *)
(*  Leibniz equality (=), so [rewrite] works natively — no setoid bridge     *)
(*  needed.                                                                  *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 RelationClasses Morphisms Ring_theory.
From HB Require Import structures.
From Semiring Require Import Structures.

Import SemiringNotations.

(* ========================================================================= *)
(*  Properties                                                               *)
(* ========================================================================= *)
Section Matrixdef. 

  Definition Matrix {Node : FinType.type} 
    {R : Semiring.type} := Node → Node → R.

End Matrixdef. 

Section OrelProps.

  Definition Orel {R : Semiring.type} (a b : R) : Prop := a + b = b.

  Local Infix "≤" := Orel (at level 70).

  (* ----------------------------------------------------------------------- *)
  (*  Orel is a partial order                                                *)
  (* ----------------------------------------------------------------------- *)

  Lemma orel_refl {R : IdempotentSemiring.type} : ∀ (a : R), a ≤ a.
  Proof. intro a. unfold Orel. apply add_idem. Qed.

  Lemma orel_trans {R : Semiring.type} : ∀ (a b c : R), a ≤ b → b ≤ c → a ≤ c.
  Proof.
    unfold Orel. intros a b c Hab Hbc.
    rewrite <- Hbc at 1.
    rewrite <- addA, Hab, Hbc.
    reflexivity.
  Qed.

  Lemma orel_antisym {R : Semiring.type} : ∀ (a b : R), a ≤ b → b ≤ a → a = b.
  Proof.
    unfold Orel. intros a b Hab Hba.
    rewrite <- Hab. rewrite addC. rewrite Hba. reflexivity.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Typeclass instances — enables [rewrite] and [setoid_rewrite] with ≤   *)
  (* ----------------------------------------------------------------------- *)

  #[export] Instance Orel_preorder {R : IdempotentSemiring.type} : 
    @PreOrder R Orel.
  Proof. split; [exact orel_refl | exact orel_trans]. Qed.


  #[export] Instance add_proper {R : Semiring.type} : 
    Proper (Orel ==> Orel ==> @Orel R) add.
  Proof.
    unfold Proper, respectful, Orel.
    intros a a' Ha b b' Hb.
    (* Goal: (a + b) + (a' + b') = a' + b' *)
    rewrite <- (addA (a + b) a' b').
    (* Goal: ((a + b) + a') + b' = a' + b' *)
    rewrite (addC (a + b) a').
    (* Goal: (a' + (a + b)) + b' = a' + b' *)
    rewrite <- (addA a' a b).
    (* Goal: ((a' + a) + b) + b' = a' + b' *)
    rewrite (addC a' a), Ha.
    (* Goal: (a' + b) + b' = a' + b' *)
    rewrite (addA a' b b').
    (* Goal: a' + (b + b') = a' + b' *)
    rewrite Hb.
    (* Goal: a' + b' = a' + b' *)
    reflexivity.
  Qed.

  #[export] Instance mul_proper {R : Semiring.type} : 
    Proper (Orel ==> Orel ==> @Orel R) mul.
  Proof.
    unfold Proper, respectful, Orel.
    intros a a' Ha b b' Hb.
    (* Goal: (a*b) + (a'*b') = a'*b' *)
    transitivity ((a * b) + ((a + a') * b')).
    { apply (f_equal (fun x => a * b + x * b')). symmetry. exact Ha. }
    transitivity ((a * b) + (a * b' + a' * b')).
    { apply (f_equal (fun x => a * b + x)). apply (mulDr a a' b'). }
    transitivity (((a * b) + (a * b')) + a' * b').
    { symmetry. apply addA. }
    transitivity (a * (b + b') + a' * b').
    { apply (f_equal (fun x => x + a' * b')). symmetry. apply (mulDl a b b'). }
    transitivity (a * b' + a' * b').
    { apply (f_equal (fun x => a * x + a' * b')). exact Hb. }
    transitivity (a' * b').
    { symmetry. rewrite <- Ha at 1. apply (mulDr a a' b'). }
    reflexivity.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Basic order-theoretic lemmas                                           *)
  (* ----------------------------------------------------------------------- *)

  Lemma zero_is_bottom {R : Semiring.type} : ∀ (a : R), 0 ≤ a.
  Proof. intro a. unfold Orel. apply add0r. Qed.

  (* Every element is ≤ itself plus something (adding only increases).        *)
  Lemma plus_upper_left {R : IdempotentSemiring.type} : ∀ (a b : R), a ≤ a + b.
  Proof.
    intros a b. unfold Orel.
    transitivity ((a + a) + b).
    - symmetry. apply addA.
    - apply (f_equal (fun x => x + b) (add_idem a)).
  Qed.

  Lemma plus_upper_right {R : IdempotentSemiring.type} : ∀ (a b : R), b ≤ a + b.
  Proof.
    intros a b. unfold Orel. rewrite addC, addA.
    apply (f_equal (fun x => a + x) (add_idem b)).
  Qed.

  

  (* ----------------------------------------------------------------------- *)
  (*  Compatibility lemmas (also derivable from Proper instances)             *)
  (* ----------------------------------------------------------------------- *)

  Lemma plus_orel_compat {R : IdempotentSemiring.type} : 
    ∀ (a b c : R), a ≤ b → a + c ≤ b + c.
  Proof.
    intros a b c H.
    apply (@add_proper R); [exact H | apply orel_refl].
  Qed.

  Lemma mul_orel_compat_l {R : IdempotentSemiring.type} : 
    ∀ (a b c : R), a ≤ b → a * c ≤ b * c.
  Proof.
    intros a b c H.
    apply mul_proper; [exact H | apply orel_refl].
  Qed.

  Lemma mul_orel_compat_r {R : IdempotentSemiring.type} : 
    ∀ (a b c : R), a ≤ b → c * a ≤ c * b.
  Proof.
    intros a b c H.
    apply mul_proper; [apply orel_refl | exact H].
  Qed.

  (* ----------------------------------------------------------------------- *)
  (*  Absorption / boundedness                                               *)
  (* ----------------------------------------------------------------------- *)

  (* If the semiring is bounded (1 absorbs everything: 1 + b = 1), then      *)
  (* multiplying by b can only decrease (or keep equal): a·b·c ≤ a·c.        *)
  Lemma path_weight_rel {R : BoundedSemiring.type} : 
    ∀ (a b c : R),
    a * b * c ≤ a * c.
  Proof.
    unfold Orel. intros a b c.
    (* Goal: (a * b * c) + (a * c) = a * c *)
    transitivity ((a * (b * c)) + (a * c)).
    - apply (f_equal (fun x => x + (a * c)) (mulA a b c)).
    - transitivity (a * ((b * c) + c)).
      + symmetry. apply mulDl.
      + transitivity (a * (c + (b * c))).
        * apply (f_equal (fun x => a * x) (addC (b * c) c)).
        * transitivity (a * ((1 * c) + (b * c))).
          { apply (f_equal (fun x => a * (x + (b * c)))).
            symmetry. apply (mul1r c). }
          transitivity (a * ((1 + b) * c)).
          { apply (f_equal (fun x => a * x)).
            symmetry. apply mulDr. }
          transitivity (a * (1 * c)).
          { apply (f_equal (fun x => a * (x * c)) (@add_bound _ b)). }
          apply (f_equal (fun x => a * x) (mul1r c)).
  Qed.

End OrelProps.
