(** * How atomic are the axioms of the hierarchy?

    Two of the conditions the hierarchy uses have simpler equivalent forms.

    - "A product lies below a factor" is boundedness, whichever factor one
      picks: each one-sided inequality is equivalent to [1 + a = 1] over a
      plain semiring.  So assuming [a * b <= b] directly is not a weaker
      starting point than boundedness.

    - Over a bounded semiring the meet property is exactly idempotence of
      multiplication, [x * x = x].

    The carrier witnesses showing the three axioms independent are in
    examples/Independence.v. *)

From Stdlib Require Import Utf8.
From HB Require Import structures.
From Semiring Require Import Structures OrelN SchulzeOrderN.
Import SemiringNotations.

Local Infix "≤" := Orel (at level 70).

Section Atomicity.

  Theorem bounded_iff_mul_le_right {R : Semiring.type} :
    (forall a : R, 1 + a = 1) <-> (forall a b : R, a * b ≤ b).
  Proof.
    split.
    - intros Hb a b. unfold Orel.
      assert (E : (a + 1) * b = a * b + 1 * b) by apply mulDr.
      rewrite mul1r in E. rewrite <- E, addC, Hb, mul1r. reflexivity.
    - intros H a. specialize (H a 1). unfold Orel in H.
      rewrite mulr1, addC in H. exact H.
  Qed.

  Theorem bounded_iff_mul_le_left {R : Semiring.type} :
    (forall a : R, 1 + a = 1) <-> (forall a b : R, a * b ≤ a).
  Proof.
    split.
    - intros Hb a b. unfold Orel.
      assert (E : a * (b + 1) = a * b + a * 1) by apply mulDl.
      rewrite mulr1 in E. rewrite <- E, addC, Hb, mulr1. reflexivity.
    - intros H b. specialize (H 1 b). unfold Orel in H.
      rewrite mul1r, addC in H. exact H.
  Qed.

  (** Over a bounded semiring the meet property is [x * x = x]. *)
  Theorem meet_iff_mul_idempotent {R : BoundedSemiring.type} :
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) <->
    (forall x : R, x * x = x).
  Proof.
    split.
    - intros Hmeet x. apply orel_antisym.
      + apply bounded_mul_lower_left.
      + apply Hmeet; apply bounded_orel_refl.
    - intros Hidem m a b Ha Hb.
      rewrite <- (Hidem m).
      eapply orel_trans.
      + apply bounded_mul_orel_compat_l. exact Ha.
      + apply bounded_mul_orel_compat_r. exact Hb.
  Qed.

End Atomicity.
