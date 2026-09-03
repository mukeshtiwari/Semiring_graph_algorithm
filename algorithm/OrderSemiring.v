(** * Building semirings from a totally ordered carrier

    A recurring pattern in this development: the carrier comes with a total
    order, addition is "pick the better of the two", and multiplication is
    some composition operation.  This file isolates exactly what has to be
    checked in that situation.

    The single obligation is that multiplication is MONOTONE in the order;
    both distributive laws then follow, and the whole additive commutative
    monoid comes for free from the order axioms alone.

    This is the abstract form of an argument carried out by hand for the
    widest-shortest-path semiring in examples/WidestShortestPath.v.  The
    naive encoding rejected at the top of that file fails precisely because
    monotonicity fails: multiplying by a saturated "no path" value leaves
    the lexicographic tiebreaker live, so it can reorder the results.

    Note which hypothesis does the work.  [le_antisym] is with respect to
    Leibniz equality, so an order that merely ranks elements up to an
    equivalence (Schulze's strict weak orders on vote-count pairs, where
    every pairwise tie is equivalent) does not qualify until the equivalence
    classes have been collapsed to canonical representatives. *)

From Stdlib Require Import Utf8.

Section OrderMax.

  Context {A : Type} (le : A -> A -> bool).

  (** Addition: the maximum under [le]. *)
  Definition add_max (u v : A) : A := if le v u then u else v.

  Hypothesis le_refl    : forall a, le a a = true.
  Hypothesis le_trans   : forall a b c, le a b = true -> le b c = true -> le a c = true.
  Hypothesis le_antisym : forall a b, le a b = true -> le b a = true -> a = b.
  Hypothesis le_total   : forall a b, le a b = true \/ le b a = true.

  (** ** [add_max] computes the maximum *)

  Lemma add_max_r : forall u v, le u v = true -> add_max u v = v.
  Proof.
    intros u v Huv. unfold add_max. destruct (le v u) eqn:Hvu.
    - exact (le_antisym u v Huv Hvu).
    - reflexivity.
  Qed.

  Lemma add_max_l : forall u v, le v u = true -> add_max u v = u.
  Proof. intros u v Hvu. unfold add_max. rewrite Hvu. reflexivity. Qed.

  (** ** The additive commutative monoid, from the order axioms alone *)

  Lemma add_max_idem : forall u, add_max u u = u.
  Proof. intro u. unfold add_max. destruct (le u u); reflexivity. Qed.

  Lemma add_max_comm : forall u v, add_max u v = add_max v u.
  Proof.
    intros u v. unfold add_max.
    destruct (le v u) eqn:Hvu; destruct (le u v) eqn:Huv.
    - exact (le_antisym u v Huv Hvu).
    - reflexivity.
    - reflexivity.
    - destruct (le_total u v) as [H|H]; congruence.
  Qed.

  Lemma add_max_assoc : forall u v w,
    add_max (add_max u v) w = add_max u (add_max v w).
  Proof.
    intros u v w.
    destruct (le_total u v) as [Huv|Hvu]; destruct (le_total v w) as [Hvw|Hwv].
    - rewrite (add_max_r u v Huv), (add_max_r v w Hvw).
      symmetry. exact (add_max_r u w (le_trans u v w Huv Hvw)).
    - rewrite (add_max_r u v Huv), (add_max_l v w Hwv).
      symmetry. exact (add_max_r u v Huv).
    - rewrite (add_max_l u v Hvu), (add_max_r v w Hvw). reflexivity.
    - rewrite (add_max_l u v Hvu), (add_max_l v w Hwv).
      rewrite (add_max_l u w (le_trans w v u Hwv Hvu)).
      symmetry. exact (add_max_l u v Hvu).
  Qed.

  (** A least element is the additive identity. *)
  Lemma add_max_bot_l (bot : A) (Hbot : forall a, le bot a = true) :
    forall a, add_max bot a = a.
  Proof. intro a. exact (add_max_r bot a (Hbot a)). Qed.

  Lemma add_max_bot_r (bot : A) (Hbot : forall a, le bot a = true) :
    forall a, add_max a bot = a.
  Proof. intro a. exact (add_max_l a bot (Hbot a)). Qed.

  (** A greatest element absorbs, which is [add_bound] for a bounded semiring. *)
  Lemma add_max_top_l (top : A) (Htop : forall a, le a top = true) :
    forall a, add_max top a = top.
  Proof. intro a. exact (add_max_l top a (Htop a)). Qed.

  (** ** Distributivity, from monotonicity of multiplication *)

  Section Distributivity.

    Context (mul : A -> A -> A).

    Hypothesis mul_mono_l :
      forall a b c, le a b = true -> le (mul a c) (mul b c) = true.
    Hypothesis mul_mono_r :
      forall a b c, le b c = true -> le (mul a b) (mul a c) = true.

    Theorem mul_add_max_distr_l : forall a b c,
      mul a (add_max b c) = add_max (mul a b) (mul a c).
    Proof.
      intros a b c.
      destruct (le_total b c) as [Hbc|Hcb].
      - rewrite (add_max_r b c Hbc).
        symmetry. exact (add_max_r (mul a b) (mul a c) (mul_mono_r a b c Hbc)).
      - rewrite (add_max_l b c Hcb).
        symmetry. exact (add_max_l (mul a b) (mul a c) (mul_mono_r a c b Hcb)).
    Qed.

    Theorem mul_add_max_distr_r : forall a b c,
      mul (add_max a b) c = add_max (mul a c) (mul b c).
    Proof.
      intros a b c.
      destruct (le_total a b) as [Hab|Hba].
      - rewrite (add_max_r a b Hab).
        symmetry. exact (add_max_r (mul a c) (mul b c) (mul_mono_l a b c Hab)).
      - rewrite (add_max_l a b Hba).
        symmetry. exact (add_max_l (mul a c) (mul b c) (mul_mono_l b a c Hba)).
    Qed.

  End Distributivity.

  (** ** The meet is always monotone

      So when multiplication is the minimum of the same order — the
      "strength of a path is its weakest link" reading — distributivity
      is automatic and nothing has to be checked.  This is the case for
      every one of Schulze's link-strength measures, and it is what
      separates them from the widest-shortest-path encoding, where
      multiplication acts component-wise instead. *)

  Definition meet (u v : A) : A := if le u v then u else v.

  Lemma meet_mono_r : forall a b c,
    le b c = true -> le (meet a b) (meet a c) = true.
  Proof.
    intros a b c Hbc. unfold meet.
    destruct (le a b) eqn:Hab; destruct (le a c) eqn:Hac.
    - apply le_refl.
    - exfalso. rewrite (le_trans a b c Hab Hbc) in Hac. discriminate.
    - destruct (le_total b a) as [Hba|Hab']; [exact Hba | congruence].
    - exact Hbc.
  Qed.

  Lemma meet_mono_l : forall a b c,
    le a b = true -> le (meet a c) (meet b c) = true.
  Proof.
    intros a b c Hab. unfold meet.
    destruct (le a c) eqn:Hac; destruct (le b c) eqn:Hbc.
    - exact Hab.
    - exact Hac.
    - destruct (le_total c a) as [Hca|Hac'];
        [exact (le_trans c a b Hca Hab) | congruence].
    - apply le_refl.
  Qed.

  Corollary meet_add_max_distr_l : forall a b c,
    meet a (add_max b c) = add_max (meet a b) (meet a c).
  Proof. exact (mul_add_max_distr_l meet meet_mono_r). Qed.

  Corollary meet_add_max_distr_r : forall a b c,
    meet (add_max a b) c = add_max (meet a c) (meet b c).
  Proof. exact (mul_add_max_distr_r meet meet_mono_l). Qed.

  (** ** [meet] as the multiplicative structure

      Dual to the [add_max] laws above, and together with the two
      distributivity corollaries these are exactly the obligations of a
      bounded commutative semiring with + = join and * = meet. *)

  Lemma meet_l : forall u v, le u v = true -> meet u v = u.
  Proof. intros u v Huv. unfold meet. rewrite Huv. reflexivity. Qed.

  Lemma meet_r : forall u v, le v u = true -> meet u v = v.
  Proof.
    intros u v Hvu. unfold meet. destruct (le u v) eqn:Huv.
    - exact (le_antisym u v Huv Hvu).
    - reflexivity.
  Qed.

  Lemma meet_comm : forall u v, meet u v = meet v u.
  Proof.
    intros u v. unfold meet.
    destruct (le u v) eqn:Huv; destruct (le v u) eqn:Hvu.
    - exact (le_antisym u v Huv Hvu).
    - reflexivity.
    - reflexivity.
    - destruct (le_total u v) as [H|H]; congruence.
  Qed.

  Lemma meet_assoc : forall u v w, meet (meet u v) w = meet u (meet v w).
  Proof.
    intros u v w.
    destruct (le_total u v) as [Huv|Hvu]; destruct (le_total v w) as [Hvw|Hwv].
    - rewrite (meet_l u v Huv), (meet_l v w Hvw).
      rewrite (meet_l u w (le_trans u v w Huv Hvw)), (meet_l u v Huv).
      reflexivity.
    - rewrite (meet_l u v Huv), (meet_r v w Hwv). reflexivity.
    - rewrite (meet_r u v Hvu), (meet_l v w Hvw).
      symmetry. exact (meet_r u v Hvu).
    - rewrite (meet_r u v Hvu), (meet_r v w Hwv).
      rewrite (meet_r u w (le_trans w v u Hwv Hvu)). reflexivity.
  Qed.

  (** A greatest element is the multiplicative identity. *)
  Lemma meet_top_l (top : A) (Htop : forall a, le a top = true) :
    forall a, meet top a = a.
  Proof. intro a. exact (meet_r top a (Htop a)). Qed.

  Lemma meet_top_r (top : A) (Htop : forall a, le a top = true) :
    forall a, meet a top = a.
  Proof. intro a. exact (meet_l a top (Htop a)). Qed.

  (** A least element is the multiplicative annihilator. *)
  Lemma meet_bot_l (bot : A) (Hbot : forall a, le bot a = true) :
    forall a, meet bot a = bot.
  Proof. intro a. exact (meet_l bot a (Hbot a)). Qed.

  Lemma meet_bot_r (bot : A) (Hbot : forall a, le bot a = true) :
    forall a, meet a bot = bot.
  Proof. intro a. exact (meet_r a bot (Hbot a)). Qed.

End OrderMax.
