From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: order and semiring algebra over a bounded semiring
    Split out of the former monolithic SocialchoiceN.v. *)

Section SchulzeOrderN.

  Context {Node : FinType.type}.



  (** [bounded_add_idem] (a + a = a) is proved once, in PathN.v, and used
      throughout here.  It was duplicated in this file before the split. *)

  Lemma bounded_orel_refl {R : BoundedSemiring.type} (a : R) : a ≤ a.
  Proof. unfold Orel. apply bounded_add_idem. Qed.

  Lemma bounded_mul_orel_compat_r {R : BoundedSemiring.type} (a b c : R) :
    a ≤ b -> c * a ≤ c * b.
  Proof.
    unfold Orel. intros Hab.
    transitivity (c * (a + b)).
    - symmetry. apply (mulDl c a b).
    - apply (f_equal (fun t => mul c t)). exact Hab.
  Qed.

  Lemma bounded_mul_orel_compat_l {R : BoundedSemiring.type} (a b c : R) :
    a ≤ b -> a * c ≤ b * c.
  Proof.
    unfold Orel. intros Hab.
    transitivity ((a + b) * c).
    - symmetry. apply (mulDr a b c).
    - apply (f_equal (fun t => mul t c)). exact Hab.
  Qed.

  Lemma bounded_mul_lower_left {R : BoundedSemiring.type} (a b : R) : a * b ≤ a.
  Proof.
    unfold Orel.
    transitivity (a * b + a * 1).
    - apply (f_equal (fun t => a * b + t)). symmetry. apply mulr1.
    - transitivity (a * (b + 1)).
      + symmetry. apply (mulDl a b 1).
      + transitivity (a * 1).
        * apply (f_equal (fun t => a * t)). rewrite addC. apply (add_bound (s := R) b).
        * apply mulr1.
  Qed.

  Lemma bounded_mul_lower_right {R : BoundedSemiring.type} (a b : R) : a * b ≤ b.
  Proof.
    unfold Orel.
    transitivity (a * b + 1 * b).
    - apply (f_equal (fun t => a * b + t)). symmetry. apply mul1r.
    - transitivity ((a + 1) * b).
      + symmetry. apply (mulDr a 1 b).
      + transitivity (1 * b).
        * apply (f_equal (fun t => t * b)). rewrite addC. apply (add_bound (s := R) a).
        * apply mul1r.
  Qed.

  (** Commutativity is not an independent axiom of the classification: on a
      bounded semiring the meet property already forces it.  Both [a * b] and
      [b * a] are lower bounds of the pair by [bounded_mul_lower_left] and
      [bounded_mul_lower_right], the meet property makes each of them the
      greatest such, and a greatest lower bound is unique.  The consequence is
      that every result below whose hypotheses include the meet property may
      use commutativity for free; see [reversal_symmetry_O_level2]. *)
  Lemma mul_comm_of_meet {R : BoundedSemiring.type}
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) :
    forall a b : R, a * b = b * a.
  Proof.
    intros a b. apply orel_antisym.
    - apply H_meet_lower_bound.
      + apply bounded_mul_lower_right.
      + apply bounded_mul_lower_left.
    - apply H_meet_lower_bound.
      + apply bounded_mul_lower_right.
      + apply bounded_mul_lower_left.
  Qed.

  (** The structure theorem for bottleneck carriers, pointwise: on a carrier
      that is selective (so the natural order is a chain) addition returns
      the larger argument and, given the meet-lower-bound property,
      multiplication returns the smaller.  Together: + is the join (max) and
      * is the meet (min) of the chain.                                       *)
  Lemma structure_add_is_max {R : BoundedSemiring.type} (a b : R) :
    a ≤ b -> a + b = b /\ b + a = b.
  Proof.
    intro h. split; [exact h | rewrite addC; exact h].
  Qed.

  Lemma structure_mul_is_min {R : BoundedSemiring.type}
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b)
    (a b : R) :
    a ≤ b -> a * b = a /\ b * a = a.
  Proof.
    intro h. split; apply orel_antisym.
    - apply bounded_mul_lower_left.
    - apply H_meet_lower_bound; [apply bounded_orel_refl | exact h].
    - apply bounded_mul_lower_right.
    - apply H_meet_lower_bound; [exact h | apply bounded_orel_refl].
  Qed.

  (** If every term of a sum is ≤ v, then the whole sum is ≤ v. *)
  Lemma sum_orel_bound {R : Semiring.type} 
    (f : Node -> R) (v : R) :
    (forall x, (f x) ≤ v) -> (sum f) ≤ v.
  Proof.
    unfold Orel, sum.
    intro H.
    induction (@elements Node) as [|a l IH]; cbn.
    - apply add0r.
    - (* Goal: (f a + fold_right ... l) + v = v *)
      (** addA: (x+y)+z = x+(y+z) *)
      transitivity (f a + (fold_right (fun (x : Node) (y : R) => f x + y) 0 l + v)).
      + apply addA.
      + assert (Htmp : fold_right (fun (x : Node) (y : R) => f x + y) 0 l + v = v).
        { apply IH. }
        rewrite Htmp. apply (H a).
  Qed.

  (** If a ≤ c and b ≤ c then a+b ≤ c.  Works for any commutative monoid. *)
  Lemma add_orel_bound {R : CommutativeMonoid.type} (a b c : R) :
    a ≤ c -> b ≤ c -> (a + b) ≤ c.
  Proof.
    unfold Orel. intros Ha Hb.
    rewrite addA, Hb, Ha. reflexivity.
  Qed.

  (** [x < y] and [y ≤ z] give [x < z]. *)
  Lemma orel_lt_le_trans {R : CommutativeMonoid.type} (x y z : R) :
    x < y -> y ≤ z -> x < z.
  Proof.
    intros [Hxy_le Hxy_neq] Hyz. split.
    - exact (orel_trans _ _ _ Hxy_le Hyz).
    - intro Heq. apply Hxy_neq.
      apply orel_antisym; [exact Hxy_le | rewrite Heq; exact Hyz].
  Qed.

  (** Transitivity: x ≤ y and y < z implies x < z. *)
  Lemma orel_lt_trans {R : CommutativeMonoid.type} (x y z : R) :
    x ≤ y -> y < z -> x < z.
  Proof.
    intros Hxy [Hyz_le Hyz_neq]. split.
    - unfold Orel.
      red in Hxy. red in Hyz_le.
      rewrite <- Hyz_le at 1. (* z → y + z *)
      rewrite <- addA.        (* x + (y + z) → (x + y) + z *)
      rewrite Hxy.             (* x + y → y *)
      rewrite Hyz_le. reflexivity.
    - intro Heq. subst x. apply Hyz_neq.
      apply orel_antisym; assumption.
  Qed.

  Lemma bounded_plus_upper_left {R : BoundedSemiring.type} (a b : R) : a ≤ a + b.
  Proof.
    unfold Orel. rewrite <- addA. rewrite (bounded_add_idem a). reflexivity.
  Qed.

  Lemma orel_plus_upper_right {R : BoundedSemiring.type} (a b : R) : a ≤ b + a.
  Proof.
    unfold Orel.
    rewrite <- (addA a b a).
    rewrite (addC a b).
    rewrite (addA b a a).
    rewrite (bounded_add_idem a).
    reflexivity.
  Qed.

  
  (** In a bounded semiring, the diagonal of geom_sum is always 1. *)
  Lemma geom_sum_diag_one {R : BoundedSemiring.type}
    (M : @Matrix Node R) (n : nat) (A : Node) :
    geom_sum M n A A = 1.
  Proof.
    induction n as [|n IH]; cbn [geom_sum].
    - unfold I. destruct (fin_eq_dec A A) as [_|Hc]; [reflexivity | congruence].
    - unfold matrix_add. rewrite IH. apply (add_bound (s := R) (pow M (S n) A A)).
  Qed.

  (** * Selectivity: the closure invents no new values

      [Htotal] and [Hmeet] together — the pair already assumed by
      [prudence] and [minmax_beats], and satisfied by the max-min semiring
      of the Schulze instance — make both operations SELECTIVE: [x + y]
      and [x * y] each return one of their arguments.  So every entry of
      the closure is either a bound or the strength of an actual link.
      This is the algebraic content of the paper's habit of naming the
      critical link of a strongest path, e.g. in 4.2.1.

      Note what this does NOT give: the value being some link's strength
      says nothing about WHICH link, or that it lies on a path from [a] to
      [b].  Recovering that — and with it the paper's path-splitting
      arguments — needs the witness, not just the value. *)

  (** With a total order the meet of two elements is one of them. *)
  Lemma mul_selective {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x) (x y : R) :
    x * y = x \/ x * y = y.
  Proof.
    destruct (Htotal x y) as [Hc | Hc].
    - right. assert (Hyx : y ≤ x) by (unfold Orel; rewrite addC; exact Hc).
      exact (proj2 (Hmeet y x Hyx)).
    - left. exact (proj1 (Hmeet x y Hc)).
  Qed.

  (** A selective join over a list returns [0] or one of the summands. *)
  Lemma fold_selective {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (f : Node -> R) :
    forall l : list Node,
      fold_right (fun x acc => f x + acc) 0 l = 0 \/
      exists z, In z l /\ fold_right (fun x acc => f x + acc) 0 l = f z.
  Proof.
    induction l as [|a l IH]; cbn [fold_right].
    - left. reflexivity.
    - destruct (Htotal (f a) (fold_right (fun x acc => f x + acc) 0 l)) as [Hc | Hc].
      + right. exists a. split; [left; reflexivity | exact Hc].
      + destruct IH as [H0 | [z [Hz Hfz]]].
        * left. rewrite Hc. exact H0.
        * right. exists z. split; [right; exact Hz |]. rewrite Hc. exact Hfz.
  Qed.

  Lemma sum_selective {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (f : Node -> R) :
    sum f = 0 \/ exists z, sum f = f z.
  Proof.
    unfold sum.
    destruct (fold_selective Htotal f (@elements Node)) as [H0 | [z [_ Hz]]].
    - left. exact H0.
    - right. exists z. exact Hz.
  Qed.



  (** * Helper lemmas for the Pareto proofs *)

  (** If every element of a list is ≤ v, then the fold-right sum is ≤ v. *)
  Lemma fold_right_orel_bound {R : CommutativeMonoid.type} (l : list R) (v : R) :
    (forall x, In x l -> x ≤ v) ->
    fold_right (fun a b => a + b) (0 : R) l ≤ v.
  Proof.
    induction l as [|a l IH]; cbn; intros H.
    - unfold Orel. apply add0r.
    - apply add_orel_bound.
      + apply H. left; reflexivity.
      + apply IH. intros x Hx. apply H. right; exact Hx.
  Qed.

  (** When the order is total, a strict upper bound survives addition. *)
  Lemma add_lt_bound {R : CommutativeMonoid.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (a b v : R) :
    a < v -> b < v -> a + b < v.
  Proof.
    intros Ha Hb.
    destruct (Htotal a b) as [Hcase|Hcase]; rewrite Hcase; assumption.
  Qed.

  (** …and hence a finite sum of terms each strictly below [v] stays below [v]. *)
  Lemma fold_right_lt_bound {R : CommutativeMonoid.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (l : list R) (v : R) :
    0 < v ->
    (forall x, In x l -> x < v) ->
    fold_right (fun a b => a + b) (0 : R) l < v.
  Proof.
    intros H0 Hall. induction l as [|a l IH]; cbn [fold_right].
    - exact H0.
    - apply (add_lt_bound Htotal).
      + apply Hall. left; reflexivity.
      + apply IH. intros x Hx. apply Hall. right; exact Hx.
  Qed.








  (** Two-term join stays below a bound if both summands do (needs totality:
      without it, two incomparable elements can join to something exceeding
      both, as happens in a non-chain lattice). *)
  Lemma orel_lt_add_lt {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (a b c : R) :
    a < c -> b < c -> (a + b) < c.
  Proof.
    intros [Hale Hane] [Hble Hbne].
    destruct (Htotal a b) as [Hcase|Hcase]; rewrite Hcase; split; assumption.
  Qed.

  (** Finite sums stay strictly below a bound if every summand does
      (the bound [c] is arbitrary; this only needs totality, not
      boundedness at [c]). *)
  Lemma sum_lt_bound_if_all_lt {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (f : Node -> R) (c : R) :
    (forall z, f z < c) -> sum f < c.
  Proof.
    intros Hlt. unfold sum.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    assert (Hgen : forall (l : list Node), l <> [] ->
      fold_right (fun x acc => f x + acc) 0 l < c).
    { induction l as [|x l' IH]; intros Hne.
      - contradiction.
      - destruct l' as [|y l''].
        + cbn. rewrite addr0. apply Hlt.
        + apply orel_lt_add_lt; [exact Htotal | apply Hlt | apply IH; discriminate]. }
    apply Hgen.
    destruct (elements (s := Node)) as [|z l]; [simpl in Hlen; lia | discriminate].
  Qed.

  (** * Shared helpers for prudence (§4.9) and the MinMax set (§4.8) *)

  (** Every term of a finite sum lies below the sum. *)
  Lemma fold_right_in_le {R : BoundedSemiring.type}
    (f : Node -> R) (l : list Node) (x : Node) :
    In x l -> f x ≤ fold_right (fun a b => f a + b) (0 : R) l.
  Proof.
    induction l as [|a l IH]; cbn [fold_right]; [contradiction |].
    intros [Heq|Hin].
    - subst a. apply bounded_plus_upper_left.
    - exact (orel_trans _ _ _ (IH Hin) (orel_plus_upper_right _ _)).
  Qed.

  Lemma le_sum {R : BoundedSemiring.type} (f : Node -> R) (x : Node) :
    f x ≤ sum f.
  Proof.
    unfold sum. apply fold_right_in_le. apply elements_complete.
  Qed.

  (** [1] is the top of the natural order. *)
  Lemma le_one {R : BoundedSemiring.type} (x : R) : x ≤ 1.
  Proof. unfold Orel. rewrite addC. apply (add_bound (s := R) x). Qed.

  (** Order helpers available once the order is total. *)
  Lemma not_le_lt {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (x y : R) :
    ~ (x ≤ y) -> y < x.
  Proof.
    intro Hn. split.
    - destruct (Htotal x y) as [Hc|Hc].
      + unfold Orel. rewrite addC. exact Hc.
      + exfalso. exact (Hn Hc).
    - intro Heq. apply Hn. rewrite Heq. apply bounded_orel_refl.
  Qed.

  (** A product stays strictly above a bound that both factors clear — this
      is where multiplication has to be the meet. *)
  Lemma lt_mul {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x) (c x y : R) :
    c < x -> c < y -> c < x * y.
  Proof.
    intros Hx Hy. destruct (Htotal x y) as [Hc|Hc].
    - assert (Hyx : y ≤ x) by (unfold Orel; rewrite addC; exact Hc).
      destruct (Hmeet y x Hyx) as [_ Hxy]. rewrite Hxy. exact Hy.
    - destruct (Hmeet x y Hc) as [Hxy _]. rewrite Hxy. exact Hx.
  Qed.

End SchulzeOrderN.
