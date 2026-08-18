From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN
  ReversalsymmetryN MonotonicityN ParetoN CondorcetN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ======================================================== *)
(*  Schulze over a semiring: the Smith criterion (4.7.3/4) *)
(*  Split out of the former monolithic SocialchoiceN.v.    *)
(* ======================================================== *)

Section SmithN.

  Context {Node : FinType.type}.




  
  (** [smith_criterion], with the global [H_pair_sum_one] normalization
      replaced by a single shared threshold [c0] separating the two sides
      of the cut, rather than forcing every B1-to-B2 edge to equal the
      literal top [1]. This subsumes the theorem's own per-pair cut
      hypothesis (["forall a b, In a B1 -> In b B2 -> M b a < M a b"]),
      which follows immediately by chaining [M b a < c0 <= M a b] — so it
      is dropped as a separate premise here.
  *)
  (** No walk from [B2] into [B1] can reach the threshold: every such walk
      must eventually cross the boundary, and every crossing link is below
      [c].  This is the engine of both the Smith criterion and Smith-IIA. *)
  Lemma pow_from_B2_lt {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c) :
    forall n y, In y B2 -> forall x, In x B1 -> pow M n y x < c.
  Proof.
    induction n as [|n IH]; intros y Hy x Hx.
    - cbn [pow]. unfold I.
      destruct (fin_eq_dec y x) as [Heq|Hneq].
      + subst x. exfalso. apply (proj1 (H_partition y) Hx). exact Hy.
      + exact H0.
    - simpl. unfold matrix_mul.
      apply sum_lt_bound_if_all_lt; [exact H_total_order |].
      intro z.
      destruct (in_dec fin_eq_dec z B1) as [HzB1|HzB1'].
      + apply (orel_lt_trans (M y z * pow M n z x) (M y z) c).
        * apply bounded_mul_lower_left.
        * apply H_lt; assumption.
      + assert (HzB2 : In z B2).
        { destruct (in_dec fin_eq_dec z B2) as [Hz|Hz]; [exact Hz|].
          exfalso. apply HzB1'. apply (proj2 (H_partition z)). exact Hz. }
        apply (orel_lt_trans (M y z * pow M n z x) (pow M n z x) c).
        * apply bounded_mul_lower_right.
        * apply IH; assumption.
  Qed.

  (** Schulze (4.7.3): every member of [B1] beats every member of [B2].  The
      whole strength of the criterion lives here — no walk from [B2] into [B1]
      can rise to the threshold [c], while the direct link out of [B1] already
      clears it.  (4.7.4) below is then just "so no winner sits in [B2]". *)
  Theorem smith_beats {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y) :
    forall (B1 B2 : list Node),
      (forall (x : Node), In x B1 <-> ~ In x B2) ->
      (exists c : R,
        (forall a b, In a B1 -> In b B2 -> M b a < c) ∧
        (forall a b, In a B1 -> In b B2 -> c ≤ M a b)) ->
      forall a b, In a B1 -> In b B2 -> schulze_beats M a b.
  Proof.
    intros B1 B2 H_partition (c & H_lt & H_ge) a b Ha Hb.
    assert (H0_lt_c : (0 : R) < c).
    { apply (orel_lt_trans 0 (M b a) c).
      - apply zero_is_bottom.
      - apply H_lt; assumption. }
    pose proof (pow_from_B2_lt M H_total_order B1 B2 c H_partition H_lt
                  H0_lt_c) as H_pow_lt.
    unfold schulze_beats, beats.
    apply (orel_lt_le_trans (mat_star M b a) c (mat_star M a b)).
    - apply (mat_star_lt_bound H_total_order). intro n.
      apply H_pow_lt; assumption.
    - apply (orel_trans c (M a b) (mat_star M a b)).
      + apply H_ge; assumption.
      + apply link_le_mat_star.
  Qed.

  (** Schulze (4.7.4): [S ⊆ B1].  Immediate from (4.7.3) — a winner in [B2]
      would be beaten by any member of [B1], and [B1] is non-empty. *)
  Theorem smith_criterion_weaker {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y) :
    forall (B1 B2 : list Node), B1 <> [] ->
      (forall (x : Node), In x B1 <-> ~ In x B2) ->
      (exists c : R,
        (forall a b, In a B1 -> In b B2 -> M b a < c) ∧
        (forall a b, In a B1 -> In b B2 -> c ≤ M a b)) ->
      forall (w : Node), schulze_winner M w -> In w B1.
  Proof.
    intros B1 B2 H_B1_nonempty H_partition Hc w H_winner.
    destruct (in_dec fin_eq_dec w B1) as [Hin|Hnotin_B1]; [exact Hin|].
    destruct (in_dec fin_eq_dec w B2) as [Hw_B2|Hnotin_B2];
      [| apply H_partition in Hnotin_B2; contradiction].
    exfalso.
    destruct B1 as [|a0 B1']; [congruence|].
    assert (Ha0 : In a0 (a0 :: B1')) by (left; reflexivity).
    assert (Hne : a0 <> w).
    { intro Heq. subst w. apply (proj1 (H_partition a0) Ha0). exact Hw_B2. }
    exact (H_winner a0 Hne
             (smith_beats M H_total_order (a0 :: B1') B2 H_partition Hc
                a0 w Ha0 Hw_B2)).
  Qed.

End SmithN.
