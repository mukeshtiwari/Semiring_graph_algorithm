From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: transitivity of the beat relation, and its characterisation (4.1)
    Split out of the former monolithic SocialchoiceN.v. *)

Section TransitivityN.

  Context {Node : FinType.type}.


  (** * 4.1 Transitivity of Schulze beats — meet-semiring proof

      Schulze's §4.1 Claim ("The binary relation O, as defined in (2.2.1),
      is transitive"): premises (4.1.1) [ab ∈ O] and (4.1.2) [bc ∈ O] give
      the conclusion (4.1.3) [ac ∈ O].

      Same conclusion as [schulze_trans] (if [a] beats [b] and [b] beats [c]
      then [a] beats [c]), but replacing the strong normalisation hypothesis
      [H_pair_sum_one] with a meet-lower-bound axiom:

        H_meet_lower_bound : m ≤ a → m ≤ b → m ≤ a * b

      This axiom says that if [m] is a lower bound of both [a] and [b], then
      [m] is also a lower bound of their product [a * b].  Together with the
      bounded-semiring facts [a * b ≤ a] and [a * b ≤ b], this makes [*]
      into a greatest-lower-bound (meet) operation.
  *)
  Theorem schulze_trans_weaker_necessary {R : BoundedSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) :
    forall (M : @Matrix Node R) (a b c : Node),
      schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c.
  Proof.
    intros M a b c H_ab H_bc.
    unfold schulze_beats, beats in *.
    destruct H_ab as [H_ab_le H_ab_ne].   (* S b a ≤ S a b ∧ S b a ≠ S a b *)
    destruct H_bc as [H_bc_le H_bc_ne].   (* S c b ≤ S b c ∧ S c b ≠ S b c *)
    (** m := S a b * S b c
        m ≤ S a c by star_path_compose *)
    pose proof (star_path_compose M a b c) as Hm_Sac.
    (** H_total_order gives total preorder on Orel *)
    assert (H_total_orel : forall x y : R, x ≤ y \/ y ≤ x).
    { intros x y.
      destruct (H_total_order x y) as [Hcase | Hcase].
      - right. unfold Orel. rewrite addC. exact Hcase.
      - left. unfold Orel. exact Hcase. }
    (** Lemma: mat_star M a c ≤ mat_star M c a is impossible *)
    assert (H_not_ac_le_ca : ~ (mat_star M a c ≤ mat_star M c a)).
    { intro H_ac_le_ca.
      (** Then m ≤ S c a via Hm_Sac and H_ac_le_ca *)
      assert (Hm_Sca : mat_star M a b * mat_star M b c ≤ mat_star M c a).
      { eapply orel_trans; [exact Hm_Sac | exact H_ac_le_ca]. }
      (** Case split on S a b vs S b c *)
      destruct (H_total_orel (mat_star M a b) (mat_star M b c))
        as [Hab_le_Hbc | Hbc_le_Hab].
      - (* Case A: S a b ≤ S b c.  Then m = S a b. *)
        assert (Hm_eq_Sab : mat_star M a b * mat_star M b c = mat_star M a b).
        { apply orel_antisym.
          - apply (@bounded_mul_lower_left R (mat_star M a b) (mat_star M b c)).
          - apply H_meet_lower_bound.
            + apply (@bounded_orel_refl R (mat_star M a b)).
            + exact Hab_le_Hbc. }
        rewrite Hm_eq_Sab in Hm_Sca.             (* S a b ≤ S c a *)
        (** S b c ≥ S a b = m *)
        assert (H_Sbc_ge_m : mat_star M a b ≤ mat_star M b c).
        { rewrite <- Hm_eq_Sab.
          apply (@bounded_mul_lower_right R (mat_star M a b) (mat_star M b c)). }
        (** H_meet_lower_bound: m ≤ S b c and m ≤ S c a → m ≤ S b c * S c a *)
        assert (Hm_Sbc_Sca : mat_star M a b ≤
                             mat_star M b c * mat_star M c a).
        { apply H_meet_lower_bound; [exact H_Sbc_ge_m | exact Hm_Sca]. }
        (** star_path_compose: S b c * S c a ≤ S b a *)
        pose proof (star_path_compose M b c a) as H_comp.
        assert (Hm_Sba : mat_star M a b ≤ mat_star M b a).
        { eapply orel_trans; [exact Hm_Sbc_Sca | exact H_comp]. }
        (** Antisymmetry with S b a ≤ S a b from beats a b *)
        assert (Heq : mat_star M b a = mat_star M a b).
        { apply orel_antisym; [exact H_ab_le | exact Hm_Sba]. }
        exact (H_ab_ne Heq).
      - (* Case B: S b c ≤ S a b.  Then m = S b c. *)
        assert (Hm_eq_Sbc : mat_star M a b * mat_star M b c = mat_star M b c).
        { apply orel_antisym.
          - apply (@bounded_mul_lower_right R (mat_star M a b) (mat_star M b c)).
          - apply H_meet_lower_bound.
            + exact Hbc_le_Hab.
            + apply (@bounded_orel_refl R (mat_star M b c)). }
        rewrite Hm_eq_Sbc in Hm_Sca.             (* S b c ≤ S c a *)
        (** S a b ≥ S b c = m *)
        assert (H_Sab_ge_m : mat_star M b c ≤ mat_star M a b).
        { rewrite <- Hm_eq_Sbc.
          apply (@bounded_mul_lower_left R (mat_star M a b) (mat_star M b c)). }
        (** H_meet_lower_bound: m ≤ S c a and m ≤ S a b → m ≤ S c a * S a b *)
        assert (Hm_Sca_Sab : mat_star M b c ≤
                             mat_star M c a * mat_star M a b).
        { apply H_meet_lower_bound; [exact Hm_Sca | exact H_Sab_ge_m]. }
        pose proof (star_path_compose M c a b) as H_comp.
        assert (Hm_Scb : mat_star M b c ≤ mat_star M c b).
        { eapply orel_trans; [exact Hm_Sca_Sab | exact H_comp]. }
        assert (Heq : mat_star M c b = mat_star M b c).
        { apply orel_antisym; [exact H_bc_le | exact Hm_Scb]. }
        exact (H_bc_ne Heq). }
    (** Now: S a c ≤ S c a is impossible, so by total order, S c a ≤ S a c *)
    destruct (H_total_orel (mat_star M a c) (mat_star M c a))
      as [Hac_le_Sca | Hca_le_Sac].
    - exfalso. exact (H_not_ac_le_ca Hac_le_Sca).
    - split; [exact Hca_le_Sac |].
      intro Heq. apply H_not_ac_le_ca. rewrite Heq.
      apply (@bounded_orel_refl R (mat_star M a c)).
  Qed.


  Theorem schulze_trans_weaker_sufficient {R : BoundedSemiring.type} :
    (3 <= length (@elements Node))%nat ->
    (forall x y : R, {x = y} + {x <> y}) ->
    (forall (M : @Matrix Node R) a b c,
      schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c) ->
    (forall x y : R, x + y = x \/ x + y = y) /\
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    intros Hlen Hdec Htrans.
    destruct (three_distinct_nodes Hlen) as (X & Y & Z & HXY & HYZ & HXZ).
    split.
    - (* selectivity: otherwise x, y are incomparable, and the triangle with
         r := x * y makes the two X-Z closures tie *)
      intros x y.
      destruct (Hdec (x + y) x) as [Hx|Hx]; [left; exact Hx |].
      destruct (Hdec (x + y) y) as [Hy|Hy]; [right; exact Hy |].
      exfalso.
      assert (Hxy : ~ (x ≤ y)) by exact Hy.
      assert (Hyx : ~ (y ≤ x)).
      { intro h. apply Hx. unfold Orel in h. rewrite addC. exact h. }
      assert (K1 : y * (x * y) ≤ x)
        by exact (orel_trans _ _ _ (@bounded_mul_lower_right R y (x * y))
                    (@bounded_mul_lower_left R x y)).
      assert (K1' : y * (x * y) <> x).
      { intro h. apply Hxy. rewrite <- h.
        apply (@bounded_mul_lower_left R y (x * y)). }
      assert (K2 : (x * y) * x ≤ y)
        by exact (orel_trans _ _ _ (@bounded_mul_lower_left R (x * y) x)
                    (@bounded_mul_lower_right R x y)).
      assert (K2' : (x * y) * x <> y).
      { intro h. apply Hyx. rewrite <- h.
        apply (@bounded_mul_lower_right R (x * y) x). }
      destruct (tri_witness X Y Z HXY HYZ HXZ x y (x * y) K1 K1' K2 K2' Htrans)
        as [_ Hne].
      exact (Hne eq_refl).
    - (* meet lower bound: the triangle with (p, q, r) := (a, b, m) yields
         m ≤ a*b outright, provided the two links are strict.  Each way for
         a link to go slack collapses one of a, b onto m, and a re-chosen
         triangle then contradicts the assumption directly. *)
      intros m a b Hma Hmb.
      destruct (Hdec (m + a * b) (a * b)) as [H|H]; [exact H |].
      exfalso.
      assert (Hnle : ~ (m ≤ a * b)) by exact H.
      destruct (Hdec (b * m) a) as [E1|K1'].
      + (* b*m = a forces a = m, so the triangle (b, m, m) applies and its
           conclusion m <> b*m contradicts E1. *)
        assert (Ham : a = m).
        { apply orel_antisym; [rewrite <- E1;
            apply (@bounded_mul_lower_right R b m) | exact Hma]. }
        assert (Hmb' : m * b <> m).
        { intro h. apply Hnle. rewrite Ham, h. apply (@bounded_orel_refl R m). }
        assert (H1 : m * m ≤ b)
          by exact (orel_trans _ _ _ (@bounded_mul_lower_left R m m) Hmb).
        assert (H1' : m * m <> b).
        { intro h.
          assert (Hbm : b = m).
          { apply orel_antisym; [rewrite <- h;
              apply (@bounded_mul_lower_left R m m) | exact Hmb]. }
          apply Hmb'. rewrite Hbm, h. exact Hbm. }
        destruct (tri_witness X Y Z HXY HYZ HXZ b m m H1 H1'
                    (@bounded_mul_lower_left R m b) Hmb' Htrans) as [_ Hne].
        apply Hne. rewrite E1, Ham. reflexivity.
      + destruct (Hdec (m * a) b) as [E2|K2'].
        * (* dually: m*a = b forces b = m, and the triangle (m, a, m)
             contradicts E2. *)
          assert (Hbm : b = m).
          { apply orel_antisym; [rewrite <- E2;
              apply (@bounded_mul_lower_left R m a) | exact Hmb]. }
          assert (Ham' : a * m <> m).
          { intro h. apply Hnle. rewrite Hbm, h. apply (@bounded_orel_refl R m). }
          assert (H2 : m * m ≤ a)
            by exact (orel_trans _ _ _ (@bounded_mul_lower_left R m m) Hma).
          assert (H2' : m * m <> a).
          { intro h.
            assert (Ham : a = m).
            { apply orel_antisym; [rewrite <- h;
                apply (@bounded_mul_lower_left R m m) | exact Hma]. }
            apply Ham'. rewrite Ham, h. exact Ham. }
          destruct (tri_witness X Y Z HXY HYZ HXZ m a m
                      (@bounded_mul_lower_right R a m) Ham' H2 H2' Htrans)
            as [_ Hne].
          apply Hne. rewrite E2, Hbm. reflexivity.
        * (* both links strict: the triangle (a, b, m) gives m ≤ a*b. *)
          assert (K1 : b * m ≤ a)
            by exact (orel_trans _ _ _ (@bounded_mul_lower_right R b m) Hma).
          assert (K2 : m * a ≤ b)
            by exact (orel_trans _ _ _ (@bounded_mul_lower_left R m a) Hmb).
          destruct (tri_witness X Y Z HXY HYZ HXZ a b m K1 K1' K2 K2' Htrans)
            as [Hle _].
          exact (Hnle Hle).
  Qed.


  (** [Hdec] is needed only for the left-to-right direction: both conclusions
      are decidable statements, and deriving them from a refutation argument
      requires deciding them.  It is the same hypothesis [winner_exists_weaker]
      already carries, and holds in every concrete instance.
 
      Note that no commutativity of [*] is assumed: it is a CONSEQUENCE.  The
      right-hand side says [a * b] is the greatest lower bound of [a] and [b]
      (it is always a lower bound, by [bounded_mul_lower_left/right]), and a
      greatest lower bound is unique, so [a * b = b * a].                    *)
  Theorem transitivity_characterisation {R : BoundedSemiring.type} :
    (3 <= length (@elements Node))%nat ->
    (forall x y : R, {x = y} + {x <> y}) ->
    (forall (M : @Matrix Node R) (a b c : Node),
     schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c) <->
    (forall x y : R, x + y = x ∨ x + y = y) ∧
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    intros ha hdec.
    split; intros * hb *.
    + eapply  schulze_trans_weaker_sufficient;
    [exact ha | exact hdec | exact hb].
    + intros hc hd. destruct hb as (hbl & hbr).
      eapply schulze_trans_weaker_necessary; 
      try assumption;[exact hc | exact hd].
  Qed.

End TransitivityN.
