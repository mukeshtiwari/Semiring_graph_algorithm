From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN
  ReversalsymmetryN MonotonicityN ParetoN CondorcetN
  SmithN PrudenceN MinMaxN NeutralityN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: Smith-IIA in isolation form (4.7.5a), and the isolate operator
    Split out of the former monolithic SocialchoiceN.v. *)

Section IsolateN.

  Context {Node : FinType.type}.


  (** Isolating [d]: cut every link into and out of it. *)
  Definition isolate {R : Semiring.type} (M : @Matrix Node R) (d : Node)
    : @Matrix Node R :=
    fun x y => if fin_eq_dec x d then 0
               else if fin_eq_dec y d then 0 else M x y.

  Lemma isolate_off {R : Semiring.type} (M : @Matrix Node R) (d x y : Node) :
    x <> d -> y <> d -> isolate M d x y = M x y.
  Proof.
    intros Hx Hy. unfold isolate.
    destruct (fin_eq_dec x d); [contradiction |].
    destruct (fin_eq_dec y d); [contradiction | reflexivity].
  Qed.

  Lemma isolate_le {R : BoundedSemiring.type} (M : @Matrix Node R) (d x y : Node) :
    isolate M d x y ≤ M x y.
  Proof.
    unfold isolate.
    destruct (fin_eq_dec x d); [apply zero_is_bottom |].
    destruct (fin_eq_dec y d); [apply zero_is_bottom | apply bounded_orel_refl].
  Qed.

  (** Isolation only removes walks, so it can only lower the closure. *)
  Lemma mat_star_isolate_le {R : BoundedSemiring.type}
    (M : @Matrix Node R) (d x y : Node) :
    mat_star (isolate M d) x y ≤ mat_star M x y.
  Proof.
    unfold mat_star. apply geom_sum_monotone. intros i j. apply isolate_le.
  Qed.

  (** Every walk into [B1] is either matched by an isolated walk, or is too
      weak to matter — because reaching [d ∈ B2] commits it to a crossing
      back into [B1], and every crossing link is below [c]. *)
  Lemma pow_isolate_dichotomy {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R) (d : Node)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c) (Hd : In d B2) (f : Node) (Hf : In f B1) :
    forall n x, x <> d ->
      pow M n x f ≤ mat_star (isolate M d) x f \/ pow M n x f < c.
  Proof.
    induction n as [|k IH]; intros x Hx.
    - left. cbn [pow]. unfold I.
      destruct (fin_eq_dec x f) as [Heq|_].
      + subst f. unfold mat_star. rewrite geom_sum_diag_one.
        apply bounded_orel_refl.
      + apply zero_is_bottom.
    - simpl. unfold matrix_mul.
      destruct (sum_selective H_total_order
                  (fun z => M x z * pow M k z f)) as [H0eq | [z Hz]].
      + left. rewrite H0eq. apply zero_is_bottom.
      + rewrite Hz. cbv beta.
        destruct (fin_eq_dec z d) as [Hzd | Hzd].
        * subst z. right.
          apply (orel_lt_trans (M x d * pow M k d f) (pow M k d f) c).
          -- apply bounded_mul_lower_right.
          -- exact (pow_from_B2_lt M H_total_order B1 B2 c H_partition H_lt H0
                      k d Hd f Hf).
        * destruct (IH z Hzd) as [Hle | Hlt].
          -- left.
             rewrite <- (isolate_off M d x z Hx Hzd).
             eapply orel_trans;
               [apply (bounded_mul_orel_compat_r _ _ _ Hle) |].
             eapply orel_trans;
               [apply (bounded_mul_orel_compat_l _ _ _
                         (link_le_mat_star (isolate M d) x z)) |].
             apply star_path_compose.
          -- right.
             apply (orel_lt_trans (M x z * pow M k z f) (pow M k z f) c).
             ++ apply bounded_mul_lower_right.
             ++ exact Hlt.
  Qed.

  (** A closure entry between two members of [B1] that already clears the
      threshold is untouched by isolating [d]: its strongest walk cannot have
      gone through [B2]. *)
  Lemma mat_star_isolate_preserved {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htotal : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R) (d : Node)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c) (Hd : In d B2)
    (e f : Node) (He : In e B1) (Hf : In f B1) (Hc : c ≤ mat_star M e f) :
    mat_star M e f = mat_star (isolate M d) e f.
  Proof.
    apply orel_antisym; [| apply mat_star_isolate_le].
    assert (Hed : e <> d).
    { intro Heq. subst e. exact (proj1 (H_partition d) He Hd). }
    destruct (geom_sum_selective Htotal M (@kleene_exp Node) e f) as [k [Hk Heq]].
    destruct (pow_isolate_dichotomy M Htotal B1 B2 c d H_partition H_lt H0 Hd
                f Hf k e Hed) as [Hle | Hlt].
    - unfold mat_star. rewrite Heq. exact Hle.
    - exfalso. destruct Hlt as [Hlt_le Hlt_ne]. apply Hlt_ne.
      apply orel_antisym; [exact Hlt_le |].
      unfold mat_star in Hc. rewrite Heq in Hc. exact Hc.
  Qed.

  (** ** Smith-IIA (4.7.5a) — isolation rather than removal

      The paper compares the method before and after REMOVING a weak
      alternative [d ∈ B2].  Removal is not expressible here: [sum] folds
      over [elements], the whole [FinType] enumeration, so [matrix_mul],
      [pow], [geom_sum], [mat_star] and [kleene_exp] are all tied to one
      fixed alternative set, and there is no closure over a subset to
      write [P_new] with.

      What is expressible is ISOLATION: cut every link into and out of
      [d], leaving the node in place.  [smith_iia_isolate] then says the
      relation O restricted to [B1] is unchanged — the content of
      (4.7.5)(a).  Two caveats, both real:

      - It needs [Hsep], which the paper gets from (2.1.2): between two
        distinct alternatives the stronger direction is at least a tie,
        hence clears the threshold.  The Smith hypotheses alone relate
        only B1-to-B2 pairs, so this has to be assumed.

      - (4.7.5)(b) [S_old = S_new] does NOT transfer to isolation.  An
        isolated [d] has every link at [0], so nobody beats it and it
        becomes a spurious winner — an artefact of leaving the node in
        place.  Only removal gets (b) right. *)

  (** Smith-IIA (4.7.5)(a), in the isolation reading: a weak alternative has
      no bearing on how the strong ones compare. *)
  Theorem smith_iia_isolate {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htotal : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R) (d : Node)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c) (Hd : In d B2)
    (Hsep : forall x y : Node, x <> y -> c ≤ M x y + M y x) :
    forall e f, In e B1 -> In f B1 ->
      (schulze_beats M e f <-> schulze_beats (isolate M d) e f).
  Proof.
    intros e f He Hf.
    assert (Hed : e <> d).
    { intro Heq. subst e. exact (proj1 (H_partition d) He Hd). }
    assert (Hfd : f <> d).
    { intro Heq. subst f. exact (proj1 (H_partition d) Hf Hd). }
    (** a closure entry that dominates its converse already clears c *)
    assert (Hclears : forall x y, x <> y ->
              mat_star M y x ≤ mat_star M x y -> c ≤ mat_star M x y).
    { intros x y Hxy Hdom.
      eapply orel_trans; [exact (Hsep x y Hxy) |].
      apply add_orel_bound.
      - apply link_le_mat_star.
      - eapply orel_trans; [apply link_le_mat_star | exact Hdom]. }
    split.
    - intros [Hle Hne].
      assert (Hef_ne : e <> f).
      { intro Heq. subst f. apply Hne. reflexivity. }
      pose proof (Hclears e f Hef_ne Hle) as Hc.
      pose proof (mat_star_isolate_preserved M Htotal B1 B2 c d H_partition
                    H_lt H0 Hd e f He Hf Hc) as Hef.
      split.
      + eapply orel_trans; [apply mat_star_isolate_le |].
        eapply orel_trans; [exact Hle |]. rewrite Hef. apply bounded_orel_refl.
      + intro Heq0.
        apply Hne. apply orel_antisym; [exact Hle |].
        rewrite Hef, <- Heq0. apply mat_star_isolate_le.
    - intros [Hle' Hne'].
      assert (Hef_ne : e <> f).
      { intro Heq. subst f. apply Hne'. reflexivity. }
      assert (Hc' : c ≤ mat_star (isolate M d) e f).
      { eapply orel_trans; [exact (Hsep e f Hef_ne) |].
        apply add_orel_bound.
        - rewrite <- (isolate_off M d e f Hed Hfd). apply link_le_mat_star.
        - eapply orel_trans; [| exact Hle'].
          rewrite <- (isolate_off M d f e Hfd Hed). apply link_le_mat_star. }
      assert (Hc : c ≤ mat_star M e f)
        by (eapply orel_trans; [exact Hc' | apply mat_star_isolate_le]).
      pose proof (mat_star_isolate_preserved M Htotal B1 B2 c d H_partition
                    H_lt H0 Hd e f He Hf Hc) as Hef.
      (** were the converse also above c it would be preserved too, forcing a
          tie in the isolated profile *)
      assert (Hno_converse : ~ (mat_star M e f ≤ mat_star M f e)).
      { intro Hbad.
        assert (Hcfe : c ≤ mat_star M f e)
          by (eapply orel_trans; [exact Hc | exact Hbad]).
        pose proof (mat_star_isolate_preserved M Htotal B1 B2 c d H_partition
                      H_lt H0 Hd f e Hf He Hcfe) as Hfe.
        apply Hne'. apply orel_antisym; [exact Hle' |].
        rewrite <- Hef, <- Hfe. exact Hbad. }
      split.
      + destruct (Htotal (mat_star M f e) (mat_star M e f)) as [Hc1 | Hc1].
        * exfalso. apply Hno_converse. unfold Orel. rewrite addC. exact Hc1.
        * exact Hc1.
      + intro Heq0. apply Hno_converse.
        rewrite Heq0. apply bounded_orel_refl.
  Qed.


  (** ** Removing a strong alternative (Schulze 4.7.6)

      The mirror of the block above: [d] now lies in [B1], and the
      relation left untouched is the one on [B2].  The dichotomy is
      simpler than for a weak [d]: a walk out of [B2] that enters [B1]
      at all is already below [c] at its first crossing link, so the
      crossing is detected at the head edge and no analogue of
      [pow_from_B2_lt] is needed. *)

  (** Every walk out of [B2] is either matched by an isolated walk, or is
      too weak to matter — entering [B1] costs a crossing link below [c]. *)
  Lemma pow_isolate_strong_dichotomy {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R) (d : Node)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (Hd : In d B1) (f : Node) :
    forall n x, In x B2 ->
      pow M n x f ≤ mat_star (isolate M d) x f \/ pow M n x f < c.
  Proof.
    induction n as [|k IH]; intros x Hx.
    - left. cbn [pow]. unfold I.
      destruct (fin_eq_dec x f) as [Heq|_].
      + subst f. unfold mat_star. rewrite geom_sum_diag_one.
        apply bounded_orel_refl.
      + apply zero_is_bottom.
    - simpl. unfold matrix_mul.
      destruct (sum_selective H_total_order
                  (fun z => M x z * pow M k z f)) as [H0eq | [z Hz]].
      + left. rewrite H0eq. apply zero_is_bottom.
      + rewrite Hz. cbv beta.
        destruct (in_dec fin_eq_dec z B1) as [HzB1 | HzB1].
        * (* the head edge crosses into [B1] and is below the threshold *)
          right.
          apply (orel_lt_trans (M x z * pow M k z f) (M x z) c).
          -- apply bounded_mul_lower_left.
          -- exact (H_lt z x HzB1 Hx).
        * (* still in [B2]: the head edge survives isolation, recurse *)
          assert (HzB2 : In z B2).
          { destruct (in_dec fin_eq_dec z B2) as [Hz2|Hz2]; [exact Hz2|].
            exfalso. apply HzB1. apply (proj2 (H_partition z)). exact Hz2. }
          assert (Hxd : x <> d).
          { intro Heq. subst x. exact (proj1 (H_partition d) Hd Hx). }
          assert (Hzd : z <> d).
          { intro Heq. subst z. exact (proj1 (H_partition d) Hd HzB2). }
          destruct (IH z HzB2) as [Hle | Hlt].
          -- left.
             rewrite <- (isolate_off M d x z Hxd Hzd).
             eapply orel_trans;
               [apply (bounded_mul_orel_compat_r _ _ _ Hle) |].
             eapply orel_trans;
               [apply (bounded_mul_orel_compat_l _ _ _
                         (link_le_mat_star (isolate M d) x z)) |].
             apply star_path_compose.
          -- right.
             apply (orel_lt_trans (M x z * pow M k z f) (pow M k z f) c).
             ++ apply bounded_mul_lower_right.
             ++ exact Hlt.
  Qed.

  (** A closure entry out of [B2] that already clears the threshold is
      untouched by isolating a strong [d]: its strongest walk cannot have
      entered [B1]. *)
  Lemma mat_star_isolate_strong_preserved {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htotal : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R) (d : Node)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (Hd : In d B1)
    (e f : Node) (He : In e B2) (Hc : c ≤ mat_star M e f) :
    mat_star M e f = mat_star (isolate M d) e f.
  Proof.
    apply orel_antisym; [| apply mat_star_isolate_le].
    destruct (geom_sum_selective Htotal M (@kleene_exp Node) e f) as [k [Hk Heq]].
    destruct (pow_isolate_strong_dichotomy M Htotal B1 B2 c d H_partition H_lt Hd
                f k e He) as [Hle | Hlt].
    - unfold mat_star. rewrite Heq. exact Hle.
    - exfalso. destruct Hlt as [Hlt_le Hlt_ne]. apply Hlt_ne.
      apply orel_antisym; [exact Hlt_le |].
      unfold mat_star in Hc. rewrite Heq in Hc. exact Hc.
  Qed.

  (** Smith-IIA (4.7.6), in the isolation reading: a strong alternative has
      no bearing on how the weak ones compare among themselves. *)
  Theorem smith_iia_isolate_strong {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htotal : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R) (d : Node)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (Hd : In d B1)
    (Hsep : forall x y : Node, x <> y -> c ≤ M x y + M y x) :
    forall e f, In e B2 -> In f B2 ->
      (schulze_beats M e f <-> schulze_beats (isolate M d) e f).
  Proof.
    intros e f He Hf.
    assert (Hed : e <> d).
    { intro Heq. subst e. exact (proj1 (H_partition d) Hd He). }
    assert (Hfd : f <> d).
    { intro Heq. subst f. exact (proj1 (H_partition d) Hd Hf). }
    (** a closure entry that dominates its converse already clears c *)
    assert (Hclears : forall x y, x <> y ->
              mat_star M y x ≤ mat_star M x y -> c ≤ mat_star M x y).
    { intros x y Hxy Hdom.
      eapply orel_trans; [exact (Hsep x y Hxy) |].
      apply add_orel_bound.
      - apply link_le_mat_star.
      - eapply orel_trans; [apply link_le_mat_star | exact Hdom]. }
    split.
    - intros [Hle Hne].
      assert (Hef_ne : e <> f).
      { intro Heq. subst f. apply Hne. reflexivity. }
      pose proof (Hclears e f Hef_ne Hle) as Hc.
      pose proof (mat_star_isolate_strong_preserved M Htotal B1 B2 c d
                    H_partition H_lt Hd e f He Hc) as Hef.
      split.
      + eapply orel_trans; [apply mat_star_isolate_le |].
        eapply orel_trans; [exact Hle |]. rewrite Hef. apply bounded_orel_refl.
      + intro Heq0.
        apply Hne. apply orel_antisym; [exact Hle |].
        rewrite Hef, <- Heq0. apply mat_star_isolate_le.
    - intros [Hle' Hne'].
      assert (Hef_ne : e <> f).
      { intro Heq. subst f. apply Hne'. reflexivity. }
      assert (Hc' : c ≤ mat_star (isolate M d) e f).
      { eapply orel_trans; [exact (Hsep e f Hef_ne) |].
        apply add_orel_bound.
        - rewrite <- (isolate_off M d e f Hed Hfd). apply link_le_mat_star.
        - eapply orel_trans; [| exact Hle'].
          rewrite <- (isolate_off M d f e Hfd Hed). apply link_le_mat_star. }
      assert (Hc : c ≤ mat_star M e f)
        by (eapply orel_trans; [exact Hc' | apply mat_star_isolate_le]).
      pose proof (mat_star_isolate_strong_preserved M Htotal B1 B2 c d
                    H_partition H_lt Hd e f He Hc) as Hef.
      (** were the converse also above c it would be preserved too, forcing a
          tie in the isolated profile *)
      assert (Hno_converse : ~ (mat_star M e f ≤ mat_star M f e)).
      { intro Hbad.
        assert (Hcfe : c ≤ mat_star M f e)
          by (eapply orel_trans; [exact Hc | exact Hbad]).
        pose proof (mat_star_isolate_strong_preserved M Htotal B1 B2 c d
                      H_partition H_lt Hd f e Hf Hcfe) as Hfe.
        apply Hne'. apply orel_antisym; [exact Hle' |].
        rewrite <- Hef, <- Hfe. exact Hbad. }
      split.
      + destruct (Htotal (mat_star M f e) (mat_star M e f)) as [Hc1 | Hc1].
        * exfalso. apply Hno_converse. unfold Orel. rewrite addC. exact Hc1.
        * exact Hc1.
      + intro Heq0. apply Hno_converse.
        rewrite Heq0. apply bounded_orel_refl.
  Qed.

  (** ** Removing the whole weak block at once

      [isolate M d] neutralises one weak alternative.  [isolate_out B1 M]
      keeps only the links inside [B1], which is the same operation for
      the whole of [B2] at once.  Every lemma below is the corresponding
      single-node lemma with the test "is this [d]?" replaced by "is this
      outside [B1]?", and the argument is unchanged: a walk that leaves
      [B1] has to cross back, and every crossing link is below [c]. *)

  Definition isolate_out {R : Semiring.type} (B : list Node) (M : @Matrix Node R)
    : @Matrix Node R :=
    fun x y => if List.in_dec fin_eq_dec x B
               then (if List.in_dec fin_eq_dec y B then M x y else 0)
               else 0.

  Lemma isolate_out_off {R : Semiring.type} (B : list Node) (M : @Matrix Node R)
    (x y : Node) :
    List.In x B -> List.In y B -> isolate_out B M x y = M x y.
  Proof.
    intros Hx Hy. unfold isolate_out.
    destruct (List.in_dec fin_eq_dec x B); [| contradiction].
    destruct (List.in_dec fin_eq_dec y B); [reflexivity | contradiction].
  Qed.

  Lemma isolate_out_dead {R : Semiring.type} (B : list Node) (M : @Matrix Node R)
    (x y : Node) :
    ~ List.In x B -> isolate_out B M x y = 0.
  Proof.
    intros Hx. unfold isolate_out.
    destruct (List.in_dec fin_eq_dec x B); [contradiction | reflexivity].
  Qed.

  Lemma isolate_out_le {R : BoundedSemiring.type} (B : list Node)
    (M : @Matrix Node R) (x y : Node) :
    isolate_out B M x y ≤ M x y.
  Proof.
    unfold isolate_out.
    destruct (List.in_dec fin_eq_dec x B); [| apply zero_is_bottom].
    destruct (List.in_dec fin_eq_dec y B);
      [apply bounded_orel_refl | apply zero_is_bottom].
  Qed.

  Lemma mat_star_isolate_out_le {R : BoundedSemiring.type} (B : list Node)
    (M : @Matrix Node R) (x y : Node) :
    mat_star (isolate_out B M) x y ≤ mat_star M x y.
  Proof.
    unfold mat_star. apply geom_sum_monotone. intros i j. apply isolate_out_le.
  Qed.

  (** The dichotomy of [pow_isolate_dichotomy], for the whole weak block at
      once: a walk into [B1] either stays inside [B1], and is then matched by
      the restricted matrix, or it leaves and must cross back, which costs it
      the threshold. *)
  Lemma pow_isolate_out_dichotomy {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c) (f : Node) (Hf : In f B1) :
    forall n x, In x B1 ->
      pow M n x f ≤ mat_star (isolate_out B1 M) x f \/ pow M n x f < c.
  Proof.
    induction n as [|k IH]; intros x Hx.
    - left. cbn [pow]. unfold I.
      destruct (fin_eq_dec x f) as [Heq|_].
      + subst f. unfold mat_star. rewrite geom_sum_diag_one.
        apply bounded_orel_refl.
      + apply zero_is_bottom.
    - simpl. unfold matrix_mul.
      destruct (sum_selective H_total_order
                  (fun z => M x z * pow M k z f)) as [H0eq | [z Hz]].
      + left. rewrite H0eq. apply zero_is_bottom.
      + rewrite Hz. cbv beta.
        destruct (List.in_dec fin_eq_dec z B1) as [HzB1 | HzB1].
        * destruct (IH z HzB1) as [Hle | Hlt].
          -- left.
             rewrite <- (isolate_out_off B1 M x z Hx HzB1).
             eapply orel_trans;
               [apply (bounded_mul_orel_compat_r _ _ _ Hle) |].
             eapply orel_trans;
               [apply (bounded_mul_orel_compat_l _ _ _
                         (link_le_mat_star (isolate_out B1 M) x z)) |].
             apply star_path_compose.
          -- right.
             apply (orel_lt_trans (M x z * pow M k z f) (pow M k z f) c).
             ++ apply bounded_mul_lower_right.
             ++ exact Hlt.
        * right.
          assert (HzB2 : In z B2).
          { destruct (List.in_dec fin_eq_dec z B2) as [h|h]; [exact h |].
            exfalso. apply HzB1. apply (proj2 (H_partition z)). exact h. }
          apply (orel_lt_trans (M x z * pow M k z f) (pow M k z f) c).
          -- apply bounded_mul_lower_right.
          -- exact (pow_from_B2_lt M H_total_order B1 B2 c H_partition H_lt H0
                      k z HzB2 f Hf).
  Qed.

  Lemma mat_star_isolate_out_preserved {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htotal : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c)
    (e f : Node) (He : In e B1) (Hf : In f B1) (Hc : c ≤ mat_star M e f) :
    mat_star M e f = mat_star (isolate_out B1 M) e f.
  Proof.
    apply orel_antisym; [| apply mat_star_isolate_out_le].
    destruct (geom_sum_selective Htotal M (@kleene_exp Node) e f) as [k [Hk Heq]].
    destruct (pow_isolate_out_dichotomy M Htotal B1 B2 c H_partition H_lt H0
                f Hf k e He) as [Hle | Hlt].
    - unfold mat_star. rewrite Heq. exact Hle.
    - exfalso. destruct Hlt as [Hlt_le Hlt_ne]. apply Hlt_ne.
      apply orel_antisym; [exact Hlt_le |].
      unfold mat_star in Hc. rewrite Heq in Hc. exact Hc.
  Qed.

  (** Smith-IIA for the whole weak block, in the isolation reading. *)
  Theorem smith_iia_isolate_out {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htotal : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c)
    (Hsep : forall x y : Node, x <> y -> c ≤ M x y + M y x) :
    forall e f, In e B1 -> In f B1 ->
      (schulze_beats M e f <-> schulze_beats (isolate_out B1 M) e f).
  Proof.
    intros e f He Hf.
    assert (Hclears : forall x y, x <> y ->
              mat_star M y x ≤ mat_star M x y -> c ≤ mat_star M x y).
    { intros x y Hxy Hdom.
      eapply orel_trans; [exact (Hsep x y Hxy) |].
      apply add_orel_bound.
      - apply link_le_mat_star.
      - eapply orel_trans; [apply link_le_mat_star | exact Hdom]. }
    split.
    - intros [Hle Hne].
      assert (Hef_ne : e <> f).
      { intro Heq. subst f. apply Hne. reflexivity. }
      pose proof (Hclears e f Hef_ne Hle) as Hc.
      pose proof (mat_star_isolate_out_preserved M Htotal B1 B2 c H_partition
                    H_lt H0 e f He Hf Hc) as Hef.
      split.
      + eapply orel_trans; [apply mat_star_isolate_out_le |].
        eapply orel_trans; [exact Hle |]. rewrite Hef. apply bounded_orel_refl.
      + intro Heq0.
        apply Hne. apply orel_antisym; [exact Hle |].
        rewrite Hef, <- Heq0. apply mat_star_isolate_out_le.
    - intros [Hle' Hne'].
      assert (Hef_ne : e <> f).
      { intro Heq. subst f. apply Hne'. reflexivity. }
      assert (Hc' : c ≤ mat_star (isolate_out B1 M) e f).
      { eapply orel_trans; [exact (Hsep e f Hef_ne) |].
        apply add_orel_bound.
        - rewrite <- (isolate_out_off B1 M e f He Hf). apply link_le_mat_star.
        - eapply orel_trans; [| exact Hle'].
          rewrite <- (isolate_out_off B1 M f e Hf He). apply link_le_mat_star. }
      assert (Hc : c ≤ mat_star M e f)
        by (eapply orel_trans; [exact Hc' | apply mat_star_isolate_out_le]).
      pose proof (mat_star_isolate_out_preserved M Htotal B1 B2 c H_partition
                    H_lt H0 e f He Hf Hc) as Hef.
      assert (Hno_converse : ~ (mat_star M e f ≤ mat_star M f e)).
      { intro Hbad.
        assert (Hcfe : c ≤ mat_star M f e)
          by (eapply orel_trans; [exact Hc | exact Hbad]).
        pose proof (mat_star_isolate_out_preserved M Htotal B1 B2 c H_partition
                      H_lt H0 f e Hf He Hcfe) as Hfe.
        apply Hne'. apply orel_antisym; [exact Hle' |].
        rewrite <- Hef, <- Hfe. exact Hbad. }
      split.
      + destruct (Htotal (mat_star M f e) (mat_star M e f)) as [Hc1 | Hc1].
        * exfalso. apply Hno_converse. unfold Orel. rewrite addC. exact Hc1.
        * exact Hc1.
      + intro Heq0. apply Hno_converse.
        rewrite Heq0. apply bounded_orel_refl.
  Qed.

End IsolateN.
