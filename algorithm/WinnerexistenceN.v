From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: winner existence, and its characterisation (4.1.14)
    Split out of the former monolithic SocialchoiceN.v. *)

Section WinnerexistenceN.

  Context {Node : FinType.type}.


  (** Non-selectivity refutes winner existence, using four alternatives.
      No commutativity is needed: incomparability of x and y gives both
      [x * y < y] and [y * x < x] directly. *)
  Lemma selectivity_from_winner_exists {R : BoundedSemiring.type}
    (Hlen : (4 <= List.length (@elements Node))%nat)
    (Hdec : forall u v : R, {u = v} + {u <> v})
    (Hwin : forall (A B C D : Node) (u v : R),
              exists a : Node, schulze_winner (sq_matrix A B C D u v) a) :
    forall u v : R, u + v = u \/ u + v = v.
  Proof.
    intros x y.
    destruct (Hdec (x + y) x) as [Hx|Hx]; [left; exact Hx |].
    destruct (Hdec (x + y) y) as [Hy|Hy]; [right; exact Hy |].
    exfalso.
    (** x and y are incomparable *)
    assert (Hxy : ~ (x ≤ y)) by exact Hy.
    assert (Hyx : ~ (y ≤ x)).
    { intro h. apply Hx. unfold Orel in h. rewrite addC. exact h. }
    assert (H1 : x * y ≤ y) by apply (@bounded_mul_lower_right R x y).
    assert (H1' : x * y <> y).
    { intro h. apply Hyx. rewrite <- h. apply (@bounded_mul_lower_left R x y). }
    assert (H2 : y * x ≤ x) by apply (@bounded_mul_lower_right R y x).
    assert (H2' : y * x <> x).
    { intro h. apply Hxy. rewrite <- h. apply (@bounded_mul_lower_left R y x). }
    assert (Hy0 : y <> 0).
    { intro h. apply Hyx. rewrite h. apply zero_is_bottom. }
    destruct (four_distinct_nodes Hlen)
      as (A & B & C & D & HAB & HAC & HAD & HBC & HBD & HCD).
    destruct (Hwin A B C D x y) as [w Hw].
    exact (sq_no_winner A B C D HAB HAC HAD HBC HBD HCD x y
             Hy0 H1 H1' H2 H2' w Hw).
  Qed.

  (** The proof only ever establishes the meet property, never selectivity —
      see the discussion in the ICALP paper (Section 6, "Why the
      winner-existence witness cannot be the same one") for why the natural
      three-node witness cannot also rule out non-selectivity: the analogous
      triangle T(x, y, x*y) ties on its third edge instead of cycling, since
      that edge compares x*y against itself by construction. The conclusion
      is stated as the meet property outright, matching what is actually
      proved, rather than as a disjunction with an unused left disjunct. *)
  Theorem winner_exists_weaker_sufficient {R : BoundedSemiring.type}
    (Hlen : (3 <= length (@elements Node))%nat)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (Hcomm : forall x y : R, x * y = y * x) :
    (forall  (M : @Matrix Node R), exists (a : Node), schulze_winner M a) ->
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    intros Hwin m a b Hma Hmb.
    destruct (Hdec (m + a * b) (a * b)) as [H|H]; [exact H |].
    exfalso.
    assert (Hnle : ~ (m ≤ a * b)) by exact H.
    destruct (three_distinct_nodes Hlen) as (X & Y & Z & HXY & HYZ & HXZ).
    (** [a] is not the bottom: there both [m] and [a * b] would collapse to it *)
    assert (Hp : a <> 0).
    { intro h. apply Hnle.
      assert (Hab : a * b ≤ a) by apply (@bounded_mul_lower_left R a b).
      rewrite h in Hma, Hab. rewrite h.
      rewrite (orel_antisym _ _ Hma (zero_is_bottom m)).
      rewrite (orel_antisym _ _ Hab (zero_is_bottom (0 * b))).
      apply (@bounded_orel_refl R 0). }
    (** Raise [m] to [m + a*b], which still lies below [a] and [b] but now has
        [a * b] STRICTLY below it — the third edge of the cycle. *)
    assert (Hna : m + a * b ≤ a)
      by (apply add_orel_bound;
          [exact Hma | apply (@bounded_mul_lower_left R a b)]).
    assert (Hnb : m + a * b ≤ b)
      by (apply add_orel_bound;
          [exact Hmb | apply (@bounded_mul_lower_right R a b)]).
    assert (H3 : a * b ≤ m + a * b) by apply orel_plus_upper_right.
    assert (H3' : a * b <> m + a * b)
      by (intro h; apply Hnle; unfold Orel; symmetry; exact h).
    (** The other two edges.  Each can only tie by collapsing [a] or [b] onto
        the normalised value, which contradicts [H3']. *)
    assert (H1 : b * (m + a * b) ≤ a)
      by exact (orel_trans _ _ _
                  (@bounded_mul_lower_right R b (m + a * b)) Hna).
    assert (H1' : b * (m + a * b) <> a).
    { intro h.
      assert (Han : a = m + a * b).
      { apply orel_antisym;
          [rewrite <- h at 1; apply (@bounded_mul_lower_right R b (m + a * b))
          | exact Hna]. }
      rewrite <- Han in h. apply H3'. rewrite <- Han, (Hcomm a b). exact h. }
    assert (H2 : (m + a * b) * a ≤ b)
      by exact (orel_trans _ _ _
                  (@bounded_mul_lower_left R (m + a * b) a) Hnb).
    assert (H2' : (m + a * b) * a <> b).
    { intro h.
      assert (Hbn : b = m + a * b).
      { apply orel_antisym;
          [rewrite <- h at 1; apply (@bounded_mul_lower_left R (m + a * b) a)
          | exact Hnb]. }
      rewrite <- Hbn in h. apply H3'. rewrite <- Hbn, (Hcomm a b). exact h. }
    (** The triangle X → Y → Z → X carrying (a, b, m + a*b) has no winner. *)
    destruct (Hwin (tri_matrix X Y Z a b (m + a * b))) as [w Hw].
    exact (tri_no_winner X Y Z HXY HYZ HXZ a b (m + a * b)
             Hp H1 H1' H2 H2' H3 H3' w Hw).
  Qed.
  



  (** With selectivity already in hand the meet property follows without any
      commutativity assumption.  Totality turns [~ (m <= a*b)] into
      [a*b < m] outright, so no raising of [m] is needed, and each degenerate
      case collapses one of [a], [b] onto [m] and is refuted by the UNIFORM
      triangle on that element: [a <= b] forces [a*a <= a*b < a]. *)
  Lemma meet_from_winner_exists {R : BoundedSemiring.type}
    (Hlen : (3 <= List.length (@elements Node))%nat)
    (Hdec : forall u v : R, {u = v} + {u <> v})
    (Hsel : forall u v : R, u + v = u \/ u + v = v)
    (Hwin : forall (X Y Z : Node) (p q r : R),
              exists a : Node, schulze_winner (tri_matrix X Y Z p q r) a) :
    forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b.
  Proof.
    intros m a b Hma Hmb.
    destruct (Hdec (m + a * b) (a * b)) as [H|H]; [exact H |].
    exfalso.
    assert (Hnle : ~ (m ≤ a * b)) by exact H.
    (** totality: a * b sits strictly below m *)
    assert (Hab_le : a * b ≤ m).
    { destruct (Hsel m (a * b)) as [h|h].
      - unfold Orel. rewrite addC. exact h.
      - exfalso. apply Hnle. unfold Orel. exact h. }
    assert (Hab_ne : a * b <> m).
    { intro h. apply Hnle. unfold Orel. rewrite h. apply (@bounded_orel_refl R m). }
    destruct (three_distinct_nodes Hlen) as (X & Y & Z & HXY & HYZ & HXZ).
    destruct (Hdec (b * m) a) as [E1|K1].
    - (* b*m = a forces a = m; the uniform triangle on a refutes it *)
      assert (Ham : a = m).
      { apply orel_antisym;
          [ rewrite <- E1; apply (@bounded_mul_lower_right R b m) | exact Hma ]. }
      assert (Hab' : a ≤ b) by (rewrite Ham; exact Hmb).
      assert (Haa_le : a * a ≤ a) by apply (@bounded_mul_lower_left R a a).
      assert (Haa_ne : a * a <> a).
      { intro h.
        assert (Hmono : a * a ≤ a * b)
          by (apply bounded_mul_orel_compat_r; exact Hab').
        rewrite h in Hmono. apply Hnle. rewrite <- Ham. exact Hmono. }
      assert (Hp : a <> 0).
      { intro h. apply Haa_ne. rewrite h. apply (@mul0r R). }
      destruct (Hwin X Y Z a a a) as [w Hw].
      exact (tri_no_winner X Y Z HXY HYZ HXZ a a a Hp
               Haa_le Haa_ne Haa_le Haa_ne Haa_le Haa_ne w Hw).
    - destruct (Hdec (m * a) b) as [E2|K2].
      + (* dually, m*a = b forces b = m *)
        assert (Hbm : b = m).
        { apply orel_antisym;
            [ rewrite <- E2; apply (@bounded_mul_lower_left R m a) | exact Hmb ]. }
        assert (Hba' : b ≤ a) by (rewrite Hbm; exact Hma).
        assert (Hbb_le : b * b ≤ b) by apply (@bounded_mul_lower_left R b b).
        assert (Hbb_ne : b * b <> b).
        { intro h.
          assert (Hmono : b * b ≤ a * b)
            by (apply bounded_mul_orel_compat_l; exact Hba').
          rewrite h in Hmono. apply Hnle. rewrite <- Hbm. exact Hmono. }
        assert (Hp : b <> 0).
        { intro h. apply Hbb_ne. rewrite h. apply (@mul0r R). }
        destruct (Hwin X Y Z b b b) as [w Hw].
        exact (tri_no_winner X Y Z HXY HYZ HXZ b b b Hp
                 Hbb_le Hbb_ne Hbb_le Hbb_ne Hbb_le Hbb_ne w Hw).
      + (* both edges strict: the triangle (a, b, m) has no winner *)
        assert (K1' : b * m ≤ a)
          by exact (orel_trans _ _ _ (@bounded_mul_lower_right R b m) Hma).
        assert (K2' : m * a ≤ b)
          by exact (orel_trans _ _ _ (@bounded_mul_lower_left R m a) Hmb).
        assert (Hp : a <> 0).
        { intro h. apply Hab_ne. rewrite h, (@mul0r R). symmetry.
          rewrite h in Hma.
          apply orel_antisym; [ exact Hma | apply zero_is_bottom ]. }
        destruct (Hwin X Y Z a b m) as [w Hw].
        exact (tri_no_winner X Y Z HXY HYZ HXZ a b m Hp
                 K1' K1 K2' K2 Hab_le Hab_ne w Hw).
  Qed.

  (** A non-empty list has an element that nothing else in the list beats —
      [schulze_beats] is a strict order, so a finite list has a maximal
      element.  Shared by [winner_exists_weaker_necessary] and
      [winner_beats_nonwinner]. *)
  Lemma exists_maximal_in_list {R : BoundedSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b)
    (M : @Matrix Node R) :
    forall (l : list Node), l <> [] ->
      exists w, In w l /\ (forall b, In b l -> b <> w -> ~ schulze_beats M b w).
  Proof.
    intro l. induction l as [|a l IH]; intros Hnonempty.
    - exfalso. apply Hnonempty. reflexivity.
    - destruct l as [|b l].
      + exists a. split; [left; reflexivity |].
        intros b0 Hb0 Hneq. inversion Hb0 as [Heq|Hfalse].
        * exfalso. apply Hneq. symmetry. exact Heq.
        * inversion Hfalse.
      + assert (Hnonempty_tail : b :: l <> []) by discriminate.
        destruct (IH Hnonempty_tail) as [w [Hin_w Hw_undefeated]].
        destruct (schulze_beats_dec M a w Hdec) as [H_aw | H_not_aw].
        * exists a. split; [left; reflexivity |].
          intros x Hx_in Hx_neq_a.
          inversion Hx_in as [Heq_a | Hx_in_tail].
          { exfalso. apply Hx_neq_a. symmetry. exact Heq_a. }
          intro Hx_beats_a.
          pose proof (@schulze_trans_weaker_necessary Node R
            H_total_order H_meet_lower_bound M x a w Hx_beats_a H_aw) as Hxw.
          destruct (fin_eq_dec x w) as [Heq_xw | Hneq_xw].
          { subst x. apply (schulze_beats_irrefl M w). exact Hxw. }
          { apply (Hw_undefeated x Hx_in_tail Hneq_xw). exact Hxw. }
        * exists w. split.
          { right. exact Hin_w. }
          intros x Hx_in Hx_neq_w.
          inversion Hx_in as [Heq_a | Hx_in_tail].
          { subst x. exact H_not_aw. }
          { apply (Hw_undefeated x Hx_in_tail Hx_neq_w). }
  Qed.

  (** * Winner existence — meet-semiring version

      The headline of Schulze's §4.1 corollary: "the set S of winners, as
      defined in (2.2.2), is non-empty".  (The corollary's displayed form
      (4.1.14) is the stronger [winner_beats_nonwinner] below.)

      a Schulze winner is a
      maximal element of the strict partial order [schulze_beats], and
      such an element always exists on a finite set.  The only change is
      which transitivity lemma is invoked in the induction step.

      Hypothesis summary:
      - [H_total_order]    : addition is a total order (x+y = x ∨ x+y = y)
      - [Hdec]            : decidable equality on R
      - [H_meet_lower_bound]: m ≤ a → m ≤ b → m ≤ a * b                    *)
  Theorem winner_exists_weaker_necessary {R : BoundedSemiring.type} 
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) :
    forall (M : @Matrix Node R), exists (a : Node), schulze_winner M a.
  Proof.
    intro M.
    pose proof (exists_maximal_in_list H_total_order Hdec H_meet_lower_bound M)
      as Hmax.
    assert (Hnonempty : @elements Node <> []).
    { intro Hnil.
      pose proof (elements_two_or_more (s := Node)) as Hlen.
      rewrite Hnil in Hlen. simpl in Hlen. lia. }
    destruct (Hmax (@elements Node) Hnonempty) as [w [Hin_w Hw_undefeated]].
    exists w. unfold schulze_winner.
    intros b Hb_neq_w.
    apply (Hw_undefeated b).
    - apply (elements_complete b).
    - exact Hb_neq_w.
  Qed.

  (** Winner existence characterises the bottleneck semirings, exactly as
      transitivity does.  Four alternatives are needed rather than three:
      over the four-element distributive lattice, which has the meet property
      but is not selective, every matrix of order three still has a winner,
      so no three-node witness can establish selectivity. *)
  Theorem winner_exists_characterisation {R : BoundedSemiring.type} :
    (4 <= List.length (@elements Node))%nat ->
    (forall u v : R, {u = v} + {u <> v}) ->
    (forall (M : @Matrix Node R), exists a : Node, schulze_winner M a) <->
    (forall u v : R, u + v = u \/ u + v = v) /\
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    intros Hlen Hdec. split.
    - intro Hwin.
      assert (Hsel : forall u v : R, u + v = u \/ u + v = v)
        by exact (selectivity_from_winner_exists Hlen Hdec
                    (fun A B C D u v => Hwin (sq_matrix A B C D u v))).
      split; [exact Hsel |].
      assert (Hlen3 : (3 <= List.length (@elements Node))%nat) by lia.
      exact (meet_from_winner_exists Hlen3 Hdec Hsel
               (fun X Y Z p q r => Hwin (tri_matrix X Y Z p q r))).
    - intros (Hsel & Hmeet).
      exact (winner_exists_weaker_necessary Hsel Hdec Hmeet).
  Qed.

 

  (** Schulze §2.2: "Output of the proposed method are (1) a strict partial
      order O on A and (2) a set ∅ ≠ S ⊆ A of winners."

      Both halves in one statement.  Asymmetry of O is immediate from the
      asymmetry of the strict order on path strengths; transitivity is §4.1;
      non-emptiness of S is the corollary (4.1.14) that §4.1 draws from it.
      The claim [S ⊆ A] carries no content here — [schulze_winner M] is a
      predicate on [Node], so it is a subset of the alternatives by typing.

      This sits after [winner_exists_weaker_necessary] because it depends on
      it, even though the paper states it up front in §2.2. *)
  Theorem schulze_output_well_formed {R : BoundedSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b)
    (M : @Matrix Node R) :
    strict_partial_order (schulze_beats M) /\ (exists a, schulze_winner M a).
  Proof.
    split.
    - split.
      + exact (schulze_trans_weaker_necessary H_total_order H_meet_lower_bound M).
      + exact (schulze_beats_asym M).
    - exact (winner_exists_weaker_necessary H_total_order Hdec
               H_meet_lower_bound M).
  Qed.

  (** Schulze's corollary (4.1.14): every non-winner is beaten by some actual
      winner.  This strengthens [winner_exists_weaker_necessary], which only
      says the winner set is non-empty, and it is what the reversal-symmetry
      results below need.

      The paper climbs from the non-winner through beaters until it reaches a
      winner.  Equivalently, and more directly: take a maximal element [w] of
      the set of alternatives that beat [b].  It beats [b] by construction, and
      it is maximal in the whole population, since anything beating [w] would
      beat [b] by transitivity and so already lie in that set. *)
  Theorem winner_beats_nonwinner {R : BoundedSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) :
    forall (M : @Matrix Node R) (b : Node),
      ~ schulze_winner M b -> exists a, schulze_winner M a /\ schulze_beats M a b.
  Proof.
    intros M b Hnw.
    destruct (beater_or_winner Hdec M b) as [[x Hx] | Hw]; [| contradiction].
    set (test := fun y : Node =>
      if schulze_beats_dec M y b Hdec then true else false).
    assert (Hmem : forall y, schulze_beats M y b ->
                     In y (List.filter test (@elements Node))).
    { intros y Hy. apply filter_In. split; [apply elements_complete |].
      unfold test. destruct (schulze_beats_dec M y b Hdec);
        [reflexivity | contradiction]. }
    assert (Hback : forall y, In y (List.filter test (@elements Node)) ->
                      schulze_beats M y b).
    { intros y Hy. apply filter_In in Hy as [_ Ht]. unfold test in Ht.
      destruct (schulze_beats_dec M y b Hdec); [assumption | discriminate]. }
    assert (HL : List.filter test (@elements Node) <> []).
    { intro H0. pose proof (Hmem x Hx) as Hin. rewrite H0 in Hin. inversion Hin. }
    destruct (exists_maximal_in_list H_total_order Hdec H_meet_lower_bound M
                (List.filter test (@elements Node)) HL) as [w [HwL Hwmax]].
    exists w. split.
    - intros y Hy_ne Hy_beats.
      apply (Hwmax y (Hmem y (schulze_trans_weaker_necessary H_total_order
               H_meet_lower_bound M y w b Hy_beats (Hback w HwL))) Hy_ne).
      exact Hy_beats.
    - exact (Hback w HwL).
  Qed.

End WinnerexistenceN.
