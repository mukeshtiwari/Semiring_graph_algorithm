From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN
  ReversalsymmetryN MonotonicityN ParetoN CondorcetN
  SmithN PrudenceN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: the MinMax set (4.8)
    Split out of the former monolithic SocialchoiceN.v. *)

Section MinMaxN.

  Context {Node : FinType.type}.


  (** * MinMax set (Section 4.8)

      Γ_D(B) — [cut_in M B] — is the strength of the strongest link
      entering the set [B] from outside, β_D its minimum over the proper
      non-empty sets, and 𝔅_D the union of the minimising sets.  We take
      subsets as boolean predicates and keep β_D as a parameter [beta]
      constrained by hypotheses, rather than as a minimum computed over
      the powerset: the semiring has joins but no meets, so a minimum
      over subsets is not an operation of the algebra.  [Hmin] says beta
      is a lower bound for every cut (β_D is the minimum), [Ba] with
      [cut_in M Ba = beta] witnesses [a ∈ 𝔅_D], and [Hb_out] says no cut
      around [b] attains beta, i.e. [b ∉ 𝔅_D]. *)

  Definition proper_nonempty (B : Node -> bool) : Prop :=
    (exists x, B x = true) /\ (exists y, B y = false).

  (** [Γ_D(B)], the strongest link entering [B] — the definition opening
      Schulze's §4.8 (also (6.3) in his §6). *)
  Definition cut_in {R : Semiring.type}
    (M : @Matrix Node R) (B : Node -> bool) : R :=
    sum (fun y => sum (fun x => if andb (negb (B y)) (B x) then M y x else 0)).

  (** Every link entering [B] is below the cut. *)
  Lemma cut_in_ge {R : BoundedSemiring.type} (M : @Matrix Node R)
    (B : Node -> bool) (y x : Node) :
    B y = false -> B x = true -> M y x ≤ cut_in M B.
  Proof.
    intros Hy Hx. unfold cut_in.
    eapply orel_trans; [| exact (le_sum _ y)]. cbv beta.
    eapply orel_trans; [| exact (le_sum _ x)]. cbv beta.
    rewrite Hy, Hx. cbn. apply bounded_orel_refl.
  Qed.

  (** Claim [#1] (4.8.7).  A path that starts outside [B] and ends inside it
      must cross the boundary, and its measure is below the crossing link. *)
  Lemma path_into_B_le_cut {R : BoundedSemiring.type}
    (M : @Matrix Node R) (B : Node -> bool) :
    forall (k : nat) (x y : Node) (p : list (Node * Node * R)),
      B x = false -> B y = true ->
      List.In p (all_paths_klength elements M k x y) ->
      measure_of_path p ≤ cut_in M B.
  Proof.
    induction k as [|k IH]; intros x y p Hx Hy Hin.
    - cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec x y) as [Heq|_]; [subst y; congruence | inversion Hin].
    - destruct (all_paths_klength_S_inv M k x y p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (B z) eqn:Hz.
      + (* the head edge already crosses the boundary *)
        exact (orel_trans _ _ _ (bounded_mul_lower_left _ _)
          (cut_in_ge M B x z Hx Hz)).
      + (* still outside [B]: the tail crosses it *)
        exact (orel_trans _ _ _ (bounded_mul_lower_right _ _)
          (IH z y q Hz Hy Hq)).
  Qed.

  Lemma pow_into_B_le_cut {R : BoundedSemiring.type}
    (M : @Matrix Node R) (B : Node -> bool) (n : nat) (x y : Node) :
    B x = false -> B y = true -> pow M n x y ≤ cut_in M B.
  Proof.
    intros Hx Hy.
    apply pow_bound_of_paths.
    intros p Hin.
    exact (path_into_B_le_cut M B n x y p Hx Hy Hin).
  Qed.

  Lemma mat_star_into_B_le_cut {R : BoundedSemiring.type}
    (M : @Matrix Node R) (B : Node -> bool) (x y : Node) :
    B x = false -> B y = true -> mat_star M x y ≤ cut_in M B.
  Proof.
    intros Hx Hy. apply mat_star_bound. intro n.
    exact (pow_into_B_le_cut M B n x y Hx Hy).
  Qed.

  (** Decidable search for a link satisfying a boolean test. *)
  Lemma exists_edge_dec (P : Node -> Node -> bool) :
    (forall f g, P f g = false) \/ (exists f g, P f g = true).
  Proof.
    destruct (existsb (fun f => existsb (fun g => P f g) elements) elements) eqn:E.
    - right. apply existsb_exists in E as [f [_ Hf]].
      apply existsb_exists in Hf as [g [_ Hg]]. exists f, g. exact Hg.
    - left. intros f g. destruct (P f g) eqn:HP; [exfalso | reflexivity].
      assert (Htrue :
        existsb (fun f' => existsb (fun g' => P f' g') elements) elements = true).
      { apply existsb_exists. exists f. split; [apply elements_complete |].
        apply existsb_exists. exists g. split; [apply elements_complete | exact HP]. }
      rewrite E in Htrue. discriminate.
  Qed.

  (** Claim [#2] (4.8.11).  The closure out of [a] reaches [b] with strength
      above beta.  The paper grows a set greedily; equivalently, take the set
      of nodes that [a] does *not* reach above beta — if [b] were in it, that
      set would be a proper non-empty cut whose strongest entering link is
      itself above beta, and following that link would reach a node of the
      set above beta, a contradiction. *)
  Lemma minmax_reach {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node) (beta : R)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (Hmin : forall B : Node -> bool, proper_nonempty B -> beta ≤ cut_in M B)
    (Hb_out : forall B : Node -> bool,
      proper_nonempty B -> B b = true -> cut_in M B ≠ beta) :
    ~ (mat_star M a b ≤ beta).
  Proof.
    intro Hab_le.
    set (C := fun h : Node =>
      if Hdec (mat_star M a h + beta) beta then true else false).
    assert (HC_true : forall h, C h = true -> mat_star M a h ≤ beta).
    { intros h Hh. unfold C in Hh.
      destruct (Hdec (mat_star M a h + beta) beta) as [He|_];
        [exact He | discriminate]. }
    assert (HC_false : forall h, C h = false -> ~ (mat_star M a h ≤ beta)).
    { intros h Hh Hle. unfold C in Hh.
      destruct (Hdec (mat_star M a h + beta) beta) as [_|Hne];
        [discriminate | exact (Hne Hle)]. }
    assert (HCb : C b = true).
    { unfold C. destruct (Hdec (mat_star M a b + beta) beta) as [_|Hne];
        [reflexivity | exfalso; exact (Hne Hab_le)]. }
    destruct (C a) eqn:HCa.
    - (* [a] itself is not reached above beta, so beta is the top and every
         cut attains it — contradicting [b ∉ 𝔅_D] *)
      exfalso.
      assert (Hone_le : (1 : R) ≤ beta).
      { rewrite <- (mat_star_diag_one M a). exact (HC_true a HCa). }
      assert (Hbeta_one : beta = 1)
        by (apply orel_antisym; [apply le_one | exact Hone_le]).
      destruct (exists_other b) as [y Hy].
      pose (Bb := fun z : Node => if fin_eq_dec z b then true else false).
      assert (HBb : Bb b = true).
      { unfold Bb. destruct (fin_eq_dec b b) as [_|Hc]; [reflexivity | congruence]. }
      assert (Hpn : proper_nonempty Bb).
      { split; [exists b; exact HBb | exists y].
        unfold Bb. destruct (fin_eq_dec y b) as [Hc|_]; [congruence | reflexivity]. }
      apply (Hb_out Bb Hpn HBb).
      apply orel_antisym; [rewrite Hbeta_one; apply le_one | exact (Hmin Bb Hpn)].
    - (* [C] is a proper non-empty set containing [b] *)
      assert (Hpn : proper_nonempty C)
        by (split; [exists b; exact HCb | exists a; exact HCa]).
      assert (Hcut_gt : beta < cut_in M C).
      { split; [exact (Hmin C Hpn) | intro Heq; exact (Hb_out C Hpn HCb (eq_sym Heq))]. }
      destruct (exists_edge_dec (fun f g =>
        andb (andb (negb (C f)) (C g))
             (if Hdec (M f g + beta) beta then false else true)))
        as [Hnone | [f [g Hfg]]].
      + (* every link into [C] is below beta, so the cut is too *)
        exfalso. destruct Hcut_gt as [Hle Hne]. apply Hne, orel_antisym; [exact Hle |].
        unfold cut_in.
        apply bounded_sum_orel_bound. intro y. cbv beta.
        apply bounded_sum_orel_bound. intro x. cbv beta.
        destruct (andb (negb (C y)) (C x)) eqn:Hguard; [| apply zero_is_bottom].
        specialize (Hnone y x). rewrite Hguard in Hnone. cbn in Hnone.
        destruct (Hdec (M y x + beta) beta) as [He|_]; [exact He | discriminate].
      + (* the crossing link reaches a node of [C] above beta *)
        exfalso.
        destruct (C f) eqn:Hf; cbn in Hfg; [discriminate |].
        destruct (C g) eqn:Hg; cbn in Hfg; [| discriminate].
        assert (HMfg : ~ (M f g ≤ beta)).
        { destruct (Hdec (M f g + beta) beta) as [_|Hne];
            [discriminate Hfg | exact Hne]. }
        assert (Hprod : beta < mat_star M a f * M f g).
        { apply (lt_mul Htotal Hmeet).
          - exact (not_le_lt Htotal _ _ (HC_false f Hf)).
          - exact (not_le_lt Htotal _ _ HMfg). }
        assert (Hle_g : mat_star M a f * M f g ≤ mat_star M a g).
        { eapply orel_trans; [| apply star_path_compose].
          apply bounded_mul_orel_compat_r. apply link_le_mat_star. }
        destruct Hprod as [Hbx Hbx_ne].
        apply Hbx_ne, orel_antisym; [exact Hbx |].
        exact (orel_trans _ _ _ Hle_g (HC_true g Hg)).
  Qed.

  (** MinMax (4.8.1): every member of the MinMax set beats every non-member. *)
  Theorem minmax_beats {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node) (beta : R) (Ba : Node -> bool)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (Hpn_a : proper_nonempty Ba) (Ha : Ba a = true) (Hcut_a : cut_in M Ba = beta)
    (Hmin : forall B : Node -> bool, proper_nonempty B -> beta ≤ cut_in M B)
    (Hb_out : forall B : Node -> bool,
      proper_nonempty B -> B b = true -> cut_in M B ≠ beta) :
    schulze_beats M a b.
  Proof.
    (** [b] cannot lie in a minimising set *)
    assert (Hb : Ba b = false).
    { destruct (Ba b) eqn:Hbb; [exfalso | reflexivity].
      exact (Hb_out Ba Hpn_a Hbb Hcut_a). }
    assert (Hrev : mat_star M b a ≤ beta).
    { rewrite <- Hcut_a. exact (mat_star_into_B_le_cut M Ba b a Hb Ha). }
    assert (Hfwd : beta < mat_star M a b).
    { apply (not_le_lt Htotal).
      exact (minmax_reach M a b beta Htotal Hmeet Hdec Hmin Hb_out). }
    unfold schulze_beats, beats.
    exact (orel_lt_trans _ _ _ Hrev Hfwd).
  Qed.

  (** MinMax (4.8.2): [S ⊆ 𝔅_D] — a node outside the MinMax set is no winner. *)
  Corollary minmax_winner {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node) (beta : R) (Ba : Node -> bool)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (Hpn_a : proper_nonempty Ba) (Ha : Ba a = true) (Hcut_a : cut_in M Ba = beta)
    (Hmin : forall B : Node -> bool, proper_nonempty B -> beta ≤ cut_in M B)
    (Hb_out : forall B : Node -> bool,
      proper_nonempty B -> B b = true -> cut_in M B ≠ beta) : 
    ~ schulze_winner M b.
  Proof.
    intro Hwin.
    assert (Hab : a ≠ b).
    { intro Heq. rewrite Heq in Ha.
      destruct (Ba b) eqn:Hbb; [| discriminate].
      exact (Hb_out Ba Hpn_a Hbb Hcut_a). }
    exact (Hwin a Hab (minmax_beats M a b beta Ba Htotal Hmeet Hdec
      Hpn_a Ha Hcut_a Hmin Hb_out)).
  Qed.

End MinMaxN.
