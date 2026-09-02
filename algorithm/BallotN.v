(* ========================================================================= *)
(*  The ballot layer: from profiles to a strength matrix, generically         *)
(*                                                                           *)
(*  Everything else in this development starts from a matrix [M] of link      *)
(*  strengths.  That is where the algebra lives, but it is not where several   *)
(*  of Schulze's arguments live: Pareto appeals to the transitivity of each    *)
(*  ballot, Smith and Condorcet to the fact that the two entries [M a b] and   *)
(*  [M b a] come from ONE pair of counts, monotonicity and clone independence  *)
(*  to how the counts move when ballots change.  A matrix has discarded all    *)
(*  of that, so the criterion files carry it as hypotheses on [M].            *)
(*                                                                           *)
(*  This file supplies the missing layer and discharges those hypotheses.     *)
(*  A ballot is a ranking function [Node -> nat], lower being better; every    *)
(*  strict weak order on a finite set is representable this way, and           *)
(*  transitivity comes for free.  A profile is a list of ballots, [count P i j] *)
(*  is the number of voters who strictly prefer [i] to [j], and [matrix_of P]  *)
(*  sends each off-diagonal pair of counts through a [Measure] (MeasureN.v),   *)
(*  which is any of Schulze's strength measures satisfying (2.1.1) and (2.1.2).*)
(*                                                                           *)
(*  Nothing here changes a matrix-level theorem.  Each section below states    *)
(*  Schulze's ballot-level premise, derives the matrix hypotheses of the       *)
(*  corresponding theorem from it, and applies that theorem to [matrix_of P]. *)
(*  Changes to a profile (raising, cloning, reversing) are relations between   *)
(*  profiles, stated as [Forall2] of a relation between ballots, so that       *)
(*  "some voters do X" is expressed without choosing which voters.            *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 List Arith Lia Sorting.Permutation.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN OrderSemiring
  NormalizedOrder ExtendOrder MeasureN SocialchoiceN SchulzeOnNT
  ClosureTransportN BeatsOnN CloneN.
Import ListNotations.

(* The weak order [≤] on strengths is the [Orel] notation from the imports.
   The strict one is written out as a conjunction, so that [<] keeps its
   meaning on vote counts. *)

Section BallotN.

  Context {Node : FinType.type}.

  (* ------------------------------------------------------------------ *)
  (*  Ballots, profiles, pairwise counts                                 *)
  (* ------------------------------------------------------------------ *)

  Definition Ballot := Node -> nat.
  Definition Profile := list Ballot.

  (** Voter [b] strictly prefers [i] to [j]. *)
  Definition prefers (b : Ballot) (i j : Node) : bool := Nat.ltb (b i) (b j).

  (** [N[i,j]]: how many voters strictly prefer [i] to [j]. *)
  Definition count (P : Profile) (i j : Node) : nat :=
    length (filter (fun b => prefers b i j) P).

  Lemma count_le_length : forall P i j, count P i j <= length P.
  Proof.
    intros P i j. unfold count.
    induction P as [|b P IH]; cbn [filter length]; [lia |].
    destruct (prefers b i j); cbn [length]; lia.
  Qed.

  (** Each ballot is a strict weak order: asymmetric, irreflexive, transitive. *)
  Lemma prefers_asym : forall (b : Ballot) i j,
    prefers b i j = true -> prefers b j i = false.
  Proof.
    intros b i j H. unfold prefers in *.
    apply Nat.ltb_lt in H. apply Nat.ltb_nlt. lia.
  Qed.

  Lemma prefers_irrefl : forall (b : Ballot) i, prefers b i i = false.
  Proof. intros b i. unfold prefers. apply Nat.ltb_nlt. lia. Qed.

  Lemma prefers_trans : forall (b : Ballot) i j k,
    prefers b i j = true -> prefers b j k = true -> prefers b i k = true.
  Proof.
    intros b i j k H1 H2. unfold prefers in *.
    apply Nat.ltb_lt in H1, H2. apply Nat.ltb_lt. lia.
  Qed.

  (** No voter prefers each of two alternatives to the other. *)
  Lemma count_pair_le : forall P i j, count P i j + count P j i <= length P.
  Proof.
    intros P i j. unfold count.
    induction P as [|b P IH]; cbn [filter length]; [lia |].
    destruct (prefers b i j) eqn:E1; destruct (prefers b j i) eqn:E2;
      cbn [length]; try lia.
    rewrite (prefers_asym b i j E1) in E2. discriminate.
  Qed.

  Lemma count_diag : forall P i, count P i i = 0.
  Proof.
    intros P i. unfold count.
    induction P as [|b P IH]; cbn [filter length]; [reflexivity |].
    rewrite prefers_irrefl. exact IH.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Comparing counts across profiles                                   *)
  (*                                                                     *)
  (*  Every bridge below is one of these four facts about filtered       *)
  (*  lengths: a pointwise implication within a profile, a pointwise     *)
  (*  implication or equivalence between two profiles related voter by   *)
  (*  voter, and invariance under permutation.                           *)
  (* ------------------------------------------------------------------ *)

  Lemma filter_length_le_incl (f g : Ballot -> bool) (P : Profile) :
    (forall b, In b P -> f b = true -> g b = true) ->
    length (filter f P) <= length (filter g P).
  Proof.
    induction P as [|b P IH]; intro H; cbn [filter]; [lia |].
    assert (IH' : length (filter f P) <= length (filter g P)).
    { apply IH. intros b' Hb' Hf. apply H; [right; exact Hb' | exact Hf]. }
    destruct (f b) eqn:Ef.
    - rewrite (H b (or_introl eq_refl) Ef). cbn [length]. lia.
    - destruct (g b); cbn [length]; lia.
  Qed.

  Lemma filter_length_le_forall2 (Rel : Ballot -> Ballot -> Prop)
    (f g : Ballot -> bool) (P P' : Profile) :
    Forall2 Rel P P' ->
    (forall b b', Rel b b' -> f b = true -> g b' = true) ->
    length (filter f P) <= length (filter g P').
  Proof.
    intros HF H.
    induction HF as [| b b' P P' Hbb' HF IH]; cbn [filter]; [lia |].
    destruct (f b) eqn:Ef.
    - rewrite (H b b' Hbb' Ef). cbn [length]. lia.
    - destruct (g b'); cbn [length]; lia.
  Qed.

  Lemma filter_length_eq_forall2 (Rel : Ballot -> Ballot -> Prop)
    (f g : Ballot -> bool) (P P' : Profile) :
    Forall2 Rel P P' ->
    (forall b b', Rel b b' -> f b = g b') ->
    length (filter f P) = length (filter g P').
  Proof.
    intros HF H.
    induction HF as [| b b' P P' Hbb' HF IH]; cbn [filter]; [reflexivity |].
    rewrite (H b b' Hbb'). destruct (g b'); cbn [length]; lia.
  Qed.

  Lemma filter_length_perm (f : Ballot -> bool) (P P' : Profile) :
    Permutation P P' -> length (filter f P) = length (filter f P').
  Proof.
    intro HP.
    induction HP as [| b P P' HP IH | b b' P | P P' P'' HP1 IH1 HP2 IH2];
      cbn [filter].
    - reflexivity.
    - destruct (f b); cbn [length]; lia.
    - destruct (f b), (f b'); cbn [length]; lia.
    - lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Unanimity                                                          *)
  (* ------------------------------------------------------------------ *)

  Definition unanimous (P : Profile) (i j : Node) : Prop :=
    forall b, In b P -> prefers b i j = true.

  Lemma unanimous_count : forall P i j,
    unanimous P i j -> count P i j = length P.
  Proof.
    intros P i j H. unfold count.
    induction P as [|b P IH]; cbn [filter length]; [reflexivity |].
    rewrite (H b (or_introl eq_refl)). cbn [length].
    rewrite IH; [reflexivity |].
    intros b' Hin. apply H. right. exact Hin.
  Qed.

  (** …and conversely, a count equal to the electorate is unanimity. *)
  Lemma count_full_unanimous : forall P i j,
    count P i j = length P -> unanimous P i j.
  Proof.
    intros P i j. unfold count, unanimous.
    induction P as [|b P IH]; cbn [filter length]; [intros _ b' []|].
    destruct (prefers b i j) eqn:E; cbn [length]; intro Hlen.
    - intros b' [Heq|Hin]; [subst b'; exact E |].
      apply IH; [lia | exact Hin].
    - exfalso. pose proof (count_le_length P i j) as Hle.
      unfold count in Hle. lia.
  Qed.

  Lemma unanimous_count_rev : forall P i j,
    unanimous P i j -> count P j i = 0.
  Proof.
    intros P i j H. unfold count.
    induction P as [|b P IH]; cbn [filter length]; [reflexivity |].
    rewrite (prefers_asym b i j (H b (or_introl eq_refl))).
    apply IH. intros b' Hin. apply H. right. exact Hin.
  Qed.

  (** Unanimous preference is transitive because each ballot is. *)
  Lemma unanimous_trans : forall P i j k,
    unanimous P i j -> unanimous P j k -> unanimous P i k.
  Proof.
    intros P i j k H1 H2 b Hb.
    exact (prefers_trans b i j k (H1 b Hb) (H2 b Hb)).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The closure depends on the matrix only pointwise                   *)
  (*                                                                     *)
  (*  Two profiles related voter by voter give two matrices that agree   *)
  (*  entrywise but are not the same function.  These lemmas carry the   *)
  (*  Schulze relations across such an agreement; they hold over any     *)
  (*  bounded semiring.                                                  *)
  (* ------------------------------------------------------------------ *)

  Lemma mat_star_ext {R : BoundedSemiring.type} (M N : @Matrix Node R) :
    (forall i j, M i j = N i j) -> forall a b, mat_star M a b = mat_star N a b.
  Proof.
    intros H a b. apply orel_antisym.
    - unfold mat_star. apply geom_sum_monotone.
      intros i j. rewrite H. apply bounded_orel_refl.
    - unfold mat_star. apply geom_sum_monotone.
      intros i j. rewrite H. apply bounded_orel_refl.
  Qed.

  Lemma schulze_beats_ext {R : BoundedSemiring.type} (M N : @Matrix Node R) :
    (forall i j, M i j = N i j) ->
    forall a b, schulze_beats M a b <-> schulze_beats N a b.
  Proof.
    intros H a b. unfold schulze_beats, beats.
    rewrite (mat_star_ext M N H a b), (mat_star_ext M N H b a). reflexivity.
  Qed.

  Lemma schulze_winner_ext {R : BoundedSemiring.type} (M N : @Matrix Node R) :
    (forall i j, M i j = N i j) ->
    forall a, schulze_winner M a <-> schulze_winner N a.
  Proof.
    intros H a. unfold schulze_winner.
    split; intros Hw b Hb Hbeat; apply (Hw b Hb);
      apply (schulze_beats_ext M N H); exact Hbeat.
  Qed.

  Lemma strict_winner_ext {R : BoundedSemiring.type} (M N : @Matrix Node R) :
    (forall i j, M i j = N i j) ->
    forall a, strict_winner M a <-> strict_winner N a.
  Proof.
    intros H a. unfold strict_winner.
    split; intros Hw b Hb; apply (schulze_beats_ext M N H); exact (Hw b Hb).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The induced strength matrix                                        *)
  (*                                                                     *)
  (*  The diagonal is the top by convention: Schulze's paths never       *)
  (*  traverse it, and the criterion files expect [1] there.             *)
  (* ------------------------------------------------------------------ *)

  Context (m : Measure).

  Definition matrix_of (P : Profile) : @Matrix Node (Strength m) :=
    fun i j =>
      if fin_eq_dec i j then one else strength m (count P i j, count P j i).

  Lemma matrix_of_diag : forall P i j, i = j -> matrix_of P i j = one.
  Proof.
    intros P i j Hij. unfold matrix_of.
    destruct (fin_eq_dec i j) as [_|Hne]; [reflexivity | contradiction].
  Qed.

  Lemma matrix_of_off : forall P i j, i <> j ->
    matrix_of P i j = strength m (count P i j, count P j i).
  Proof.
    intros P i j Hij. unfold matrix_of.
    destruct (fin_eq_dec i j) as [Heq|_]; [contradiction | reflexivity].
  Qed.

  (** A real link never has the strength of the diagonal. *)
  Lemma matrix_of_ne_one : forall P i j, i <> j -> matrix_of P i j <> one.
  Proof.
    intros P i j Hij. rewrite (matrix_of_off P i j Hij). apply strength_ne_one.
  Qed.

  (* ================================================================== *)
  (*  Pareto, strict form (Schulze 4.3.1)                                *)
  (*                                                                     *)
  (*  Premise: every voter strictly prefers [A] to [B], and somebody     *)
  (*  voted.  The five matrix hypotheses of [pareto_stronger_iff] follow: *)
  (*  [Hmax] and [Hpos] from (2.1.1), [Hdiag] by construction, and        *)
  (*  [Htop_trans] because a link as strong as the unanimous one IS       *)
  (*  unanimous (full_strength_inv), and unanimity composes because each  *)
  (*  ballot is transitive.  This is the one bridge that needs the        *)
  (*  individual ballots rather than the counts alone.                    *)
  (* ================================================================== *)

  Section Pareto.

    Variable P : Profile.
    Variable A B : Node.
    Hypothesis HAB : A <> B.
    Hypothesis Hvoters : 0 < length P.
    Hypothesis Hunan : unanimous P A B.

    Notation M := (matrix_of P).

    Lemma link_AB : M A B = strength m (length P, 0).
    Proof.
      rewrite (matrix_of_off P A B HAB).
      rewrite (unanimous_count P A B Hunan), (unanimous_count_rev P A B Hunan).
      reflexivity.
    Qed.

    (** (2.1.1): no link is stronger than a unanimous one. *)
    Lemma profile_Hmax : forall X Y, X <> Y -> Orel (M X Y) (M A B).
    Proof.
      intros X Y HXY. rewrite (matrix_of_off P X Y HXY), link_AB.
      apply strength_mono_weak; [apply count_le_length | lia].
    Qed.

    (** The unanimous link is not the bottom, since somebody voted. *)
    Lemma profile_pos : Orel zero (M A B) /\ zero <> M A B.
    Proof.
      split; [apply zero_is_bottom |].
      intro H. apply (strength_ne_zero m (length P, 0)).
      rewrite <- link_AB. symmetry. exact H.
    Qed.

    (** The key step: a link as strong as the unanimous one is unanimous. *)
    Lemma top_link_unanimous : forall X Y, X <> Y ->
      M X Y = M A B -> unanimous P X Y.
    Proof.
      intros X Y HXY Heq.
      rewrite (matrix_of_off P X Y HXY), link_AB in Heq.
      destruct (full_strength_inv m (length P) _ _ (count_le_length P X Y) Heq)
        as [Hc _].
      exact (count_full_unanimous P X Y Hc).
    Qed.

    (** [Htop_trans], derived: maximal links compose because ballots do. *)
    Theorem profile_Htop_trans : forall X Y Z,
      M X Y = M A B -> M Y Z = M A B -> M X Z = M A B.
    Proof.
      intros X Y Z HXY HYZ.
      (* the diagonal is the top, which is not the strength of a real link *)
      assert (Hne : forall U V, M U V = M A B -> U <> V).
      { intros U V H Huv. rewrite (matrix_of_diag P U V Huv), link_AB in H.
        exact (strength_ne_one m (length P, 0) (eq_sym H)). }
      pose proof (Hne X Y HXY) as HXY'. pose proof (Hne Y Z HYZ) as HYZ'.
      pose proof (unanimous_trans P X Y Z (top_link_unanimous X Y HXY' HXY)
                    (top_link_unanimous Y Z HYZ' HYZ)) as HuXZ.
      (* nobody prefers an alternative to itself, so [X ≠ Z] *)
      assert (HXZ : X <> Z).
      { intro Habs. subst Z. destruct P as [|b0 P']; [cbn in Hvoters; lia |].
        pose proof (HuXZ b0 (or_introl eq_refl)) as Hb0.
        rewrite prefers_irrefl in Hb0. discriminate. }
      rewrite (matrix_of_off P X Z HXZ), link_AB.
      rewrite (unanimous_count P X Z HuXZ), (unanimous_count_rev P X Z HuXZ).
      reflexivity.
    Qed.

    Lemma link_BA : M B A = strength m (0, length P).
    Proof.
      rewrite (matrix_of_off P B A (not_eq_sym HAB)).
      rewrite (unanimous_count_rev P A B Hunan), (unanimous_count P A B Hunan).
      reflexivity.
    Qed.

    Lemma link_BA_ne_AB : M B A <> M A B.
    Proof.
      rewrite link_AB, link_BA.
      exact (proj2 (strength_211 m (length P) 0 0 (length P)
                      (or_introl (conj Hvoters (Nat.le_0_l _))))).
    Qed.

    (** Schulze (4.3.1.2): the unanimously preferred alternative beats the
        dominated one.  Every hypothesis is about the profile. *)
    Theorem pareto_from_profile : schulze_beats M A B.
    Proof.
      apply (pareto_stronger_iff M A B (NT_selective (spec m)) profile_Htop_trans
               HAB profile_pos profile_Hmax (matrix_of_diag P)).
      exact link_BA_ne_AB.
    Qed.

    (** Schulze (4.3.1.3): the dominated alternative is not a winner. *)
    Theorem pareto_loser_from_profile : ~ schulze_winner M B.
    Proof. intro Hwin. exact (Hwin A HAB pareto_from_profile). Qed.

  End Pareto.

  (* ================================================================== *)
  (*  Pareto, weak form (Schulze 4.3.2)                                  *)
  (*                                                                     *)
  (*  Premise: every voter ranks [A] at least as high as [B].  The row   *)
  (*  and column inequalities of [pareto_weaker] are then inclusions of  *)
  (*  filtered voter sets: a voter with [B ≻ X] also has [A ≻ X], and a   *)
  (*  voter with [X ≻ A] also has [X ≻ B].                                *)
  (* ================================================================== *)

  Lemma count_zero_of_none : forall (P : Profile) i j,
    (forall b, In b P -> prefers b i j = false) -> count P i j = 0.
  Proof.
    intros P i j H. unfold count.
    induction P as [|b P IH]; cbn [filter]; [reflexivity |].
    rewrite (H b (or_introl eq_refl)). apply IH.
    intros b' Hb'. apply H. right. exact Hb'.
  Qed.

  Section ParetoWeak.

    Variable P : Profile.
    Variable A B : Node.
    Hypothesis HAB : A <> B.
    Hypothesis Hweak : forall b, In b P -> b A <= b B.

    Notation M := (matrix_of P).

    (** Nobody strictly prefers [B] to [A], so the reverse link is a
        zero-support link and cannot exceed the forward one. *)
    Lemma weak_Hle : Orel (M B A) (M A B).
    Proof.
      rewrite (matrix_of_off P B A (not_eq_sym HAB)), (matrix_of_off P A B HAB).
      rewrite (count_zero_of_none P B A).
      - apply strength_mono_weak; lia.
      - intros b Hb. unfold prefers. apply Nat.ltb_nlt.
        pose proof (Hweak b Hb). lia.
    Qed.

    Lemma weak_Hrow : forall X, X <> A -> X <> B -> Orel (M B X) (M A X).
    Proof.
      intros X HXA HXB.
      rewrite (matrix_of_off P B X (not_eq_sym HXB)),
              (matrix_of_off P A X (not_eq_sym HXA)).
      apply strength_mono_weak; unfold count; apply filter_length_le_incl;
        intros b Hb Hf; unfold prefers in *; apply Nat.ltb_lt in Hf;
        apply Nat.ltb_lt; pose proof (Hweak b Hb); lia.
    Qed.

    Lemma weak_Hcol : forall X, X <> A -> X <> B -> Orel (M X A) (M X B).
    Proof.
      intros X HXA HXB.
      rewrite (matrix_of_off P X A HXA), (matrix_of_off P X B HXB).
      apply strength_mono_weak; unfold count; apply filter_length_le_incl;
        intros b Hb Hf; unfold prefers in *; apply Nat.ltb_lt in Hf;
        apply Nat.ltb_lt; pose proof (Hweak b Hb); lia.
    Qed.

    (** Schulze (4.3.2.2): [ba ∉ O]. *)
    Theorem pareto_weak_from_profile : Orel (mat_star M B A) (mat_star M A B).
    Proof.
      exact (pareto_weaker M A B HAB weak_Hle weak_Hrow weak_Hcol
               (matrix_of_diag P)).
    Qed.

    (** Schulze (4.3.2.5): if [B] wins then so does [A]. *)
    Theorem pareto_weak_winner_from_profile :
      schulze_winner M B -> schulze_winner M A.
    Proof.
      exact (pareto_weaker_winner_transfer M A B HAB weak_Hle weak_Hrow
               weak_Hcol (matrix_of_diag P)).
    Qed.

    (** Schulze (4.3.2.3) and (4.3.2.4): whatever [B] beats, [A] beats, and
        whatever beats [A] beats [B]. *)
    Theorem pareto_weak_beats_from_profile : forall F, F <> A -> F <> B ->
      schulze_beats M B F -> schulze_beats M A F.
    Proof.
      exact (pareto_weaker_beats_transfer M A B (matrix_of_diag P)
               weak_Hrow weak_Hcol).
    Qed.

    Theorem pareto_weak_loses_from_profile : forall F, F <> A -> F <> B ->
      schulze_beats M F A -> schulze_beats M F B.
    Proof.
      exact (pareto_weaker_loses_transfer M A B (matrix_of_diag P)
               weak_Hrow weak_Hcol).
    Qed.

  End ParetoWeak.

  (* ================================================================== *)
  (*  Condorcet (the remark in Schulze 4.7)                              *)
  (*                                                                     *)
  (*  Premise: [A] wins every pairwise comparison.  The matrix           *)
  (*  hypothesis [H_cross] of [condorcet_implies_strict_winner_weaker]   *)
  (*  asks every link INTO [A] to lie strictly below every closure entry *)
  (*  OUT of [A].  On an abstract matrix that is a genuine assumption;    *)
  (*  here it is (2.1.2): a link into [A] is a defeat, so it sits below   *)
  (*  the tie, and a link out of [A] is a victory, so it sits above it.   *)
  (* ================================================================== *)

  Section Condorcet.

    Variable P : Profile.
    Variable A : Node.
    Hypothesis Hcw : forall X, X <> A -> count P X A < count P A X.

    Notation M := (matrix_of P).

    Lemma condorcet_winner_of_profile : condorcet_winner M A.
    Proof.
      intros X HXA. unfold beats.
      rewrite (matrix_of_off P X A HXA), (matrix_of_off P A X (not_eq_sym HXA)).
      apply strength_211. left.
      split; [apply Hcw; exact HXA | apply Nat.lt_le_incl; apply Hcw; exact HXA].
    Qed.

    (** The tie strength separates the links into [A] from those out of it. *)
    Lemma profile_H_cross : forall Z X, Z <> A -> X <> A -> Z <> X ->
      Orel (M Z A) (mat_star M A X) /\ M Z A <> mat_star M A X.
    Proof.
      intros Z X HZA HXA HZX.
      apply (orel_lt_le_trans (M Z A) (strength m (0, 0)) (mat_star M A X)).
      - rewrite (matrix_of_off P Z A HZA). apply defeat_lt_tie. apply Hcw. exact HZA.
      - apply (orel_trans _ (M A X) _).
        + rewrite (matrix_of_off P A X (not_eq_sym HXA)).
          exact (proj1 (tie_lt_victory m _ _ (Hcw X HXA))).
        + exact (link_le_mat_star (matrix_of P) A X).
    Qed.

    (** A Condorcet winner is a strict Schulze winner… *)
    Theorem condorcet_from_profile : strict_winner M A.
    Proof.
      exact (condorcet_implies_strict_winner_weaker M A (NT_selective (spec m))
               profile_H_cross condorcet_winner_of_profile).
    Qed.

    (** …and therefore the only winner. *)
    Theorem condorcet_unique_from_profile : forall w, schulze_winner M w -> w = A.
    Proof.
      intros w Hw. destruct (fin_eq_dec w A) as [Heq | Hne]; [exact Heq | exfalso].
      exact (strict_winner_excludes_others M A w condorcet_from_profile Hne Hw).
    Qed.

  End Condorcet.

  (* ================================================================== *)
  (*  Smith (Schulze 4.7.3 and 4.7.4)                                    *)
  (*                                                                     *)
  (*  Premise: every member of [B1] pairwise beats every member of [B2]. *)
  (*  The separator [c] that [smith_criterion_weaker] asks for is the    *)
  (*  tie strength, again by (2.1.2).  SchulzeOnNT.v notes that no       *)
  (*  carrier construction can supply this hypothesis; the count layer   *)
  (*  does, because [M b a] and [M a b] come from one pair of counts.    *)
  (* ================================================================== *)

  Section Smith.

    Variable P : Profile.
    Variable B1 B2 : list Node.
    Hypothesis H_partition : forall x, In x B1 <-> ~ In x B2.
    Hypothesis Hcut : forall a b, In a B1 -> In b B2 -> count P b a < count P a b.

    Notation M := (matrix_of P).

    Lemma cut_ne : forall a b, In a B1 -> In b B2 -> a <> b.
    Proof. intros a b Ha Hb Heq. subst b. exact (proj1 (H_partition a) Ha Hb). Qed.

    Lemma profile_separator :
      exists c : Strength m,
        (forall a b, In a B1 -> In b B2 -> Orel (M b a) c /\ M b a <> c) /\
        (forall a b, In a B1 -> In b B2 -> Orel c (M a b)).
    Proof.
      exists (strength m (0, 0)). split.
      - intros a b Ha Hb.
        rewrite (matrix_of_off P b a (not_eq_sym (cut_ne a b Ha Hb))).
        apply defeat_lt_tie. exact (Hcut a b Ha Hb).
      - intros a b Ha Hb. rewrite (matrix_of_off P a b (cut_ne a b Ha Hb)).
        exact (proj1 (tie_lt_victory m _ _ (Hcut a b Ha Hb))).
    Qed.

    (** Schulze (4.7.3): every member of [B1] beats every member of [B2]. *)
    Theorem smith_beats_from_profile : forall a b,
      In a B1 -> In b B2 -> schulze_beats M a b.
    Proof.
      exact (smith_beats M (NT_selective (spec m)) B1 B2 H_partition
               profile_separator).
    Qed.

    (** Schulze (4.7.4): the winners lie in [B1]. *)
    Theorem smith_from_profile : B1 <> [] -> forall w, schulze_winner M w -> In w B1.
    Proof.
      intro Hne.
      exact (smith_criterion_weaker M (NT_selective (spec m)) B1 B2 Hne
               H_partition profile_separator).
    Qed.

  End Smith.

  (* ================================================================== *)
  (*  Monotonicity (Schulze 4.5)                                         *)
  (*                                                                     *)
  (*  Premise: Schulze's (4.5.1) to (4.5.3), voter by voter.  A voter    *)
  (*  who preferred [A] to [f] still does, a voter who did not prefer    *)
  (*  [f] to [A] still does not, and preferences not involving [A] are   *)
  (*  unchanged.  The three matrix hypotheses of [winner_monotonicity]   *)
  (*  are then count inequalities carried through (2.1.1).               *)
  (* ================================================================== *)

  Lemma filter_length_ge_forall2 (Rel : Ballot -> Ballot -> Prop)
    (f g : Ballot -> bool) (P P' : Profile) :
    Forall2 Rel P P' ->
    (forall b b', Rel b b' -> g b' = true -> f b = true) ->
    length (filter g P') <= length (filter f P).
  Proof.
    intros HF H.
    induction HF as [| b b' P P' Hbb' HF IH]; cbn [filter]; [lia |].
    destruct (g b') eqn:Eg.
    - rewrite (H b b' Hbb' Eg). cbn [length]. lia.
    - destruct (f b); cbn [length]; lia.
  Qed.

  Section Monotonicity.

    Variable A : Node.

    (** One voter raises [A]: (4.5.1), (4.5.2), and (4.5.3). *)
    Definition raised (b b' : Ballot) : Prop :=
      (forall f, f <> A -> prefers b A f = true -> prefers b' A f = true) /\
      (forall f, f <> A -> prefers b f A = false -> prefers b' f A = false) /\
      (forall e f, e <> A -> f <> A -> prefers b e f = prefers b' e f).

    (** Some voters raise [A]; the others keep their ballots (which is
        [raised] with [b' = b]). *)
    Definition raise (P P' : Profile) : Prop := Forall2 raised P P'.

    Variable P P' : Profile.
    Hypothesis Hraise : raise P P'.

    Notation M := (matrix_of P).
    Notation M' := (matrix_of P').

    (** (4.5.10): [A]'s outgoing links do not weaken. *)
    Lemma raise_Hrow : forall Y, Orel (M A Y) (M' A Y).
    Proof.
      intro Y. destruct (fin_eq_dec A Y) as [HAY | HAY].
      - rewrite (matrix_of_diag P A Y HAY), (matrix_of_diag P' A Y HAY).
        apply (@bounded_orel_refl (Strength m)).
      - rewrite (matrix_of_off P A Y HAY), (matrix_of_off P' A Y HAY).
        apply strength_mono_weak.
        + unfold count. apply (filter_length_le_forall2 raised _ _ P P' Hraise).
          intros b b' [H1 _] Hf. exact (H1 Y (not_eq_sym HAY) Hf).
        + unfold count. apply (filter_length_ge_forall2 raised _ _ P P' Hraise).
          intros b b' [_ [H2 _]] Hf. destruct (prefers b Y A) eqn:E; [reflexivity |].
          rewrite (H2 Y (not_eq_sym HAY) E) in Hf. discriminate.
    Qed.

    (** (4.5.11): [A]'s incoming links do not strengthen. *)
    Lemma raise_Hcol : forall X, Orel (M' X A) (M X A).
    Proof.
      intro X. destruct (fin_eq_dec X A) as [HXA | HXA].
      - rewrite (matrix_of_diag P X A HXA), (matrix_of_diag P' X A HXA).
        apply (@bounded_orel_refl (Strength m)).
      - rewrite (matrix_of_off P X A HXA), (matrix_of_off P' X A HXA).
        apply strength_mono_weak.
        + unfold count. apply (filter_length_ge_forall2 raised _ _ P P' Hraise).
          intros b b' [_ [H2 _]] Hf. destruct (prefers b X A) eqn:E; [reflexivity |].
          rewrite (H2 X HXA E) in Hf. discriminate.
        + unfold count. apply (filter_length_le_forall2 raised _ _ P P' Hraise).
          intros b b' [H1 _] Hf. exact (H1 X HXA Hf).
    Qed.

    (** (4.5.12): everything else is unchanged. *)
    Lemma raise_Heq : forall X Y, X <> A -> Y <> A -> M X Y = M' X Y.
    Proof.
      intros X Y HXA HYA. destruct (fin_eq_dec X Y) as [HXY | HXY].
      - rewrite (matrix_of_diag P X Y HXY), (matrix_of_diag P' X Y HXY). reflexivity.
      - rewrite (matrix_of_off P X Y HXY), (matrix_of_off P' X Y HXY).
        f_equal. f_equal.
        + unfold count. apply (filter_length_eq_forall2 raised _ _ P P' Hraise).
          intros b b' [_ [_ H3]]. exact (H3 X Y HXA HYA).
        + unfold count. apply (filter_length_eq_forall2 raised _ _ P P' Hraise).
          intros b b' [_ [_ H3]]. exact (H3 Y X HYA HXA).
    Qed.

    (** Schulze (4.5.6), the [a ∈ S_old ⇒ a ∈ S_new] half: raising a
        winner keeps it a winner. *)
    Theorem monotonicity_from_profile : schulze_winner M A -> schulze_winner M' A.
    Proof. exact (winner_monotonicity M M' A raise_Hrow raise_Hcol raise_Heq). Qed.

    (** Schulze (4.5.5): a defeat [A] avoided before, it still avoids. *)
    Theorem monotonicity_unbeaten_from_profile :
      forall b, ~ schulze_beats M b A -> ~ schulze_beats M' b A.
    Proof. exact (monotonicity_unbeaten M M' A raise_Hrow raise_Hcol raise_Heq). Qed.

  End Monotonicity.

  (* ================================================================== *)
  (*  Independence of clones (Schulze 4.6)                               *)
  (*                                                                     *)
  (*  Premise: Schulze's (4.6.1) to (4.6.3), voter by voter.  Every      *)
  (*  clone takes [d]'s place against each surviving alternative, and    *)
  (*  preferences among survivors are unchanged.  The three matrix       *)
  (*  hypotheses (4.6.12) to (4.6.14) of CloneN are then count           *)
  (*  equalities; nothing is assumed about how voters order the clones.  *)
  (* ================================================================== *)

  Section Clones.

    Variable A_old K : list Node.
    Variable d : Node.
    Hypothesis Hd_old : In d A_old.
    Hypothesis HK_nonempty : K <> [].
    Hypothesis HK_fresh : forall x, In x K -> ~ In x A_old.

    (** One voter's ballot before and after [d] is replaced by [K]. *)
    Definition cloned (b b' : Ballot) : Prop :=
      (forall e g, In e A_old -> e <> d -> In g K -> prefers b e d = prefers b' e g) /\
      (forall f g, In f A_old -> f <> d -> In g K -> prefers b d f = prefers b' g f) /\
      (forall e f, In e A_old -> e <> d -> In f A_old -> f <> d ->
         prefers b e f = prefers b' e f).

    Variable P_old P_new : Profile.
    Hypothesis Hclone : Forall2 cloned P_old P_new.

    Notation M_old := (matrix_of P_old).
    Notation M_new := (matrix_of P_new).

    Lemma clone_ne_old : forall a g, In a A_old -> In g K -> a <> g.
    Proof. intros a g Ha Hg Heq. subst g. exact (HK_fresh a Hg Ha). Qed.

    (** (4.6.13): every clone inherits the outgoing links of [d]. *)
    Lemma clone_Hout : forall a g, In a A_old -> a <> d -> In g K ->
      M_new g a = M_old d a.
    Proof.
      intros a g Ha Had Hg.
      rewrite (matrix_of_off P_new g a (not_eq_sym (clone_ne_old a g Ha Hg))).
      rewrite (matrix_of_off P_old d a (not_eq_sym Had)).
      f_equal. f_equal.
      - unfold count. symmetry.
        apply (filter_length_eq_forall2 cloned _ _ P_old P_new Hclone).
        intros b b' [_ [H2 _]]. exact (H2 a g Ha Had Hg).
      - unfold count. symmetry.
        apply (filter_length_eq_forall2 cloned _ _ P_old P_new Hclone).
        intros b b' [H1 _]. exact (H1 a g Ha Had Hg).
    Qed.

    (** (4.6.12): every clone inherits the incoming links of [d]. *)
    Lemma clone_Hin : forall a g, In a A_old -> a <> d -> In g K ->
      M_new a g = M_old a d.
    Proof.
      intros a g Ha Had Hg.
      rewrite (matrix_of_off P_new a g (clone_ne_old a g Ha Hg)).
      rewrite (matrix_of_off P_old a d Had).
      f_equal. f_equal.
      - unfold count. symmetry.
        apply (filter_length_eq_forall2 cloned _ _ P_old P_new Hclone).
        intros b b' [H1 _]. exact (H1 a g Ha Had Hg).
      - unfold count. symmetry.
        apply (filter_length_eq_forall2 cloned _ _ P_old P_new Hclone).
        intros b b' [_ [H2 _]]. exact (H2 a g Ha Had Hg).
    Qed.

    (** (4.6.14): links between survivors are untouched. *)
    Lemma clone_Hext : forall a b, In a A_old -> a <> d -> In b A_old -> b <> d ->
      M_new a b = M_old a b.
    Proof.
      intros a b Ha Had Hb Hbd.
      destruct (fin_eq_dec a b) as [Hab | Hab].
      - rewrite (matrix_of_diag P_new a b Hab), (matrix_of_diag P_old a b Hab).
        reflexivity.
      - rewrite (matrix_of_off P_new a b Hab), (matrix_of_off P_old a b Hab).
        f_equal. f_equal.
        + unfold count. symmetry.
          apply (filter_length_eq_forall2 cloned _ _ P_old P_new Hclone).
          intros x y [_ [_ H3]]. exact (H3 a b Ha Had Hb Hbd).
        + unfold count. symmetry.
          apply (filter_length_eq_forall2 cloned _ _ P_old P_new Hclone).
          intros x y [_ [_ H3]]. exact (H3 b a Hb Hbd Ha Had).
    Qed.

    (** Schulze (4.6.7) and (4.6.8): replacing [d] by clones changes no
        survivor's winner status, and puts a clone in the winner set exactly
        when [d] was in it. *)
    Theorem clones_from_profile :
      (forall a, In a A_old -> a <> d ->
         (winner_on A_old M_old a <-> winner_on (A_new A_old K d) M_new a))
      /\ (winner_on A_old M_old d <->
          exists g, In g K /\ winner_on (A_new A_old K d) M_new g).
    Proof.
      exact (independence_of_clones_selective A_old K d M_old M_new Hd_old
               HK_nonempty HK_fresh (matrix_of_diag P_old) (matrix_of_diag P_new)
               clone_Hout clone_Hin clone_Hext
               (NT_selective (spec m)) (NT_eq_dec (spec m))
               (NT_meet_lower_bound (spec m))).
    Qed.

  End Clones.

  (* ================================================================== *)
  (*  Reversal symmetry (Schulze 4.4)                                    *)
  (*                                                                     *)
  (*  Premise: every ballot is reversed.  The counts swap, so the new    *)
  (*  matrix agrees entrywise with the transpose that the reversal       *)
  (*  theorems are stated for.                                           *)
  (* ================================================================== *)

  Definition reversed (b b' : Ballot) : Prop :=
    forall x y, prefers b' x y = prefers b y x.

  Definition reverse (P P' : Profile) : Prop := Forall2 reversed P P'.

  (** A concrete reversal: flip the ranks below any bound on them. *)
  Definition rev_ballot (n : nat) (b : Ballot) : Ballot := fun x => n - b x.

  Lemma rev_ballot_reversed : forall n b,
    (forall x, b x <= n) -> reversed b (rev_ballot n b).
  Proof.
    intros n b Hb. unfold reversed, rev_ballot, prefers. intros x y.
    pose proof (Hb x). pose proof (Hb y).
    destruct (Nat.ltb (n - b x) (n - b y)) eqn:E1;
      destruct (Nat.ltb (b y) (b x)) eqn:E2; try reflexivity.
    - apply Nat.ltb_lt in E1. apply Nat.ltb_nlt in E2. lia.
    - apply Nat.ltb_nlt in E1. apply Nat.ltb_lt in E2. lia.
  Qed.

  Lemma count_reverse : forall P P', reverse P P' ->
    forall i j, count P' i j = count P j i.
  Proof.
    intros P P' HR i j. unfold count. symmetry.
    apply (filter_length_eq_forall2 reversed _ _ P P' HR).
    intros b b' Hbb'. symmetry. exact (Hbb' i j).
  Qed.

  Lemma matrix_of_reverse : forall P P', reverse P P' ->
    forall i j, matrix_of P' i j = matrix_of P j i.
  Proof.
    intros P P' HR i j. destruct (fin_eq_dec i j) as [Hij | Hij].
    - rewrite (matrix_of_diag P' i j Hij), (matrix_of_diag P j i (eq_sym Hij)).
      reflexivity.
    - rewrite (matrix_of_off P' i j Hij), (matrix_of_off P j i (not_eq_sym Hij)).
      rewrite (count_reverse P P' HR i j), (count_reverse P P' HR j i). reflexivity.
  Qed.

  (** Schulze (4.4.2) at winner level: a strict winner cannot stay one when
      every ballot is reversed. *)
  Theorem reversal_from_profile : forall P P', reverse P P' ->
    forall A, strict_winner (matrix_of P) A -> ~ strict_winner (matrix_of P') A.
  Proof.
    intros P P' HR A Hwin Hwin'.
    apply (reversal_symmetry (matrix_of P) A Hwin).
    exact (proj1 (strict_winner_ext (matrix_of P') (fun i j => matrix_of P j i)
                    (matrix_of_reverse P P' HR) A) Hwin').
  Qed.

  (** Schulze (4.4.3): some winner is displaced by the reversal exactly
      when some non-winner is promoted by it. *)
  Theorem reversal_S_from_profile : forall P P', reverse P P' ->
    (exists i, schulze_winner (matrix_of P) i /\ ~ schulze_winner (matrix_of P') i)
    <->
    (exists j, ~ schulze_winner (matrix_of P) j /\ schulze_winner (matrix_of P') j).
  Proof.
    intros P P' HR.
    pose proof (reversal_symmetry_S (NT_selective (spec m)) (NT_eq_dec (spec m))
                  (NT_meet_lower_bound (spec m)) (matrix_of P)) as H.
    pose proof (schulze_winner_ext (matrix_of P') (fun i j => matrix_of P j i)
                  (matrix_of_reverse P P' HR)) as E.
    split.
    - intros [i [Hi Hni]].
      destruct (proj1 H (ex_intro _ i (conj Hi (fun Hc => Hni (proj2 (E i) Hc)))))
        as [j [Hnj Hj]].
      exists j. split; [exact Hnj | apply (E j); exact Hj].
    - intros [j [Hnj Hj]].
      destruct (proj2 H (ex_intro _ j (conj Hnj (proj1 (E j) Hj))))
        as [i [Hi Hni]].
      exists i. split; [exact Hi | intro Hc; apply Hni; apply (E i); exact Hc].
  Qed.

  (* ================================================================== *)
  (*  Anonymity (Schulze 2.1)                                            *)
  (*                                                                     *)
  (*  Schulze observes that a method whose link strengths depend only on *)
  (*  the counts is anonymous.  Here that is a permutation invariance of *)
  (*  [count].                                                           *)
  (* ================================================================== *)

  Lemma count_perm : forall P P', Permutation P P' ->
    forall i j, count P i j = count P' i j.
  Proof. intros P P' HP i j. unfold count. apply filter_length_perm. exact HP. Qed.

  Lemma matrix_of_perm : forall P P', Permutation P P' ->
    forall i j, matrix_of P i j = matrix_of P' i j.
  Proof.
    intros P P' HP i j. destruct (fin_eq_dec i j) as [Hij | Hij].
    - rewrite (matrix_of_diag P i j Hij), (matrix_of_diag P' i j Hij). reflexivity.
    - rewrite (matrix_of_off P i j Hij), (matrix_of_off P' i j Hij).
      rewrite (count_perm P P' HP i j), (count_perm P P' HP j i). reflexivity.
  Qed.

  Theorem anonymity_from_profile : forall P P', Permutation P P' ->
    forall a, schulze_winner (matrix_of P) a <-> schulze_winner (matrix_of P') a.
  Proof. intros P P' HP. exact (schulze_winner_ext _ _ (matrix_of_perm P P' HP)). Qed.

End BallotN.
