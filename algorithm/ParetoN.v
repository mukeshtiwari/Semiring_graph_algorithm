From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN
  ReversalsymmetryN MonotonicityN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: the Pareto criteria (4.3)
    Split out of the former monolithic SocialchoiceN.v. *)

Section ParetoN.

  Context {Node : FinType.type}.


  (** For any path from [x] to [A] (with [x ≠ A]), swapping the destination
      from [A] to [B] gives an upper bound via [mat_star M x B].
      Proved by induction on the path length [k].  Nothing about the link
      [B → A] is needed: in the one branch that reaches it (the path is the
      single edge [B → A]) the target is [mat_star M B B], which is the top. *)
  Lemma path_xA_measure_le_mat_star_xB {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) :
    forall (k : nat) (x : Node) (p : list (Node * Node * R)),
      x ≠ A ->
      List.In p (all_paths_klength elements M k x A) ->
      measure_of_path p ≤ mat_star M x B.
  Proof.
    induction k as [|k IH]; intros x p Hx_ne_A Hin.
    - (* k = 0: all_paths_klength 0 x A = [] since x ≠ A *)
      cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec x A) as [Heq|Heq]; [congruence|].
      inversion Hin.
    - (* k = S k: peel off the head edge (x, z, M x z) *)
      destruct (all_paths_klength_S_inv M k x A p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (fin_eq_dec z A) as [Heq_zA|Hneq_zA].
      + (* z = A: q ∈ all_paths_klength k A A *)
        subst z.
        assert (Hq_le_one : measure_of_path q ≤ 1).
        { apply measure_of_path_le_one. }
        apply (orel_trans _ _ _ (bounded_mul_orel_compat_r _ _ _ Hq_le_one)).
        rewrite mulr1.
        destruct (fin_eq_dec x B) as [Heq_xB|Hneq_xB].
        * (* x = B: the target [mat_star M B B] is the top *)
          subst x. unfold mat_star. rewrite geom_sum_diag_one.
          unfold Orel. rewrite addC. apply (add_bound (s := R) (M B A)).
        * apply (orel_trans _ _ _ (Hcol x Hx_ne_A Hneq_xB)).
          apply link_le_mat_star.
      + (* z ≠ A: chain the head link with the tail through [z] *)
        assert (Hq_bound : measure_of_path q ≤ mat_star M z B).
        { apply IH; [exact Hneq_zA | exact Hq]. }
        apply (orel_trans _ _ _ (bounded_mul_orel_compat_r _ _ _ Hq_bound)).
        apply (orel_trans _ _ _
          (bounded_mul_orel_compat_l _ _ _ (link_le_mat_star M x z))).
        apply star_path_compose.
  Qed.

  (** [pow M n B A ≤ mat_star M A B] — the core lemma.
      Uses [path_xA_measure_le_mat_star_xB] for the inductive step
      when the first edge goes to a third party, and [star_path_compose]
      to chain through the intermediate node. *)
  Lemma pow_BA_le_mat_star_AB {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hneq : A ≠ B) (Hle : M B A ≤ M A B)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (n : nat) : pow M n B A ≤ mat_star M A B.
  Proof.
    apply pow_bound_of_paths.
    induction n as [|k IH]; intros p Hin.
    - (* n = 0: all_paths_klength 0 B A = [] since B ≠ A *)
      cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec B A) as [Heq_BA|_]; [congruence | inversion Hin].
    - (* n = S k: peel off the head edge (B, z, M B z) *)
      destruct (all_paths_klength_S_inv M k B A p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (fin_eq_dec z A) as [Heq_zA|Hneq_zA].
      + (* z = A: the head edge is the direct link (B, A); bound the whole
           path by it, then by [M A B] and hence by the closure *)
        subst z.
        eapply orel_trans; [apply bounded_mul_lower_left |].
        eapply orel_trans; [exact Hle | apply link_le_mat_star].
      + destruct (fin_eq_dec z B) as [Heq_zB|Hneq_zB].
        * (* z = B: a self-loop of weight 1, the tail is still a path B ⇝ A *)
          subst z. rewrite (Hdiag_one B B eq_refl), mul1r.
          apply (IH _ Hq).
        * (* z ≠ A, B: bound the tail by [mat_star M z B] and chain *)
          assert (Hq_bound : measure_of_path q ≤ mat_star M z B).
          { exact (path_xA_measure_le_mat_star_xB M A B Hcol
              k z q Hneq_zA Hq). }
          apply (orel_trans _ _ _
            (bounded_mul_orel_compat_l _ _ _ (Hrow z Hneq_zA Hneq_zB))).
          apply (orel_trans _ _ _ (bounded_mul_orel_compat_r _ _ _ Hq_bound)).
          apply (orel_trans _ _ _
            (bounded_mul_orel_compat_l _ _ _ (link_le_mat_star M A z))).
          apply star_path_compose.
  Qed.


  (** ** Pareto criterion (Section 4.3)

      Two versions appear in the literature:
        1. If a ≻ᵥ b for all v ∈ V, then a ≻ b.
        2. If a ≿ᵥ b for all v ∈ V and a ≻ᵥ b for some v ∈ V,
           then a ≻ b.

      The Schulze method satisfies both.  We formalise the second
      (stronger) version as [pareto_stronger] below.  The first
      (weaker) version is [pareto]. *)


  


  (** ** Version 1 — pareto_weaker (weaker form):  a ≽ᵥ b ∀v  →  a ≽ b

      If A dominates B head to head and in every third-party comparison,
      then A is at least as strong as B in the Schulze ranking:
      mat_star M B A ≤ mat_star M A B.  This is Schulze (4.3.2.10),
      which gives (4.3.2.2) [ba ∉ O].

      The stronger form (strict <) is [pareto_stronger] below; it needs
      two extra hypotheses, see the comment there.

      Hypotheses:
        A ≠ B            — distinct candidates
        M B A ≤ M A B    — A is at least as strong as B head to head.
                            Schulze's (4.3.2.1) — no voter strictly
                            prefers B to A — gives the stronger
                            M B A = 0, which implies this; the proof
                            only needs the inequality, and it cannot be
                            dropped altogether: the two hypotheses below
                            both exclude X ∈ {A, B}, so nothing else
                            constrains the link B → A.
        M B X ≤ M A X    — ballot transitivity: voters who have B≻X
                            also have A≻X (since A≽B)
        M X A ≤ M X B    — ballot transitivity: voters who have X≻A
                            also have X≻B (since A≽B)
        M i i = 1         — diagonal is the multiplicative identity *)


  Theorem pareto_weaker {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node) :
    A ≠ B -> M B A ≤ M A B ->
    (forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X) ->
    (forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) ->
    (forall i j, i = j -> M i j = 1) ->
    (mat_star M B A ≤ mat_star M A B).
  Proof.
    intros Hneq Hle Hrow Hcol Hdiag_one.
    apply mat_star_bound. intro n.
    exact (pow_BA_le_mat_star_AB M A B Hneq Hle Hrow Hcol Hdiag_one n).
  Qed.

  (** ** The remaining Pareto [#2] conclusions (4.3.2.3 / .4 / .5)

      All three rest on the paper's two path-rewriting steps: (4.3.2.11)
      swaps the SOURCE of a path out of [B] to [A], and (4.3.2.12) swaps
      its TARGET from [A] to [B].  Schulze performs both by editing the
      strongest path; here they are inductions on the closure. *)

  (** (4.3.2.11): [P_D[a,f] ≽ P_D[b,f]].  Every walk out of [B] is dominated
      by one out of [A]: its first edge improves by [Hrow], and once the walk
      has left [{A, B}] the rest is bounded by the closure. *)
  Lemma pareto_star_source_swap {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hdiag : forall u v : Node, u = v -> M u v = 1)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (F : Node) (HFB : F ≠ B) :
    mat_star M B F ≤ mat_star M A F.
  Proof.
    apply mat_star_bound. intro n.
    induction n as [|k IH].
    - cbn [pow]. unfold I.
      destruct (fin_eq_dec B F) as [Heq|_];
        [exfalso; apply HFB; symmetry; exact Heq | apply zero_is_bottom].
    - simpl. unfold matrix_mul.
      apply sum_orel_bound. intro z.
      destruct (fin_eq_dec z A) as [HzA|HzA].
      + (* the walk reaches A: the tail is a walk A ⇝ F *)
        subst z. eapply orel_trans; [apply bounded_mul_lower_right |].
        apply pow_le_mat_star_any; exact Hdiag.
      + destruct (fin_eq_dec z B) as [HzB|HzB].
        * (* still at B: recurse *)
          subst z. eapply orel_trans; [apply bounded_mul_lower_right |]. exact IH.
        * (* left {A,B}: improve the head edge by Hrow, then chain *)
          eapply orel_trans;
            [apply (bounded_mul_orel_compat_l _ _ _ (Hrow z HzA HzB)) |].
          eapply orel_trans;
            [apply (bounded_mul_orel_compat_r _ _ _
                      (pow_le_mat_star_any M Hdiag k z F)) |].
          eapply orel_trans;
            [apply (bounded_mul_orel_compat_l _ _ _ (link_le_mat_star M A z)) |].
          apply star_path_compose.
  Qed.

  (** (4.3.2.12): [P_D[f,b] ≽ P_D[f,a]].  This is exactly what
      [path_xA_measure_le_mat_star_xB] already says, lifted from paths to the
      closure. *)
  Lemma pareto_star_target_swap {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B)
    (F : Node) (HFA : F ≠ A) :
    mat_star M F A ≤ mat_star M F B.
  Proof.
    apply mat_star_bound. intro n.
    apply pow_bound_of_paths. intros p Hp.
    exact (path_xA_measure_le_mat_star_xB M A B Hcol n F p HFA Hp).
  Qed.

  (** Pareto (4.3.2.3): if [B] beats [F] then so does [A]. *)
  Theorem pareto_weaker_beats_transfer {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hdiag : forall u v : Node, u = v -> M u v = 1)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) :
    forall F, F ≠ A -> F ≠ B -> schulze_beats M B F -> schulze_beats M A F.
  Proof.
    intros F HFA HFB HBF.
    unfold schulze_beats, beats in *.
    apply (orel_lt_le_trans (mat_star M F A) (mat_star M B F) (mat_star M A F)).
    - apply (orel_lt_trans (mat_star M F A) (mat_star M F B) (mat_star M B F)).
      + exact (pareto_star_target_swap M A B Hcol F HFA).
      + exact HBF.
    - exact (pareto_star_source_swap M A B Hdiag Hrow F HFB).
  Qed.

  (** Pareto (4.3.2.4): if [F] beats [A] then it also beats [B]. *)
  Theorem pareto_weaker_loses_transfer {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hdiag : forall u v : Node, u = v -> M u v = 1)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) :
    forall F, F ≠ A -> F ≠ B -> schulze_beats M F A -> schulze_beats M F B.
  Proof.
    intros F HFA HFB HF_beats_A.
    unfold schulze_beats, beats in *.
    apply (orel_lt_le_trans (mat_star M B F) (mat_star M F A) (mat_star M F B)).
    - apply (orel_lt_trans (mat_star M B F) (mat_star M A F) (mat_star M F A)).
      + exact (pareto_star_source_swap M A B Hdiag Hrow F HFB).
      + exact HF_beats_A.
    - exact (pareto_star_target_swap M A B Hcol F HFA).
  Qed.

  (** Pareto (4.3.2.5): if [B] is a winner then so is [A].  The [f = B] case
      is (4.3.2.2), i.e. [pareto_weaker]; every other [f] goes through
      (4.3.2.4). *)
  Theorem pareto_weaker_winner_transfer {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hneq : A ≠ B) (Hle : M B A ≤ M A B)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B)
    (Hdiag : forall i j : Node, i = j -> M i j = 1) :
    schulze_winner M B -> schulze_winner M A.
  Proof.
    intros HB f Hf_ne_A Hbeats.
    destruct (fin_eq_dec f B) as [HfB | HfB].
    - subst f. destruct Hbeats as [Hle' Hne'].
      apply Hne'. apply orel_antisym; [exact Hle' |].
      exact (pareto_weaker M A B Hneq Hle Hrow Hcol Hdiag).
    - exact (HB f HfB
               (pareto_weaker_loses_transfer M A B Hdiag Hrow Hcol
                  f Hf_ne_A HfB Hbeats)).
  Qed.

  (** Key lemma.  Every path into [A] starting from some [x ≠ A] has measure
      at most the strongest link [M A B], and it attains [M A B] only when the
      direct link [x → A] is itself of maximal strength.

      This is the algebraic form of Schulze's observation that a route made
      entirely of unanimous links is itself a unanimous link: at each step the
      head edge either loses strength (so the whole product does) or is
      maximal, and [Htop_trans] composes it with the maximal tail. *)
  Lemma path_to_A_measure_top {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htop_trans : forall X Y Z, M X Y = M A B ->
      M Y Z = M A B -> M X Z = M A B)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1) :
    forall (k : nat) (x : Node) (p : list (Node * Node * R)),
      x ≠ A ->
      List.In p (all_paths_klength elements M k x A) ->
      measure_of_path p ≤ M A B
      /\ (measure_of_path p = M A B -> M x A = M A B).
  Proof.
    induction k as [|k IH]; intros x p Hx_ne_A Hin.
    - (* k = 0: no path, since x ≠ A *)
      cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec x A) as [Heq|Heq]; [congruence|].
      inversion Hin.
    - (* k = S k: peel off the head edge (x, z, M x z) *)
      destruct (all_paths_klength_S_inv M k x A p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (fin_eq_dec z A) as [Heq_zA|Hneq_zA].
      + (* head edge already lands on A *)
        subst z.
        assert (HxA_le : M x A ≤ M A B) by (apply Hmax; exact Hx_ne_A).
        assert (Hlow : M x A * measure_of_path q ≤ M x A)
          by apply bounded_mul_lower_left.
        split.
        * exact (orel_trans _ _ _ Hlow HxA_le).
        * intro Heq.
          apply orel_antisym; [exact HxA_le | rewrite <- Heq; exact Hlow].
      + (* head edge goes to a third node z, so the tail is a path z ⇝ A *)
        destruct (IH z q Hneq_zA Hq) as [Hq_le Hq_top].
        destruct (fin_eq_dec x z) as [Hxz|Hxz].
        * (* self-loop: weight 1, the measure is unchanged *)
          subst z. rewrite (Hdiag_one x x eq_refl), mul1r.
          split; [exact Hq_le | exact Hq_top].
        * assert (Hxz_le : M x z ≤ M A B) by (apply Hmax; exact Hxz).
          split.
          { exact (orel_trans _ _ _ (bounded_mul_lower_left _ _) Hxz_le). }
          { intro Heq.
            (** the product attains the top, so both factors do *)
            assert (Hxz_top : M x z = M A B).
            { apply orel_antisym;
              [exact Hxz_le | rewrite <- Heq; apply bounded_mul_lower_left]. }
            assert (Hq_eq : measure_of_path q = M A B).
            { apply orel_antisym;
              [exact Hq_le | rewrite <- Heq; apply bounded_mul_lower_right]. }
            exact (Htop_trans x z A Hxz_top (Hq_top Hq_eq)). }
  Qed.

  (** No route from [B] back to [A] can match the link [A → B], as long as the
      link [B → A] is not itself maximal.  Unanimity gives that for free:
      [M B A = 0 ≠ M A B]. *)
  Lemma path_BA_measure_lt {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htop_trans : forall X Y Z, M X Y = M A B -> M Y Z = M A B -> M X Z = M A B)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (Hneq : A ≠ B) (Hne_top : M B A ≠ M A B) :
    forall (k : nat) (p : list (Node * Node * R)),
      List.In p (all_paths_klength elements M k B A) ->
      measure_of_path p < M A B.
  Proof.
    intros k p Hin.
    assert (HB_ne_A : B ≠ A).
    { intro Habs. apply Hneq. symmetry. exact Habs. }
    destruct (path_to_A_measure_top M A B Htop_trans Hmax Hdiag_one
      k B p HB_ne_A Hin) as [Hle Htop].
    split; [exact Hle |].
    intro Heq. exact (Hne_top (Htop Heq)).
  Qed.

  (** Each power of [M] is therefore strictly below the link [A → B] at [B, A]. *)
  Lemma pow_BA_lt_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B -> M Y Z = M A B -> M X Z = M A B)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (Hneq : A ≠ B) (Hne_top : M B A ≠ M A B) (Hpos : 0 < M A B)
    (n : nat) : pow M n B A < M A B.
  Proof.
    apply (pow_lt_bound_of_paths Htotal); [exact Hpos |].
    intros p Hin.
    exact (path_BA_measure_lt M A B Htop_trans Hmax Hdiag_one
      Hneq Hne_top n p Hin).
  Qed.

  (** …and so is the whole closure. *)
  Lemma mat_star_BA_lt_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B -> 
      M Y Z = M A B -> M X Z = M A B)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (Hneq : A ≠ B) (Hne_top : M B A ≠ M A B) (Hpos : 0 < M A B) :
    mat_star M B A < M A B.
  Proof.
    apply (mat_star_lt_bound Htotal). intro n.
    exact (pow_BA_lt_link M A B Htotal Htop_trans Hmax Hdiag_one
      Hneq Hne_top Hpos n).
  Qed.

  (** Pareto (4.3.1.2): the unanimously preferred alternative beats the
      dominated one, [ab ∈ O] — here as the strict closure comparison that
      (2.2.1) reads as [ab ∈ O]. *)
  Theorem pareto_stronger {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B ->
      M Y Z = M A B -> M X Z = M A B) :
    A ≠ B -> M B A = 0 -> 0 < M A B ->
    (forall X Y, X ≠ Y -> M X Y ≤ M A B) ->
    (forall i j, i = j -> M i j = 1) ->
    mat_star M B A < mat_star M A B.
  Proof.
    intros Hneq Hzero Hpos Hmax Hdiag_one.
    (** unanimity makes the reverse link [B → A] non-maximal *)
    assert (Hne_top : M B A ≠ M A B).
    { rewrite Hzero. exact (proj2 Hpos). }
    (** the reverse closure is strictly below the link, so (2.2.4) applies *)
    apply link_beats.
    exact (mat_star_BA_lt_link M A B Htotal Htop_trans Hmax Hdiag_one
      Hneq Hne_top Hpos).
  Qed.

  (** Pareto (4.3.1.3): the unanimously dominated alternative is not a winner. *)
  Corollary pareto_stronger_loser {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B ->
      M Y Z = M A B -> M X Z = M A B) :
    A ≠ B -> M B A = 0 -> 0 < M A B ->
    (forall X Y, X ≠ Y -> M X Y ≤ M A B) ->
    (forall i j, i = j -> M i j = 1) ->
    ~ schulze_winner M B.
  Proof.
    intros Hneq Hzero Hpos Hmax Hdiag_one Hwin.
    exact (Hwin A Hneq (pareto_stronger M A B Htotal Htop_trans
      Hneq Hzero Hpos Hmax Hdiag_one)).
  Qed.

  (** ** The converse

      Unanimity itself is not recoverable from the conclusion: the
      Schulze order ranks candidates strictly in profiles that contain no
      unanimous pair at all (the paper's own Example 1, formalised in
      examples/Schulze.v, has d ≻ a with every pairwise count non-zero).
      What does reverse is the property the proof actually turns on:
      under the standing hypotheses, [A] beats [B] in the closure exactly
      when the reverse link [B → A] is not itself of maximal strength.
      [pareto_stronger] is the instance [M B A = 0]. *)

  (** A path between two distinct nodes is bounded by the strongest link: it
      must contain a non-loop edge, and a product lies below each factor. *)
  Lemma path_measure_le_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1) :
    forall (k : nat) (x y : Node) (p : list (Node * Node * R)),
      x ≠ y ->
      List.In p (all_paths_klength elements M k x y) ->
      measure_of_path p ≤ M A B.
  Proof.
    induction k as [|k IH]; intros x y p Hxy Hin.
    - cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec x y) as [Heq|_]; [congruence | inversion Hin].
    - destruct (all_paths_klength_S_inv M k x y p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (fin_eq_dec x z) as [Hxz|Hxz].
      + (* self-loop of weight 1: the tail is still a path from x to y *)
        subst z. rewrite (Hdiag_one x x eq_refl), mul1r.
        exact (IH x y q Hxy Hq).
      + exact (orel_trans _ _ _ (bounded_mul_lower_left _ _) (Hmax x z Hxz)).
  Qed.

  Lemma pow_xy_le_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (n : nat) (x y : Node) : x ≠ y -> pow M n x y ≤ M A B.
  Proof.
    intros Hxy.
    apply pow_bound_of_paths.
    intros p Hin.
    exact (path_measure_le_link M A B Hmax Hdiag_one n x y p Hxy Hin).
  Qed.

  Lemma mat_star_le_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (x y : Node) : x ≠ y -> mat_star M x y ≤ M A B.
  Proof.
    intros Hxy. apply mat_star_bound. intro n.
    exact (pow_xy_le_link M A B Hmax Hdiag_one n x y Hxy).
  Qed.

  (** The strongest link is its own closure — no detour improves on it. *)
  Lemma mat_star_link_eq {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (Hneq : A ≠ B) : mat_star M A B = M A B.
  Proof.
    apply orel_antisym.
    - exact (mat_star_le_link M A B Hmax Hdiag_one A B Hneq).
    - apply link_le_mat_star.
  Qed.

  (** Both directions.  [pareto_stronger] is the special case [M B A = 0]. *)
  Theorem pareto_stronger_iff {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B ->
      M Y Z = M A B -> M X Z = M A B) :
    A ≠ B -> 0 < M A B ->
    (forall X Y, X ≠ Y -> M X Y ≤ M A B) ->
    (forall i j, i = j -> M i j = 1) ->
    (mat_star M B A < mat_star M A B <-> M B A ≠ M A B).
  Proof.
    intros Hneq Hpos Hmax Hdiag_one.
    assert (Hstar_AB : mat_star M A B = M A B).
    { exact (mat_star_link_eq M A B Hmax Hdiag_one Hneq). }
    split.
    - (* a maximal reverse link would already tie the two closures *)
      intros [Hle Hne] Habs.
      apply Hne, orel_antisym; [exact Hle |].
      rewrite Hstar_AB, <- Habs.
      apply link_le_mat_star.
    - intros Hne_top.
      eapply orel_lt_le_trans.
      + exact (mat_star_BA_lt_link M A B Htotal Htop_trans Hmax Hdiag_one
          Hneq Hne_top Hpos).
      + rewrite Hstar_AB. apply bounded_orel_refl.
  Qed.

End ParetoN.
