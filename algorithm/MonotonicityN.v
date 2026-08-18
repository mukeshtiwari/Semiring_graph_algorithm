From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN
  ReversalsymmetryN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ===================================================== *)
(*  Schulze over a semiring: monotonicity (4.5)         *)
(*  Split out of the former monolithic SocialchoiceN.v. *)
(* ===================================================== *)

Section MonotonicityN.

  Context {Node : FinType.type}.


  (** * Monotonicity (Section 4.2 of the Schulze paper)

      If we strengthen candidate [A] — increasing [A]'s wins over other
      candidates and decreasing other candidates' wins over [A], while
      leaving all other pairwise comparisons unchanged — then [A]'s
      Kleene-star strength to any candidate [C] does not decrease:
        mat_star M A C ≤ mat_star M' A C.

      Hypotheses:
        [Hrow]:  M A Y  ≤ M' A Y   (A's outgoing edges increase)
        [Heq]:   M X Y  = M' X Y   for X≠A, Y≠A (everything else unchanged)
  *)
  (* ===================================================================== *)
  (*  Row / column irrelevance of the closure.                              *)
  (*                                                                        *)
  (*  In a bounded semiring the closure entry OUT of a node [A] does not    *)
  (*  depend on the edges INTO [A], and the entry INTO [A] does not depend  *)
  (*  on the edges OUT of [A]: a walk A -> .. -> A -> .. -> b is dominated  *)
  (*  by its suffix from the last visit to [A], and a walk b -> .. -> A ->  *)
  (*  .. -> A by its prefix to the first visit, because in a bounded        *)
  (*  semiring a product is below each factor.  Algebraically each fact is  *)
  (*  a single induction on the power, peeling the last (respectively the   *)
  (*  first) edge.  Neither selectivity nor commutativity is involved.      *)
  (* ===================================================================== *)

  Lemma one_le_mat_star_diag {R : BoundedSemiring.type}
    (N : @Matrix Node R) (a : Node) : (1 : R) ≤ mat_star N a a.
  Proof.
    pose proof (pow_le_geom_sum N (@kleene_exp Node) 0 a a ltac:(lia)) as H.
    cbn [pow] in H. revert H. unfold mat_star, I.
    destruct (fin_eq_dec a a) as [_ | C]; [exact (fun H => H) | congruence].
  Qed.

  (** If [M] and [N] agree everywhere outside column [A], every power of
      [M] out of [A] is below the closure of [N] out of [A]. *)
  Lemma pow_le_mat_star_col_agree {R : BoundedSemiring.type}
    (M N : @Matrix Node R) (A : Node)
    (Hagree : forall x y : Node, y <> A -> M x y = N x y) :
    forall (k : nat) (z : Node), pow M k A z ≤ mat_star N A z.
  Proof.
    assert (Hone : forall v : R, v ≤ 1)
      by (intro v; unfold Orel; rewrite addC; apply add_bound).
    induction k as [|k IH]; intro z.
    - cbn [pow].
      pose proof (pow_le_geom_sum N (@kleene_exp Node) 0 A z ltac:(lia)) as H.
      cbn [pow] in H. unfold mat_star. exact H.
    - cbn [pow].
      assert (Epeel : matrix_mul M (pow M k) A z = matrix_mul (pow M k) M A z)
        by apply pow_comm.
      rewrite Epeel. unfold matrix_mul.
      apply sum_orel_bound. intro w.
      destruct (fin_eq_dec z A) as [-> | HzA].
      + eapply orel_trans; [apply Hone |]. apply one_le_mat_star_diag.
      + rewrite (Hagree w z HzA).
        eapply orel_trans.
        { apply bounded_mul_orel_compat_l. exact (IH w). }
        eapply orel_trans.
        { apply bounded_mul_orel_compat_r. apply link_le_mat_star. }
        apply star_path_compose.
  Qed.

  (** Dually: if [M] and [N] agree everywhere outside row [A], every power
      of [M] into [A] is below the closure of [N] into [A]. *)
  Lemma pow_le_mat_star_row_agree {R : BoundedSemiring.type}
    (M N : @Matrix Node R) (A : Node)
    (Hagree : forall x y : Node, x <> A -> M x y = N x y) :
    forall (k : nat) (z : Node), pow M k z A ≤ mat_star N z A.
  Proof.
    assert (Hone : forall v : R, v ≤ 1)
      by (intro v; unfold Orel; rewrite addC; apply add_bound).
    induction k as [|k IH]; intro z.
    - cbn [pow].
      pose proof (pow_le_geom_sum N (@kleene_exp Node) 0 z A ltac:(lia)) as H.
      cbn [pow] in H. unfold mat_star. exact H.
    - cbn [pow]. unfold matrix_mul.
      apply sum_orel_bound. intro w.
      destruct (fin_eq_dec z A) as [-> | HzA].
      + eapply orel_trans; [apply Hone |]. apply one_le_mat_star_diag.
      + rewrite (Hagree z w HzA).
        eapply orel_trans.
        { apply bounded_mul_orel_compat_r. exact (IH w). }
        eapply orel_trans.
        { apply bounded_mul_orel_compat_l. apply link_le_mat_star. }
        apply star_path_compose.
  Qed.

  (** * Monotonicity — forward direction (strength OUT of [A])

      Raising [A]'s row cannot lower any closure entry out of [A].  Proof:
      replace column [A] of [M] by that of [M'] — column irrelevance says
      the closure out of [A] does not change — and the result is entrywise
      below [M'], so closure monotonicity finishes.  No totality and no
      commutativity: this holds over any bounded semiring. *)
  Theorem monotonicity {R : BoundedSemiring.type}
    (M M' : @Matrix Node R) (A : Node) :
    (forall (Y : Node), M A Y ≤ M' A Y) ->
    (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
    forall (C : Node), mat_star M A C ≤ mat_star M' A C.
  Proof.
    intros Hrow Heq C.
    set (Mid := fun x y : Node => if fin_eq_dec y A then M' x A else M x y).
    assert (Hagree : forall x y : Node, y <> A -> M x y = Mid x y).
    { intros x y Hy. unfold Mid.
      destruct (fin_eq_dec y A) as [E|_]; [congruence | reflexivity]. }
    assert (Hup : forall x y : Node, Mid x y ≤ M' x y).
    { intros x y. unfold Mid.
      destruct (fin_eq_dec y A) as [-> | Hy].
      - apply (@bounded_orel_refl R _).
      - destruct (fin_eq_dec x A) as [-> | Hx].
        + apply Hrow.
        + rewrite (Heq x y Hx Hy). apply (@bounded_orel_refl R _). }
    eapply orel_trans.
    - apply mat_star_bound. intro n.
      exact (pow_le_mat_star_col_agree M Mid A Hagree n C).
    - unfold mat_star. exact (geom_sum_monotone Mid M' (@kleene_exp Node) Hup A C).
  Qed.

  (** * Monotonicity — reverse direction (strength INTO [A])

      Lowering [A]'s column cannot raise any closure entry into [A].  Same
      shape: replace row [A] of [M'] by that of [M] — row irrelevance says
      the closure into [A] does not change — and the result is entrywise
      below [M].  The previous proof went through the transpose and thereby
      needed commutativity of [*]; this one does not. *)
  Lemma monotonicity_rev {R : BoundedSemiring.type}
    (M M' : @Matrix Node R) (A : Node) :
    (forall (X : Node), M' X A ≤ M X A) ->
    (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
    forall (C : Node), mat_star M' C A ≤ mat_star M C A.
  Proof.
    intros Hcol Heq C.
    set (Mid := fun x y : Node => if fin_eq_dec x A then M x y else M' x y).
    assert (Hagree : forall x y : Node, x <> A -> M' x y = Mid x y).
    { intros x y Hx. unfold Mid.
      destruct (fin_eq_dec x A) as [E|_]; [congruence | reflexivity]. }
    assert (Hdown : forall x y : Node, Mid x y ≤ M x y).
    { intros x y. unfold Mid.
      destruct (fin_eq_dec x A) as [-> | Hx].
      - apply (@bounded_orel_refl R _).
      - destruct (fin_eq_dec y A) as [-> | Hy].
        + apply Hcol.
        + rewrite <- (Heq x y Hx Hy). apply (@bounded_orel_refl R _). }
    eapply orel_trans.
    - apply mat_star_bound. intro n.
      exact (pow_le_mat_star_row_agree M' Mid A Hagree n C).
    - unfold mat_star. exact (geom_sum_monotone Mid M (@kleene_exp Node) Hdown C A).
  Qed.

  (** * Monotonicity — winner level (paper §4.2: "a winner stays a winner")

      Raising [A] cannot harm a winner: if [A] is a Schulze winner in the
      original profile, then [A] is still a Schulze winner after [A] is
      raised.  Both directions are used: the forward theorem bounds [A]'s
      outgoing strengths below, and [monotonicity_rev] bounds the incoming
      strengths above, so the strict comparison [beats] is preserved.

      Hypotheses (exactly the pairwise-matrix content of "raise [A]"):
        [Hrow]:  M A Y  ≤ M' A Y   (A's outgoing edges increase)
        [Hcol]:  M' X A ≤ M X A    (A's incoming edges decrease)
        [Heq]:   M X Y  = M' X Y   for X≠A, Y≠A (everything else unchanged)
  *)
  Theorem winner_monotonicity {R : BoundedSemiring.type}
    (M M' : @Matrix Node R) (A : Node) :
    (forall (Y : Node), M A Y ≤ M' A Y) ->
    (forall (X : Node), M' X A ≤ M X A) ->
    (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
    schulze_winner M A -> schulze_winner M' A.
  Proof.
    intros Hrow Hcol Heq Hwin b Hb_ne_A.
    pose proof (monotonicity M M' A Hrow Heq b) as Hout.
    pose proof (monotonicity_rev M M' A Hcol Heq b) as Hin.
    intro Hbeats.
    apply (Hwin b Hb_ne_A).
    unfold schulze_beats, beats in Hbeats |- *.
    destruct Hbeats as [Hle Hne].
    split.
    - (* mat_star M A b ≤ mat_star M b A, chained through the raised profile *)
      apply (orel_trans _ _ _ Hout).
      apply (orel_trans _ _ _ Hle).
      exact Hin.
    - (* mat_star M A b ≠ mat_star M b A: otherwise the raised comparison ties *)
      intro Heq0.
      apply Hne.
      apply orel_antisym.
      + exact Hle.
      + eapply orel_trans; [exact Hin |].
        rewrite <- Heq0. exact Hout.
  Qed.

  (** Monotonicity (4.5.4): a victory of [A] survives the raise. *)
  Theorem monotonicity_beats {R : BoundedSemiring.type}
    (M M' : @Matrix Node R) (A : Node)
    (Hrow : forall Y : Node, M A Y ≤ M' A Y)
    (Hcol : forall X : Node, M' X A ≤ M X A)
    (Heq : forall X Y : Node, X ≠ A -> Y ≠ A -> M X Y = M' X Y) :
    forall b, schulze_beats M A b -> schulze_beats M' A b.
  Proof.
    intros b [Hle Hne].
    pose proof (monotonicity M M' A Hrow Heq b) as Hout.
    pose proof (monotonicity_rev M M' A Hcol Heq b) as Hin.
    split.
    - apply (orel_trans _ _ _ Hin). apply (orel_trans _ _ _ Hle). exact Hout.
    - intro Heq0.
      apply Hne. apply orel_antisym; [exact Hle |].
      apply (orel_trans _ _ _ Hout). rewrite Heq0 in Hin. exact Hin.
  Qed.

  (** Monotonicity (4.5.5): a defeat that [A] avoided before, it still avoids.
      The pointwise form of [winner_monotonicity]. *)
  Theorem monotonicity_unbeaten {R : BoundedSemiring.type}
    (M M' : @Matrix Node R) (A : Node)
    (Hrow : forall Y : Node, M A Y ≤ M' A Y)
    (Hcol : forall X : Node, M' X A ≤ M X A)
    (Heq : forall X Y : Node, X ≠ A -> Y ≠ A -> M X Y = M' X Y) :
    forall b, ~ schulze_beats M b A -> ~ schulze_beats M' b A.
  Proof.
    intros b Hnb Hbeats.
    pose proof (monotonicity M M' A Hrow Heq b) as Hout.
    pose proof (monotonicity_rev M M' A Hcol Heq b) as Hin.
    apply Hnb. destruct Hbeats as [Hle Hne]. split.
    - apply (orel_trans _ _ _ Hout). apply (orel_trans _ _ _ Hle). exact Hin.
    - intro Heq0. apply Hne. apply orel_antisym; [exact Hle |].
      apply (orel_trans _ _ _ Hin). rewrite <- Heq0. exact Hout.
  Qed.

  (** Monotonicity (4.5.6), the [S_new ⊆ S_old] half — under the extra
      hypothesis that [A] is nowhere tied in the closure of [M].

      That hypothesis is not in the paper, and it is doing real work.  With it,
      [untied_winner_is_strict] upgrades [A] from "unbeaten" to "beats
      everyone", so (4.5.4) carries each of those victories across the raise
      and [A] is left the only winner of [M'] — which is contained in [S_old].

      Without it the paper argues differently, and that argument is out of
      reach here.  When [A] is merely tied with some [h ∉ S_old], the raise
      need not break the tie, so the alternative that must still beat [h] in
      [M'] is some third [g].  Establishing that needs to compare
      [P_new[g,h]] with [P_new[h,g]] for [g, h ≠ A], and neither
      [monotonicity] nor [monotonicity_rev] says anything about such a pair:
      a path from [g] to [h] through [A] uses one edge into [A] (weakened)
      and one out of [A] (strengthened).  Schulze resolves it by locating the
      weakest link of each strongest path and splitting there (his cases 1
      and 2) — the same critical-link machinery that §4.2.1 needs, and which
      [mat_star_link_or_extreme] does not provide, since it yields the value
      of a closure entry but not the link witnessing it. *)
  Theorem winner_monotonicity_subset {R : BoundedSemiring.type}
    (M M' : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hrow : forall Y : Node, M A Y ≤ M' A Y)
    (Hcol : forall X : Node, M' X A ≤ M X A)
    (Heq : forall X Y : Node, X ≠ A -> Y ≠ A -> M X Y = M' X Y)
    (Hnoties : forall b, b <> A -> mat_star M A b <> mat_star M b A)
    (HA : schulze_winner M A) :
    forall h, schulze_winner M' h -> schulze_winner M h.
  Proof.
    intros h Hh.
    destruct (fin_eq_dec h A) as [HhA | HhA]; [subst h; exact HA |].
    exfalso.
    pose proof (untied_winner_is_strict H_total_order M A Hnoties HA) as Hstrict.
    exact (Hh A (fun e => HhA (eq_sym e))
             (monotonicity_beats M M' A Hrow Hcol Heq h
                (Hstrict h HhA))).
  Qed.

End MonotonicityN.
