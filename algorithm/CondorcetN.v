From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN
  ReversalsymmetryN MonotonicityN ParetoN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ===================================================== *)
(*  Schulze over a semiring: Condorcet consistency      *)
(*  Split out of the former monolithic SocialchoiceN.v. *)
(* ===================================================== *)

Section CondorcetN.

  Context {Node : FinType.type}.



  (** * Condorcet consistency.  In the paper this is not a separate section:
      it is the Remark in §4.7 — "If B1 consists of only one alternative
      a ∈ A, then this is the so-called Condorcet criterion" — i.e. the
      Smith criterion (4.7.3)/(4.7.4) with [B1 = {a}].  Here it is proved
      directly, and in a stronger form: the Condorcet winner is a strict
      winner, not merely undefeated.

      [condorcet_implies_strict_winner], with [H_pair_sum_one] replaced by
      [H_cross] — every edge *into* the Condorcet winner [A] is strictly below
      the closure strength *out of* [A], rather than forcing every outgoing
      edge to equal the semiring's top [1].

      Two things about the shape of [H_cross] are deliberate.

      It is restricted to distinct endpoints [Z ≠ X].  Stated for all [Z] and
      [X] against the direct link it would also assert [M X A < M A X] for
      every [X ≠ A], which is exactly [condorcet_winner M A] — the Condorcet
      premise would then be implied by the side condition and contribute
      nothing.  With the diagonal excluded the two hypotheses are independent:
      [H_cross] handles [Z ≠ X] and the Condorcet property supplies [Z = X],
      via [M X A < M A X ≤ mat_star M A X].

      Its right-hand side is the closure [mat_star M A X], not the direct link
      [M A X].  This is strictly weaker — [M A X ≤ mat_star M A X] always — and
      it is what the proof actually needs, since the conclusion compares
      closures.  The difference matters: [A] may beat [X] only weakly head to
      head while dominating it through a beatpath, which is the very situation
      the Schulze method exists to handle.  On three nodes in the max-min
      semiring (top [3]), take [M A B = 1], [M B A = 0], [M A C = 3],
      [M C A = 2], [M C B = 3], [M B C = 0].  Then [A] is a Condorcet winner
      and a strict Schulze winner, because [mat_star M A B = 3] via the
      beatpath [A → C → B] even though the direct link [M A B] is only [1].
      The direct-link form of the hypothesis rejects this profile at
      [Z = C, X = B] (since [M C A = 2 ≥ 1 = M A B]), while the closure form
      accepts it ([2 < 3 = mat_star M A B]).  *)
  Theorem condorcet_implies_strict_winner_weaker  {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (H_cross : forall Z X, Z <> A -> X <> A -> Z <> X ->
       M Z A < mat_star M A X) :
    condorcet_winner M A -> strict_winner M A.
  Proof.
    intros Hcw X0 HX0.
    unfold schulze_beats, beats.
    (* Every edge into [A] is strictly below the target [mat_star M A X0]:
       off-diagonal by [H_cross], diagonal by the Condorcet hypothesis. *)
    assert (Hdom : forall w, w <> A -> M w A < mat_star M A X0).
    { intros w Hw. destruct (fin_eq_dec w X0) as [->|Hne].
      - eapply orel_lt_le_trans; [exact (Hcw X0 HX0) | apply link_le_mat_star].
      - exact (H_cross w X0 Hw HX0 Hne). }
    (* Every walk of length n into A, from any w <> A, stays strictly below
       that same target. *)
    assert (H_pow_lt : forall n w, w <> A -> pow M n w A < mat_star M A X0).
    { induction n as [|n IH]; intros w Hw.
      - (* n = 0: pow M 0 w A = I w A = 0, since w <> A *)
        cbn [pow]. unfold I.
        destruct (fin_eq_dec w A) as [Heq|Hneq]; [congruence|].
        split.
        + apply zero_is_bottom.
        + intro Heq0.
          destruct (Hdom X0 HX0) as [Hd_le Hd_ne].
          apply Hd_ne. unfold Orel in Hd_le.
          rewrite <- Heq0 in Hd_le. rewrite addr0 in Hd_le.
          rewrite Hd_le. exact Heq0.
      - (* n = S n: pow M (S n) w A = sum_z M w z * pow M n z A *)
        simpl. unfold matrix_mul.
        apply sum_lt_bound_if_all_lt; [exact H_total_order |].
        intro z.
        destruct (fin_eq_dec z A) as [Heqz|Hneqz].
        + (* z = A: bound via the first factor, M w A < mat_star M A X0 *)
          subst z.
          apply (orel_lt_trans (M w A * pow M n A A) (M w A) (mat_star M A X0)).
          * apply bounded_mul_lower_left.
          * apply Hdom; assumption.
        + (* z <> A: bound via the second factor, IH gives the bound on the tail *)
          apply (orel_lt_trans (M w z * pow M n z A) (pow M n z A)
                   (mat_star M A X0)).
          * apply bounded_mul_lower_right.
          * apply IH. exact Hneqz. }
    (* The target is already the closure, so no final chaining step is needed. *)
    apply (mat_star_lt_bound H_total_order). intro n.
    apply H_pow_lt. exact HX0.
  Qed.

End CondorcetN.
