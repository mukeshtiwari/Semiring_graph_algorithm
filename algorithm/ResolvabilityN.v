From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: resolvability, the resolution step (Schulze 4.2)
    Split out of the former monolithic SocialchoiceN.v. *)

Section ResolvabilityN.

  Context {Node : FinType.type}.

  (** * Both formulations of the paper's resolvability criterion (Sect. 4.2)

      Schulze states two versions of resolvability.  Formulation [#1]
      (4.2.1) says the proportion of profiles without a unique winner
      tends to zero as the number of voters grows, which is proved by
      reducing to the combinatorial claim below: profiles where two links
      happen to have equivalent strength become vanishingly rare as the
      electorate grows.

      Formulation [#2] (4.2.2) is the ballot-adding version: for every
      alternative [a] among several winners, one can add a single new
      ballot so that [a] becomes the unique winner.  This file develops
      only the combinatorial core underlying Formulation [#1]; the box below
      states precisely how much of it is proved here.  The rest lives in
      two later files: CriticalLinkN.v proves the combinatorial core of
      Formulation [#1] (pairwise distinct link strengths force a unique
      winner), and ResolvabilityBallotN.v proves Formulation [#2] from the
      ballots of BallotN.v. *)

  (** * Resolvability (Section 4.2) — the resolution step only

      Schulze's 4.2.1 argues that two distinct winners [a] and [b] force
      a tie [P_D[a,b] ≈ P_D[b,a]] (4.2.1.3), and then rules that out when
      no two links have equivalent strength.  What follows is the
      contrapositive of the first half: a winner that is never tied in the
      closure beats everyone, hence is the unique winner.

      The second half — that distinct LINK strengths force an untied
      closure — is [distinct_links_unique_winner] in CriticalLinkN.v.  The
      paper proves it by locating the weakest link of the strongest path
      and splitting both paths there; that file replaces the path surgery
      by threshold and cut arguments on the closure.  What remains
      unformalised is the criterion as literally stated: 4.2.1 is a limit
      over profiles as the electorate grows, and has no counterpart here. *)

  (** A winner that is nowhere tied in the closure beats everyone. *)
  Theorem untied_winner_is_strict {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (M : @Matrix Node R) (a : Node)
    (Hnoties : forall b, b <> a -> mat_star M a b <> mat_star M b a) :
    schulze_winner M a -> strict_winner M a.
  Proof.
    intros Hwin X HX.
    unfold schulze_beats, beats.
    destruct (Htotal (mat_star M a X) (mat_star M X a)) as [Hc | Hc].
    - (* mat_star M X a ≤ mat_star M a X, and they differ *)
      split.
      + unfold Orel. rewrite addC. exact Hc.
      + intro Heq. exact (Hnoties X HX (eq_sym Heq)).
    - (* the other orientation would make X beat a *)
      exfalso. apply (Hwin X HX). split; [exact Hc |].
      exact (Hnoties X HX).
  Qed.

  (** …and is therefore the only winner: the resolution step of 4.2.1. *)
  Corollary untied_winner_unique {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (M : @Matrix Node R) (a : Node)
    (Hnoties : forall b, b <> a -> mat_star M a b <> mat_star M b a) :
    schulze_winner M a -> forall w, schulze_winner M w -> w = a.
  Proof.
    intros Hwin w Hw.
    destruct (fin_eq_dec w a) as [Heq | Hne]; [exact Heq | exfalso].
    exact (strict_winner_excludes_others M a w
             (untied_winner_is_strict Htotal M a Hnoties Hwin) Hne Hw).
  Qed.

End ResolvabilityN.
