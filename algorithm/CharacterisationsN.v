From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ===================================================================== *)
(*  Schulze over a semiring: the joint characterisations.               *)
(*                                                                      *)
(*  Transitivity and winner existence are each characterised in their   *)
(*  own file, beside the criterion they complete.  The three results    *)
(*  below belong to neither, because each combines both structural      *)
(*  guarantees, so they are collected here.                             *)
(*                                                                      *)
(*  Well-formedness of the output (Schulze's Section 2.2) is            *)
(*  characterised at three alternatives, because the transitivity       *)
(*  component already supplies the converse.  The corollary that every  *)
(*  non-winner is beaten by a winner (4.1.14) is characterised at four, *)
(*  because refuting it means refuting winner existence.                *)
(* ===================================================================== *)

Section CharacterisationsN.

  Context {Node : FinType.type}.

  Theorem output_well_formed_characterisation {R : BoundedSemiring.type} :
    (3 <= List.length (@elements Node))%nat ->
    (forall x y : R, {x = y} + {x <> y}) ->
    (forall M : @Matrix Node R,
       strict_partial_order (schulze_beats M) /\
       (exists a : Node, schulze_winner M a))
    <->
    (forall x y : R, x + y = x \/ x + y = y) /\
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    intros Hlen Hdec. split.
    - intro H. apply (schulze_trans_weaker_sufficient Hlen Hdec).
      intros M a b c. exact (proj1 (proj1 (H M)) a b c).
    - intros (Hsel & Hmeet) M.
      exact (schulze_output_well_formed Hsel Hdec Hmeet M).
  Qed.

  Theorem strict_partial_order_characterisation {R : BoundedSemiring.type} :
    (3 <= List.length (@elements Node))%nat ->
    (forall x y : R, {x = y} + {x <> y}) ->
    (forall M : @Matrix Node R, strict_partial_order (schulze_beats M))
    <->
    (forall x y : R, x + y = x \/ x + y = y) /\
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    intros Hlen Hdec. split.
    - intro H. apply (schulze_trans_weaker_sufficient Hlen Hdec).
      intros M a b c. exact (proj1 (H M) a b c).
    - intros (Hsel & Hmeet) M.
      exact (proj1 (schulze_output_well_formed Hsel Hdec Hmeet M)).
  Qed.

  Theorem winner_beats_nonwinner_characterisation {R : BoundedSemiring.type} :
    (4 <= List.length (@elements Node))%nat ->
    (forall x y : R, {x = y} + {x <> y}) ->
    (forall (M : @Matrix Node R) (b : Node),
       ~ schulze_winner M b ->
       exists a : Node, schulze_winner M a /\ schulze_beats M a b)
    <->
    (forall x y : R, x + y = x \/ x + y = y) /\
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    intros Hlen Hdec. split.
    - intro H. apply (proj1 (winner_exists_characterisation Hlen Hdec)).
      intro M.
      destruct (@three_distinct_nodes Node ltac:(lia)) as (a0 & _ & _ & _ & _ & _).
      destruct (schulze_winner_dec M a0 Hdec) as [Hw | Hnw].
      + exact (ex_intro _ a0 Hw).
      + destruct (H M a0 Hnw) as (w & Hw & _). exact (ex_intro _ w Hw).
    - intros (Hsel & Hmeet) M b Hnb.
      exact (winner_beats_nonwinner Hsel Hdec Hmeet M b Hnb).
  Qed.

End CharacterisationsN.
