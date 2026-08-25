From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN
  ReversalsymmetryN MonotonicityN ParetoN CondorcetN
  SmithN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ===================================================== *)
(*  Schulze over a semiring: prudence (4.9)             *)
(*  Split out of the former monolithic SocialchoiceN.v. *)
(* ===================================================== *)

Section PrudenceN.

  Context {Node : FinType.type}.


  (* ==================================================================== *)
  (*  Prudence (Section 4.9)                                              *)
  (*                                                                      *)
  (*  [λ_D] is the strength of the strongest directed cycle.  A cycle      *)
  (*  through the link [a → b] (with [a ≠ b], since the paper's paths      *)
  (*  never repeat a node consecutively) is that link followed by a path   *)
  (*  back, so its strength is [M a b * mat_star M b a]; joining over all  *)
  (*  ordered pairs of distinct nodes gives λ_D.  The [a ≠ b] guard is     *)
  (*  essential: with [M i i = 1] a self-loop would be a cycle of maximal  *)
  (*  strength and λ_D would collapse to the top.                          *)
  (*                                                                      *)
  (*  [Hmeet] — multiplication is the meet of the natural order — is the   *)
  (*  algebraic content of the slogan that the strength of a path is the   *)
  (*  strength of its weakest link.  It holds in the max-min semiring of   *)
  (*  the Schulze instance.  Without it the statement fails: in max-times  *)
  (*  a link can dominate every cycle while a two-step detour ties it.     *)
  (* ==================================================================== *)

  (** [λ_D], the strength of the strongest directed cycle — Schulze (4.9.2). *)
  Definition cycle_strength {R : Semiring.type} (M : @Matrix Node R) : R :=
    sum (fun a => sum (fun b =>
      if fin_eq_dec a b then 0 else M a b * mat_star M b a)).

  (** Each cycle through a link is bounded by the strongest cycle. *)
  Lemma cycle_strength_ge {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node) :
    a ≠ b -> M a b * mat_star M b a ≤ cycle_strength M.
  Proof.
    intros Hab. unfold cycle_strength.
    eapply orel_trans; [| exact (le_sum _ a)]. cbv beta.
    eapply orel_trans; [| exact (le_sum _ b)]. cbv beta.
    destruct (fin_eq_dec a b) as [Heq|_]; [contradiction | apply bounded_orel_refl].
  Qed.

  (** Prudence (4.9.3, local form): a link strictly stronger than every cycle
      through that very link is respected by the Schulze relation.  This is the
      paper's exact statement: [ab ∈ O] unless [ab] lies in a directed cycle
      whose links are each at least as strong as [ab].  The hypothesis
      [M a b * mat_star M b a < M a b] says the strongest cycle through [a → b]
      (the link followed by the strongest return path) is strictly weaker than
      the link itself.

      The paper's [a ≠ b] side condition is not needed here and is therefore
      not assumed: the cycle hypothesis already fails when [a = b], since
      [mat_star M a a = 1] makes the two sides equal.  [prudence] below still
      takes [a ≠ b], which it needs for [cycle_strength_ge]. *)
  Theorem prudence_local {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node)
    (* Htotal and Hmeet are both satisfied by max-min semiring 
    but not in general *)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x) :
    M a b * mat_star M b a < M a b -> schulze_beats M a b.
  Proof.
    intros Hlam.
    (* the reverse closure cannot even reach the link's strength: if it did,
       the link together with the return path would be a cycle as strong as
       the link itself *)
    assert (Hstar_le : mat_star M b a ≤ M a b).
    { destruct (Htotal (mat_star M b a) (M a b)) as [Hcase|Hcase]; [| exact Hcase].
      exfalso.
      assert (Hge : M a b ≤ mat_star M b a).
      { unfold Orel. rewrite addC. exact Hcase. }
      destruct Hlam as [Hle Hne].
      assert (Heq : M a b * mat_star M b a = M a b) by (apply (Hmeet _ _ Hge)).
      apply Hne. exact Heq. }
    assert (Hstar_ne : mat_star M b a ≠ M a b).
    { intro Heq.
      destruct Hlam as [Hle Hne].
      assert (Hself : M a b * mat_star M b a = M a b).
      { rewrite Heq. apply (Hmeet (M a b) (M a b) (bounded_orel_refl _)). }
      apply Hne. exact Hself. }
    (* the reverse closure is strictly below the link, so (2.2.4) applies *)
    apply link_beats.
    split; [exact Hstar_le | exact Hstar_ne].
  Qed.

  (** Prudence (4.9.3, global form): a link strictly stronger than every
      directed cycle — stronger than [λ_D = cycle_strength M] — is respected
      by the Schulze relation.  This follows from [prudence_local], because the
      strongest cycle through [a → b] is bounded by the strongest cycle
      anywhere, which is itself strictly weaker than the link. *)
  Theorem prudence {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node)
    (* Htotal and Hmeet are both satisfied by max-min semiring 
    but not in general *)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x) :
    a ≠ b -> cycle_strength M < M a b -> schulze_beats M a b.
  Proof.
    intros Hab Hlam.
    apply (prudence_local M a b Htotal Hmeet).
    destruct Hlam as [Hle Hne]. split.
    - eapply orel_trans; [ exact (cycle_strength_ge M a b Hab) | exact Hle ].
    - intro Heq.
      apply Hne. apply orel_antisym; [ exact Hle | ].
      rewrite <- Heq. exact (cycle_strength_ge M a b Hab).
  Qed.

  (** Prudence (4.9.4): the loser of such a link is not a winner. *)
  Corollary prudence_not_winner {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x) :
    a ≠ b -> cycle_strength M < M a b -> ~ schulze_winner M b.
  Proof.
    intros Hab Hlam Hwin.
    exact (Hwin a Hab (prudence M a b Htotal Hmeet Hab Hlam)).
  Qed.

End PrudenceN.
