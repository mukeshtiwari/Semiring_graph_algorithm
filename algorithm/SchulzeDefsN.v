From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: the five definitions and the Kleene star
    Split out of the former monolithic SocialchoiceN.v. *)

Section SchulzeDefsN.

  Context {Node : FinType.type}.

  Definition kleene_exp := (List.length (@elements Node) - 1)%nat.

  (** * Kleene star as a named definition for readability *)

  Definition mat_star {R : Semiring.type} (M : @Matrix Node R)
    : @Matrix Node R :=
    geom_sum M kleene_exp.

  (** [mat_star] is the closure over the full alternative set, viewed
      through matrix multiplication; [path_star] is the same closure viewed
      through its path characterisation, but taken over an arbitrary list of
      alternatives.  They agree at [elements].  This is the single point at
      which a development over varying candidate lists, which is what
      criteria like independence of clones need, reconnects to every theorem
      stated below in terms of [mat_star]. *)
  Lemma path_star_elements_is_mat_star {R : Semiring.type}
    (M : @Matrix Node R) (c d : Node) :
    path_star (@elements Node) M c d = mat_star M c d.
  Proof.
    unfold path_star, mat_star, kleene_exp.
    rewrite connect_partial_sum_mat_paths.
    reflexivity.
  Qed.


  (** * Relationship between the four definitions (all built from beats):

        beats N a b          := N_{ba} < N_{ab}     (fundamental)
        condorcet_winner M a := ∀X≠a, beats M a X   (direct matrix)
        schulze_beats M a b  := beats (mat_star M) a b  (Kleene star order)
        strict_winner M a    := ∀X≠a, schulze_beats M a X  (beats all)
        schulze_winner M a   := ∀b≠a, ~ schulze_beats M b a  (undefeated)

      The paper's Definition 2.2.1 (relation O) is schulze_beats.
      The paper's Definition 2.2.2 (winner set S) is schulze_winner.
      Stabilization lemma: pow (M+I) stabilizes after |N|-1 steps. *)


  (** Fundamental: a beats b in matrix N if N_{ba} < N_{ab}
      — i.e., N b a ≤ N a b  ∧  N b a ≠ N a b. *)

  Definition beats {R : Semiring.type}
    (N : @Matrix Node R) (a b : Node) : Prop :=
    N b a < N a b.

  (** Condorcet winner: beats everyone in the DIRECT matrix M
      condorcet_winner M a := ∀X≠a, beats M a X *)

  Definition condorcet_winner {R : Semiring.type}
    (M : @Matrix Node R) (a : Node) : Prop :=
    forall (X : Node), X ≠ a -> beats M a X.

  (** Schulze order: beats in the Kleene star M*
      schulze_beats M a b := beats (mat_star M) a b
      (Definition 2.2.1 in the paper) *)

  Definition schulze_beats {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) : Prop :=
    beats (mat_star M) a b.

  (** Strict winner: beats everyone in the Schulze sense (via M* )
      strict_winner M a := ∀X≠a, schulze_beats M a X *)

  Definition strict_winner {R : Semiring.type}
    (M : @Matrix Node R) (a : Node) : Prop :=
    forall (X : Node), X ≠ a -> schulze_beats M a X.

  (** Schulze winner: nobody beats me in the Schulze sense
      schulze_winner M a := ∀b≠a, ~ schulze_beats M b a
      (Definition 2.2.2 in the paper) *)

  Definition schulze_winner {R : Semiring.type}
    (M : @Matrix Node R) (a : Node) : Prop :=
    forall (b : Node), b ≠ a -> ~ schulze_beats M b a.

  (** Strict partial order (Definition in §2.1): transitive and asymmetric.
      This is the shape the paper claims for the output relation O; see
      [schulze_output_well_formed] below. *)

  Definition strict_partial_order (Rel : Node -> Node -> Prop) : Prop :=
    (forall a b c, Rel a b -> Rel b c -> Rel a c) /\
    (forall a b, Rel a b -> ~ Rel b a).

  (** Asymmetry already yields irreflexivity, so the paper's two conditions
      are all that a strict partial order has to supply. *)
  Remark spo_irreflexive (Rel : Node -> Node -> Prop) :
    strict_partial_order Rel -> forall a, ~ Rel a a.
  Proof. intros [_ Hasym] a Ha. exact (Hasym a a Ha Ha). Qed.

End SchulzeDefsN.
