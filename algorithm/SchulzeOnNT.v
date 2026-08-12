(* ========================================================================= *)
(*  The Schulze theorems on a normalised carrier                             *)
(*                                                                           *)
(*  Several results in SocialchoiceN.v are stated with hypotheses on the      *)
(*  carrier: selectivity of [+], the meet-lower-bound property of [*], and    *)
(*  decidable equality.  Read as assumptions about an arbitrary semiring      *)
(*  those look strong — the comment on [H_meet_lower_bound] in that file      *)
(*  calls it "simply max-min semiring in disguise".                          *)
(*                                                                           *)
(*  For a carrier built by NormalizedOrder they are not assumptions.  They    *)
(*  are consequences of the construction: [+] is the join and [*] the meet    *)
(*  of a total order, so both return one of their arguments.  This file       *)
(*  discharges them once, so the theorems apply to EVERY link-strength        *)
(*  measure fed through the pipeline with nothing left to supply.             *)
(*                                                                           *)
(*  What does NOT become free is worth noting too.  [smith_criterion_weaker]  *)
(*  and [condorcet_implies_strict_winner_weaker] each keep a condition about  *)
(*  the MATRIX — a value separating the two blocks, and dominance of the      *)
(*  Condorcet winner respectively.  Those are properties of a profile, not    *)
(*  of an algebra, and no carrier construction can supply them.  The split    *)
(*  is exactly the algebraic / ballot-level division of labour.               *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 List.
From Semiring Require Import Structures OrelN MatN SemimoduleN
  OrderSemiring NormalizedOrder SocialchoiceN.
Import ListNotations.

(* The order notations are Local to SocialchoiceN.v, so they are restated
   here; they unfold to the same thing. *)
Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y /\ x <> y) (at level 70).

Section SchulzeOnNT.

  Context {Node : FinType.type} {A : Type} (cs : CanonSpec A).

  (** Transitivity of the Schulze relation — Schulze §4.1 — with no
      hypotheses beyond the carrier being normalised. *)
  Theorem schulze_trans_normalized (M : @Matrix Node (NT cs)) :
    forall a b c : Node,
      schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c.
  Proof.
    exact (schulze_trans_weaker_necessary M (NT_selective cs) (NT_meet_lower_bound cs)).
  Qed.

  (** …hence the winner set is non-empty (Schulze's corollary 4.1.14). *)
  Theorem winner_exists_normalized (M : @Matrix Node (NT cs)) :
    exists a : Node, schulze_winner M a.
  Proof.
    exact (winner_exists_weaker_necessary M (NT_selective cs) (NT_eq_dec cs)
             (NT_meet_lower_bound cs)).
  Qed.

  (** The Smith criterion keeps its hypothesis about the matrix — a strength
      separating the two blocks — but sheds the algebraic one. *)
  Theorem smith_criterion_normalized (M : @Matrix Node (NT cs)) :
    forall (B1 B2 : list Node), B1 <> [] ->
      (forall x : Node, In x B1 <-> ~ In x B2) ->
      (exists c : NT cs,
        (forall a b, In a B1 -> In b B2 -> M b a < c) /\
        (forall a b, In a B1 -> In b B2 -> c ≤ M a b)) ->
      forall w : Node, schulze_winner M w -> In w B1.
  Proof.
    exact (smith_criterion_weaker M (NT_selective cs)).
  Qed.

End SchulzeOnNT.
