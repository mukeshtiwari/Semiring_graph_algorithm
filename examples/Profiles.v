(* ========================================================================= *)
(*  Schulze's three concrete strength measures as [Measure]s                 *)
(*                                                                           *)
(*  MeasureN.v asks a strength measure for Schulze's two conditions (2.1.1)  *)
(*  and (2.1.2), and BallotN.v discharges the ballot-level hypotheses of the  *)
(*  criterion theorems for any measure that has them.  This file supplies the *)
(*  conditions for margin, winning votes, and losing votes, each proved once  *)
(*  from the order characterisation its own file already provides, and then   *)
(*  instantiates the profile-level theorems at margin and at winning votes.   *)
(*                                                                           *)
(*  Ratio is not treated: it is not among the measures formalised in this     *)
(*  directory.                                                               *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 List Arith Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN OrderSemiring
  NormalizedOrder ExtendOrder MeasureN SocialchoiceN SchulzeOnNT BallotN
  ResolvabilityBallotN.
From Examples Require Import MarginMeasure WinningVotes LosingVotes.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(*  Margin                                                             *)
(*                                                                     *)
(*  [mle (x1,x2) (y1,y2)] is [x1 + y2 <= y1 + x2].  Both conditions    *)
(*  say that the left margin is strictly larger, which is arithmetic.  *)
(* ------------------------------------------------------------------ *)

Lemma margin_211 : forall x1 x2 y1 y2 : nat,
  (y1 < x1 /\ x2 <= y2) \/ (y1 <= x1 /\ x2 < y2) -> mle (x1, x2) (y1, y2) = false.
Proof. intros x1 x2 y1 y2 H. unfold mle. cbn [fst snd]. apply Nat.leb_nle. lia. Qed.

Lemma margin_212 : forall x1 x2 y1 y2 : nat,
  (x2 < x1 /\ y1 <= y2) \/ (x2 <= x1 /\ y1 < y2) -> mle (x1, x2) (y1, y2) = false.
Proof. intros x1 x2 y1 y2 H. unfold mle. cbn [fst snd]. apply Nat.leb_nle. lia. Qed.

Definition margin_measure : Measure :=
  {| m_pre := margin_pre; m_211 := margin_211; m_212 := margin_212 |}.

(* The carrier is the one MarginMeasure.v already built, definitionally. *)
Check (eq_refl : Strength margin_measure = Margin).
Check (eq_refl : spec margin_measure = margin_spec).

(* ------------------------------------------------------------------ *)
(*  Winning votes and losing votes                                     *)
(*                                                                     *)
(*  Both orders are characterised arithmetically ([wle_spec],          *)
(*  [lle_spec]) in terms of the victory/tie/defeat class [vclass].      *)
(*  Each condition is then a case analysis on the two classes and the  *)
(*  clauses of the characterisation, closed by [lia].                  *)
(* ------------------------------------------------------------------ *)

Lemma wv_211 : forall x1 x2 y1 y2 : nat,
  (y1 < x1 /\ x2 <= y2) \/ (y1 <= x1 /\ x2 < y2) -> wle (x1, x2) (y1, y2) = false.
Proof.
  intros x1 x2 y1 y2 H.
  destruct (wle (x1, x2) (y1, y2)) eqn:E; [exfalso | reflexivity].
  apply wle_spec in E. cbn [fst snd] in E.
  pose proof (vclass_spec (x1, x2)) as Vx. pose proof (vclass_spec (y1, y2)) as Vy.
  cbn [fst snd] in Vx, Vy.
  destruct Vx as [[Vx1 Vx2]|[[Vx1 Vx2]|[Vx1 Vx2]]];
  destruct Vy as [[Vy1 Vy2]|[[Vy1 Vy2]|[Vy1 Vy2]]];
  destruct E as [E|[E1 [E2|[E2|[E2 E3]]]]]; lia.
Qed.

Lemma wv_212 : forall x1 x2 y1 y2 : nat,
  (x2 < x1 /\ y1 <= y2) \/ (x2 <= x1 /\ y1 < y2) -> wle (x1, x2) (y1, y2) = false.
Proof.
  intros x1 x2 y1 y2 H.
  destruct (wle (x1, x2) (y1, y2)) eqn:E; [exfalso | reflexivity].
  apply wle_spec in E. cbn [fst snd] in E.
  pose proof (vclass_spec (x1, x2)) as Vx. pose proof (vclass_spec (y1, y2)) as Vy.
  cbn [fst snd] in Vx, Vy.
  destruct Vx as [[Vx1 Vx2]|[[Vx1 Vx2]|[Vx1 Vx2]]];
  destruct Vy as [[Vy1 Vy2]|[[Vy1 Vy2]|[Vy1 Vy2]]];
  destruct E as [E|[E1 [E2|[E2|[E2 E3]]]]]; lia.
Qed.

Definition wv_measure : Measure :=
  {| m_pre := wv_pre; m_211 := wv_211; m_212 := wv_212 |}.

Check (eq_refl : Strength wv_measure = WinningVotes).

Lemma lv_211 : forall x1 x2 y1 y2 : nat,
  (y1 < x1 /\ x2 <= y2) \/ (y1 <= x1 /\ x2 < y2) -> lle (x1, x2) (y1, y2) = false.
Proof.
  intros x1 x2 y1 y2 H.
  destruct (lle (x1, x2) (y1, y2)) eqn:E; [exfalso | reflexivity].
  apply lle_spec in E. cbn [fst snd] in E.
  pose proof (vclass_spec (x1, x2)) as Vx. pose proof (vclass_spec (y1, y2)) as Vy.
  cbn [fst snd] in Vx, Vy.
  destruct Vx as [[Vx1 Vx2]|[[Vx1 Vx2]|[Vx1 Vx2]]];
  destruct Vy as [[Vy1 Vy2]|[[Vy1 Vy2]|[Vy1 Vy2]]];
  destruct E as [E|[E1 [E2|[E2|[E2 E3]]]]]; lia.
Qed.

Lemma lv_212 : forall x1 x2 y1 y2 : nat,
  (x2 < x1 /\ y1 <= y2) \/ (x2 <= x1 /\ y1 < y2) -> lle (x1, x2) (y1, y2) = false.
Proof.
  intros x1 x2 y1 y2 H.
  destruct (lle (x1, x2) (y1, y2)) eqn:E; [exfalso | reflexivity].
  apply lle_spec in E. cbn [fst snd] in E.
  pose proof (vclass_spec (x1, x2)) as Vx. pose proof (vclass_spec (y1, y2)) as Vy.
  cbn [fst snd] in Vx, Vy.
  destruct Vx as [[Vx1 Vx2]|[[Vx1 Vx2]|[Vx1 Vx2]]];
  destruct Vy as [[Vy1 Vy2]|[[Vy1 Vy2]|[Vy1 Vy2]]];
  destruct E as [E|[E1 [E2|[E2|[E2 E3]]]]]; lia.
Qed.

Definition lv_measure : Measure :=
  {| m_pre := lv_pre; m_211 := lv_211; m_212 := lv_212 |}.

Check (eq_refl : Strength lv_measure = LosingVotes).

(* ------------------------------------------------------------------ *)
(*  Margin-strength Schulze, from the ballots                          *)
(*                                                                     *)
(*  Every hypothesis below is about the profile.  Everything the       *)
(*  algebra needed is discharged: selectivity and the meet property by *)
(*  the carrier, the matrix conditions by BallotN.                     *)
(* ------------------------------------------------------------------ *)

Section MarginProfiles.

  Context {Node : FinType.type}.

  Notation M := (matrix_of margin_measure).

  (** Pareto (4.3.1): unanimity decides the pair. *)
  Theorem margin_pareto (P : @Profile Node) (A B : Node) :
    A <> B -> 0 < length P -> unanimous P A B -> schulze_beats (M P) A B.
  Proof. exact (pareto_from_profile margin_measure P A B). Qed.

  Theorem margin_pareto_loser (P : @Profile Node) (A B : Node) :
    A <> B -> 0 < length P -> unanimous P A B -> ~ schulze_winner (M P) B.
  Proof. exact (pareto_loser_from_profile margin_measure P A B). Qed.

  (** Condorcet: a pairwise champion is the unique winner. *)
  Theorem margin_condorcet (P : @Profile Node) (A : Node) :
    (forall X, X <> A -> count P X A < count P A X) ->
    forall w, schulze_winner (M P) w -> w = A.
  Proof. exact (condorcet_unique_from_profile margin_measure P A). Qed.

  (** Smith (4.7.4): the winners lie in a dominant set. *)
  Theorem margin_smith (P : @Profile Node) (B1 B2 : list Node) :
    (forall x, In x B1 <-> ~ In x B2) ->
    (forall a b, In a B1 -> In b B2 -> count P b a < count P a b) ->
    B1 <> [] -> forall w, schulze_winner (M P) w -> In w B1.
  Proof. exact (smith_from_profile margin_measure P B1 B2). Qed.

  (** Monotonicity (4.5.6): raising a winner keeps it a winner. *)
  Theorem margin_monotonicity (A : Node) (P P' : @Profile Node) :
    raise A P P' -> schulze_winner (M P) A -> schulze_winner (M P') A.
  Proof. exact (monotonicity_from_profile margin_measure A P P'). Qed.

  (** Reversal symmetry (4.4.2): reversing every ballot displaces a strict
      winner. *)
  Theorem margin_reversal (P P' : @Profile Node) :
    reverse P P' -> forall A, strict_winner (M P) A -> ~ strict_winner (M P') A.
  Proof. exact (reversal_from_profile margin_measure P P'). Qed.

  (** Resolvability, first formulation, combinatorial core (4.2.1): pairwise
      distinct link strengths leave at most one winner. *)
  Theorem margin_distinct_links (P : @Profile Node) :
    (forall e f g h, e <> f -> g <> h -> M P e f = M P g h -> e = g /\ f = h) ->
    forall a b, schulze_winner (M P) a -> schulze_winner (M P) b -> a = b.
  Proof. exact (distinct_links_unique_winner_from_profile margin_measure P). Qed.

  (** Resolvability, second formulation (4.2.2): one added ballot makes any
      winner the unique winner. *)
  Theorem margin_resolvability (P : @Profile Node) (a : Node) :
    schulze_winner (M P) a ->
    exists w : @Ballot Node,
      strict_winner (M (w :: P)) a /\ forall x, schulze_winner (M (w :: P)) x <-> x = a.
  Proof. exact (resolvability_from_profile margin_measure P a). Qed.

End MarginProfiles.

(* ------------------------------------------------------------------ *)
(*  …and the same for winning votes, to show nothing was margin-specific *)
(* ------------------------------------------------------------------ *)

Section WinningVotesProfiles.

  Context {Node : FinType.type}.

  Notation M := (matrix_of wv_measure).

  Theorem wv_pareto (P : @Profile Node) (A B : Node) :
    A <> B -> 0 < length P -> unanimous P A B -> schulze_beats (M P) A B.
  Proof. exact (pareto_from_profile wv_measure P A B). Qed.

  Theorem wv_condorcet (P : @Profile Node) (A : Node) :
    (forall X, X <> A -> count P X A < count P A X) ->
    forall w, schulze_winner (M P) w -> w = A.
  Proof. exact (condorcet_unique_from_profile wv_measure P A). Qed.

  Theorem wv_monotonicity (A : Node) (P P' : @Profile Node) :
    raise A P P' -> schulze_winner (M P) A -> schulze_winner (M P') A.
  Proof. exact (monotonicity_from_profile wv_measure A P P'). Qed.

End WinningVotesProfiles.
