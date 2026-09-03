(** * Schulze's MARGIN measure as a bounded commutative semiring

    Schulze §2.1, Example 1: the strength of the link ef is the difference
    N[e,f] - N[f,e] between its support and its opposition, and

      (x1,x2) >margin (y1,y2)  iff  x1 - x2 > y1 - y2.

    Two things have to be dealt with to make this a carrier for the Kleene
    theory, and they are exactly the two the machinery was built for.

    TIES.  Margin is a total PREORDER, not an order: (3,1) and (5,3) both
    have margin 2, so they are equivalent without being equal, and
    antisymmetry with respect to Leibniz equality fails.  [mnorm] picks the
    canonical representative of each margin class — (d,0) for a victory,
    (0,d) for a defeat — and NormalizedOrder works in its image.

    BOUNDS.  Margins are unbounded in both directions, so there is no least
    or greatest element to serve as the semiring's 0 and 1.  ExtendOrder
    adjoins them.

    Comparison is written without subtraction, as x1 + y2 <= x2 + y1, so
    that truncated nat subtraction never enters the order itself. *)

From Stdlib Require Import Utf8 Arith Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN OrderSemiring
  NormalizedOrder ExtendOrder SocialchoiceN SchulzeOnNT.

(** ** The order *)

Definition pair_eq_dec (p q : nat * nat) : {p = q} + {p <> q}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(** [mle p q]: the margin of [p] is no greater than the margin of [q]. *)
Definition mle (p q : nat * nat) : bool :=
  Nat.leb (fst p + snd q) (fst q + snd p).

(** Canonical representative of a margin class: a victory by [d] becomes
    [(d,0)], a defeat by [d] becomes [(0,d)], a tie becomes [(0,0)]. *)
Definition mnorm (p : nat * nat) : nat * nat :=
  if Nat.leb (snd p) (fst p)
  then (fst p - snd p, 0)
  else (0, snd p - fst p).

Lemma mle_refl : forall p, mle p p = true.
Proof. intros [x y]. unfold mle. cbn. apply Nat.leb_le. lia. Qed.

Lemma mle_trans : forall p q r, mle p q = true -> mle q r = true -> mle p r = true.
Proof.
  intros [x1 y1] [x2 y2] [x3 y3] H1 H2. unfold mle in *. cbn in *.
  apply Nat.leb_le in H1, H2. apply Nat.leb_le. lia.
Qed.

Lemma mle_total : forall p q, mle p q = true \/ mle q p = true.
Proof.
  intros [x1 y1] [x2 y2]. unfold mle. cbn.
  destruct (Nat.le_ge_cases (x1 + y2) (x2 + y1)) as [H|H];
    [left | right]; apply Nat.leb_le; lia.
Qed.

Lemma mnorm_idem : forall p, mnorm (mnorm p) = mnorm p.
Proof.
  intros [x y]. unfold mnorm. cbn.
  destruct (Nat.leb y x) eqn:E; cbn.
  - f_equal; lia.
  - apply Nat.leb_nle in E.
    destruct (Nat.leb (y - x) 0) eqn:E2.
    + apply Nat.leb_le in E2. exfalso. lia.
    + f_equal; lia.
Qed.

Lemma mnorm_le : forall p, mle p (mnorm p) = true.
Proof.
  intros [x y]. unfold mle, mnorm. cbn.
  destruct (Nat.leb y x) eqn:E; cbn; apply Nat.leb_le.
  - apply Nat.leb_le in E. lia.
  - apply Nat.leb_nle in E. lia.
Qed.

Lemma mnorm_ge : forall p, mle (mnorm p) p = true.
Proof.
  intros [x y]. unfold mle, mnorm. cbn.
  destruct (Nat.leb y x) eqn:E; cbn; apply Nat.leb_le.
  - apply Nat.leb_le in E. lia.
  - apply Nat.leb_nle in E. lia.
Qed.

Lemma mnorm_compl : forall p q,
  mle p q = true -> mle q p = true -> mnorm p = mnorm q.
Proof.
  intros [x1 y1] [x2 y2] H1 H2. unfold mle in *. cbn in *.
  apply Nat.leb_le in H1, H2. unfold mnorm. cbn.
  destruct (Nat.leb y1 x1) eqn:E1; destruct (Nat.leb y2 x2) eqn:E2.
  - apply Nat.leb_le in E1, E2. f_equal; lia.
  - apply Nat.leb_le in E1. apply Nat.leb_nle in E2. f_equal; lia.
  - apply Nat.leb_nle in E1. apply Nat.leb_le in E2. f_equal; lia.
  - apply Nat.leb_nle in E1, E2. f_equal; lia.
Qed.

(** ** …packaged, extended with bounds, and normalised *)

Definition margin_pre : PreSpec (nat * nat) :=
  {| ps_eq_dec      := pair_eq_dec;
     ps_le          := mle;
     ps_norm        := mnorm;
     ps_refl        := mle_refl;
     ps_trans       := mle_trans;
     ps_total       := mle_total;
     ps_norm_idem   := mnorm_idem;
     ps_norm_le     := mnorm_le;
     ps_norm_ge     := mnorm_ge;
     ps_norm_compl  := mnorm_compl |}.

Definition margin_spec : CanonSpec (Ext (nat * nat)) := ext_spec margin_pre.

(** The carrier of margin strengths. *)
Definition Margin : Type := NT margin_spec.

(** The payoff: everything in SocialchoiceN.v that is parametric in the
    carrier now applies to margin-strength Schulze. *)
Check (Margin : BoundedSemiring.type).
Check (Margin : BoundedCommutativeSemiring.type).

(** …and the order it was built from is the derived order the theorems use. *)
Check (Orel_iff_leN margin_spec
        : forall x y : Margin, Orel x y <-> leN margin_spec x y = true).

(** ** Sanity: the tie class is real and is collapsed *)

Example margin_ties_equivalent :
  mle (3, 1) (5, 3) = true /\ mle (5, 3) (3, 1) = true /\ (3, 1) <> (5, 3).
Proof. repeat split; try reflexivity; discriminate. Qed.

Example margin_ties_share_normal_form : mnorm (3, 1) = mnorm (5, 3).
Proof. reflexivity. Qed.

Example margin_victory_normal_form : mnorm (14, 7) = (7, 0).
Proof. reflexivity. Qed.

Example margin_defeat_normal_form : mnorm (7, 14) = (0, 7).
Proof. reflexivity. Qed.

(** ** The lexicographic path, end to end

    Combining margin with itself is artificial — it is margin, since
    the tiebreaker never fires on a class its own comparison already
    collapsed — but it exercises the whole pipeline: combine two
    PreSpecs, adjoin the bounds AFTERWARDS, normalise, and land in the
    semiring.  Replacing either argument with another measure is then
    a one-line change. *)

Definition margin_lex_spec : CanonSpec (Ext (nat * nat * (nat * nat))) :=
  ext_spec (lex_pre margin_pre margin_pre).

Definition MarginLex : Type := NT margin_lex_spec.

Check (MarginLex : BoundedCommutativeSemiring.type).

(** ** Schulze's theorems for margin, with nothing left to supply

    Transitivity of the winner relation and non-emptiness of the
    winner set hold for margin-strength Schulze with NO hypotheses:
    selectivity, the meet-lower-bound property and decidable equality
    are all discharged by the construction of the carrier. *)

Section MarginSchulze.

  Context {Node : FinType.type}.

  Theorem margin_schulze_trans (M : @Matrix Node Margin) :
    forall a b c : Node,
      schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c.
  Proof. exact (schulze_trans_normalized margin_spec M). Qed.

  Theorem margin_winner_exists (M : @Matrix Node Margin) :
    exists a : Node, schulze_winner M a.
  Proof. exact (winner_exists_normalized margin_spec M). Qed.

End MarginSchulze.
