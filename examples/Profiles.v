(* ========================================================================= *)
(*  The profile layer: from ballots to a strength matrix                     *)
(*                                                                           *)
(*  Everything so far has started from a matrix [M] of link strengths.  That  *)
(*  is where the algebra lives, but it is not where Schulze's argument        *)
(*  lives: several of his steps appeal to properties of the BALLOTS, and a    *)
(*  matrix has already discarded those.  This file supplies the missing       *)
(*  layer — profiles, pairwise counts, and the matrix they induce — so that   *)
(*  the hypotheses those theorems currently assume can be discharged.         *)
(*                                                                           *)
(*  A ballot is a ranking function [Node -> nat], lower being better.  Every  *)
(*  strict weak order on a finite set is representable this way, so nothing   *)
(*  is lost, and transitivity and totality of each voter's preference come    *)
(*  for free instead of being carried around as proof obligations.            *)
(*                                                                           *)
(*  The measure is fixed to margin here.  Generalising means abstracting      *)
(*  Schulze's (2.1.1) and (2.1.2) as per-measure obligations; margin          *)
(*  satisfies both, and the proofs below use only that.                       *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 List Arith Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN OrderSemiring
  NormalizedOrder ExtendOrder SocialchoiceN SchulzeOnNT.
From Examples Require Import MarginMeasure.
Import ListNotations.

Section Profiles.

  Context {Node : FinType.type}.

  (* ------------------------------------------------------------------ *)
  (*  Ballots, profiles, pairwise counts                                 *)
  (* ------------------------------------------------------------------ *)

  Definition Ballot := Node -> nat.
  Definition Profile := list Ballot.

  (** Voter [b] strictly prefers [i] to [j]. *)
  Definition prefers (b : Ballot) (i j : Node) : bool := Nat.ltb (b i) (b j).

  (** [N[i,j]]: how many voters strictly prefer [i] to [j]. *)
  Definition count (P : Profile) (i j : Node) : nat :=
    length (filter (fun b => prefers b i j) P).

  Lemma count_le_length : forall P i j, count P i j <= length P.
  Proof.
    intros P i j. unfold count.
    induction P as [|b P IH]; cbn [filter length]; [lia |].
    destruct (prefers b i j); cbn [length]; lia.
  Qed.

  (** No voter prefers [i] to [j] and [j] to [i], so the two counts of a
      pair cannot together exceed the electorate. *)
  Lemma count_pair_le : forall P i j, count P i j + count P j i <= length P.
  Proof.
    intros P i j. unfold count.
    induction P as [|b P IH]; cbn [filter length]; [lia |].
    destruct (prefers b i j) eqn:E1; destruct (prefers b j i) eqn:E2;
      cbn [length]; try lia.
    (* no voter can prefer each of the two to the other *)
    unfold prefers in E1, E2.
    apply Nat.ltb_lt in E1. apply Nat.ltb_lt in E2. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Unanimity                                                          *)
  (* ------------------------------------------------------------------ *)

  Definition unanimous (P : Profile) (i j : Node) : Prop :=
    forall b, In b P -> prefers b i j = true.

  Lemma unanimous_count : forall P i j,
    unanimous P i j -> count P i j = length P.
  Proof.
    intros P i j H. unfold count.
    induction P as [|b P IH]; cbn [filter length]; [reflexivity |].
    rewrite (H b (or_introl eq_refl)). cbn [length].
    rewrite IH; [reflexivity |].
    intros b' Hin. apply H. right. exact Hin.
  Qed.

  (** …and conversely, a count equal to the electorate is unanimity. *)
  Lemma count_full_unanimous : forall P i j,
    count P i j = length P -> unanimous P i j.
  Proof.
    intros P i j. unfold count, unanimous.
    induction P as [|b P IH]; cbn [filter length]; [intros _ b' []|].
    destruct (prefers b i j) eqn:E; cbn [length]; intro Hlen.
    - intros b' [Heq|Hin]; [subst b'; exact E |].
      apply IH; [lia | exact Hin].
    - exfalso. pose proof (count_le_length P i j) as Hle.
      unfold count in Hle. lia.
  Qed.

  Lemma unanimous_count_rev : forall P i j,
    unanimous P i j -> count P j i = 0.
  Proof.
    intros P i j H. unfold count.
    induction P as [|b P IH]; cbn [filter length]; [reflexivity |].
    assert (Hb : prefers b i j = true) by (apply H; left; reflexivity).
    assert (Hrev : prefers b j i = false).
    { unfold prefers in *. apply Nat.ltb_lt in Hb. apply Nat.ltb_nlt. lia. }
    rewrite Hrev. apply IH. intros b' Hin. apply H. right. exact Hin.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The induced strength matrix                                        *)
  (*                                                                     *)
  (*  The diagonal is set to the top by convention: Schulze's paths never *)
  (*  traverse it, and [Hdiag_one] in SocialchoiceN.v expects [1] there.  *)
  (* ------------------------------------------------------------------ *)

  Definition matrix_of (P : Profile) : @Matrix Node Margin :=
    fun i j =>
      if fin_eq_dec i j
      then topN margin_spec
      else inj margin_spec (EMid (count P i j, count P j i)).

  (* [one] is written out rather than [1]: SemiringNotations is deliberately
     not imported here, since this file also does ordinary nat arithmetic on
     vote counts and the two families of literals would collide. *)
  Lemma matrix_of_diag : forall P i j, i = j -> matrix_of P i j = one.
  Proof.
    intros P i j Hij. unfold matrix_of.
    destruct (fin_eq_dec i j) as [_|Hne]; [reflexivity | contradiction].
  Qed.

  Lemma matrix_of_off : forall P i j, i <> j ->
    matrix_of P i j = inj margin_spec (EMid (count P i j, count P j i)).
  Proof.
    intros P i j Hij. unfold matrix_of.
    destruct (fin_eq_dec i j) as [Heq|_]; [contradiction | reflexivity].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Reading a link strength back as a pair of counts                   *)
  (*                                                                     *)
  (*  [inj] normalises, so equal matrix entries mean equal margins, not   *)
  (*  equal counts.  These two lemmas move between the two.               *)
  (* ------------------------------------------------------------------ *)

  Lemma inj_EMid_eq : forall p q,
    inj margin_spec (EMid p) = inj margin_spec (EMid q) -> mnorm p = mnorm q.
  Proof.
    intros p q H.
    apply (f_equal (val margin_spec)) in H. cbn in H.
    injection H. exact (fun h => h).
  Qed.

  (** A unanimous victory has the largest margin available, and only a
      unanimous victory does.  This is Schulze's (2.1.1) doing its work:
      strength responds to support and opposition in the right direction. *)
  Lemma margin_full_iff_unanimous : forall P i j, i <> j ->
    (mnorm (count P i j, count P j i) = (length P, 0) <-> unanimous P i j).
  Proof.
    intros P i j Hij. split.
    - intro Hm. apply count_full_unanimous.
      pose proof (count_pair_le P i j) as Hpair.
      pose proof (count_le_length P i j) as Hle.
      unfold mnorm in Hm. cbn [fst snd] in Hm.
      destruct (Nat.leb (count P j i) (count P i j)) eqn:E.
      + apply Nat.leb_le in E. injection Hm; intros; lia.
      + apply Nat.leb_nle in E. injection Hm; intros; lia.
    - intro Hu.
      rewrite (unanimous_count P i j Hu), (unanimous_count_rev P i j Hu).
      unfold mnorm. cbn [fst snd].
      destruct (Nat.leb 0 (length P)) eqn:E; cbn.
      + f_equal. lia.
      + apply Nat.leb_nle in E. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Schulze's hypotheses, discharged from the profile                  *)
  (* ------------------------------------------------------------------ *)

  Variable P : Profile.
  Variable A B : Node.
  Hypothesis HAB : A <> B.
  Hypothesis Hvoters : 0 < length P.
  Hypothesis Hunan : unanimous P A B.

  Notation M := (matrix_of P).

  Lemma link_AB : M A B = inj margin_spec (EMid (length P, 0)).
  Proof.
    rewrite (matrix_of_off P A B HAB).
    rewrite (unanimous_count P A B Hunan), (unanimous_count_rev P A B Hunan).
    reflexivity.
  Qed.

  (** (2.1.1): no link is stronger than a unanimous one. *)
  Lemma profile_Hmax : forall X Y, X <> Y -> Orel (M X Y) (M A B).
  Proof.
    intros X Y HXY. rewrite (matrix_of_off P X Y HXY), link_AB.
    apply (Orel_iff_leN margin_spec). apply inj_mono.
    cbn. unfold mle. cbn [fst snd].
    apply Nat.leb_le.
    pose proof (count_pair_le P X Y) as H1.
    pose proof (count_le_length P X Y) as H2. lia.
  Qed.

  (** The diagonal convention. *)
  Lemma profile_Hdiag : forall i j : Node, i = j -> M i j = one.
  Proof. exact (matrix_of_diag P). Qed.

  (** The strongest link is not the bottom, since somebody voted. *)
  Lemma profile_pos : Orel zero (M A B) /\ zero <> M A B.
  Proof.
    split; [apply zero_is_bottom |].
    rewrite link_AB. intro Habs.
    apply (f_equal (val margin_spec)) in Habs. cbn in Habs.
    discriminate.
  Qed.

  (** The key step.  A link as strong as the unanimous one IS unanimous —
      so [Htop_trans] reduces to transitivity of the individual ballots. *)
  Lemma top_link_unanimous : forall X Y, X <> Y ->
    M X Y = M A B -> unanimous P X Y.
  Proof.
    intros X Y HXY Heq.
    rewrite (matrix_of_off P X Y HXY), link_AB in Heq.
    apply inj_EMid_eq in Heq.
    apply (margin_full_iff_unanimous P X Y HXY).
    rewrite Heq. unfold mnorm. cbn [fst snd].
    destruct (Nat.leb 0 (length P)) eqn:E; cbn; [f_equal; lia |].
    apply Nat.leb_nle in E. lia.
  Qed.

  (** [Htop_trans], derived: maximal links compose because ballots do. *)
  Theorem profile_Htop_trans : forall X Y Z,
    M X Y = M A B -> M Y Z = M A B -> M X Z = M A B.
  Proof.
    intros X Y Z HXY HYZ.
    (* the diagonal is the top, which is not the strength of a real link *)
    assert (Hne : forall U V, M U V = M A B -> U <> V).
    { intros U V H Huv. rewrite (matrix_of_diag P U V Huv), link_AB in H.
      apply (f_equal (val margin_spec)) in H. cbn in H. discriminate. }
    pose proof (Hne X Y HXY) as HXY'. pose proof (Hne Y Z HYZ) as HYZ'.
    assert (HuXY : unanimous P X Y) by (apply top_link_unanimous; assumption).
    assert (HuYZ : unanimous P Y Z) by (apply top_link_unanimous; assumption).
    (* transitivity of each ballot's ranking *)
    assert (HuXZ : unanimous P X Z).
    { intros b Hb. pose proof (HuXY b Hb) as H1. pose proof (HuYZ b Hb) as H2.
      unfold prefers in *. apply Nat.ltb_lt in H1, H2. apply Nat.ltb_lt. lia. }
    assert (HXZ : X <> Z).
    { intro Habs. subst Z. pose proof (HuXY (nth 0 P (fun _ => 0))) as H1.
      pose proof (HuYZ (nth 0 P (fun _ => 0))) as H2.
      destruct P as [|b0 P']; [cbn in Hvoters; lia |].
      cbn in H1, H2. specialize (H1 (or_introl eq_refl)).
      specialize (H2 (or_introl eq_refl)).
      unfold prefers in *. apply Nat.ltb_lt in H1, H2. lia. }
    rewrite (matrix_of_off P X Z HXZ), link_AB.
    f_equal. f_equal.
    rewrite (unanimous_count P X Z HuXZ), (unanimous_count_rev P X Z HuXZ).
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Pareto, with nothing assumed about the algebra                     *)
  (* ------------------------------------------------------------------ *)

  Lemma link_BA : M B A = inj margin_spec (EMid (0, length P)).
  Proof.
    assert (HBA : B <> A) by (intro h; apply HAB; symmetry; exact h).
    rewrite (matrix_of_off P B A HBA).
    rewrite (unanimous_count_rev P A B Hunan), (unanimous_count P A B Hunan).
    reflexivity.
  Qed.

  Lemma link_BA_ne_AB : M B A <> M A B.
  Proof.
    rewrite link_AB, link_BA. intro Habs.
    apply inj_EMid_eq in Habs.
    unfold mnorm in Habs. cbn [fst snd] in Habs.
    destruct (Nat.leb (length P) 0) eqn:E1; destruct (Nat.leb 0 (length P)) eqn:E2;
      cbn in Habs.
    - apply Nat.leb_le in E1. lia.
    - apply Nat.leb_nle in E2. lia.
    - injection Habs; intros; lia.
    - apply Nat.leb_nle in E2. lia.
  Qed.

  (** Schulze's Pareto criterion (§4.3.1) for margin-strength Schulze.
      The hypotheses are [A <> B], a non-empty electorate, and unanimity —
      all statements about the PROFILE.  Everything the algebra needed is
      discharged: selectivity from the carrier, [Hmax] and [Hdiag] from the
      counts, and [Htop_trans] from transitivity of the ballots. *)
  Theorem pareto_from_profile : schulze_beats M A B.
  Proof.
    apply (pareto_stronger_iff M A B
             (NT_selective margin_spec) profile_Htop_trans
             HAB profile_pos profile_Hmax profile_Hdiag).
    exact link_BA_ne_AB.
  Qed.

  (** …and the dominated alternative is not a winner (Schulze's 4.3.1.3). *)
  Theorem pareto_loser_from_profile : ~ schulze_winner M B.
  Proof. intro Hwin. exact (Hwin A HAB pareto_from_profile). Qed.

End Profiles.
