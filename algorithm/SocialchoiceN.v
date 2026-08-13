From Stdlib Require Import List Utf8 Lia Wf_nat.
From Semiring Require Import PathN MatN OrelN 
  SemimoduleN Structures.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ========================================================================= *)
(*  Social choice — the Schulze method over an arbitrary semiring            *)
(*                                                                           *)
(*  Reference: M. Schulze, A new monotonic, clone-independent, reversal      *)
(*  symmetric, and Condorcet-consistent single-winner election method,       *)
(*  Soc Choice Welf (2011) 36:267-303.  Section and equation numbers below   *)
(*  are the paper's.                                                         *)
(*                                                                           *)
(*  MODELLING.  The paper's link strengths live in N0 x N0 ordered by a      *)
(*  strict weak order, with path strength = weakest link (min) and the       *)
(*  strength of an indirect comparison = strongest path (max).  Here that    *)
(*  is an arbitrary semiring: [*] is path composition, [+] is path           *)
(*  selection, and [Orel] (a ≤ b := a + b = b) is the induced order.  So     *)
(*  P_D[a,b] is [mat_star M a b] = geom_sum M (|A|-1) a b.  The two agree:   *)
(*  in a bounded semiring [a*b ≤ a] and [a*b ≤ b], so deleting a repeated    *)
(*  segment from a walk never lowers its measure, and the join over walks    *)
(*  of length ≤ |A|-1 is the join over the paper's paths (which forbid       *)
(*  c(i) ≡ c(i+1)).                                                          *)
(*                                                                           *)
(*  BASIC DEFINITIONS                                                        *)
(*    §2.1     strict partial order  strict_partial_order                    *)
(*    (2.2.1)  relation O            schulze_beats   (via [beats], [mat_star]) *)
(*    (2.2.2)  winner set S          schulze_winner                          *)
(*    (2.2.3)  link is a path        link_le_mat_star                        *)
(*    (2.2.4)  a link beating the                                            *)
(*             return closure is                                             *)
(*             respected by O        link_beats                              *)
(*    (2.2.5)  path composition      star_path_compose                       *)
(*                                                                           *)
(*    §2.2     the method outputs a strict partial order O and a non-empty   *)
(*             winner set S         schulze_output_well_formed           (†) *)
(*                                                                           *)
(*  RESULTS.  Where the paper's proof uses properties of its concrete order  *)
(*  that a bare semiring lacks, the Rocq statement carries them as explicit  *)
(*  hypotheses; [SchulzeOnNT.v] discharges those for a normalised carrier,   *)
(*  giving the paper's unconditional form.  Such entries are marked (†), and *)
(*  the discharged version is named there.                                   *)
(*                                                                           *)
(*    §4.1     transitivity of O     schulze_trans_weaker_necessary      (†) *)
(*             converse              schulze_trans_weaker_sufficient  ADMITTED *)
(*             characterisation      transitivity_characterisation           *)
(*                                     — depends on the admitted converse    *)
(*    (4.1.14) a winner beats every                                          *)
(*             non-winner            winner_beats_nonwinner              (†) *)
(*             …hence S ≠ ∅          winner_exists_weaker_necessary      (†) *)
(*    §4.2     resolvability — only the resolution step of 4.2.1: an untied  *)
(*             winner beats everyone and is unique                           *)
(*                                   untied_winner_is_strict,                *)
(*                                   untied_winner_unique                (†) *)
(*             see the NOT FORMALISED note below for the two halves missing  *)
(*    §4.3.1   Pareto #1             pareto_stronger, pareto_stronger_loser  *)
(*             both directions       pareto_stronger_iff                     *)
(*    (4.3.2.2/10) Pareto #2         pareto_weaker                           *)
(*    (4.3.2.11/12) the two path-rewriting steps behind #2                   *)
(*                                   pareto_star_source_swap,                *)
(*                                   pareto_star_target_swap                 *)
(*    (4.3.2.3) B beats F ⇒ A beats F  pareto_weaker_beats_transfer          *)
(*    (4.3.2.4) F beats A ⇒ F beats B  pareto_weaker_loses_transfer          *)
(*    (4.3.2.5) B ∈ S ⇒ A ∈ S         pareto_weaker_winner_transfer          *)
(*    (4.4.2)  reversal reverses O   reversal_symmetry_O                     *)
(*    (4.4.3)  reversal displaces a                                          *)
(*             winner iff it promotes                                        *)
(*             a non-winner          reversal_symmetry_S                 (†) *)
(*    (4.4.4)  S unchanged iff S = A reversal_symmetry_all_tied          (†) *)
(*    (4.5.13/14) monotonicity of P  monotonicity, monotonicity_rev          *)
(*    (4.5.4)  A's victories survive  monotonicity_beats                     *)
(*    (4.5.5)  A's non-defeats survive monotonicity_unbeaten                 *)
(*    (4.5.6, ⇒) a ∈ S_old ⇒ a ∈ S_new  winner_monotonicity                 *)
(*    (4.5.6, ⊆) S_new ⊆ S_old   winner_monotonicity_subset — but ONLY      *)
(*             under an extra no-ties hypothesis on A; see its comment and  *)
(*             the NOT FORMALISED note                                       *)
(*    (4.7.3)  Smith: every a∈B1                                            *)
(*             beats every b∈B2  smith_beats                          (†) *)
(*    (4.7.4)  Smith: S ⊆ B1         smith_criterion_weaker              (†) *)
(*    (4.7.5a) Smith-IIA: a weak alternative does not affect how the       *)
(*             strong ones compare   smith_iia_isolate — but for ISOLATION *)
(*             of d, not removal, and with an extra separation hypothesis; *)
(*             see the section comment and the NOT FORMALISED note         *)
(*    (4.8.1)  MinMax set beats                                              *)
(*             its complement        minmax_beats                            *)
(*    (4.8.2)  S ⊆ 𝔅_D               minmax_winner                          *)
(*    (4.9.3)  prudence              prudence, prudence_local                *)
(*    (4.9.4)  its loser is no winner prudence_not_winner                    *)
(*                                                                           *)
(*  Not from the paper, but proved here: uniqueness and order facts about    *)
(*  the two winner notions (strict_winner_unique, condorcet_winner_unique,   *)
(*  strict_winner_is_schulze_winner, strict_winner_excludes_others,          *)
(*  schulze_beats_asym, schulze_beats_irrefl), the Condorcet criterion in    *)
(*  the form "Condorcet winner ⇒ beats everyone"                             *)
(*  (condorcet_implies_strict_winner_weaker), the observation that the meet  *)
(*  property forces commutativity (meet_lower_bound_implies_comm), and the   *)
(*  selectivity facts (mul_selective, sum_selective, pow_link_or_extreme,    *)
(*  mat_star_link_or_extreme) saying that under [Htotal] and [Hmeet] the     *)
(*  closure invents no values beyond the link strengths and the bounds.      *)
(*                                                                           *)
(*  NOT FORMALISED                                                           *)
(*    §4.2.1   the outer layers of resolvability #1.  The paper's claim is   *)
(*             that distinct LINK strengths give at most one WINNER; note    *)
(*             it is NOT that distinct links give an untied closure, which   *)
(*             is false (on four nodes in max-min, all twelve off-diagonal   *)
(*             links can be distinct with mat_star a b = mat_star b a).  The *)
(*             paper's proof therefore leans on the winner hypotheses: it    *)
(*             identifies the critical link shared by the two strongest      *)
(*             paths and splits both paths there.  That needs the WITNESS    *)
(*             link, which [mat_star_link_or_extreme] does not supply — it   *)
(*             gives only the value.  Also missing: the asymptotic wrapper   *)
(*             over profiles.  The inner resolution step, which is what the  *)
(*             winner hypotheses feed, is [untied_winner_unique] above.      *)
(*    §4.2.2   resolvability #2 — constructs a ballot to add to the profile  *)
(*    §4.6     independence of clones                                        *)
(*    (4.7.5/6) Smith-IIA for genuine REMOVAL of an alternative.  The       *)
(*             closure is defined over the fixed [elements] of the FinType, *)
(*             so there is no closure over a subset to compare against;     *)
(*             stating it needs either a list-parameterised closure or a    *)
(*             transfer lemma across two FinTypes.  The isolation surrogate *)
(*             for (4.7.5)(a) is [smith_iia_isolate]; (4.7.5)(b) does not   *)
(*             survive that surrogate, since an isolated d becomes a        *)
(*             spurious winner.  (4.7.6) needs the mirrored argument for    *)
(*             pairs inside B2.                                             *)
(*    (4.5.6, ⊆) S_new ⊆ S_old in general.  Proved under a no-ties          *)
(*             hypothesis on A (winner_monotonicity_subset); the paper's    *)
(*             tie case needs the critical link of a strongest path, the    *)
(*             same gap as §4.2.1                                            *)
(*    majority for solid coalitions, majority, majority loser, Condorcet     *)
(*    loser — the paper derives all of these from Smith (§4.7)               *)
(*    participation — the paper notes it is violated, so nothing to prove    *)
(* ========================================================================= *)

Section SocialChoice.

  Context 
    {Node : FinType.type}.

  (* Kleene star:  A* = I + A + A² + … + A^{|N|-1}                          *)
  Definition kleene_exp := (List.length (@elements Node) - 1)%nat.

  (* =====================================================================  *)
  (*  Kleene star as a named definition for readability                     *)
  (* =====================================================================  *)

  Definition mat_star {R : Semiring.type} (M : @Matrix Node R) 
    : @Matrix Node R :=
    geom_sum M kleene_exp.


  (* =====================================================================  *)
  (*  Relationship between the four definitions (all built from beats):      *)
  (*                                                                          *)
  (*    beats N a b          := N_{ba} < N_{ab}     (fundamental)            *)
  (*    condorcet_winner M a := ∀X≠a, beats M a X   (direct matrix)         *)
  (*    schulze_beats M a b  := beats (mat_star M) a b  (Kleene star order) *)
  (*    strict_winner M a    := ∀X≠a, schulze_beats M a X  (beats all)     *)
  (*    schulze_winner M a   := ∀b≠a, ~ schulze_beats M b a  (undefeated)  *)
  (*                                                                          *)
  (*  The paper's Definition 2.2.1 (relation O) is schulze_beats.            *)
  (*  The paper's Definition 2.2.2 (winner set S) is schulze_winner.         *)
  (* =====================================================================  *)
  (*  Stabilization lemma: pow (M+I) stabilizes after |N|-1 steps.           *)
  (* =====================================================================  *)


  (* =====================================================================  *)
  (*  Fundamental: a beats b in matrix N if N_{ba} < N_{ab}                 *)
  (*  — i.e., N b a ≤ N a b  ∧  N b a ≠ N a b.                      *)
  (* =====================================================================  *)

  Definition beats {R : Semiring.type}
    (N : @Matrix Node R) (a b : Node) : Prop :=
    N b a < N a b.

  (* =====================================================================  *)
  (*  Condorcet winner: beats everyone in the DIRECT matrix M               *)
  (*  condorcet_winner M a := ∀X≠a, beats M a X                             *)
  (* =====================================================================  *)

  Definition condorcet_winner {R : Semiring.type}
    (M : @Matrix Node R) (a : Node) : Prop :=
    forall (X : Node), X ≠ a -> beats M a X.

  (* =====================================================================  *)
  (*  Schulze order: beats in the Kleene star M*                            *)
  (*  schulze_beats M a b := beats (mat_star M) a b                         *)
  (*  (Definition 2.2.1 in the paper)                                       *)
  (* =====================================================================  *)

  Definition schulze_beats {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) : Prop :=
    beats (mat_star M) a b.

  (* =====================================================================  *)
  (*  Strict winner: beats everyone in the Schulze sense (via M* )          *)
  (*  strict_winner M a := ∀X≠a, schulze_beats M a X                        *)
  (* =====================================================================  *)

  Definition strict_winner {R : Semiring.type}
    (M : @Matrix Node R) (a : Node) : Prop :=
    forall (X : Node), X ≠ a -> schulze_beats M a X.

  (* =====================================================================  *)
  (*  Schulze winner: nobody beats me in the Schulze sense                  *)
  (*  schulze_winner M a := ∀b≠a, ~ schulze_beats M b a                     *)
  (*  (Definition 2.2.2 in the paper)                                       *)
  (* =====================================================================  *)

  Definition schulze_winner {R : Semiring.type}
    (M : @Matrix Node R) (a : Node) : Prop :=
    forall (b : Node), b ≠ a -> ~ schulze_beats M b a.

  (* =====================================================================  *)
  (*  Strict partial order (Definition in §2.1): transitive and asymmetric. *)
  (*  This is the shape the paper claims for the output relation O; see     *)
  (*  [schulze_output_well_formed] below.                                   *)
  (* =====================================================================  *)

  Definition strict_partial_order (Rel : Node -> Node -> Prop) : Prop :=
    (forall a b c, Rel a b -> Rel b c -> Rel a c) /\
    (forall a b, Rel a b -> ~ Rel b a).

  (** Asymmetry already yields irreflexivity, so the paper's two conditions
      are all that a strict partial order has to supply. *)
  Remark spo_irreflexive (Rel : Node -> Node -> Prop) :
    strict_partial_order Rel -> forall a, ~ Rel a a.
  Proof. intros [_ Hasym] a Ha. exact (Hasym a a Ha Ha). Qed.

  (* =====================================================================  *)
  (*  Lemma: transpose commutes with Kleene star                            *)
  (*                                                                         *)
  (*  (M^T)* = (M* )^T                                                       *)
  (*  Requires commutative multiplication (mulC) for (M^T)^k = (M^k)^T.     *)
  (* =====================================================================  *)

  Lemma pow_transpose {R : CommutativeSemiring.type}
    (M : @Matrix Node R) (k : nat) (i j : Node) :
    pow (fun x y => M y x) k i j = pow M k j i.
  Proof.
    revert i j. 
    induction k as [|k IH]; intros i j; cbn [pow].
    - (* Base: I i j = I j i *)
      unfold I.
      destruct (fin_eq_dec i j) as [Heq|Hneq];
      destruct (fin_eq_dec j i) as [Heq'|Hneq'];
      try reflexivity; try congruence.
    - (* Inductive step *)
      unfold matrix_mul.
      rewrite (sum_ext (fun X => M X i * pow (fun x y => M y x) k X j)
      (fun X => M X i * pow M k j X)).
      + rewrite (sum_ext (fun X => M X i * pow M k j X)
        (fun X => pow M k j X * M X i)).
        * symmetry. apply (pow_comm k M j i).
        * intro X. apply mulC.
      + intro X. rewrite (IH X j). reflexivity.
  Qed.

  Lemma geom_sum_transpose {R : CommutativeSemiring.type}
    (M : @Matrix Node R) (n : nat) (i j : Node) :
    geom_sum (fun x y => M y x) n i j = geom_sum M n j i.
  Proof.
    induction n as [|n IH]; cbn [geom_sum].
    - unfold I.
      destruct (fin_eq_dec i j) as [Heq|Hneq];
      destruct (fin_eq_dec j i) as [Heq'|Hneq'].
      + reflexivity.
      + congruence.
      + congruence.
      + reflexivity.
    - unfold matrix_add.
      rewrite IH.
      rewrite (pow_transpose M (S n) i j).
      reflexivity.
  Qed.


  Lemma mat_star_transpose {R : CommutativeSemiring.type} : 
    forall (M : @Matrix Node R) (i j : Node),
      mat_star (fun x y => M y x) i j = mat_star M j i.
  Proof.
    intros M i j.
    unfold mat_star.
    apply geom_sum_transpose.
  Qed.


  (* In a bounded semiring, addition is idempotent: a+a = a.                 *)
  (* Proof: a = a·1 = a·(1+1) = a·1 + a·1 = a + a.                          *)
  Lemma bounded_add_idem {R : BoundedSemiring.type} (a : R) : a + a = a.
  Proof.
    transitivity (a * 1 + a * 1).
    - apply (f_equal2 add); symmetry; apply mulr1.
    - transitivity (a * (1 + 1)).
      + symmetry. apply (mulDl a 1 1).
      + transitivity (a * 1).
        * apply (f_equal (fun t => mul a t)). apply (add_bound (s := R) 1).
        * apply mulr1.
  Qed.

  Lemma bounded_orel_refl {R : BoundedSemiring.type} (a : R) : a ≤ a.
  Proof. unfold Orel. apply bounded_add_idem. Qed.

  Lemma bounded_mul_orel_compat_r {R : BoundedSemiring.type} (a b c : R) :
    a ≤ b -> c * a ≤ c * b.
  Proof.
    unfold Orel. intros Hab.
    transitivity (c * (a + b)).
    - symmetry. apply (mulDl c a b).
    - apply (f_equal (fun t => mul c t)). exact Hab.
  Qed.

  Lemma bounded_mul_orel_compat_l {R : BoundedSemiring.type} (a b c : R) :
    a ≤ b -> a * c ≤ b * c.
  Proof.
    unfold Orel. intros Hab.
    transitivity ((a + b) * c).
    - symmetry. apply (mulDr a b c).
    - apply (f_equal (fun t => mul t c)). exact Hab.
  Qed.

  Lemma bounded_mul_lower_left {R : BoundedSemiring.type} (a b : R) : a * b ≤ a.
  Proof.
    unfold Orel.
    transitivity (a * b + a * 1).
    - apply (f_equal (fun t => a * b + t)). symmetry. apply mulr1.
    - transitivity (a * (b + 1)).
      + symmetry. apply (mulDl a b 1).
      + transitivity (a * 1).
        * apply (f_equal (fun t => a * t)). rewrite addC. apply (add_bound (s := R) b).
        * apply mulr1.
  Qed.

  Lemma bounded_mul_lower_right {R : BoundedSemiring.type} (a b : R) : a * b ≤ b.
  Proof.
    unfold Orel.
    transitivity (a * b + 1 * b).
    - apply (f_equal (fun t => a * b + t)). symmetry. apply mul1r.
    - transitivity ((a + 1) * b).
      + symmetry. apply (mulDr a 1 b).
      + transitivity (1 * b).
        * apply (f_equal (fun t => t * b)). rewrite addC. apply (add_bound (s := R) a).
        * apply mul1r.
  Qed.

  (* If every term of a sum is ≤ v, then the whole sum is ≤ v.               *)
  Lemma sum_orel_bound {R : Semiring.type} 
    (f : Node -> R) (v : R) :
    (forall x, (f x) ≤ v) -> (sum f) ≤ v.
  Proof.
    unfold Orel, sum.
    intro H.
    induction (@elements Node) as [|a l IH]; cbn.
    - apply add0r.
    - (* Goal: (f a + fold_right ... l) + v = v *)
      (* addA: (x+y)+z = x+(y+z) *)
      transitivity (f a + (fold_right (fun (x : Node) (y : R) => f x + y) 0 l + v)).
      + apply addA.
      + assert (Htmp : fold_right (fun (x : Node) (y : R) => f x + y) 0 l + v = v).
        { apply IH. }
        rewrite Htmp. apply (H a).
  Qed.

  (* If a ≤ c and b ≤ c then a+b ≤ c.  Works for any commutative monoid.    *)
  Lemma add_orel_bound {R : CommutativeMonoid.type} (a b c : R) :
    a ≤ c -> b ≤ c -> (a + b) ≤ c.
  Proof.
    unfold Orel. intros Ha Hb.
    rewrite addA, Hb, Ha. reflexivity.
  Qed.

  (** [x < y] and [y ≤ z] give [x < z]. *)
  Lemma orel_lt_le_trans {R : CommutativeMonoid.type} (x y z : R) :
    x < y -> y ≤ z -> x < z.
  Proof.
    intros [Hxy_le Hxy_neq] Hyz. split.
    - exact (orel_trans _ _ _ Hxy_le Hyz).
    - intro Heq. apply Hxy_neq.
      apply orel_antisym; [exact Hxy_le | rewrite Heq; exact Hyz].
  Qed.

  (** Transitivity: x ≤ y and y < z implies x < z. *)
  Lemma orel_lt_trans {R : CommutativeMonoid.type} (x y z : R) :
    x ≤ y -> y < z -> x < z.
  Proof.
    intros Hxy [Hyz_le Hyz_neq]. split.
    - unfold Orel.
      red in Hxy. red in Hyz_le.
      rewrite <- Hyz_le at 1. (* z → y + z *)
      rewrite <- addA.        (* x + (y + z) → (x + y) + z *)
      rewrite Hxy.             (* x + y → y *)
      rewrite Hyz_le. reflexivity.
    - intro Heq. subst x. apply Hyz_neq.
      apply orel_antisym; assumption.
  Qed.

  Lemma bounded_plus_upper_left {R : BoundedSemiring.type} (a b : R) : a ≤ a + b.
  Proof.
    unfold Orel. rewrite <- addA. rewrite (bounded_add_idem a). reflexivity.
  Qed.

  Lemma orel_plus_upper_right {R : BoundedSemiring.type} (a b : R) : a ≤ b + a.
  Proof.
    unfold Orel.
    rewrite <- (addA a b a).
    rewrite (addC a b).
    rewrite (addA b a a).
    rewrite (bounded_add_idem a).
    reflexivity.
  Qed.

  
  (* In a bounded semiring, the diagonal of geom_sum is always 1.            *)
  Lemma geom_sum_diag_one {R : BoundedSemiring.type}
    (M : @Matrix Node R) (n : nat) (A : Node) :
    geom_sum M n A A = 1.
  Proof.
    induction n as [|n IH]; cbn [geom_sum].
    - unfold I. destruct (fin_eq_dec A A) as [_|Hc]; [reflexivity | congruence].
    - unfold matrix_add. rewrite IH. apply (add_bound (s := R) (pow M (S n) A A)).
  Qed.


  
  (* ==================================================================== *)
  (*  Order-theoretic facts about O and the two notions of winner          *)
  (* ==================================================================== *)

  (** With at least two alternatives, every alternative has a rival. *)
  Lemma exists_other (x : Node) : exists y : Node, y ≠ x.
  Proof.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    pose proof (elements_nodup (s := Node)) as Hnd.
    destruct (elements (s := Node)) as [|z1 [|z2 l]] eqn:He;
      cbn in Hlen; try lia.
    inversion Hnd as [|u0 l0 Hnin Hnd'].
    assert (Hz12 : z1 ≠ z2).
    { intro Habs. apply Hnin. rewrite Habs. left. reflexivity. }
    destruct (fin_eq_dec z1 x) as [Heq|Hne].
    - exists z2. intro Habs. apply Hz12. rewrite Habs. exact Heq.
    - exists z1. exact Hne.
  Qed.

  (** Asymmetry of O (§2.2): it follows from the asymmetry of the strict
      order on path strengths, exactly as in the paper. *)
  Lemma schulze_beats_asym {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) :
    schulze_beats M a b -> ~ schulze_beats M b a.
  Proof.
    unfold schulze_beats, beats.
    intros [Hab_le Hab_ne] [Hba_le _].
    apply Hab_ne, orel_antisym; assumption.
  Qed.



  (** Beating everybody implies being unbeaten: [strict_winner ⊆ schulze_winner]. *)
  Lemma strict_winner_is_schulze_winner {R : Semiring.type}
    (M : @Matrix Node R) (a : Node) :
    strict_winner M a -> schulze_winner M a.
  Proof.
    intros Hstrict b Hb_ne_a.
    exact (schulze_beats_asym M a b (Hstrict b Hb_ne_a)).
  Qed.

  (** A strict winner leaves no other winner. *)
  Lemma strict_winner_excludes_others {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) :
    strict_winner M a -> b ≠ a -> ~ schulze_winner M b.
  Proof.
    intros Ha Hb Hwin.
    exact (Hwin a (fun h => Hb (eq_sym h)) (Ha b Hb)).
  Qed.

  (** Hence there is at most one strict winner. *)
  Lemma strict_winner_unique {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) :
    strict_winner M a -> strict_winner M b -> a = b.
  Proof.
    intros Ha Hb.
    destruct (fin_eq_dec a b) as [Heq|Hne]; [exact Heq | exfalso].
    exact (schulze_beats_asym M a b
      (Ha b (fun h => Hne (eq_sym h))) (Hb a Hne)).
  Qed.

  (** The same argument one level down, on [M] itself. *)
  Lemma condorcet_winner_unique {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) :
    condorcet_winner M a -> condorcet_winner M b -> a = b.
  Proof.
    intros Ha Hb.
    destruct (fin_eq_dec a b) as [Heq|Hne]; [exact Heq | exfalso].
    destruct (Ha b (fun h => Hne (eq_sym h))) as [Hab_le Hab_ne].
    destruct (Hb a Hne) as [Hba_le _].
    apply Hab_ne, orel_antisym; assumption.
  Qed.

  (* ==================================================================== *)
  (*  Resolvability (Section 4.2) — the resolution step only               *)
  (*                                                                       *)
  (*  Schulze's 4.2.1 argues that two distinct winners [a] and [b] force   *)
  (*  a tie [P_D[a,b] ≈ P_D[b,a]] (4.2.1.3), and then rules that out when  *)
  (*  no two links have equivalent strength.  What follows is the          *)
  (*  contrapositive of the first half: a winner that is never tied in the *)
  (*  closure beats everyone, hence is the unique winner.                  *)
  (*                                                                       *)
  (*  The second half — that distinct LINK strengths force an untied       *)
  (*  closure — is not formalised.  The paper proves it by locating the    *)
  (*  weakest link of the strongest path and splitting both paths there,   *)
  (*  which needs [*] to be a selective meet (so that every closure entry  *)
  (*  is attained by some individual link) plus path-level reasoning from  *)
  (*  [PathN.v].  Nor is the criterion as literally stated: both of the    *)
  (*  paper's formulations quantify over profiles and voters, and this     *)
  (*  development has no ballot layer — [M] is an abstract matrix.         *)
  (* ==================================================================== *)

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

  (* ==================================================================== *)
  (*  Selectivity: the closure invents no new values                       *)
  (*                                                                       *)
  (*  [Htotal] and [Hmeet] together — the pair already assumed by          *)
  (*  [prudence] and [minmax_beats], and satisfied by the max-min semiring *)
  (*  of the Schulze instance — make both operations SELECTIVE: [x + y]    *)
  (*  and [x * y] each return one of their arguments.  So every entry of   *)
  (*  the closure is either a bound or the strength of an actual link.     *)
  (*  This is the algebraic content of the paper's habit of naming the     *)
  (*  critical link of a strongest path, e.g. in 4.2.1.                    *)
  (*                                                                       *)
  (*  Note what this does NOT give: the value being some link's strength   *)
  (*  says nothing about WHICH link, or that it lies on a path from [a] to *)
  (*  [b].  Recovering that — and with it the paper's path-splitting       *)
  (*  arguments — needs the witness, not just the value.                   *)
  (* ==================================================================== *)

  (** With a total order the meet of two elements is one of them. *)
  Lemma mul_selective {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x) (x y : R) :
    x * y = x \/ x * y = y.
  Proof.
    destruct (Htotal x y) as [Hc | Hc].
    - right. assert (Hyx : y ≤ x) by (unfold Orel; rewrite addC; exact Hc).
      exact (proj2 (Hmeet y x Hyx)).
    - left. exact (proj1 (Hmeet x y Hc)).
  Qed.

  (** A selective join over a list returns [0] or one of the summands. *)
  Lemma fold_selective {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (f : Node -> R) :
    forall l : list Node,
      fold_right (fun x acc => f x + acc) 0 l = 0 \/
      exists z, In z l /\ fold_right (fun x acc => f x + acc) 0 l = f z.
  Proof.
    induction l as [|a l IH]; cbn [fold_right].
    - left. reflexivity.
    - destruct (Htotal (f a) (fold_right (fun x acc => f x + acc) 0 l)) as [Hc | Hc].
      + right. exists a. split; [left; reflexivity | exact Hc].
      + destruct IH as [H0 | [z [Hz Hfz]]].
        * left. rewrite Hc. exact H0.
        * right. exists z. split; [right; exact Hz |]. rewrite Hc. exact Hfz.
  Qed.

  Lemma sum_selective {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (f : Node -> R) :
    sum f = 0 \/ exists z, sum f = f z.
  Proof.
    unfold sum.
    destruct (fold_selective Htotal f (@elements Node)) as [H0 | [z [_ Hz]]].
    - left. exact H0.
    - right. exists z. exact Hz.
  Qed.

  (** A value is a bound or the strength of some link. *)
  Definition link_or_extreme {R : Semiring.type} (M : @Matrix Node R) (v : R) : Prop :=
    v = 0 \/ v = 1 \/ exists x y, v = M x y.

  Lemma pow_link_or_extreme {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x)
    (M : @Matrix Node R) (n : nat) :
    forall a b, link_or_extreme M (pow M n a b).
  Proof.
    induction n as [|n IH]; intros a b.
    - cbn [pow]. unfold I.
      destruct (fin_eq_dec a b);
        [right; left; reflexivity | left; reflexivity].
    - cbn [pow]. unfold matrix_mul.
      destruct (sum_selective Htotal (fun z => M a z * pow M n z b))
        as [H0 | [z Hz]].
      + left. exact H0.
      + rewrite Hz. cbv beta.
        destruct (mul_selective Htotal Hmeet (M a z) (pow M n z b)) as [Hc | Hc].
        * rewrite Hc. right; right. exists a, z. reflexivity.
        * rewrite Hc. apply IH.
  Qed.

  Lemma mat_star_link_or_extreme {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x)
    (M : @Matrix Node R) (a b : Node) :
    link_or_extreme M (mat_star M a b).
  Proof.
    unfold mat_star.
    induction kleene_exp as [|K IH]; cbn [geom_sum].
    - unfold I. destruct (fin_eq_dec a b);
        [right; left; reflexivity | left; reflexivity].
    - unfold matrix_add.
      destruct (Htotal (geom_sum M K a b) (pow M (S K) a b)) as [Hc | Hc];
        setoid_rewrite Hc.
      + exact IH.
      + apply pow_link_or_extreme; assumption.
  Qed.

  (* ==================================================================== *)
  (*  Reversal symmetry (Section 4.4)                                      *)
  (* ==================================================================== *)

  (** Reversal symmetry (4.4.2): reversing every ballot reverses the whole
      relation O.  This is the paper's statement, and it is immediate from
      [mat_star_transpose]. *)
  Theorem reversal_symmetry_O {R : CommutativeSemiring.type}
    (M : @Matrix Node R) (a b : Node) :
    schulze_beats M a b <-> schulze_beats (fun i j => M j i) b a.
  Proof.
    unfold schulze_beats, beats.
    rewrite (mat_star_transpose M a b), (mat_star_transpose M b a).
    reflexivity.
  Qed.

  (** The winner-level consequence: a strict winner cannot stay one when the
      ballots are reversed. *)
  Theorem reversal_symmetry {R : CommutativeSemiring.type} :
    forall (M : @Matrix Node R) (A : Node),
      strict_winner M A -> ~ strict_winner (fun i j => M j i) A.
  Proof.
    intros M A H_win H_win_rev.
    destruct (exists_other A) as [B H_BA].
    (* [A] beats [B] originally, and beating [B] in the reversed profile is
       exactly being beaten by [B] in the original one *)
    exact (schulze_beats_asym M A B
      (H_win B H_BA)
      (proj2 (reversal_symmetry_O M B A) (H_win_rev B H_BA))).
  Qed.



  Lemma pow_pointwise {R : Semiring.type} (A B : @Matrix Node R) (n : nat) (x y : Node) :
    (forall i j, A i j = B i j) -> pow A n x y = pow B n x y.
  Proof.
    revert x y. induction n as [|n IH]; intros x y Heq; cbn.
    - (* I x y is independent of A/B *)
      reflexivity.
    - (* matrix_mul: sum over z of A x z * pow A n z y *)
      unfold matrix_mul.
      apply sum_ext. intro z.
      rewrite (Heq x z). rewrite (IH z y Heq). reflexivity.
  Qed.


  Lemma pow_MplusI_stable {R : BoundedSemiring.type}
    (M : @Matrix Node R) (n : nat) (a c : Node) :
    pow (matrix_add M (I : @Matrix Node R)) (kleene_exp + n) a c =
    pow (matrix_add M (I : @Matrix Node R)) kleene_exp a c.
  Proof.
    (* (M+I)[i,i] = M[i,i] + 1 = 1 (bounded semiring: a+1=1) *)
    assert (Hdiag : forall (u v : Node), u = v -> (matrix_add M (I : @Matrix Node R)) u v = 1).
    { intros u v Heq. subst v.
      unfold matrix_add.
      assert (Htmp : (I : @Matrix Node R) u u = 1).
      { unfold I. destruct (fin_eq_dec u u); [reflexivity | congruence]. }
      rewrite Htmp.
      transitivity ((1 : R) + (M u u : R)).
      { apply (addC (M u u : R) (1 : R)). }
      { apply (add_bound (s := R) (M u u)). } }
    eapply eq_sym.
    unfold kleene_exp.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    replace (length elements - 1 + n)%nat with 
      (n + length (@elements Node) - 1)%nat by lia.
    (* Apply fixpoint lemma with m := M+I (diagonal = 1). *)
    pose proof (@matrix_pow_fixpoint_after_node_bound Node R n
      (matrix_add M (I : @Matrix Node R)) a c
      (fun u v Heq => Hdiag u v Heq)) as Hfix.
    (* Key: (M+I)+I = M+I pointwise (since I+I=I in bounded semiring). *)
    assert (Hidem : forall i j, (matrix_add (matrix_add M (I : @Matrix Node R)) (I : @Matrix Node R)) i j =
                                (matrix_add M (I : @Matrix Node R)) i j).
    { intros i j. unfold matrix_add.
      destruct (fin_eq_dec i j) as [Heq|Hneq].
      - subst j. unfold I.
        destruct (fin_eq_dec i i); [|congruence].
        rewrite (addA (M i i) 1 1).
        apply (f_equal (fun t => M i i + t)). apply (add_bound (s := R) 1).
      - unfold I. destruct (fin_eq_dec i j); [congruence|].
        rewrite !addr0. reflexivity. }
    (* Use pow_pointwise to lift pointwise equality to pow equality *)
    pose proof (pow_pointwise _ _ (length (@elements Node) - 1) a c Hidem) as Heq1.
    pose proof (pow_pointwise _ _ (n + length (@elements Node) - 1) a c Hidem) as Heq2.
    rewrite Heq1, Heq2 in Hfix.
    exact Hfix.
  Qed.
    
  (* =====================================================================  *)
  (*  Lemma: path concatenation (Kleene star idempotence)                     *)
  (*                                                                          *)
  (*  M*_{ab} * M*_{bc} ≤ M*_{ac}                                             *)
  (*                                                                          *)
  (*  Algebraic proof:                                                        *)
  (*  1. mat_star M = pow (M+I)^K (matrix_pow_idempotence_bounded)           *)
  (*  2. pow B^K a b * pow B^K b c ≤ (pow B^K · pow B^K) a c                *)
  (*     (b is one summand in the matrix multiplication)                      *)
  (*  3. (pow B^K · pow B^K) = pow B^{2K} (pow_add)                          *)
  (*  4. pow B^{2K} = pow B^K (stabilization lemma above)                    *)
  (*  5. pow B^K = mat_star M (matrix_pow_idempotence_bounded)               *)
  (* =====================================================================  *)

  Lemma star_path_compose {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b c : Node) :
    mat_star M a b * mat_star M b c ≤ mat_star M a c.
  Proof.
    set (B := matrix_add M (I : @Matrix Node R)).
    set (K := kleene_exp).
    (* Step 1: rewrite mat_star M to pow B K pointwise *)
    assert (Hstar_pt : forall x y, mat_star M x y = pow B K x y).
    { intros x y. unfold mat_star, B, K.
      symmetry. apply (matrix_pow_idempotence_bounded K M x y). }
    rewrite !Hstar_pt.
    (* Goal: pow B K a b * pow B K b c ≤ pow B K a c *)
    (* Step 2: bound by matrix multiplication *)
    assert (Hmul : pow B K a b * pow B K b c ≤ matrix_mul (pow B K) (pow B K) a c).
    { unfold matrix_mul, sum.
      assert (Hin : In b (@elements Node)).
      { apply elements_complete. }
      induction (@elements Node) as [|x xs IH].
      - inversion Hin.
      - cbn. destruct (fin_eq_dec x b) as [Heq|Hneq].
        + subst x. apply bounded_plus_upper_left.
        + assert (Hin' : In b xs) by (inversion Hin; [congruence | assumption]).
          specialize (IH Hin').
          set (S := fold_right (λ (x0 : Node) (y : R), pow B K a x0 * pow B K x0 c + y) 0 xs).
          assert (Htmp : S ≤ pow B K a x * pow B K x c + S).
          { apply orel_plus_upper_right. }
          unfold S in IH.
          eapply orel_trans; [exact IH | exact Htmp]. }
    (* Step 3-4: matrix multiplication = pow B (2K) = pow B K *)
    assert (Hpow : matrix_mul (pow B K) (pow B K) a c = pow B K a c).
    { unfold K, B.
      rewrite <- (pow_add (matrix_add M (I : @Matrix Node R)) kleene_exp kleene_exp a c).
      rewrite (pow_MplusI_stable M kleene_exp a c).
      reflexivity. }
    rewrite Hpow in Hmul.
    exact Hmul.
  Qed.

  (** * 4.1 Transitivity of Schulze beats — meet-semiring proof

      Same conclusion as [schulze_trans] (if [a] beats [b] and [b] beats [c]
      then [a] beats [c]), but replacing the strong normalisation hypothesis
      [H_pair_sum_one] with a meet-lower-bound axiom:

        H_meet_lower_bound : m ≤ a → m ≤ b → m ≤ a * b

      This axiom says that if [m] is a lower bound of both [a] and [b], then
      [m] is also a lower bound of their product [a * b].  Together with the
      bounded-semiring facts [a * b ≤ a] and [a * b ≤ b], this makes [*]
      into a greatest-lower-bound (meet) operation.
  *)
  Theorem schulze_trans_weaker_necessary {R : BoundedSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) :
    forall (M : @Matrix Node R) (a b c : Node),
      schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c.
  Proof.
    intros M a b c H_ab H_bc.
    unfold schulze_beats, beats in *.
    destruct H_ab as [H_ab_le H_ab_ne].   (* S b a ≤ S a b ∧ S b a ≠ S a b *)
    destruct H_bc as [H_bc_le H_bc_ne].   (* S c b ≤ S b c ∧ S c b ≠ S b c *)
    (* m := S a b * S b c *)
    (* m ≤ S a c by star_path_compose *)
    pose proof (star_path_compose M a b c) as Hm_Sac.
    (* H_total_order gives total preorder on Orel *)
    assert (H_total_orel : forall x y : R, x ≤ y \/ y ≤ x).
    { intros x y.
      destruct (H_total_order x y) as [Hcase | Hcase].
      - right. unfold Orel. rewrite addC. exact Hcase.
      - left. unfold Orel. exact Hcase. }
    (* Lemma: mat_star M a c ≤ mat_star M c a is impossible *)
    assert (H_not_ac_le_ca : ~ (mat_star M a c ≤ mat_star M c a)).
    { intro H_ac_le_ca.
      (* Then m ≤ S c a via Hm_Sac and H_ac_le_ca *)
      assert (Hm_Sca : mat_star M a b * mat_star M b c ≤ mat_star M c a).
      { eapply orel_trans; [exact Hm_Sac | exact H_ac_le_ca]. }
      (* Case split on S a b vs S b c *)
      destruct (H_total_orel (mat_star M a b) (mat_star M b c))
        as [Hab_le_Hbc | Hbc_le_Hab].
      - (* Case A: S a b ≤ S b c.  Then m = S a b. *)
        assert (Hm_eq_Sab : mat_star M a b * mat_star M b c = mat_star M a b).
        { apply orel_antisym.
          - apply (@bounded_mul_lower_left R (mat_star M a b) (mat_star M b c)).
          - apply H_meet_lower_bound.
            + apply (@bounded_orel_refl R (mat_star M a b)).
            + exact Hab_le_Hbc. }
        rewrite Hm_eq_Sab in Hm_Sca.             (* S a b ≤ S c a *)
        (* S b c ≥ S a b = m *)
        assert (H_Sbc_ge_m : mat_star M a b ≤ mat_star M b c).
        { rewrite <- Hm_eq_Sab.
          apply (@bounded_mul_lower_right R (mat_star M a b) (mat_star M b c)). }
        (* H_meet_lower_bound: m ≤ S b c and m ≤ S c a → m ≤ S b c * S c a *)
        assert (Hm_Sbc_Sca : mat_star M a b ≤
                             mat_star M b c * mat_star M c a).
        { apply H_meet_lower_bound; [exact H_Sbc_ge_m | exact Hm_Sca]. }
        (* star_path_compose: S b c * S c a ≤ S b a *)
        pose proof (star_path_compose M b c a) as H_comp.
        assert (Hm_Sba : mat_star M a b ≤ mat_star M b a).
        { eapply orel_trans; [exact Hm_Sbc_Sca | exact H_comp]. }
        (* Antisymmetry with S b a ≤ S a b from beats a b *)
        assert (Heq : mat_star M b a = mat_star M a b).
        { apply orel_antisym; [exact H_ab_le | exact Hm_Sba]. }
        exact (H_ab_ne Heq).
      - (* Case B: S b c ≤ S a b.  Then m = S b c. *)
        assert (Hm_eq_Sbc : mat_star M a b * mat_star M b c = mat_star M b c).
        { apply orel_antisym.
          - apply (@bounded_mul_lower_right R (mat_star M a b) (mat_star M b c)).
          - apply H_meet_lower_bound.
            + exact Hbc_le_Hab.
            + apply (@bounded_orel_refl R (mat_star M b c)). }
        rewrite Hm_eq_Sbc in Hm_Sca.             (* S b c ≤ S c a *)
        (* S a b ≥ S b c = m *)
        assert (H_Sab_ge_m : mat_star M b c ≤ mat_star M a b).
        { rewrite <- Hm_eq_Sbc.
          apply (@bounded_mul_lower_left R (mat_star M a b) (mat_star M b c)). }
        (* H_meet_lower_bound: m ≤ S c a and m ≤ S a b → m ≤ S c a * S a b *)
        assert (Hm_Sca_Sab : mat_star M b c ≤
                             mat_star M c a * mat_star M a b).
        { apply H_meet_lower_bound; [exact Hm_Sca | exact H_Sab_ge_m]. }
        pose proof (star_path_compose M c a b) as H_comp.
        assert (Hm_Scb : mat_star M b c ≤ mat_star M c b).
        { eapply orel_trans; [exact Hm_Sca_Sab | exact H_comp]. }
        assert (Heq : mat_star M c b = mat_star M b c).
        { apply orel_antisym; [exact H_bc_le | exact Hm_Scb]. }
        exact (H_bc_ne Heq). }
    (* Now: S a c ≤ S c a is impossible, so by total order, S c a ≤ S a c *)
    destruct (H_total_orel (mat_star M a c) (mat_star M c a))
      as [Hac_le_Sca | Hca_le_Sac].
    - exfalso. exact (H_not_ac_le_ca Hac_le_Sca).
    - split; [exact Hca_le_Sac |].
      intro Heq. apply H_not_ac_le_ca. rewrite Heq.
      apply (@bounded_orel_refl R (mat_star M a c)).
  Qed.



  Theorem schulze_trans_weaker_sufficient {R : BoundedSemiring.type} :
    (3 <= List.length (@elements Node))%nat ->
    (forall x y : R, {x = y} + {x <> y}) ->
    (forall (M : @Matrix Node R) (a b c : Node),
      schulze_beats M a b -> schulze_beats M b c ->  schulze_beats M a c) ->
    (forall x y : R, x + y = x \/ x + y = y) /\
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof. 
  Admitted.
  
  
  Theorem transitivity_characterisation {R : BoundedSemiring.type} :
    (3 <= length (@elements Node))%nat ->
    (forall x y : R, {x = y} + {x <> y}) ->
    (forall (M : @Matrix Node R) (a b c : Node),
     schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c) <->
    (forall x y : R, x + y = x ∨ x + y = y) ∧
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    intros ha hdec.
    split; intros * hb *.
    + eapply  schulze_trans_weaker_sufficient;
    [exact ha | exact hdec | exact hb].
    + intros hc hd. destruct hb as (hbl & hbr).
      eapply schulze_trans_weaker_necessary; 
      try assumption;[exact hc | exact hd].
  Qed.
  
  


  (** Each power term is ≤ the full mat_star (idempotent addition). *)
  Lemma pow_le_mat_star {R : BoundedSemiring.type} (M : @Matrix Node R) (m : nat) 
    (A B : Node) :
    (m <= kleene_exp)%nat -> pow M m A B ≤ mat_star M A B.
  Proof.
    unfold mat_star. revert m.
    induction kleene_exp as [|K IH]; intros m Hle; cbn [geom_sum].
    - assert (m = 0)%nat by lia. subst m. cbn [pow].
      unfold I, Orel. destruct (fin_eq_dec A B); apply bounded_add_idem.
    - destruct (Compare_dec.lt_eq_lt_dec m (S K)) as [[Hlt|Heq]|Hgt].
      + assert (m <= K)%nat by lia. specialize (IH m H).
        unfold matrix_add. eapply orel_trans; [apply IH |]. apply bounded_plus_upper_left.
      + subst m. unfold matrix_add. apply orel_plus_upper_right.
      + lia.
  Qed.

  (** A link is a path of length one. 2.2.3 
      ∀a,b ∈ A : P_D [a,b] ≿_D (N [a,b], N [b,a]). 
  *)
  Lemma link_le_mat_star {R : BoundedSemiring.type}
    (M : @Matrix Node R) (x y : Node) : M x y ≤ mat_star M x y.
  Proof.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    pose proof (@pow_le_mat_star R M 1 x y) as h.
    unfold kleene_exp in h. specialize (h ltac:(nia)).
    cbn [pow] in h. rewrite matrix_mul_I_r in h. exact h.
  Qed.

  (** [pow_le_mat_star] without the cap on the exponent.  Beyond [kleene_exp]
      the geometric sum has stabilised, so longer walks add nothing: go via
      [pow M k ≤ pow (M+I) k = geom_sum M k], which
      [geom_sum_stable_after_node_bound] collapses back to [geom_sum M
      kleene_exp].  The diagonal condition is what makes that stabilisation
      hold. *)
  Lemma pow_le_mat_star_any {R : BoundedSemiring.type}
    (M : @Matrix Node R) (Hdiag : forall u v : Node, u = v -> M u v = 1)
    (k : nat) (a b : Node) :
    pow M k a b ≤ mat_star M a b.
  Proof.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    destruct (Compare_dec.le_lt_dec k kleene_exp) as [Hle | Hgt].
    - exact (pow_le_mat_star M k a b Hle).
    - assert (Hstep : pow M k a b ≤ pow (matrix_add M (I : @Matrix Node R)) k a b).
      { apply pow_monotone. intros i j.
        rewrite matrix_add_unfold. apply bounded_plus_upper_left. }
      assert (Heq1 : pow (matrix_add M (I : @Matrix Node R)) k a b
                     = geom_sum M k a b)
        by apply matrix_pow_idempotence_bounded.
      assert (Heq2 : geom_sum M k a b = geom_sum M kleene_exp a b).
      { unfold kleene_exp. unfold kleene_exp in Hgt.
        replace k with ((k - (length (@elements Node) - 1)) +
                        length (@elements Node) - 1)%nat by lia.
        symmetry.
        exact (geom_sum_stable_after_node_bound
                 (k - (length (@elements Node) - 1))%nat M Hdiag a b). }
      unfold mat_star. rewrite <- Heq2, <- Heq1. exact Hstep.
  Qed.

  (** Lifting a uniform bound on the powers of [M] to the closure.  Since
      [pow M 0 = I] is the first summand of every [geom_sum], the hypothesis
      also discharges the base case, so no separate argument about [I] is
      needed at the call sites. *)
  Lemma mat_star_bound {R : BoundedSemiring.type}
    (M : @Matrix Node R) (x y : Node) (c : R) :
    (forall n, pow M n x y ≤ c) -> mat_star M x y ≤ c.
  Proof.
    intros Hpow. unfold mat_star.
    assert (Hgen : forall k, geom_sum M k x y ≤ c).
    { induction k as [|k IH]; cbn [geom_sum].
      - exact (Hpow 0%nat).
      - unfold matrix_add. apply add_orel_bound; [exact IH | exact (Hpow (S k))]. }
    apply Hgen.
  Qed.

  (** [sum_orel_bound] at the bounded-semiring coercion path. *)
  Lemma bounded_sum_orel_bound {R : BoundedSemiring.type} (f : Node -> R) (v : R) :
    (forall x, f x ≤ v) -> sum f ≤ v.
  Proof.
    intros * ha. 
    eapply sum_orel_bound; 
    assumption. 
  Qed.

  

  

  (** Commutativity is not an assumption of the characterisation — it is a
      consequence of the right-hand side.  [a * b] is always a lower bound of
      [a] and [b]; the meet-lower-bound property makes it the GREATEST one,
      and greatest lower bounds are unique. *)
  Corollary meet_lower_bound_implies_comm {R : BoundedSemiring.type} :
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) ->
    forall a b : R, a * b = b * a.
  Proof.
    intros Hmlb a b. apply orel_antisym.
    - exact (Hmlb (a * b) b a (bounded_mul_lower_right a b)
               (bounded_mul_lower_left a b)).
    - exact (Hmlb (b * a) a b (bounded_mul_lower_right b a)
               (bounded_mul_lower_left b a)).
  Qed.
  

  (* =====================================================================  *)
  (*  Theorem — WINNER EXISTENCE (Corollary of §4.1)                          *)
  (*                                                                          *)
  (*  On a finite set, a strict partial order (transitive + irreflexive)     *)
  (*  always has a maximal element.  schulze_beats is transitive (Qed)       *)
  (*  and irreflexive, so a winner exists.                                   *)
  (* =====================================================================  *)

  Lemma schulze_beats_irrefl {R : Semiring.type} (M : @Matrix Node R) (a : Node) :
    ~ schulze_beats M a a.
  Proof.
    unfold schulze_beats, beats.
    intros [Hle Hneq]. apply Hneq. reflexivity.
  Qed.


  (* schulze_beats is decidable when R has decidable equality.               *)
  (* This holds in concrete semirings like max-min (Nat) or min-plus.        *)
  Lemma schulze_beats_dec {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node)
    (Hdec : forall x y : R, {x = y} + {x ≠ y}) :
    {schulze_beats M a b} + {~ schulze_beats M a b}.
  Proof.
    unfold schulze_beats, beats, Orel.
    destruct (Hdec (mat_star M b a + mat_star M a b) (mat_star M a b)) as [Hle | Hnle].
    - destruct (Hdec (mat_star M b a) (mat_star M a b)) as [Heq | Hneq].
      + right. intros [H H']. apply H'. exact Heq.
      + left. split; assumption.
    - right. intros [H H']. apply Hnle. exact H.
  Qed.


  (** Either something beats [a] in the closure, or [a] is a winner.  A finite
      search, so no classical reasoning is needed to invert [schulze_winner]. *)
  Lemma beater_or_winner {R : Semiring.type}
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (M : @Matrix Node R) (a : Node) :
    (exists x, schulze_beats M x a) \/ schulze_winner M a.
  Proof.
    set (test := fun x : Node =>
      if schulze_beats_dec M x a Hdec then true else false).
    destruct (List.filter test (@elements Node)) as [|w ws] eqn:E.
    - right. intros b Hb Hbeats.
      assert (Hin : List.In b (List.filter test (@elements Node))).
      { apply filter_In. split; [apply elements_complete |].
        unfold test. destruct (schulze_beats_dec M b a Hdec);
          [reflexivity | contradiction]. }
      rewrite E in Hin. inversion Hin.
    - left. exists w.
      assert (Hin : List.In w (List.filter test (@elements Node)))
        by (rewrite E; left; reflexivity).
      apply filter_In in Hin as [_ Ht]. unfold test in Ht.
      destruct (schulze_beats_dec M w a Hdec); [assumption | discriminate].
  Qed.

  (** A non-empty list has an element that nothing else in the list beats —
      [schulze_beats] is a strict order, so a finite list has a maximal
      element.  Shared by [winner_exists_weaker_necessary] and
      [winner_beats_nonwinner]. *)
  Lemma exists_maximal_in_list {R : BoundedSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b)
    (M : @Matrix Node R) :
    forall (l : list Node), l <> [] ->
      exists w, In w l /\ (forall b, In b l -> b <> w -> ~ schulze_beats M b w).
  Proof.
    intro l. induction l as [|a l IH]; intros Hnonempty.
    - exfalso. apply Hnonempty. reflexivity.
    - destruct l as [|b l].
      + exists a. split; [left; reflexivity |].
        intros b0 Hb0 Hneq. inversion Hb0 as [Heq|Hfalse].
        * exfalso. apply Hneq. symmetry. exact Heq.
        * inversion Hfalse.
      + assert (Hnonempty_tail : b :: l <> []) by discriminate.
        destruct (IH Hnonempty_tail) as [w [Hin_w Hw_undefeated]].
        destruct (schulze_beats_dec M a w Hdec) as [H_aw | H_not_aw].
        * exists a. split; [left; reflexivity |].
          intros x Hx_in Hx_neq_a.
          inversion Hx_in as [Heq_a | Hx_in_tail].
          { exfalso. apply Hx_neq_a. symmetry. exact Heq_a. }
          intro Hx_beats_a.
          pose proof (@schulze_trans_weaker_necessary R
            H_total_order H_meet_lower_bound M x a w Hx_beats_a H_aw) as Hxw.
          destruct (fin_eq_dec x w) as [Heq_xw | Hneq_xw].
          { subst x. apply (schulze_beats_irrefl M w). exact Hxw. }
          { apply (Hw_undefeated x Hx_in_tail Hneq_xw). exact Hxw. }
        * exists w. split.
          { right. exact Hin_w. }
          intros x Hx_in Hx_neq_w.
          inversion Hx_in as [Heq_a | Hx_in_tail].
          { subst x. exact H_not_aw. }
          { apply (Hw_undefeated x Hx_in_tail Hx_neq_w). }
  Qed.

  (** * Winner existence — meet-semiring version


      a Schulze winner is a
      maximal element of the strict partial order [schulze_beats], and
      such an element always exists on a finite set.  The only change is
      which transitivity lemma is invoked in the induction step.

      Hypothesis summary:
      - [H_total_order]    : addition is a total order (x+y = x ∨ x+y = y)
      - [Hdec]            : decidable equality on R
      - [H_meet_lower_bound]: m ≤ a → m ≤ b → m ≤ a * b                    *)
  Theorem winner_exists_weaker_necessary {R : BoundedSemiring.type} 
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) :
    forall (M : @Matrix Node R), exists (a : Node), schulze_winner M a.
  Proof.
    intro M.
    pose proof (exists_maximal_in_list H_total_order Hdec H_meet_lower_bound M)
      as Hmax.
    assert (Hnonempty : @elements Node <> []).
    { intro Hnil.
      pose proof (elements_two_or_more (s := Node)) as Hlen.
      rewrite Hnil in Hlen. simpl in Hlen. lia. }
    destruct (Hmax (@elements Node) Hnonempty) as [w [Hin_w Hw_undefeated]].
    exists w. unfold schulze_winner.
    intros b Hb_neq_w.
    apply (Hw_undefeated b).
    - apply (elements_complete b).
    - exact Hb_neq_w.
  Qed.

 

  (** Schulze §2.2: "Output of the proposed method are (1) a strict partial
      order O on A and (2) a set ∅ ≠ S ⊆ A of winners."

      Both halves in one statement.  Asymmetry of O is immediate from the
      asymmetry of the strict order on path strengths; transitivity is §4.1;
      non-emptiness of S is the corollary (4.1.14) that §4.1 draws from it.
      The claim [S ⊆ A] carries no content here — [schulze_winner M] is a
      predicate on [Node], so it is a subset of the alternatives by typing.

      This sits after [winner_exists_weaker_necessary] because it depends on
      it, even though the paper states it up front in §2.2. *)
  Theorem schulze_output_well_formed {R : BoundedSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b)
    (M : @Matrix Node R) :
    strict_partial_order (schulze_beats M) /\ (exists a, schulze_winner M a).
  Proof.
    split.
    - split.
      + exact (schulze_trans_weaker_necessary H_total_order H_meet_lower_bound M).
      + exact (schulze_beats_asym M).
    - exact (winner_exists_weaker_necessary H_total_order Hdec
               H_meet_lower_bound M).
  Qed.

  (** Schulze's corollary (4.1.14): every non-winner is beaten by some actual
      winner.  This strengthens [winner_exists_weaker_necessary], which only
      says the winner set is non-empty, and it is what the reversal-symmetry
      results below need.

      The paper climbs from the non-winner through beaters until it reaches a
      winner.  Equivalently, and more directly: take a maximal element [w] of
      the set of alternatives that beat [b].  It beats [b] by construction, and
      it is maximal in the whole population, since anything beating [w] would
      beat [b] by transitivity and so already lie in that set. *)
  Theorem winner_beats_nonwinner {R : BoundedSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) :
    forall (M : @Matrix Node R) (b : Node),
      ~ schulze_winner M b -> exists a, schulze_winner M a /\ schulze_beats M a b.
  Proof.
    intros M b Hnw.
    destruct (beater_or_winner Hdec M b) as [[x Hx] | Hw]; [| contradiction].
    set (test := fun y : Node =>
      if schulze_beats_dec M y b Hdec then true else false).
    assert (Hmem : forall y, schulze_beats M y b ->
                     In y (List.filter test (@elements Node))).
    { intros y Hy. apply filter_In. split; [apply elements_complete |].
      unfold test. destruct (schulze_beats_dec M y b Hdec);
        [reflexivity | contradiction]. }
    assert (Hback : forall y, In y (List.filter test (@elements Node)) ->
                      schulze_beats M y b).
    { intros y Hy. apply filter_In in Hy as [_ Ht]. unfold test in Ht.
      destruct (schulze_beats_dec M y b Hdec); [assumption | discriminate]. }
    assert (HL : List.filter test (@elements Node) <> []).
    { intro H0. pose proof (Hmem x Hx) as Hin. rewrite H0 in Hin. inversion Hin. }
    destruct (exists_maximal_in_list H_total_order Hdec H_meet_lower_bound M
                (List.filter test (@elements Node)) HL) as [w [HwL Hwmax]].
    exists w. split.
    - intros y Hy_ne Hy_beats.
      apply (Hwmax y (Hmem y (schulze_trans_weaker_necessary H_total_order
               H_meet_lower_bound M y w b Hy_beats (Hback w HwL))) Hy_ne).
      exact Hy_beats.
    - exact (Hback w HwL).
  Qed.



  (** Reversal symmetry (4.4.3): reversing the ballots displaces a winner
      exactly when it promotes a non-winner.  The winner-level statement the
      paper actually makes about [S]; [reversal_symmetry] above is the much
      weaker claim about [strict_winner]. *)
  Theorem reversal_symmetry_S {R : BoundedCommutativeSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b)
    (M : @Matrix Node R) :
    (exists i, schulze_winner M i /\ ~ schulze_winner (fun x y => M y x) i) <->
    (exists j, ~ schulze_winner M j /\ schulze_winner (fun x y => M y x) j).
  Proof.
    split.
    - intros [i [Hi_old Hi_new]].
      destruct (winner_beats_nonwinner H_total_order Hdec H_meet_lower_bound
                  (fun x y => M y x) i Hi_new) as [j [Hj_new Hj_beats]].
      exists j. split; [| exact Hj_new].
      intro Hj_old.
      assert (Hij : schulze_beats M i j)
        by (apply (reversal_symmetry_O M i j); exact Hj_beats).
      destruct (fin_eq_dec i j) as [Heq|Hne].
      + subst j. exact (schulze_beats_irrefl M i Hij).
      + exact (Hj_old i Hne Hij).
    - intros [j [Hj_old Hj_new]].
      destruct (winner_beats_nonwinner H_total_order Hdec H_meet_lower_bound
                  M j Hj_old) as [i [Hi_old Hi_beats]].
      exists i. split; [exact Hi_old |].
      intro Hi_new.
      assert (Hji : schulze_beats (fun x y => M y x) j i)
        by (apply (reversal_symmetry_O M i j); exact Hi_beats).
      destruct (fin_eq_dec j i) as [Heq|Hne].
      + subst i. exact (schulze_beats_irrefl M j Hi_beats).
      + exact (Hi_new j Hne Hji).
  Qed.

  (** Reversal symmetry (4.4.4): the reversed profile has the same winner set
      as the original exactly when every alternative wins — i.e. the only way
      reversal changes nothing is that there was nothing to change. *)
  Theorem reversal_symmetry_all_tied {R : BoundedCommutativeSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b)
    (M : @Matrix Node R) :
    (forall x, schulze_winner M x <-> schulze_winner (fun i j => M j i) x) <->
    (forall x, schulze_winner M x).
  Proof.
    split.
    - (* if the two winner sets agree, everybody wins *)
      intros Hsame x.
      destruct (beater_or_winner Hdec M x) as [[y Hy] | Hx]; [| exact Hx].
      exfalso.
      assert (Hx_not : ~ schulze_winner M x).
      { intro Hw. destruct (fin_eq_dec y x) as [Heq|Hne].
        - subst y. exact (schulze_beats_irrefl M x Hy).
        - exact (Hw y Hne Hy). }
      destruct (winner_beats_nonwinner H_total_order Hdec H_meet_lower_bound
                  M x Hx_not) as [i [Hi_old Hi_beats]].
      assert (Hi_new : schulze_winner (fun p q => M q p) i)
        by (apply Hsame; exact Hi_old).
      assert (Hxi : schulze_beats (fun p q => M q p) x i)
        by (apply (reversal_symmetry_O M i x); exact Hi_beats).
      destruct (fin_eq_dec x i) as [Heq|Hne].
      + subst i. exact (schulze_beats_irrefl M x Hi_beats).
      + exact (Hi_new x Hne Hxi).
    - (* everybody wins: then nobody beats anybody, in either direction *)
      intros Hall x.
      assert (Hno : forall i j, ~ schulze_beats M i j).
      { intros i j Hij. destruct (fin_eq_dec i j) as [Heq|Hne].
        - subst j. exact (schulze_beats_irrefl M i Hij).
        - exact (Hall j i Hne Hij). }
      split; intro; [| apply Hall].
      intros b Hb Hbeats.
      exact (Hno x b (proj2 (reversal_symmetry_O M x b) Hbeats)).
  Qed.

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
  Theorem monotonicity {R : BoundedSemiring.type}
    (M M' : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y) :
    (forall (Y : Node), M A Y ≤ M' A Y) ->
    (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
    forall (C : Node), mat_star M A C ≤ mat_star M' A C.
  Proof.
    intros Hrow Heq C.
    unfold mat_star.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    (* Mutual induction: P(n) = (pow M n A C ≤ star') ∧ (∀z≠A, pow M n z C ≤ star' A C + star' z C) *)
    assert (Hmutual : forall n,
      (pow M n A C ≤ geom_sum M' kleene_exp A C) /\
      (forall z, z ≠ A -> pow M n z C ≤ geom_sum M' kleene_exp A C + geom_sum M' kleene_exp z C)).
    { induction n as [|n IH]; split.
      - (* part 1, base: I A C *)
        cbn [pow]. unfold I.
        destruct (fin_eq_dec A C);
        [subst C; rewrite geom_sum_diag_one; apply bounded_orel_refl
        |unfold Orel; apply add0r].
      - (* part 2, base: I z C for z ≠ A *)
        intros z HzneA. cbn [pow]. unfold I.
        destruct (fin_eq_dec z C); [subst C|].
        + rewrite (geom_sum_diag_one M' kleene_exp z).
          (* 1 ≤ star' A C + star' z z = star' A C + 1 *)
          unfold Orel.
          transitivity (1 : R); [apply (@add_bound R (geom_sum M' kleene_exp A z + 1)) |].
          symmetry. rewrite addC. apply (@add_bound R (geom_sum M' kleene_exp A z)).
        + (* 0 ≤ star' A C + star' z C *)
          unfold Orel; apply add0r.
      - (* part 1, inductive: pow M (S n) A C *)
        simpl. unfold matrix_mul.
        apply sum_orel_bound. intro z.
        destruct (fin_eq_dec z A) as [HeqzA|HnezA].
        + (* z = A *)
          subst z. destruct IH as [IH1 _].
          apply (orel_trans _ (M A A * geom_sum M' kleene_exp A C)).
          { apply bounded_mul_orel_compat_r. apply IH1. }
          { 
            apply (orel_trans _ (mat_star M' A A * mat_star M' A C)).
            { apply bounded_mul_orel_compat_l.
              unfold mat_star. rewrite (geom_sum_diag_one M' kleene_exp A).
              unfold Orel. rewrite addC. apply (@add_bound R _). }
            { apply star_path_compose. } }
        + (* z ≠ A *)
          destruct IH as [_ IH2].
          pose proof (IH2 z HnezA) as Hz_bound.
          (* M A z * pow M n z C ≤ M A z * (star' A C + star' z C) *)
          apply (orel_trans _ (M A z * (geom_sum M' kleene_exp A C + geom_sum M' kleene_exp z C))).
          { apply bounded_mul_orel_compat_r. apply Hz_bound. }
          (* distribute and use total order *)
          setoid_rewrite (mulDl (M A z) (geom_sum M' kleene_exp A C) (geom_sum M' kleene_exp z C)).
          destruct (H_total_order (M A z * geom_sum M' kleene_exp A C) 
                                  (M A z * geom_sum M' kleene_exp z C)) as [Hcase|Hcase].
          * setoid_rewrite Hcase.
            apply (orel_trans _ (1 * geom_sum M' kleene_exp A C)).
            { apply bounded_mul_orel_compat_l. unfold Orel; rewrite addC; apply (@add_bound R _). }
            rewrite mul1r. apply bounded_orel_refl.
          * setoid_rewrite Hcase.
            apply (orel_trans _ (M' A z * geom_sum M' kleene_exp z C)).
            { apply bounded_mul_orel_compat_l. apply Hrow. }
            apply (orel_trans _ (mat_star M' A z * mat_star M' z C)).
            { apply bounded_mul_orel_compat_l. apply link_le_mat_star. }
            { apply star_path_compose. }
      - (* part 2, inductive: pow M (S n) z C for z ≠ A *)
        intros z HzneA. simpl. unfold matrix_mul.
        apply sum_orel_bound. intro w.
        destruct (fin_eq_dec w A) as [HeqwA|HnewA].
        + (* w = A *)
          subst w. destruct IH as [IH1 _].
          apply (orel_trans _ (M z A * geom_sum M' kleene_exp A C)).
          { apply bounded_mul_orel_compat_r. apply IH1. }
          apply (orel_trans _ (1 * geom_sum M' kleene_exp A C)).
          { apply bounded_mul_orel_compat_l. unfold Orel; rewrite addC; apply (@add_bound R _). }
          rewrite mul1r.
          (* star' A C ≤ star' A C + star' z C *)
          apply bounded_plus_upper_left.
        + (* w ≠ A *)
          destruct IH as [_ IH2].
          pose proof (IH2 w HnewA) as Hw_bound.
          rewrite (Heq z w HzneA HnewA). (* M z w = M' z w *)
          apply (orel_trans _ (M' z w * (geom_sum M' kleene_exp A C + geom_sum M' kleene_exp w C))).
          { apply bounded_mul_orel_compat_r. apply Hw_bound. }
          setoid_rewrite (mulDl (M' z w) (geom_sum M' kleene_exp A C) (geom_sum M' kleene_exp w C)).
          destruct (H_total_order (M' z w * geom_sum M' kleene_exp A C) 
                                  (M' z w * geom_sum M' kleene_exp w C)) as [Hcase|Hcase].
          * setoid_rewrite Hcase.
            apply (orel_trans _ (1 * geom_sum M' kleene_exp A C)).
            { apply bounded_mul_orel_compat_l. unfold Orel; rewrite addC; apply (@add_bound R _). }
            rewrite mul1r. apply bounded_plus_upper_left.
          * setoid_rewrite Hcase.
            apply (orel_trans _ (mat_star M' z w * mat_star M' w C)).
            { apply bounded_mul_orel_compat_l. apply link_le_mat_star. }
            (* mat_star M' z w * mat_star M' w C ≤ mat_star M' z C ≤ star' A C + star' z C *)
            apply (orel_trans _ (mat_star M' z C)).
            { apply star_path_compose. }
            apply orel_plus_upper_right. }
    (* Now use the mutual IH to prove the main result *)
    apply mat_star_bound. intro n. apply Hmutual.
  Qed.


  (** * Monotonicity — reverse direction (strength INTO [A])
  *)
  Lemma monotonicity_rev {R : BoundedCommutativeSemiring.type}
    (M M' : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y) :
    (forall (X : Node), M' X A ≤ M X A) ->
    (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
    forall (C : Node), mat_star M' C A ≤ mat_star M C A.
  Proof.
    intros Hcol Heq C.
    (* put both sides in transposed form: mat_star N A C with N = M'ᵀ, Mᵀ *)
    setoid_rewrite (eq_sym (mat_star_transpose M' A C)).
    setoid_rewrite (eq_sym (mat_star_transpose M A C)).
    (* the transposed pair is exactly a "raise A" pair for [monotonicity]:
       its row-hypothesis is [Hcol] and its agreement-hypothesis is [Heq] *)
    apply (monotonicity (fun x y => M' y x) (fun x y => M y x) A H_total_order).
    - intro Y. exact (Hcol Y).
    - intros X Y HX HY. exact (eq_sym (Heq Y X HY HX)).
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
  Theorem winner_monotonicity {R : BoundedCommutativeSemiring.type}
    (M M' : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y) :
    (forall (Y : Node), M A Y ≤ M' A Y) ->
    (forall (X : Node), M' X A ≤ M X A) ->
    (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
    schulze_winner M A -> schulze_winner M' A.
  Proof.
    intros Hrow Hcol Heq Hwin b Hb_ne_A.
    pose proof (monotonicity M M' A H_total_order Hrow Heq b) as Hout.
    pose proof (monotonicity_rev M M' A H_total_order Hcol Heq b) as Hin.
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
  Theorem monotonicity_beats {R : BoundedCommutativeSemiring.type}
    (M M' : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hrow : forall Y : Node, M A Y ≤ M' A Y)
    (Hcol : forall X : Node, M' X A ≤ M X A)
    (Heq : forall X Y : Node, X ≠ A -> Y ≠ A -> M X Y = M' X Y) :
    forall b, schulze_beats M A b -> schulze_beats M' A b.
  Proof.
    intros b [Hle Hne].
    pose proof (monotonicity M M' A H_total_order Hrow Heq b) as Hout.
    pose proof (monotonicity_rev M M' A H_total_order Hcol Heq b) as Hin.
    split.
    - apply (orel_trans _ _ _ Hin). apply (orel_trans _ _ _ Hle). exact Hout.
    - intro Heq0.
      apply Hne. apply orel_antisym; [exact Hle |].
      apply (orel_trans _ _ _ Hout). rewrite Heq0 in Hin. exact Hin.
  Qed.

  (** Monotonicity (4.5.5): a defeat that [A] avoided before, it still avoids.
      The pointwise form of [winner_monotonicity]. *)
  Theorem monotonicity_unbeaten {R : BoundedCommutativeSemiring.type}
    (M M' : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hrow : forall Y : Node, M A Y ≤ M' A Y)
    (Hcol : forall X : Node, M' X A ≤ M X A)
    (Heq : forall X Y : Node, X ≠ A -> Y ≠ A -> M X Y = M' X Y) :
    forall b, ~ schulze_beats M b A -> ~ schulze_beats M' b A.
  Proof.
    intros b Hnb Hbeats.
    pose proof (monotonicity M M' A H_total_order Hrow Heq b) as Hout.
    pose proof (monotonicity_rev M M' A H_total_order Hcol Heq b) as Hin.
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
  Theorem winner_monotonicity_subset {R : BoundedCommutativeSemiring.type}
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
             (monotonicity_beats M M' A H_total_order Hrow Hcol Heq h
                (Hstrict h HhA))).
  Qed.



  (* =====================================================================  *)
  (*  Helper lemmas for the Pareto proofs                                   *)
  (* =====================================================================  *)

  (** If every element of a list is ≤ v, then the fold-right sum is ≤ v. *)
  Lemma fold_right_orel_bound {R : CommutativeMonoid.type} (l : list R) (v : R) :
    (forall x, In x l -> x ≤ v) ->
    fold_right (fun a b => a + b) (0 : R) l ≤ v.
  Proof.
    induction l as [|a l IH]; cbn; intros H.
    - unfold Orel. apply add0r.
    - apply add_orel_bound.
      + apply H. left; reflexivity.
      + apply IH. intros x Hx. apply H. right; exact Hx.
  Qed.

  
  (** In a BoundedSemiring, any path measure is ≤ 1. *)
  Lemma measure_of_path_le_one {R : BoundedSemiring.type}
    (p : list (Node * Node * R)) :
    measure_of_path p ≤ 1.
  Proof.
    induction p as [|[[x y] w] p IH]; cbn [measure_of_path].
    - apply bounded_orel_refl.
    - eapply orel_trans; [apply bounded_mul_lower_right | apply IH].
  Qed.

  (** If a non-empty list has source [a] and source [b], then [a = b]. *)
  Lemma source_inj {R : Semiring.type} (a b : Node) (l : list (Node * Node * R)) :
    l ≠ [] -> source a l = true -> source b l = true -> a = b.
  Proof.
    intros Hne Ha Hb.
    destruct l as [|[[u v] w] l']; [exfalso; apply Hne; reflexivity|].
    unfold source in Ha, Hb. simpl in Ha, Hb.
    destruct (fin_eq_dec a u) as [Heq_a|Hneq_a]; [|discriminate].
    destruct (fin_eq_dec b u) as [Heq_b|Hneq_b]; [|discriminate].
    subst. reflexivity.
  Qed.

  (** Inversion principle for a path of length [S k]: it is the edge
      [(x, z, M x z)] out of its source followed by a path of length [k]
      from [z].  Every induction over [all_paths_klength] below peels a
      path this way, so the [append_node_in_paths] bookkeeping is done
      once here rather than at each such proof. *)
  Lemma all_paths_klength_S_inv {R : Semiring.type}
    (M : @Matrix Node R) (k : nat) (x y : Node) (p : list (Node * Node * R)) :
    List.In p (all_paths_klength elements M (S k) x y) ->
    exists (z : Node) (q : list (Node * Node * R)),
      p = (x, z, M x z) :: q /\
      List.In q (all_paths_klength elements M k z y).
  Proof.
    intros Hin.
    cbn [all_paths_klength] in Hin.
    pose proof Hin as Hin_shape.
    apply (append_node_in_paths_In M x
      (List.flat_map (fun z => all_paths_klength elements M k z y) elements) p) in Hin.
    destruct Hin as [w [q [Hp Hq_lf]]].
    apply append_node_in_paths_shape in Hin_shape.
    destruct Hin_shape as (w' & q' & Hp' & Hsrc_x & Hsrc_w' & Hq_ne).
    subst p.
    inversion Hp' as [[Heq_hd Heq_tl]].
    inversion Heq_hd. subst w' q'. clear Hp'.
    apply in_flat_map in Hq_lf. destruct Hq_lf as [z [Hz_el Hq_in]].
    pose proof Hq_in as Hq_in_copy.
    apply non_empty_paths_in_kpath in Hq_in as (_ & Hsrc_z & _).
    assert (Hw_eq_z : w = z). { eapply source_inj; eassumption. }
    subst w.
    exists z, q. split; [reflexivity | exact Hq_in_copy].
  Qed.

  (** A bound holding of every path of length [n] from [x] to [y] is a bound
      on [pow M n x y], which is the join of exactly those path measures. *)
  Lemma pow_bound_of_paths {R : BoundedSemiring.type}
    (M : @Matrix Node R) (n : nat) (x y : Node) (c : R) :
    (forall p, List.In p (all_paths_klength elements M n x y) ->
       measure_of_path p ≤ c) ->
    pow M n x y ≤ c.
  Proof.
    intros Hall.
    rewrite (matrix_path_equation n M x y).
    unfold sum_all_rvalues, get_all_rvalues.
    apply fold_right_orel_bound.
    intros v Hv. apply in_map_iff in Hv. destruct Hv as [path [Hm Hin]].
    destruct path as [[s d] p]. cbn in Hm. subst v.
    unfold construct_all_paths in Hin.
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hin']].
    inversion Heq. subst s d q. clear Heq.
    exact (Hall p Hin').
  Qed.

  (** For any path from [x] to [A] (with [x ≠ A]), swapping the destination
      from [A] to [B] gives an upper bound via [mat_star M x B].
      Proved by induction on the path length [k].  Nothing about the link
      [B → A] is needed: in the one branch that reaches it (the path is the
      single edge [B → A]) the target is [mat_star M B B], which is the top. *)
  Lemma path_xA_measure_le_mat_star_xB {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) :
    forall (k : nat) (x : Node) (p : list (Node * Node * R)),
      x ≠ A ->
      List.In p (all_paths_klength elements M k x A) ->
      measure_of_path p ≤ mat_star M x B.
  Proof.
    induction k as [|k IH]; intros x p Hx_ne_A Hin.
    - (* k = 0: all_paths_klength 0 x A = [] since x ≠ A *)
      cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec x A) as [Heq|Heq]; [congruence|].
      inversion Hin.
    - (* k = S k: peel off the head edge (x, z, M x z) *)
      destruct (all_paths_klength_S_inv M k x A p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (fin_eq_dec z A) as [Heq_zA|Hneq_zA].
      + (* z = A: q ∈ all_paths_klength k A A *)
        subst z.
        assert (Hq_le_one : measure_of_path q ≤ 1).
        { apply measure_of_path_le_one. }
        apply (orel_trans _ _ _ (bounded_mul_orel_compat_r _ _ _ Hq_le_one)).
        rewrite mulr1.
        destruct (fin_eq_dec x B) as [Heq_xB|Hneq_xB].
        * (* x = B: the target [mat_star M B B] is the top *)
          subst x. unfold mat_star. rewrite geom_sum_diag_one.
          unfold Orel. rewrite addC. apply (add_bound (s := R) (M B A)).
        * apply (orel_trans _ _ _ (Hcol x Hx_ne_A Hneq_xB)).
          apply link_le_mat_star.
      + (* z ≠ A: chain the head link with the tail through [z] *)
        assert (Hq_bound : measure_of_path q ≤ mat_star M z B).
        { apply IH; [exact Hneq_zA | exact Hq]. }
        apply (orel_trans _ _ _ (bounded_mul_orel_compat_r _ _ _ Hq_bound)).
        apply (orel_trans _ _ _
          (bounded_mul_orel_compat_l _ _ _ (link_le_mat_star M x z))).
        apply star_path_compose.
  Qed.

  (** [pow M n B A ≤ mat_star M A B] — the core lemma.
      Uses [path_xA_measure_le_mat_star_xB] for the inductive step
      when the first edge goes to a third party, and [star_path_compose]
      to chain through the intermediate node. *)
  Lemma pow_BA_le_mat_star_AB {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hneq : A ≠ B) (Hle : M B A ≤ M A B)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (n : nat) : pow M n B A ≤ mat_star M A B.
  Proof.
    apply pow_bound_of_paths.
    induction n as [|k IH]; intros p Hin.
    - (* n = 0: all_paths_klength 0 B A = [] since B ≠ A *)
      cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec B A) as [Heq_BA|_]; [congruence | inversion Hin].
    - (* n = S k: peel off the head edge (B, z, M B z) *)
      destruct (all_paths_klength_S_inv M k B A p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (fin_eq_dec z A) as [Heq_zA|Hneq_zA].
      + (* z = A: the head edge is the direct link (B, A); bound the whole
           path by it, then by [M A B] and hence by the closure *)
        subst z.
        eapply orel_trans; [apply bounded_mul_lower_left |].
        eapply orel_trans; [exact Hle | apply link_le_mat_star].
      + destruct (fin_eq_dec z B) as [Heq_zB|Hneq_zB].
        * (* z = B: a self-loop of weight 1, the tail is still a path B ⇝ A *)
          subst z. rewrite (Hdiag_one B B eq_refl), mul1r.
          apply (IH _ Hq).
        * (* z ≠ A, B: bound the tail by [mat_star M z B] and chain *)
          assert (Hq_bound : measure_of_path q ≤ mat_star M z B).
          { exact (path_xA_measure_le_mat_star_xB M A B Hcol
              k z q Hneq_zA Hq). }
          apply (orel_trans _ _ _
            (bounded_mul_orel_compat_l _ _ _ (Hrow z Hneq_zA Hneq_zB))).
          apply (orel_trans _ _ _ (bounded_mul_orel_compat_r _ _ _ Hq_bound)).
          apply (orel_trans _ _ _
            (bounded_mul_orel_compat_l _ _ _ (link_le_mat_star M A z))).
          apply star_path_compose.
  Qed.


  (* ------------------------------------------------------------------ *)
  (*  Pareto criterion (Section 4.3)                                     *)
  (*                                                                      *)
  (*  Two versions appear in the literature:                              *)
  (*    1. If a ≻ᵥ b for all v ∈ V, then a ≻ b.                          *)
  (*    2. If a ≿ᵥ b for all v ∈ V and a ≻ᵥ b for some v ∈ V,           *)
  (*       then a ≻ b.                                                    *)
  (*                                                                      *)
  (*  The Schulze method satisfies both.  We formalise the second         *)
  (*  (stronger) version as [pareto_stronger] below.  The first           *)
  (*  (weaker) version is [pareto].                                       *)
  (* ------------------------------------------------------------------ *)


  


  (* ------------------------------------------------------------------ *)
  (*  Version 1 — pareto_weaker (weaker form):  a ≽ᵥ b ∀v  →  a ≽ b     *)
  (*                                                                      *)
  (*  If A dominates B head to head and in every third-party comparison,  *)
  (*  then A is at least as strong as B in the Schulze ranking:           *)
  (*  mat_star M B A ≤ mat_star M A B.  This is Schulze (4.3.2.10),       *)
  (*  which gives (4.3.2.2) [ba ∉ O].                                     *)
  (*                                                                      *)
  (*  The stronger form (strict <) is [pareto_stronger] below; it needs   *)
  (*  two extra hypotheses, see the comment there.                        *)
  (*                                                                      *)
  (*  Hypotheses:                                                          *)
  (*    A ≠ B            — distinct candidates                            *)
  (*    M B A ≤ M A B    — A is at least as strong as B head to head.     *)
  (*                        Schulze's (4.3.2.1) — no voter strictly       *)
  (*                        prefers B to A — gives the stronger           *)
  (*                        M B A = 0, which implies this; the proof      *)
  (*                        only needs the inequality, and it cannot be   *)
  (*                        dropped altogether: the two hypotheses below  *)
  (*                        both exclude X ∈ {A, B}, so nothing else      *)
  (*                        constrains the link B → A.                    *)
  (*    M B X ≤ M A X    — ballot transitivity: voters who have B≻X       *)
  (*                        also have A≻X (since A≽B)                     *)
  (*    M X A ≤ M X B    — ballot transitivity: voters who have X≻A       *)
  (*                        also have X≻B (since A≽B)                     *)
  (*    M i i = 1         — diagonal is the multiplicative identity       *)
  (* ------------------------------------------------------------------   *)


  Theorem pareto_weaker {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node) :
    A ≠ B -> M B A ≤ M A B ->
    (forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X) ->
    (forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) ->
    (forall i j, i = j -> M i j = 1) ->
    (mat_star M B A ≤ mat_star M A B).
  Proof.
    intros Hneq Hle Hrow Hcol Hdiag_one.
    apply mat_star_bound. intro n.
    exact (pow_BA_le_mat_star_AB M A B Hneq Hle Hrow Hcol Hdiag_one n).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The remaining Pareto #2 conclusions (4.3.2.3 / .4 / .5)             *)
  (*                                                                      *)
  (*  All three rest on the paper's two path-rewriting steps: (4.3.2.11)  *)
  (*  swaps the SOURCE of a path out of [B] to [A], and (4.3.2.12) swaps  *)
  (*  its TARGET from [A] to [B].  Schulze performs both by editing the   *)
  (*  strongest path; here they are inductions on the closure.            *)
  (* ------------------------------------------------------------------ *)

  (** (4.3.2.11): [P_D[a,f] ≽ P_D[b,f]].  Every walk out of [B] is dominated
      by one out of [A]: its first edge improves by [Hrow], and once the walk
      has left [{A, B}] the rest is bounded by the closure. *)
  Lemma pareto_star_source_swap {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hdiag : forall u v : Node, u = v -> M u v = 1)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (F : Node) (HFB : F ≠ B) :
    mat_star M B F ≤ mat_star M A F.
  Proof.
    apply mat_star_bound. intro n.
    induction n as [|k IH].
    - cbn [pow]. unfold I.
      destruct (fin_eq_dec B F) as [Heq|_];
        [exfalso; apply HFB; symmetry; exact Heq | apply zero_is_bottom].
    - simpl. unfold matrix_mul.
      apply sum_orel_bound. intro z.
      destruct (fin_eq_dec z A) as [HzA|HzA].
      + (* the walk reaches A: the tail is a walk A ⇝ F *)
        subst z. eapply orel_trans; [apply bounded_mul_lower_right |].
        apply pow_le_mat_star_any; exact Hdiag.
      + destruct (fin_eq_dec z B) as [HzB|HzB].
        * (* still at B: recurse *)
          subst z. eapply orel_trans; [apply bounded_mul_lower_right |]. exact IH.
        * (* left {A,B}: improve the head edge by Hrow, then chain *)
          eapply orel_trans;
            [apply (bounded_mul_orel_compat_l _ _ _ (Hrow z HzA HzB)) |].
          eapply orel_trans;
            [apply (bounded_mul_orel_compat_r _ _ _
                      (pow_le_mat_star_any M Hdiag k z F)) |].
          eapply orel_trans;
            [apply (bounded_mul_orel_compat_l _ _ _ (link_le_mat_star M A z)) |].
          apply star_path_compose.
  Qed.

  (** (4.3.2.12): [P_D[f,b] ≽ P_D[f,a]].  This is exactly what
      [path_xA_measure_le_mat_star_xB] already says, lifted from paths to the
      closure. *)
  Lemma pareto_star_target_swap {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B)
    (F : Node) (HFA : F ≠ A) :
    mat_star M F A ≤ mat_star M F B.
  Proof.
    apply mat_star_bound. intro n.
    apply pow_bound_of_paths. intros p Hp.
    exact (path_xA_measure_le_mat_star_xB M A B Hcol n F p HFA Hp).
  Qed.

  (** Pareto (4.3.2.3): if [B] beats [F] then so does [A]. *)
  Theorem pareto_weaker_beats_transfer {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hdiag : forall u v : Node, u = v -> M u v = 1)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) :
    forall F, F ≠ A -> F ≠ B -> schulze_beats M B F -> schulze_beats M A F.
  Proof.
    intros F HFA HFB HBF.
    unfold schulze_beats, beats in *.
    apply (orel_lt_le_trans (mat_star M F A) (mat_star M B F) (mat_star M A F)).
    - apply (orel_lt_trans (mat_star M F A) (mat_star M F B) (mat_star M B F)).
      + exact (pareto_star_target_swap M A B Hcol F HFA).
      + exact HBF.
    - exact (pareto_star_source_swap M A B Hdiag Hrow F HFB).
  Qed.

  (** Pareto (4.3.2.4): if [F] beats [A] then it also beats [B]. *)
  Theorem pareto_weaker_loses_transfer {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hdiag : forall u v : Node, u = v -> M u v = 1)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) :
    forall F, F ≠ A -> F ≠ B -> schulze_beats M F A -> schulze_beats M F B.
  Proof.
    intros F HFA HFB HF_beats_A.
    unfold schulze_beats, beats in *.
    apply (orel_lt_le_trans (mat_star M B F) (mat_star M F A) (mat_star M F B)).
    - apply (orel_lt_trans (mat_star M B F) (mat_star M A F) (mat_star M F A)).
      + exact (pareto_star_source_swap M A B Hdiag Hrow F HFB).
      + exact HF_beats_A.
    - exact (pareto_star_target_swap M A B Hcol F HFA).
  Qed.

  (** Pareto (4.3.2.5): if [B] is a winner then so is [A].  The [f = B] case
      is (4.3.2.2), i.e. [pareto_weaker]; every other [f] goes through
      (4.3.2.4). *)
  Theorem pareto_weaker_winner_transfer {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hneq : A ≠ B) (Hle : M B A ≤ M A B)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B)
    (Hdiag : forall i j : Node, i = j -> M i j = 1) :
    schulze_winner M B -> schulze_winner M A.
  Proof.
    intros HB f Hf_ne_A Hbeats.
    destruct (fin_eq_dec f B) as [HfB | HfB].
    - subst f. destruct Hbeats as [Hle' Hne'].
      apply Hne'. apply orel_antisym; [exact Hle' |].
      exact (pareto_weaker M A B Hneq Hle Hrow Hcol Hdiag).
    - exact (HB f HfB
               (pareto_weaker_loses_transfer M A B Hdiag Hrow Hcol
                  f Hf_ne_A HfB Hbeats)).
  Qed.


  (* ------------------------------------------------------------------ *)
  (*  Version 2 — pareto_stronger (strict form):  a ≻ᵥ b ∀v  →  a ≻ b   *)
  (*                                                                      *)
  (*  The semiring alone does not decide this: with [M A B] the strongest *)
  (*  link, a route B → C → A built from equally strong links can match   *)
  (*  it, and in the max-min semiring of the Schulze example the two      *)
  (*  closures then coincide.  Schulze rules such a route out in §4.3.1   *)
  (*  by an argument outside the algebra: the links of maximal strength   *)
  (*  are exactly the unanimous ones, and unanimous preference cannot     *)
  (*  cycle because individual ballots are transitive.  That is the       *)
  (*  content of [Htop_trans] below — maximal links compose — and it is   *)
  (*  a constraint on the ballot matrix [M], not on the semiring, so the  *)
  (*  max-min instance is still covered.  [Htotal] says the natural       *)
  (*  order is total, as in [condorcet_implies_strict_winner].            *)
  (* ------------------------------------------------------------------ *)

  (** Schulze (2.2.4): a link stronger than the return closure is respected by
      the relation O.  As in the paper this is immediate from (2.2.1) and
      (2.2.3) — the link [a → b] is itself a path, so [M a b ≤ mat_star M a b],
      and the strict comparison carries across. *)
  Lemma link_beats {R : BoundedSemiring.type} (M : @Matrix Node R) (a b : Node) :
    mat_star M b a < M a b -> schulze_beats M a b.
  Proof.
    intro H. exact (orel_lt_le_trans _ _ _ H (link_le_mat_star M a b)).
  Qed.

  (** When the order is total, a strict upper bound survives addition. *)
  Lemma add_lt_bound {R : CommutativeMonoid.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (a b v : R) :
    a < v -> b < v -> a + b < v.
  Proof.
    intros Ha Hb.
    destruct (Htotal a b) as [Hcase|Hcase]; rewrite Hcase; assumption.
  Qed.

  (** …and hence a finite sum of terms each strictly below [v] stays below [v]. *)
  Lemma fold_right_lt_bound {R : CommutativeMonoid.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (l : list R) (v : R) :
    0 < v ->
    (forall x, In x l -> x < v) ->
    fold_right (fun a b => a + b) (0 : R) l < v.
  Proof.
    intros H0 Hall. induction l as [|a l IH]; cbn [fold_right].
    - exact H0.
    - apply (add_lt_bound Htotal).
      + apply Hall. left; reflexivity.
      + apply IH. intros x Hx. apply Hall. right; exact Hx.
  Qed.

  (** Strict counterpart of [pow_bound_of_paths].  The empty join is [0], so
      the bound must be strictly above [0] for the degenerate case. *)
  Lemma pow_lt_bound_of_paths {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (M : @Matrix Node R) (n : nat) (x y : Node) (c : R) :
    0 < c ->
    (forall p, List.In p (all_paths_klength elements M n x y) ->
       measure_of_path p < c) ->
    pow M n x y < c.
  Proof.
    intros Hpos Hall.
    rewrite (matrix_path_equation n M x y).
    unfold sum_all_rvalues, get_all_rvalues.
    apply (fold_right_lt_bound Htotal); [exact Hpos |].
    intros v Hv. apply in_map_iff in Hv. destruct Hv as [path [Hm Hin]].
    destruct path as [[s d] p]. cbn in Hm. subst v.
    unfold construct_all_paths in Hin.
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hin']].
    inversion Heq. subst s d q. clear Heq.
    exact (Hall p Hin').
  Qed.

  (** Strict counterpart of [mat_star_bound]. *)
  Lemma mat_star_lt_bound {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (M : @Matrix Node R) (x y : Node) (c : R) :
    (forall n, pow M n x y < c) -> mat_star M x y < c.
  Proof.
    intros Hpow. unfold mat_star.
    assert (Hgen : forall k, geom_sum M k x y < c).
    { induction k as [|k IH]; cbn [geom_sum].
      - exact (Hpow 0%nat).
      - unfold matrix_add.
        apply (add_lt_bound Htotal); [exact IH | exact (Hpow (S k))]. }
    apply Hgen.
  Qed.

  (** Key lemma.  Every path into [A] starting from some [x ≠ A] has measure
      at most the strongest link [M A B], and it attains [M A B] only when the
      direct link [x → A] is itself of maximal strength.

      This is the algebraic form of Schulze's observation that a route made
      entirely of unanimous links is itself a unanimous link: at each step the
      head edge either loses strength (so the whole product does) or is
      maximal, and [Htop_trans] composes it with the maximal tail. *)
  Lemma path_to_A_measure_top {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htop_trans : forall X Y Z, M X Y = M A B ->
      M Y Z = M A B -> M X Z = M A B)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1) :
    forall (k : nat) (x : Node) (p : list (Node * Node * R)),
      x ≠ A ->
      List.In p (all_paths_klength elements M k x A) ->
      measure_of_path p ≤ M A B
      /\ (measure_of_path p = M A B -> M x A = M A B).
  Proof.
    induction k as [|k IH]; intros x p Hx_ne_A Hin.
    - (* k = 0: no path, since x ≠ A *)
      cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec x A) as [Heq|Heq]; [congruence|].
      inversion Hin.
    - (* k = S k: peel off the head edge (x, z, M x z) *)
      destruct (all_paths_klength_S_inv M k x A p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (fin_eq_dec z A) as [Heq_zA|Hneq_zA].
      + (* head edge already lands on A *)
        subst z.
        assert (HxA_le : M x A ≤ M A B) by (apply Hmax; exact Hx_ne_A).
        assert (Hlow : M x A * measure_of_path q ≤ M x A)
          by apply bounded_mul_lower_left.
        split.
        * exact (orel_trans _ _ _ Hlow HxA_le).
        * intro Heq.
          apply orel_antisym; [exact HxA_le | rewrite <- Heq; exact Hlow].
      + (* head edge goes to a third node z, so the tail is a path z ⇝ A *)
        destruct (IH z q Hneq_zA Hq) as [Hq_le Hq_top].
        destruct (fin_eq_dec x z) as [Hxz|Hxz].
        * (* self-loop: weight 1, the measure is unchanged *)
          subst z. rewrite (Hdiag_one x x eq_refl), mul1r.
          split; [exact Hq_le | exact Hq_top].
        * assert (Hxz_le : M x z ≤ M A B) by (apply Hmax; exact Hxz).
          split.
          { exact (orel_trans _ _ _ (bounded_mul_lower_left _ _) Hxz_le). }
          { intro Heq.
            (* the product attains the top, so both factors do *)
            assert (Hxz_top : M x z = M A B).
            { apply orel_antisym;
              [exact Hxz_le | rewrite <- Heq; apply bounded_mul_lower_left]. }
            assert (Hq_eq : measure_of_path q = M A B).
            { apply orel_antisym;
              [exact Hq_le | rewrite <- Heq; apply bounded_mul_lower_right]. }
            exact (Htop_trans x z A Hxz_top (Hq_top Hq_eq)). }
  Qed.

  (** No route from [B] back to [A] can match the link [A → B], as long as the
      link [B → A] is not itself maximal.  Unanimity gives that for free:
      [M B A = 0 ≠ M A B]. *)
  Lemma path_BA_measure_lt {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htop_trans : forall X Y Z, M X Y = M A B -> M Y Z = M A B -> M X Z = M A B)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (Hneq : A ≠ B) (Hne_top : M B A ≠ M A B) :
    forall (k : nat) (p : list (Node * Node * R)),
      List.In p (all_paths_klength elements M k B A) ->
      measure_of_path p < M A B.
  Proof.
    intros k p Hin.
    assert (HB_ne_A : B ≠ A).
    { intro Habs. apply Hneq. symmetry. exact Habs. }
    destruct (path_to_A_measure_top M A B Htop_trans Hmax Hdiag_one
      k B p HB_ne_A Hin) as [Hle Htop].
    split; [exact Hle |].
    intro Heq. exact (Hne_top (Htop Heq)).
  Qed.

  (** Each power of [M] is therefore strictly below the link [A → B] at [B, A]. *)
  Lemma pow_BA_lt_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B -> M Y Z = M A B -> M X Z = M A B)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (Hneq : A ≠ B) (Hne_top : M B A ≠ M A B) (Hpos : 0 < M A B)
    (n : nat) : pow M n B A < M A B.
  Proof.
    apply (pow_lt_bound_of_paths Htotal); [exact Hpos |].
    intros p Hin.
    exact (path_BA_measure_lt M A B Htop_trans Hmax Hdiag_one
      Hneq Hne_top n p Hin).
  Qed.

  (** …and so is the whole closure. *)
  Lemma mat_star_BA_lt_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B -> 
      M Y Z = M A B -> M X Z = M A B)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (Hneq : A ≠ B) (Hne_top : M B A ≠ M A B) (Hpos : 0 < M A B) :
    mat_star M B A < M A B.
  Proof.
    apply (mat_star_lt_bound Htotal). intro n.
    exact (pow_BA_lt_link M A B Htotal Htop_trans Hmax Hdiag_one
      Hneq Hne_top Hpos n).
  Qed.

  Theorem pareto_stronger {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B -> 
      M Y Z = M A B -> M X Z = M A B) :
    A ≠ B -> M B A = 0 -> 0 < M A B ->
    (forall X Y, X ≠ Y -> M X Y ≤ M A B) ->
    (forall i j, i = j -> M i j = 1) ->
    mat_star M B A < mat_star M A B.
  Proof.
    intros Hneq Hzero Hpos Hmax Hdiag_one.
    (* unanimity makes the reverse link [B → A] non-maximal *)
    assert (Hne_top : M B A ≠ M A B).
    { rewrite Hzero. exact (proj2 Hpos). }
    (* the reverse closure is strictly below the link, so (2.2.4) applies *)
    apply link_beats.
    exact (mat_star_BA_lt_link M A B Htotal Htop_trans Hmax Hdiag_one
      Hneq Hne_top Hpos).
  Qed.

  (** Pareto (4.3.1.3): the unanimously dominated alternative is not a winner. *)
  Corollary pareto_stronger_loser {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B ->
      M Y Z = M A B -> M X Z = M A B) :
    A ≠ B -> M B A = 0 -> 0 < M A B ->
    (forall X Y, X ≠ Y -> M X Y ≤ M A B) ->
    (forall i j, i = j -> M i j = 1) ->
    ~ schulze_winner M B.
  Proof.
    intros Hneq Hzero Hpos Hmax Hdiag_one Hwin.
    exact (Hwin A Hneq (pareto_stronger M A B Htotal Htop_trans
      Hneq Hzero Hpos Hmax Hdiag_one)).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The converse                                                        *)
  (*                                                                      *)
  (*  Unanimity itself is not recoverable from the conclusion: the        *)
  (*  Schulze order ranks candidates strictly in profiles that contain no *)
  (*  unanimous pair at all (the paper's own Example 1, formalised in     *)
  (*  examples/Schulze.v, has d ≻ a with every pairwise count non-zero).  *)
  (*  What does reverse is the property the proof actually turns on:      *)
  (*  under the standing hypotheses, [A] beats [B] in the closure exactly *)
  (*  when the reverse link [B → A] is not itself of maximal strength.    *)
  (*  [pareto_stronger] is the instance [M B A = 0].                      *)
  (* ------------------------------------------------------------------ *)

  (** A path between two distinct nodes is bounded by the strongest link: it
      must contain a non-loop edge, and a product lies below each factor. *)
  Lemma path_measure_le_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1) :
    forall (k : nat) (x y : Node) (p : list (Node * Node * R)),
      x ≠ y ->
      List.In p (all_paths_klength elements M k x y) ->
      measure_of_path p ≤ M A B.
  Proof.
    induction k as [|k IH]; intros x y p Hxy Hin.
    - cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec x y) as [Heq|_]; [congruence | inversion Hin].
    - destruct (all_paths_klength_S_inv M k x y p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (fin_eq_dec x z) as [Hxz|Hxz].
      + (* self-loop of weight 1: the tail is still a path from x to y *)
        subst z. rewrite (Hdiag_one x x eq_refl), mul1r.
        exact (IH x y q Hxy Hq).
      + exact (orel_trans _ _ _ (bounded_mul_lower_left _ _) (Hmax x z Hxz)).
  Qed.

  Lemma pow_xy_le_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (n : nat) (x y : Node) : x ≠ y -> pow M n x y ≤ M A B.
  Proof.
    intros Hxy.
    apply pow_bound_of_paths.
    intros p Hin.
    exact (path_measure_le_link M A B Hmax Hdiag_one n x y p Hxy Hin).
  Qed.

  Lemma mat_star_le_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (x y : Node) : x ≠ y -> mat_star M x y ≤ M A B.
  Proof.
    intros Hxy. apply mat_star_bound. intro n.
    exact (pow_xy_le_link M A B Hmax Hdiag_one n x y Hxy).
  Qed.

  (** The strongest link is its own closure — no detour improves on it. *)
  Lemma mat_star_link_eq {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (Hneq : A ≠ B) : mat_star M A B = M A B.
  Proof.
    apply orel_antisym.
    - exact (mat_star_le_link M A B Hmax Hdiag_one A B Hneq).
    - apply link_le_mat_star.
  Qed.

  (** Both directions.  [pareto_stronger] is the special case [M B A = 0]. *)
  Theorem pareto_stronger_iff {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Htop_trans : forall X Y Z, M X Y = M A B ->
      M Y Z = M A B -> M X Z = M A B) :
    A ≠ B -> 0 < M A B ->
    (forall X Y, X ≠ Y -> M X Y ≤ M A B) ->
    (forall i j, i = j -> M i j = 1) ->
    (mat_star M B A < mat_star M A B <-> M B A ≠ M A B).
  Proof.
    intros Hneq Hpos Hmax Hdiag_one.
    assert (Hstar_AB : mat_star M A B = M A B).
    { exact (mat_star_link_eq M A B Hmax Hdiag_one Hneq). }
    split.
    - (* a maximal reverse link would already tie the two closures *)
      intros [Hle Hne] Habs.
      apply Hne, orel_antisym; [exact Hle |].
      rewrite Hstar_AB, <- Habs.
      apply link_le_mat_star.
    - intros Hne_top.
      eapply orel_lt_le_trans.
      + exact (mat_star_BA_lt_link M A B Htotal Htop_trans Hmax Hdiag_one
          Hneq Hne_top Hpos).
      + rewrite Hstar_AB. apply bounded_orel_refl.
  Qed.








  (** Two-term join stays below a bound if both summands do (needs totality:
      without it, two incomparable elements can join to something exceeding
      both, as happens in a non-chain lattice). *)
  Lemma orel_lt_add_lt {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (a b c : R) :
    a < c -> b < c -> (a + b) < c.
  Proof.
    intros [Hale Hane] [Hble Hbne].
    destruct (Htotal a b) as [Hcase|Hcase]; rewrite Hcase; split; assumption.
  Qed.

  (** Finite sums stay strictly below a bound if every summand does
      (the bound [c] is arbitrary; this only needs totality, not
      boundedness at [c]). *)
  Lemma sum_lt_bound_if_all_lt {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (f : Node -> R) (c : R) :
    (forall z, f z < c) -> sum f < c.
  Proof.
    intros Hlt. unfold sum.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    assert (Hgen : forall (l : list Node), l <> [] ->
      fold_right (fun x acc => f x + acc) 0 l < c).
    { induction l as [|x l' IH]; intros Hne.
      - contradiction.
      - destruct l' as [|y l''].
        + cbn. rewrite addr0. apply Hlt.
        + apply orel_lt_add_lt; [exact Htotal | apply Hlt | apply IH; discriminate]. }
    apply Hgen.
    destruct (elements (s := Node)) as [|z l]; [simpl in Hlen; lia | discriminate].
  Qed.


  (** * [condorcet_implies_strict_winner], with [H_pair_sum_one] replaced by
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



  
  (** [smith_criterion], with the global [H_pair_sum_one] normalization
      replaced by a single shared threshold [c0] separating the two sides
      of the cut, rather than forcing every B1-to-B2 edge to equal the
      literal top [1]. This subsumes the theorem's own per-pair cut
      hypothesis (["forall a b, In a B1 -> In b B2 -> M b a < M a b"]),
      which follows immediately by chaining [M b a < c0 <= M a b] — so it
      is dropped as a separate premise here.
  *)
  (** No walk from [B2] into [B1] can reach the threshold: every such walk
      must eventually cross the boundary, and every crossing link is below
      [c].  This is the engine of both the Smith criterion and Smith-IIA. *)
  Lemma pow_from_B2_lt {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c) :
    forall n y, In y B2 -> forall x, In x B1 -> pow M n y x < c.
  Proof.
    induction n as [|n IH]; intros y Hy x Hx.
    - cbn [pow]. unfold I.
      destruct (fin_eq_dec y x) as [Heq|Hneq].
      + subst x. exfalso. apply (proj1 (H_partition y) Hx). exact Hy.
      + exact H0.
    - simpl. unfold matrix_mul.
      apply sum_lt_bound_if_all_lt; [exact H_total_order |].
      intro z.
      destruct (in_dec fin_eq_dec z B1) as [HzB1|HzB1'].
      + apply (orel_lt_trans (M y z * pow M n z x) (M y z) c).
        * apply bounded_mul_lower_left.
        * apply H_lt; assumption.
      + assert (HzB2 : In z B2).
        { destruct (in_dec fin_eq_dec z B2) as [Hz|Hz]; [exact Hz|].
          exfalso. apply HzB1'. apply (proj2 (H_partition z)). exact Hz. }
        apply (orel_lt_trans (M y z * pow M n z x) (pow M n z x) c).
        * apply bounded_mul_lower_right.
        * apply IH; assumption.
  Qed.

  (** Schulze (4.7.3): every member of [B1] beats every member of [B2].  The
      whole strength of the criterion lives here — no walk from [B2] into [B1]
      can rise to the threshold [c], while the direct link out of [B1] already
      clears it.  (4.7.4) below is then just "so no winner sits in [B2]". *)
  Theorem smith_beats {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y) :
    forall (B1 B2 : list Node),
      (forall (x : Node), In x B1 <-> ~ In x B2) ->
      (exists c : R,
        (forall a b, In a B1 -> In b B2 -> M b a < c) ∧
        (forall a b, In a B1 -> In b B2 -> c ≤ M a b)) ->
      forall a b, In a B1 -> In b B2 -> schulze_beats M a b.
  Proof.
    intros B1 B2 H_partition (c & H_lt & H_ge) a b Ha Hb.
    assert (H0_lt_c : (0 : R) < c).
    { apply (orel_lt_trans 0 (M b a) c).
      - apply zero_is_bottom.
      - apply H_lt; assumption. }
    pose proof (pow_from_B2_lt M H_total_order B1 B2 c H_partition H_lt
                  H0_lt_c) as H_pow_lt.
    unfold schulze_beats, beats.
    apply (orel_lt_le_trans (mat_star M b a) c (mat_star M a b)).
    - apply (mat_star_lt_bound H_total_order). intro n.
      apply H_pow_lt; assumption.
    - apply (orel_trans c (M a b) (mat_star M a b)).
      + apply H_ge; assumption.
      + apply link_le_mat_star.
  Qed.

  (** Schulze (4.7.4): [S ⊆ B1].  Immediate from (4.7.3) — a winner in [B2]
      would be beaten by any member of [B1], and [B1] is non-empty. *)
  Theorem smith_criterion_weaker {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y) :
    forall (B1 B2 : list Node), B1 <> [] ->
      (forall (x : Node), In x B1 <-> ~ In x B2) ->
      (exists c : R,
        (forall a b, In a B1 -> In b B2 -> M b a < c) ∧
        (forall a b, In a B1 -> In b B2 -> c ≤ M a b)) ->
      forall (w : Node), schulze_winner M w -> In w B1.
  Proof.
    intros B1 B2 H_B1_nonempty H_partition Hc w H_winner.
    destruct (in_dec fin_eq_dec w B1) as [Hin|Hnotin_B1]; [exact Hin|].
    destruct (in_dec fin_eq_dec w B2) as [Hw_B2|Hnotin_B2];
      [| apply H_partition in Hnotin_B2; contradiction].
    exfalso.
    destruct B1 as [|a0 B1']; [congruence|].
    assert (Ha0 : In a0 (a0 :: B1')) by (left; reflexivity).
    assert (Hne : a0 <> w).
    { intro Heq. subst w. apply (proj1 (H_partition a0) Ha0). exact Hw_B2. }
    exact (H_winner a0 Hne
             (smith_beats M H_total_order (a0 :: B1') B2 H_partition Hc
                a0 w Ha0 Hw_B2)).
  Qed.

  (* ==================================================================== *)
  (*  Smith-IIA (4.7.5a) — isolation rather than removal                   *)
  (*                                                                       *)
  (*  The paper compares the method before and after REMOVING a weak       *)
  (*  alternative [d ∈ B2].  Removal is not expressible here: [sum] folds  *)
  (*  over [elements], the whole [FinType] enumeration, so [matrix_mul],   *)
  (*  [pow], [geom_sum], [mat_star] and [kleene_exp] are all tied to one   *)
  (*  fixed alternative set, and there is no closure over a subset to      *)
  (*  write [P_new] with.                                                  *)
  (*                                                                       *)
  (*  What is expressible is ISOLATION: cut every link into and out of     *)
  (*  [d], leaving the node in place.  [smith_iia_isolate] then says the   *)
  (*  relation O restricted to [B1] is unchanged — the content of          *)
  (*  (4.7.5)(a).  Two caveats, both real:                                 *)
  (*                                                                       *)
  (*  - It needs [Hsep], which the paper gets from (2.1.2): between two    *)
  (*    distinct alternatives the stronger direction is at least a tie,    *)
  (*    hence clears the threshold.  The Smith hypotheses alone relate     *)
  (*    only B1-to-B2 pairs, so this has to be assumed.                    *)
  (*                                                                       *)
  (*  - (4.7.5)(b) [S_old = S_new] does NOT transfer to isolation.  An     *)
  (*    isolated [d] has every link at [0], so nobody beats it and it      *)
  (*    becomes a spurious winner — an artefact of leaving the node in     *)
  (*    place.  Only removal gets (b) right.                               *)
  (* ==================================================================== *)

  (** With a selective join, a geometric sum is equal to one of its terms —
      the closure is attained at some particular walk length. *)
  Lemma geom_sum_selective {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (M : @Matrix Node R) (n : nat) (a b : Node) :
    exists k, (k <= n)%nat /\ geom_sum M n a b = pow M k a b.
  Proof.
    induction n as [|m IH].
    - exists 0%nat. split; [lia | reflexivity].
    - cbn [geom_sum]. unfold matrix_add.
      destruct (Htotal (geom_sum M m a b) (pow M (S m) a b)) as [Hc | Hc].
      + destruct IH as [k [Hk Heq]]. exists k. split; [lia |].
        setoid_rewrite Hc. exact Heq.
      + exists (S m). split; [lia |]. setoid_rewrite Hc. reflexivity.
  Qed.

  (** Isolating [d]: cut every link into and out of it. *)
  Definition isolate {R : Semiring.type} (M : @Matrix Node R) (d : Node)
    : @Matrix Node R :=
    fun x y => if fin_eq_dec x d then 0
               else if fin_eq_dec y d then 0 else M x y.

  Lemma isolate_off {R : Semiring.type} (M : @Matrix Node R) (d x y : Node) :
    x <> d -> y <> d -> isolate M d x y = M x y.
  Proof.
    intros Hx Hy. unfold isolate.
    destruct (fin_eq_dec x d); [contradiction |].
    destruct (fin_eq_dec y d); [contradiction | reflexivity].
  Qed.

  Lemma isolate_le {R : BoundedSemiring.type} (M : @Matrix Node R) (d x y : Node) :
    isolate M d x y ≤ M x y.
  Proof.
    unfold isolate.
    destruct (fin_eq_dec x d); [apply zero_is_bottom |].
    destruct (fin_eq_dec y d); [apply zero_is_bottom | apply bounded_orel_refl].
  Qed.

  (** Isolation only removes walks, so it can only lower the closure. *)
  Lemma mat_star_isolate_le {R : BoundedSemiring.type}
    (M : @Matrix Node R) (d x y : Node) :
    mat_star (isolate M d) x y ≤ mat_star M x y.
  Proof.
    unfold mat_star. apply geom_sum_monotone. intros i j. apply isolate_le.
  Qed.

  (** Every walk into [B1] is either matched by an isolated walk, or is too
      weak to matter — because reaching [d ∈ B2] commits it to a crossing
      back into [B1], and every crossing link is below [c]. *)
  Lemma pow_isolate_dichotomy {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R) (d : Node)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c) (Hd : In d B2) (f : Node) (Hf : In f B1) :
    forall n x, x <> d ->
      pow M n x f ≤ mat_star (isolate M d) x f \/ pow M n x f < c.
  Proof.
    induction n as [|k IH]; intros x Hx.
    - left. cbn [pow]. unfold I.
      destruct (fin_eq_dec x f) as [Heq|_].
      + subst f. unfold mat_star. rewrite geom_sum_diag_one.
        apply bounded_orel_refl.
      + apply zero_is_bottom.
    - simpl. unfold matrix_mul.
      destruct (sum_selective H_total_order
                  (fun z => M x z * pow M k z f)) as [H0eq | [z Hz]].
      + left. rewrite H0eq. apply zero_is_bottom.
      + rewrite Hz. cbv beta.
        destruct (fin_eq_dec z d) as [Hzd | Hzd].
        * subst z. right.
          apply (orel_lt_trans (M x d * pow M k d f) (pow M k d f) c).
          -- apply bounded_mul_lower_right.
          -- exact (pow_from_B2_lt M H_total_order B1 B2 c H_partition H_lt H0
                      k d Hd f Hf).
        * destruct (IH z Hzd) as [Hle | Hlt].
          -- left.
             rewrite <- (isolate_off M d x z Hx Hzd).
             eapply orel_trans;
               [apply (bounded_mul_orel_compat_r _ _ _ Hle) |].
             eapply orel_trans;
               [apply (bounded_mul_orel_compat_l _ _ _
                         (link_le_mat_star (isolate M d) x z)) |].
             apply star_path_compose.
          -- right.
             apply (orel_lt_trans (M x z * pow M k z f) (pow M k z f) c).
             ++ apply bounded_mul_lower_right.
             ++ exact Hlt.
  Qed.

  (** A closure entry between two members of [B1] that already clears the
      threshold is untouched by isolating [d]: its strongest walk cannot have
      gone through [B2]. *)
  Lemma mat_star_isolate_preserved {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htotal : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R) (d : Node)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c) (Hd : In d B2)
    (e f : Node) (He : In e B1) (Hf : In f B1) (Hc : c ≤ mat_star M e f) :
    mat_star M e f = mat_star (isolate M d) e f.
  Proof.
    apply orel_antisym; [| apply mat_star_isolate_le].
    assert (Hed : e <> d).
    { intro Heq. subst e. exact (proj1 (H_partition d) He Hd). }
    destruct (geom_sum_selective Htotal M kleene_exp e f) as [k [Hk Heq]].
    destruct (pow_isolate_dichotomy M Htotal B1 B2 c d H_partition H_lt H0 Hd
                f Hf k e Hed) as [Hle | Hlt].
    - unfold mat_star. rewrite Heq. exact Hle.
    - exfalso. destruct Hlt as [Hlt_le Hlt_ne]. apply Hlt_ne.
      apply orel_antisym; [exact Hlt_le |].
      unfold mat_star in Hc. rewrite Heq in Hc. exact Hc.
  Qed.

  (** Smith-IIA (4.7.5)(a), in the isolation reading: a weak alternative has
      no bearing on how the strong ones compare. *)
  Theorem smith_iia_isolate {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htotal : forall x y : R, x + y = x ∨ x + y = y)
    (B1 B2 : list Node) (c : R) (d : Node)
    (H_partition : forall x : Node, In x B1 <-> ~ In x B2)
    (H_lt : forall a b, In a B1 -> In b B2 -> M b a < c)
    (H0 : (0 : R) < c) (Hd : In d B2)
    (Hsep : forall x y : Node, x <> y -> c ≤ M x y + M y x) :
    forall e f, In e B1 -> In f B1 ->
      (schulze_beats M e f <-> schulze_beats (isolate M d) e f).
  Proof.
    intros e f He Hf.
    assert (Hed : e <> d).
    { intro Heq. subst e. exact (proj1 (H_partition d) He Hd). }
    assert (Hfd : f <> d).
    { intro Heq. subst f. exact (proj1 (H_partition d) Hf Hd). }
    (* a closure entry that dominates its converse already clears c *)
    assert (Hclears : forall x y, x <> y ->
              mat_star M y x ≤ mat_star M x y -> c ≤ mat_star M x y).
    { intros x y Hxy Hdom.
      eapply orel_trans; [exact (Hsep x y Hxy) |].
      apply add_orel_bound.
      - apply link_le_mat_star.
      - eapply orel_trans; [apply link_le_mat_star | exact Hdom]. }
    split.
    - intros [Hle Hne].
      assert (Hef_ne : e <> f).
      { intro Heq. subst f. apply Hne. reflexivity. }
      pose proof (Hclears e f Hef_ne Hle) as Hc.
      pose proof (mat_star_isolate_preserved M Htotal B1 B2 c d H_partition
                    H_lt H0 Hd e f He Hf Hc) as Hef.
      split.
      + eapply orel_trans; [apply mat_star_isolate_le |].
        eapply orel_trans; [exact Hle |]. rewrite Hef. apply bounded_orel_refl.
      + intro Heq0.
        apply Hne. apply orel_antisym; [exact Hle |].
        rewrite Hef, <- Heq0. apply mat_star_isolate_le.
    - intros [Hle' Hne'].
      assert (Hef_ne : e <> f).
      { intro Heq. subst f. apply Hne'. reflexivity. }
      assert (Hc' : c ≤ mat_star (isolate M d) e f).
      { eapply orel_trans; [exact (Hsep e f Hef_ne) |].
        apply add_orel_bound.
        - rewrite <- (isolate_off M d e f Hed Hfd). apply link_le_mat_star.
        - eapply orel_trans; [| exact Hle'].
          rewrite <- (isolate_off M d f e Hfd Hed). apply link_le_mat_star. }
      assert (Hc : c ≤ mat_star M e f)
        by (eapply orel_trans; [exact Hc' | apply mat_star_isolate_le]).
      pose proof (mat_star_isolate_preserved M Htotal B1 B2 c d H_partition
                    H_lt H0 Hd e f He Hf Hc) as Hef.
      (* were the converse also above c it would be preserved too, forcing a
         tie in the isolated profile *)
      assert (Hno_converse : ~ (mat_star M e f ≤ mat_star M f e)).
      { intro Hbad.
        assert (Hcfe : c ≤ mat_star M f e)
          by (eapply orel_trans; [exact Hc | exact Hbad]).
        pose proof (mat_star_isolate_preserved M Htotal B1 B2 c d H_partition
                      H_lt H0 Hd f e Hf He Hcfe) as Hfe.
        apply Hne'. apply orel_antisym; [exact Hle' |].
        rewrite <- Hef, <- Hfe. exact Hbad. }
      split.
      + destruct (Htotal (mat_star M f e) (mat_star M e f)) as [Hc1 | Hc1].
        * exfalso. apply Hno_converse. unfold Orel. rewrite addC. exact Hc1.
        * exact Hc1.
      + intro Heq0. apply Hno_converse.
        rewrite Heq0. apply bounded_orel_refl.
  Qed.

  (* ==================================================================== *)
  (*  Shared helpers for prudence (§4.9) and the MinMax set (§4.8)         *)
  (* ==================================================================== *)

  (** Every term of a finite sum lies below the sum. *)
  Lemma fold_right_in_le {R : BoundedSemiring.type}
    (f : Node -> R) (l : list Node) (x : Node) :
    In x l -> f x ≤ fold_right (fun a b => f a + b) (0 : R) l.
  Proof.
    induction l as [|a l IH]; cbn [fold_right]; [contradiction |].
    intros [Heq|Hin].
    - subst a. apply bounded_plus_upper_left.
    - exact (orel_trans _ _ _ (IH Hin) (orel_plus_upper_right _ _)).
  Qed.

  Lemma le_sum {R : BoundedSemiring.type} (f : Node -> R) (x : Node) :
    f x ≤ sum f.
  Proof.
    unfold sum. apply fold_right_in_le. apply elements_complete.
  Qed.

  (** [1] is the top of the natural order. *)
  Lemma le_one {R : BoundedSemiring.type} (x : R) : x ≤ 1.
  Proof. unfold Orel. rewrite addC. apply (add_bound (s := R) x). Qed.

  (** The diagonal of the closure is the top. *)
  Lemma mat_star_diag_one {R : BoundedSemiring.type}
    (M : @Matrix Node R) (x : Node) : mat_star M x x = 1.
  Proof. unfold mat_star. apply geom_sum_diag_one. Qed.

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

  (* ==================================================================== *)
  (*  MinMax set (Section 4.8)                                            *)
  (*                                                                      *)
  (*  Γ_D(B) — [cut_in M B] — is the strength of the strongest link        *)
  (*  entering the set [B] from outside, β_D its minimum over the proper   *)
  (*  non-empty sets, and 𝔅_D the union of the minimising sets.  We take   *)
  (*  subsets as boolean predicates and keep β_D as a parameter [beta]     *)
  (*  constrained by hypotheses, rather than as a minimum computed over    *)
  (*  the powerset: the semiring has joins but no meets, so a minimum      *)
  (*  over subsets is not an operation of the algebra.  [Hmin] says beta   *)
  (*  is a lower bound for every cut (β_D is the minimum), [Ba] with       *)
  (*  [cut_in M Ba = beta] witnesses [a ∈ 𝔅_D], and [Hb_out] says no cut   *)
  (*  around [b] attains beta, i.e. [b ∉ 𝔅_D].                            *)
  (* ==================================================================== *)

  Definition proper_nonempty (B : Node -> bool) : Prop :=
    (exists x, B x = true) /\ (exists y, B y = false).

  Definition cut_in {R : Semiring.type}
    (M : @Matrix Node R) (B : Node -> bool) : R :=
    sum (fun y => sum (fun x => if andb (negb (B y)) (B x) then M y x else 0)).

  (** Every link entering [B] is below the cut. *)
  Lemma cut_in_ge {R : BoundedSemiring.type} (M : @Matrix Node R)
    (B : Node -> bool) (y x : Node) :
    B y = false -> B x = true -> M y x ≤ cut_in M B.
  Proof.
    intros Hy Hx. unfold cut_in.
    eapply orel_trans; [| exact (le_sum _ y)]. cbv beta.
    eapply orel_trans; [| exact (le_sum _ x)]. cbv beta.
    rewrite Hy, Hx. cbn. apply bounded_orel_refl.
  Qed.

  (** Claim #1 (4.8.7).  A path that starts outside [B] and ends inside it
      must cross the boundary, and its measure is below the crossing link. *)
  Lemma path_into_B_le_cut {R : BoundedSemiring.type}
    (M : @Matrix Node R) (B : Node -> bool) :
    forall (k : nat) (x y : Node) (p : list (Node * Node * R)),
      B x = false -> B y = true ->
      List.In p (all_paths_klength elements M k x y) ->
      measure_of_path p ≤ cut_in M B.
  Proof.
    induction k as [|k IH]; intros x y p Hx Hy Hin.
    - cbn [all_paths_klength] in Hin.
      destruct (fin_eq_dec x y) as [Heq|_]; [subst y; congruence | inversion Hin].
    - destruct (all_paths_klength_S_inv M k x y p Hin) as (z & q & -> & Hq).
      cbn [measure_of_path].
      destruct (B z) eqn:Hz.
      + (* the head edge already crosses the boundary *)
        exact (orel_trans _ _ _ (bounded_mul_lower_left _ _)
          (cut_in_ge M B x z Hx Hz)).
      + (* still outside [B]: the tail crosses it *)
        exact (orel_trans _ _ _ (bounded_mul_lower_right _ _)
          (IH z y q Hz Hy Hq)).
  Qed.

  Lemma pow_into_B_le_cut {R : BoundedSemiring.type}
    (M : @Matrix Node R) (B : Node -> bool) (n : nat) (x y : Node) :
    B x = false -> B y = true -> pow M n x y ≤ cut_in M B.
  Proof.
    intros Hx Hy.
    apply pow_bound_of_paths.
    intros p Hin.
    exact (path_into_B_le_cut M B n x y p Hx Hy Hin).
  Qed.

  Lemma mat_star_into_B_le_cut {R : BoundedSemiring.type}
    (M : @Matrix Node R) (B : Node -> bool) (x y : Node) :
    B x = false -> B y = true -> mat_star M x y ≤ cut_in M B.
  Proof.
    intros Hx Hy. apply mat_star_bound. intro n.
    exact (pow_into_B_le_cut M B n x y Hx Hy).
  Qed.

  (** Order helpers available once the order is total. *)
  Lemma not_le_lt {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (x y : R) :
    ~ (x ≤ y) -> y < x.
  Proof.
    intro Hn. split.
    - destruct (Htotal x y) as [Hc|Hc].
      + unfold Orel. rewrite addC. exact Hc.
      + exfalso. exact (Hn Hc).
    - intro Heq. apply Hn. rewrite Heq. apply bounded_orel_refl.
  Qed.

  (** A product stays strictly above a bound that both factors clear — this
      is where multiplication has to be the meet. *)
  Lemma lt_mul {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x) (c x y : R) :
    c < x -> c < y -> c < x * y.
  Proof.
    intros Hx Hy. destruct (Htotal x y) as [Hc|Hc].
    - assert (Hyx : y ≤ x) by (unfold Orel; rewrite addC; exact Hc).
      destruct (Hmeet y x Hyx) as [_ Hxy]. rewrite Hxy. exact Hy.
    - destruct (Hmeet x y Hc) as [Hxy _]. rewrite Hxy. exact Hx.
  Qed.

  (** Decidable search for a link satisfying a boolean test. *)
  Lemma exists_edge_dec (P : Node -> Node -> bool) :
    (forall f g, P f g = false) \/ (exists f g, P f g = true).
  Proof.
    destruct (existsb (fun f => existsb (fun g => P f g) elements) elements) eqn:E.
    - right. apply existsb_exists in E as [f [_ Hf]].
      apply existsb_exists in Hf as [g [_ Hg]]. exists f, g. exact Hg.
    - left. intros f g. destruct (P f g) eqn:HP; [exfalso | reflexivity].
      assert (Htrue :
        existsb (fun f' => existsb (fun g' => P f' g') elements) elements = true).
      { apply existsb_exists. exists f. split; [apply elements_complete |].
        apply existsb_exists. exists g. split; [apply elements_complete | exact HP]. }
      rewrite E in Htrue. discriminate.
  Qed.

  (** Claim #2 (4.8.11).  The closure out of [a] reaches [b] with strength
      above beta.  The paper grows a set greedily; equivalently, take the set
      of nodes that [a] does *not* reach above beta — if [b] were in it, that
      set would be a proper non-empty cut whose strongest entering link is
      itself above beta, and following that link would reach a node of the
      set above beta, a contradiction. *)
  Lemma minmax_reach {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node) (beta : R)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (Hmin : forall B : Node -> bool, proper_nonempty B -> beta ≤ cut_in M B)
    (Hb_out : forall B : Node -> bool,
      proper_nonempty B -> B b = true -> cut_in M B ≠ beta) :
    ~ (mat_star M a b ≤ beta).
  Proof.
    intro Hab_le.
    set (C := fun h : Node =>
      if Hdec (mat_star M a h + beta) beta then true else false).
    assert (HC_true : forall h, C h = true -> mat_star M a h ≤ beta).
    { intros h Hh. unfold C in Hh.
      destruct (Hdec (mat_star M a h + beta) beta) as [He|_];
        [exact He | discriminate]. }
    assert (HC_false : forall h, C h = false -> ~ (mat_star M a h ≤ beta)).
    { intros h Hh Hle. unfold C in Hh.
      destruct (Hdec (mat_star M a h + beta) beta) as [_|Hne];
        [discriminate | exact (Hne Hle)]. }
    assert (HCb : C b = true).
    { unfold C. destruct (Hdec (mat_star M a b + beta) beta) as [_|Hne];
        [reflexivity | exfalso; exact (Hne Hab_le)]. }
    destruct (C a) eqn:HCa.
    - (* [a] itself is not reached above beta, so beta is the top and every
         cut attains it — contradicting [b ∉ 𝔅_D] *)
      exfalso.
      assert (Hone_le : (1 : R) ≤ beta).
      { rewrite <- (mat_star_diag_one M a). exact (HC_true a HCa). }
      assert (Hbeta_one : beta = 1)
        by (apply orel_antisym; [apply le_one | exact Hone_le]).
      destruct (exists_other b) as [y Hy].
      pose (Bb := fun z : Node => if fin_eq_dec z b then true else false).
      assert (HBb : Bb b = true).
      { unfold Bb. destruct (fin_eq_dec b b) as [_|Hc]; [reflexivity | congruence]. }
      assert (Hpn : proper_nonempty Bb).
      { split; [exists b; exact HBb | exists y].
        unfold Bb. destruct (fin_eq_dec y b) as [Hc|_]; [congruence | reflexivity]. }
      apply (Hb_out Bb Hpn HBb).
      apply orel_antisym; [rewrite Hbeta_one; apply le_one | exact (Hmin Bb Hpn)].
    - (* [C] is a proper non-empty set containing [b] *)
      assert (Hpn : proper_nonempty C)
        by (split; [exists b; exact HCb | exists a; exact HCa]).
      assert (Hcut_gt : beta < cut_in M C).
      { split; [exact (Hmin C Hpn) | intro Heq; exact (Hb_out C Hpn HCb (eq_sym Heq))]. }
      destruct (exists_edge_dec (fun f g =>
        andb (andb (negb (C f)) (C g))
             (if Hdec (M f g + beta) beta then false else true)))
        as [Hnone | [f [g Hfg]]].
      + (* every link into [C] is below beta, so the cut is too *)
        exfalso. destruct Hcut_gt as [Hle Hne]. apply Hne, orel_antisym; [exact Hle |].
        unfold cut_in.
        apply bounded_sum_orel_bound. intro y. cbv beta.
        apply bounded_sum_orel_bound. intro x. cbv beta.
        destruct (andb (negb (C y)) (C x)) eqn:Hguard; [| apply zero_is_bottom].
        specialize (Hnone y x). rewrite Hguard in Hnone. cbn in Hnone.
        destruct (Hdec (M y x + beta) beta) as [He|_]; [exact He | discriminate].
      + (* the crossing link reaches a node of [C] above beta *)
        exfalso.
        destruct (C f) eqn:Hf; cbn in Hfg; [discriminate |].
        destruct (C g) eqn:Hg; cbn in Hfg; [| discriminate].
        assert (HMfg : ~ (M f g ≤ beta)).
        { destruct (Hdec (M f g + beta) beta) as [_|Hne];
            [discriminate Hfg | exact Hne]. }
        assert (Hprod : beta < mat_star M a f * M f g).
        { apply (lt_mul Htotal Hmeet).
          - exact (not_le_lt Htotal _ _ (HC_false f Hf)).
          - exact (not_le_lt Htotal _ _ HMfg). }
        assert (Hle_g : mat_star M a f * M f g ≤ mat_star M a g).
        { eapply orel_trans; [| apply star_path_compose].
          apply bounded_mul_orel_compat_r. apply link_le_mat_star. }
        destruct Hprod as [Hbx Hbx_ne].
        apply Hbx_ne, orel_antisym; [exact Hbx |].
        exact (orel_trans _ _ _ Hle_g (HC_true g Hg)).
  Qed.

  (** MinMax (4.8.1): every member of the MinMax set beats every non-member. *)
  Theorem minmax_beats {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node) (beta : R) (Ba : Node -> bool)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (Hpn_a : proper_nonempty Ba) (Ha : Ba a = true) (Hcut_a : cut_in M Ba = beta)
    (Hmin : forall B : Node -> bool, proper_nonempty B -> beta ≤ cut_in M B)
    (Hb_out : forall B : Node -> bool,
      proper_nonempty B -> B b = true -> cut_in M B ≠ beta) :
    schulze_beats M a b.
  Proof.
    (* [b] cannot lie in a minimising set *)
    assert (Hb : Ba b = false).
    { destruct (Ba b) eqn:Hbb; [exfalso | reflexivity].
      exact (Hb_out Ba Hpn_a Hbb Hcut_a). }
    assert (Hrev : mat_star M b a ≤ beta).
    { rewrite <- Hcut_a. exact (mat_star_into_B_le_cut M Ba b a Hb Ha). }
    assert (Hfwd : beta < mat_star M a b).
    { apply (not_le_lt Htotal).
      exact (minmax_reach M a b beta Htotal Hmeet Hdec Hmin Hb_out). }
    unfold schulze_beats, beats.
    exact (orel_lt_trans _ _ _ Hrev Hfwd).
  Qed.

  (** MinMax (4.8.2): [S ⊆ 𝔅_D] — a node outside the MinMax set is no winner. *)
  Corollary minmax_winner {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node) (beta : R) (Ba : Node -> bool)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (Hpn_a : proper_nonempty Ba) (Ha : Ba a = true) (Hcut_a : cut_in M Ba = beta)
    (Hmin : forall B : Node -> bool, proper_nonempty B -> beta ≤ cut_in M B)
    (Hb_out : forall B : Node -> bool,
      proper_nonempty B -> B b = true -> cut_in M B ≠ beta) : 
    ~ schulze_winner M b.
  Proof.
    intro Hwin.
    assert (Hab : a ≠ b).
    { intro Heq. rewrite Heq in Ha.
      destruct (Ba b) eqn:Hbb; [| discriminate].
      exact (Hb_out Ba Hpn_a Hbb Hcut_a). }
    exact (Hwin a Hab (minmax_beats M a b beta Ba Htotal Hmeet Hdec
      Hpn_a Ha Hcut_a Hmin Hb_out)).
  Qed.


End SocialChoice.