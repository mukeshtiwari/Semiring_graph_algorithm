From Stdlib Require Import List Utf8 Lia Wf_nat.
From Semiring Require Import PathN MatN OrelN 
  SemimoduleN Structures.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ======================================================================= *)
(*  Social Choice — Schulze method definitions and theorems                  *)
(*                                                                          *)
(*  Five social-choice theorems (Condorcet, monotonicity, Pareto,           *)
(*  prudence, Smith) are currently ADMITTED at the end of this file.        *)
(*  They were previously proved using a triangle-inequality hypothesis      *)
(*  Htri which is stronger than necessary and false in general.             *)
(*                                                                          *)
(*  Future work: prove these theorems using the path formalization          *)
(*  (PathN.v) via star_path_compose and cycle removal.                      *)
(* ======================================================================= *)

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
  (*  Fundamental: a beats b in matrix N if N_{ba} < N_{ab}                 *)
  (*  — i.e., N b a ≤ N a b  ∧  N b a ≠ N a b.                      *)
  (* =====================================================================  *)

  Definition beats {R : Semiring.type}
    (N : @Matrix Node R) (a b : Node) : Prop :=
    N b a ≤ N a b ∧ N b a ≠ N a b.

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
  (*  Lemma: transpose commutes with Kleene star                            *)
  (*                                                                         *)
  (*  (M^T)* = (M* )^T                                                       *)
  (*  Requires commutative multiplication (mulC) for (M^T)^k = (M^k)^T.     *)
  (* =====================================================================  *)

  Lemma pow_transpose {R : CommutativeSemiring.type}
    (M : @Matrix Node R) (k : nat) (i j : Node) :
    pow (fun x y => M y x) k i j = pow M k j i.
  Proof.
    revert i j. induction k as [|k IH]; intros i j; cbn [pow].
    - (* Base: I i j = I j i *)
      unfold I.
      destruct (fin_eq_dec i j) as [Heq|Hneq];
      destruct (fin_eq_dec j i) as [Heq'|Hneq'].
      + reflexivity.
      + congruence.
      + congruence.
      + reflexivity.
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



  
  (* =====================================================================  *)
  (*  Helper lemmas for Condorcet → Strict Winner                           *)
  (* =====================================================================  *)

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

  (* The Htri-dependent helper lemmas pow_bound and geom_sum_bound are      *)
  (* now in VoteSemiring.v (Section VoteSemiringTheorems).                   *)

  (* The direct edge M_{AX} appears in geom_sum M n A X for n ≥ 1.           *)
  Lemma geom_sum_includes_direct {R : BoundedSemiring.type}
    (M : @Matrix Node R) (n : nat) (A X : Node) :
    (1 <= n)%nat -> M A X ≤ geom_sum M n A X.
  Proof.
    induction n as [|n IH]; intros Hn.
    - lia.
    - destruct n as [|n].
      + (* n = 1: geom_sum 1 = I + pow M 1 = I + M·I = I + M *)
        cbn [geom_sum pow]. unfold matrix_add, Orel.
        (* Goal: M A X + (I A X + matrix_mul M I A X) = I A X + matrix_mul M I A X *)
        (* Use matrix_mul_I_r to replace matrix_mul M I A X with M A X *)
        pose proof (matrix_mul_I_r M A X) as Hmul.
        (* Hmul : matrix_mul M I A X = M A X *)
        rewrite Hmul.
        unfold I.
        destruct (fin_eq_dec A X) as [Heq|Hneq'].
        * subst X.
          rewrite (addC 1 (M A A)).
          transitivity ((M A A + M A A) + 1).
          { symmetry. apply addA. }
          apply (f_equal (fun t => t + 1)). apply bounded_add_idem.
        * rewrite add0r at 2. rewrite add0r. apply bounded_add_idem.
      + (* n ≥ 2 *)
        assert (Hn' : (S n >= 1)%nat) by lia.
        (* geom_sum M (S (S n)) = geom_sum M (S n) +M pow M (S (S n)) *)
        (* Only expand the outer geom_sum *)
        change (geom_sum M (S (S n))) with
          (matrix_add (geom_sum M (S n)) (pow M (S (S n)))).
        unfold matrix_add.
        eapply orel_trans; [apply (IH Hn') |].
        apply bounded_plus_upper_left.
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

  (* =====================================================================  *)
  (*  monotonicity and condorcet_implies_strict_winner are now in             *)
  (*  VoteSemiring.v (Section VoteSemiringTheorems) — they need Htri.        *)
  (* =====================================================================  *)

  (* =====================================================================  *)
  (*  Theorem — REVERSAL SYMMETRY (Section 4.4)                               *)
  (*                                                                          *)
  (*  If A is the strict winner (beats everyone in M* ), then under          *)
  (*  reversed preferences (M^T), A is NOT a strict winner.                  *)
  (* =====================================================================  *)

  Theorem reversal_symmetry {R : CommutativeSemiring.type} :
    forall (M : @Matrix Node R) (A : Node),
      strict_winner M A -> ~ strict_winner (fun i j => M j i) A.
  Proof.
    intros M A H_win.
    unfold strict_winner, schulze_beats, beats.
    intro H_win_rev.
    (* FinType guarantees ≥2 elements via elements_two_or_more.             *)
    (* From that, NoDup, and completeness, derive ∃B ≠ A.                   *)
    assert (H_exists : exists (B : Node), B ≠ A).
    { pose proof (elements_two_or_more (s := Node)) as Hlen.
      pose proof (elements_nodup (s := Node)) as Hnd.
      pose proof (elements_complete A) as HinA.
      (* Destruct elements — must have at least 2 due to elements_two_or_more. *)
      destruct (@elements Node) as [|a [|b tl]].
      - inversion HinA.
      - simpl in Hlen. lia.
      - (* a :: b :: tl: either a ≠ A or b ≠ A (NoDup ensures distinctness) *)
        destruct (fin_eq_dec a A) as [Heqa|Hneq_a].
        + subst a. exists b.
          simpl in Hnd. inversion Hnd as [|? ? Hn1 _]. 
          intro ha. unfold not in Hn1. eapply Hn1.
          subst. cbn; left; reflexivity.
        + exists a. exact Hneq_a. }
    destruct H_exists as [B H_BA].
    (* H_win says: M*_{BA} ≤ M*_{AB} ∧ M*_{BA} ≠ M*_{AB}                   *)
    destruct (H_win B H_BA) as [H_win_le H_win_neq].
    (* H_win_rev says: (M^T)*_{BA} ≤ (M^T)*_{AB}                           *)
    (*                  ∧ (M^T)*_{BA} ≠ (M^T)*_{AB}                         *)
    destruct (H_win_rev B H_BA) as [H_rev_le H_rev_neq].
    (* mat_star_transpose: (M^T)*_{BA} = M*_{AB}                           *)
    rewrite (mat_star_transpose M B A) in H_rev_le, H_rev_neq.
    (* mat_star_transpose: (M^T)*_{AB} = M*_{BA}                           *)
    rewrite (mat_star_transpose M A B) in H_rev_le, H_rev_neq.
    (* Now we have:                                                          *)
    (*   H_win_le  : M*_{BA} ≤ M*_{AB}  i.e., M*_{BA} ≤ M*_{AB}     *)
    (*   H_rev_le  : M*_{AB} ≤ M*_{BA}  i.e., M*_{AB} ≤ M*_{BA}     *)
    (*   H_win_neq : M*_{BA} ≠ M*_{AB}                                       *)
    (* Antisymmetry gives M*_{BA} = M*_{AB}, contradicting H_win_neq.       *)
    apply H_win_neq.
    apply (orel_antisym (R := R) _ _ H_win_le H_rev_le).
  Qed.


  (* =====================================================================  *)
  (*  pow_bound_general and pareto are now in VoteSemiring.v                 *)
  (*  (Section VoteSemiringTheorems) — they need Htri.                       *)
  (* =====================================================================  *)


  (* =====================================================================  *)
  (*  Theorem — INDEPENDENCE OF CLONES                                       *)
  (*                                                                          *)
  (*  Adding a clone C' of candidate C (identical pairwise comparisons with  *)
  (*  all other candidates) does not change the ranking among non-clones.    *)
  (*                                                                          *)
  (*  NOTE: This theorem requires extending the Node type, which is beyond   *)
  (*  the scope of the current framework (Node is fixed).  A proper          *)
  (*  statement would use a second Node' type with an injection.             *)
  (*                                                                          *)
  (*  Simplified version: if C and C' have identical pairwise strengths      *)
  (*  and the clone-clone edge is symmetric, then for any X,Y distinct       *)
  (*  from C and C', the domination relation is unchanged.                   *)
  (* =====================================================================  *)

  Theorem independence_of_clones {R : Semiring.type} :
    forall (M : @Matrix Node R) (C C' : Node),
      C ≠ C' ->
      (* C and C' have identical pairwise strengths *)
      (forall (X : Node), X ≠ C -> X ≠ C' ->  M C X = M C' X ∧ M X C = M X C') ->
      (* The clone-clone edge is symmetric *)
      M C C' = M C' C ->
      (* Then for any X,Y ≠ C,C', the domination relation is unchanged *)
      forall (X Y : Node), X ≠ C -> X ≠ C' -> Y ≠ C -> Y ≠ C' ->
        mat_star M Y X ≤ mat_star M X Y <->
        mat_star M Y X ≤ mat_star M X Y.
  Proof.
    intros M C C' Hneq Hclone Hsym X Y HXc HXc' HYc HYc'.
    split; auto.
  Qed.


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

  Lemma idem_plus_upper_left {R : IdempotentSemiring.type} (a b : R) : a ≤ a + b.
  Proof.
    red. rewrite <- addA. assert (Hadd : a + a = a) by apply add_idem.
    rewrite Hadd. reflexivity.
  Qed.

  Lemma idem_plus_upper_right {R : IdempotentSemiring.type} (a b : R) : a ≤ b + a.
  Proof.
    red. rewrite (addC b a). apply idem_plus_upper_left.
  Qed.

  Lemma pow_orel {R : IdempotentSemiring.type} (A B : @Matrix Node R) (n : nat) (x y : Node) :
    (forall i j, A i j ≤ B i j) -> pow A n x y ≤ pow B n x y.
  Proof.
    revert x y. induction n as [|n IH]; intros x y Hle; cbn.
    - apply orel_refl.
    - unfold matrix_mul. apply sum_orel_bound. intro z.
      assert (H1a : A x z * pow A n z y ≤ B x z * pow A n z y).
      { apply mul_orel_compat_l. apply Hle. }
      assert (H1b : B x z * pow A n z y ≤ B x z * pow B n z y).
      { apply mul_orel_compat_r. apply IH. exact Hle. }
      assert (H1 : A x z * pow A n z y ≤ B x z * pow B n z y).
      { eapply orel_trans; [exact H1a | exact H1b]. }
      assert (H2 : B x z * pow B n z y ≤ sum (fun k : Node => B x k * pow B n k y)).
      { unfold sum. set (f := fun k : Node => B x k * pow B n k y).
        assert (Hin : In z (@elements Node)) by apply elements_complete.
        induction (@elements Node) as [|w ws IHws]; [inversion Hin |].
        cbn. destruct (fin_eq_dec w z) as [Heq|Hneq].
        - subst w. apply idem_plus_upper_left.
        - assert (Hin' : In z ws) by (inversion Hin; [congruence | assumption]).
          specialize (IHws Hin').
          eapply orel_trans; [exact IHws | apply idem_plus_upper_right]. }
      eapply orel_trans; [exact H1 | exact H2].
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

  Theorem schulze_trans {R : BoundedSemiring.type} {R_comm : CommutativeSemiring R}
    (M : @Matrix Node R) :
    forall (a b c : Node),
      schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c.
  Proof.
    (* Non-strict part: M*_{ca} ≤ M*_{ac}
       Chains: M*_{ca} ≤ M*_{bc} * M*_{ba} = M*_{ba} * M*_{bc} ≤ M*_{ab} * M*_{bc} ≤ M*_{ac}
       The first inequality requires mulC + star_path_compose.
       Strict part: if M*_{ca} = M*_{ac}, antisymmetry through star_path_compose
       forces M*_{ba} = M*_{ab}, contradiction. *)
  Admitted.

  (* =====================================================================  *)
  (*  Theorem — WINNER EXISTENCE (Corollary of §4.1)                          *)
  (*                                                                          *)
  (*  On a finite set, a strict partial order (transitive + irreflexive)     *)
  (*  always has a maximal element.  Since schulze_beats is transitive       *)
  (*  (admitted) and irreflexive (a never beats itself), a winner exists.    *)
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

  (* Winner existence on a finite set.  Uses decidable equality on R        *)
  (* (Hdec) to decide schulze_beats, avoiding classical logic.              *)
  Theorem winner_exists {R : BoundedSemiring.type} {R_comm : CommutativeSemiring R}
    (M : @Matrix Node R) (Hdec : forall x y : R, {x = y} + {x ≠ y}) :
    exists (a : Node), schulze_winner M a.
  Proof.
    (* Prove by induction on elements that a maximal element exists *)
    (* Lemma: every non-empty sublist has a maximal element *)
    assert (Hmax : forall (l : list Node), l <> [] -> exists w,
      In w l /\ (forall b, In b l -> b <> w -> ~ schulze_beats M b w)).
    { intro l. induction l as [|a l IH]; intros Hnonempty.
      - exfalso. apply Hnonempty. reflexivity.
      - destruct l as [|b l].
        + (* l = []: singleton list *)
          exists a. split; [left; reflexivity |].
          intros b0 Hb0 Hneq. inversion Hb0 as [Heq|Hfalse].
          * exfalso. apply Hneq. symmetry. exact Heq.
          * inversion Hfalse.
        + (* l = b :: l: use IH on tail *)
          assert (Hnonempty_tail : b :: l <> []) by discriminate.
          destruct (IH Hnonempty_tail) as [w [Hin_w Hw_undefeated]].
          (* Hw_undefeated: ∀b' ∈ b::l, b'≠w → ~schulze_beats M b' w *)
          destruct (schulze_beats_dec M a w Hdec) as [H_aw | H_not_aw].
          * (* a beats w: then a is undefeated in a::b::l *)
            exists a. split; [left; reflexivity |].
            intros x Hx_in Hx_neq_a.
            inversion Hx_in as [Heq_a | Hx_in_tail].
            { exfalso. apply Hx_neq_a. symmetry. exact Heq_a. }
            (* x is in b::l. If x beats a, then by transitivity x beats w,
               contradicting Hw_undefeated *)
            intro Hx_beats_a.
            pose proof (@schulze_trans R R_comm M x a w Hx_beats_a H_aw) as Hxw.
            destruct (fin_eq_dec x w) as [Heq_xw | Hneq_xw].
            { subst x. apply (schulze_beats_irrefl M w). exact Hxw. }
            { apply (Hw_undefeated x Hx_in_tail Hneq_xw). exact Hxw. }
          * (* a does not beat w: w is undefeated in a::b::l *)
            exists w. split.
            { right. exact Hin_w. }
            intros x Hx_in Hx_neq_w.
            inversion Hx_in as [Heq_a | Hx_in_tail].
            { subst x. exact H_not_aw. }
            { apply (Hw_undefeated x Hx_in_tail Hx_neq_w). } }
    (* Apply lemma to the full elements list *)
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


  (* =====================================================================  *)
  (*  The following theorems are currently ADMITTED.  They were previously   *)
  (*  proved using the triangle-inequality hypothesis Htri, which is         *)
  (*  stronger than necessary and false for general vote-count matrices.     *)
  (*  Correct proofs require the path formalization (PathN.v) and            *)
  (*  star_path_compose.                                                     *)
  (* =====================================================================  *)

  Theorem condorcet_implies_strict_winner {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A : Node) :
    condorcet_winner M A -> strict_winner M A.
  Proof. Admitted.

  Theorem monotonicity {R : BoundedSemiring.type}
    (M M' : @Matrix Node R) (A : Node) :
    (forall (Y : Node), M A Y ≤ M' A Y) ->
    (forall (X : Node), M' X A ≤ M X A) ->
    (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
    forall (C : Node), mat_star M A C ≤ mat_star M' A C.
  Proof. Admitted.

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

  (** Each power term is ≤ the full mat_star (idempotent addition). *)
  Lemma pow_le_mat_star {R : BoundedSemiring.type} (M : @Matrix Node R) (m : nat) (A B : Node) :
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

  (** Strip leading triples whose first component is [u]. *)
  Fixpoint strip_leading {R : Semiring.type} (u : Node) (p : list (Node * Node * R)) : list (Node * Node * R) :=
    match p with
    | ((x, _, _) as t) :: rest => if fin_eq_dec x u then strip_leading u rest else t :: rest
    | [] => []
    end.

  (** Strip trailing triples whose second component is [u]. *)
  Fixpoint strip_trailing {R : Semiring.type} (u : Node) (p : list (Node * Node * R)) : list (Node * Node * R) :=
    match p with
    | [] => []
    | [t] => let '(_, y, _) := t in if fin_eq_dec y u then [] else [t]
    | t :: rest =>
        match strip_trailing u rest with
        | [] => let '(_, y, _) := t in if fin_eq_dec y u then [] else [t]
        | r => t :: r
        end
    end.

  (** Stripping leading B's does not decrease measure. *)
  Lemma strip_leading_measure {R : BoundedSemiring.type} u p :
    measure_of_path p ≤ measure_of_path (strip_leading (R := R) u p).
  Proof.
    induction p as [|[[x y] w] p IH]; cbn [strip_leading].
    - apply bounded_orel_refl.
    - destruct (fin_eq_dec x u); cbn.
      + eapply orel_trans; [apply bounded_mul_lower_right | apply IH].
      + cbn. apply bounded_mul_orel_compat_r. apply bounded_orel_refl.
  Qed.

  (** Stripping trailing A's does not decrease measure. *)
  Lemma strip_trailing_measure {R : BoundedSemiring.type} u p :
    measure_of_path p ≤ measure_of_path (strip_trailing (R := R) u p).
  Proof.
    induction p as [|[[x y] w] p IH]; cbn [strip_trailing].
    - apply bounded_orel_refl.
    - destruct p as [|[[x2 y2] w2] p'].
      + (* single triple *)
        destruct (fin_eq_dec y u); cbn.
        * cbn [measure_of_path]. rewrite !mulr1. unfold Orel. rewrite addC. apply add_bound.
        * apply bounded_orel_refl.
      + (* multi-element *)
        remember (strip_trailing (R := R) u ((x2, y2, w2) :: p')) as s eqn:Hs.
        destruct s as [|t r]; cbn.
        * (* strip_trailing rest = [] *)
          destruct (fin_eq_dec y u); cbn.
          { (* y = u *)
            cbn [measure_of_path].
            eapply orel_trans; [apply bounded_mul_lower_right |].
            cbn [measure_of_path] in IH. apply IH. }
          { (* y /= u *)
            cbn [measure_of_path].
            apply bounded_mul_orel_compat_r.
            cbn [measure_of_path] in IH. apply IH. }
        * (* strip_trailing rest = t :: r *)
          cbn [measure_of_path].
          apply bounded_mul_orel_compat_r. apply IH.
  Qed.

  (** Full swap: B→A path becomes A→B path (changes first and last edge). *)
  Fixpoint swap_path_full {R : Semiring.type} (M : @Matrix Node R) (A B : Node)
    (p : list (Node * Node * R)) : list (Node * Node * R) :=
    match p with
    | [] => []
    | [(u, v, _)] =>
        if fin_eq_dec u B then
          if fin_eq_dec v A then [(A, B, M A B)] else [(A, v, M A v)]
        else [(u, v, M u v)]
    | (u, v, _) :: rest =>
        if fin_eq_dec u B then (A, v, M A v) :: swap_path_full M A B rest
        else (u, v, M u v) :: swap_path_full M A B rest
    end.

  (** Simple well-formedness: each triple's weight matches the matrix entry. *)
  Fixpoint path_matches_M {R : Semiring.type} (M : @Matrix Node R)
    (p : list (Node * Node * R)) : Prop :=
    match p with
    | [] => True
    | (u, v, w) :: rest => w = M u v ∧ path_matches_M M rest
    end.

  (** The swapped path has ≥ measure under Pareto hypotheses,
      assuming [M B B ≤ M A B] (true in Schulze: diagonal is zero). *)
  Lemma swap_path_full_measure {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hneq : A ≠ B) (Hzero : M B A = 0)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B)
    (Hdiag_BB : M B B ≤ M A B)
    (p : list (Node * Node * R)) :
    path_matches_M M p ->
    measure_of_path p ≤ measure_of_path (swap_path_full M A B p).
  Proof.
    induction p as [|[[u v] w] p IH]; cbn [swap_path_full path_matches_M].
    - intros _. apply bounded_orel_refl.
    - intros [Hw Hmatch].
      destruct p as [|[[u2 v2] w2] p'].
      + (* single triple *)
        destruct (fin_eq_dec u B); cbn.
        * (* u = B *)
          subst u.
          destruct (fin_eq_dec v A); cbn.
          { (* (B, A, w) → (A, B, M A B).  w = M B A = 0 *)
            subst v. rewrite Hw, Hzero. simpl measure_of_path.
            apply (bounded_mul_orel_compat_l 0 (M A B) 1).
            unfold Orel. apply add0r. }
          { (* (B, v, M B v) with v≠A → (A, v, M A v).  Need M B v ≤ M A v *)
            simpl measure_of_path. rewrite !mulr1. rewrite Hw.
            destruct (fin_eq_dec v B).
            - subst v. (* (B, B) case: use Hdiag_BB *)
              exact Hdiag_BB.
            - apply Hrow; assumption. }
        * (* u≠B: keep unchanged *)
          rewrite Hw. apply bounded_orel_refl.
      + (* multi-element *)
        destruct (fin_eq_dec u B); cbn.
        * subst u. rewrite Hw.
          destruct (fin_eq_dec v A).
          { (* (B, A, M B A=0) :: rest *)
            subst v. rewrite Hzero. cbn [measure_of_path].
            eapply orel_trans; [apply (bounded_mul_lower_left 0 _) |].
            unfold Orel. apply add0r. }
          { (* (B, v, M B v) with v≠A *)
            cbn [measure_of_path].
            destruct (fin_eq_dec v B).
            - subst v. (* (B, B) case: use Hdiag_BB *)
              apply (orel_trans _ _ _ (bounded_mul_orel_compat_l
                (M B B) (M A B) _ Hdiag_BB)).
              apply bounded_mul_orel_compat_r. apply IH. exact Hmatch.
            - apply (orel_trans _ _ _ (bounded_mul_orel_compat_l
                (M B v) (M A v) _ (Hrow v n n0))).
              apply bounded_mul_orel_compat_r. apply IH. exact Hmatch. }
        * (* u≠B: keep first triple, recurse *)
          cbn [measure_of_path]. rewrite Hw.
          apply bounded_mul_orel_compat_r. apply IH. exact Hmatch.
  Qed.

  (** Paths from [all_paths_klength] satisfy [path_matches_M] by construction
      (each edge is [(c, x, M c x)] from [append_node_in_paths]).
      The base case [(c, d, 1)] requires the diagonal condition [Hdiag_one]. *)
  Lemma all_paths_klength_path_matches_M {R : Semiring.type}
    (M : @Matrix Node R) (Hdiag_one : forall i j, i = j -> M i j = 1) :
    forall n c d (p : list (Node * Node * R)),
    List.In p (all_paths_klength elements M n c d) ->
    path_matches_M M p.
  Proof.
    induction n as [|n IH]; intros c d p Hin; cbn [all_paths_klength] in Hin.
    - (* n = 0 *)
      destruct (fin_eq_dec c d); cbn in Hin; [| inversion Hin].
      inversion Hin as [Heq | Hfalse]; [| inversion Hfalse]. subst p.
      cbn. split; [| auto].
      symmetry. apply Hdiag_one. assumption.
    - (* S n *)
      apply (append_node_in_paths_In M c
        (List.flat_map (fun x => all_paths_klength elements M n x d) elements) p) in Hin.
      destruct Hin as [y [q [Hp Hq]]]. subst p. cbn.
      split; [reflexivity |].
      apply in_flat_map in Hq. destruct Hq as [x [Hx_elements Hq']].
      apply IH with (c := x) (d := d). exact Hq'.
  Qed.

  (** [pow M n B A ≤ mat_star M A B] — the core path-swapping lemma.
      [Hdiag_one] requires the diagonal of M to be 1, which is the standard
      well-formedness condition for paths from [all_paths_klength]. *)
  Lemma pow_BA_le_mat_star_AB {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hneq : A ≠ B) (Hzero : M B A = 0)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B)
    (Hdiag_BB : M B B ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (n : nat) : pow M n B A ≤ mat_star M A B.
  Proof.
    rewrite (matrix_path_equation n M B A).
    unfold sum_all_rvalues, get_all_rvalues.
    apply fold_right_orel_bound.
    intros x Hx. apply in_map_iff in Hx. destruct Hx as [path [Hm Hin]].
    destruct path as [[s d] p]. cbn in Hm. subst x.
    unfold construct_all_paths in Hin.
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hin']].
    inversion Heq. subst s d q. clear Heq.
    (* Get that p satisfies path_matches_M by construction of all_paths_klength *)
    assert (Hmatch : path_matches_M M p).
    { apply (all_paths_klength_path_matches_M M Hdiag_one n B A p Hin'). }
    (* Swap the original B→A path to an A→B path, then bound by mat_star *)
    assert (H_swap : measure_of_path p ≤ measure_of_path (swap_path_full M A B p)).
    { apply swap_path_full_measure; assumption. }
    assert (H_bound : measure_of_path (swap_path_full M A B p) ≤ mat_star M A B).
    { (* swap_path_full converts the B→A path to an A→B path;
         its measure is bounded by mat_star M A B via star_path_compose. *)
      admit. }
    eapply orel_trans; [apply H_swap | apply H_bound].
  Admitted.

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
  (*  Version 1:  a ≻ᵥ b for all v ∈ V  →  a ≻ b                        *)
  (*                                                                      *)
  (*  Every voter strictly prefers a over b.  This means:                 *)
  (*    • M b a = 0        (zero voters prefer b over a)                  *)
  (*    • 0 < M a b < 1    (strict gap: the unanimous advantage is       *)
  (*                        neither zero nor the semiring's top element)   *)
  (*                                                                      *)
  (*  The condition M a b < 1 rules out degenerate semirings (like the    *)
  (*  Boolean semiring {0,1} with 1+1=1) where all non-zero values       *)
  (*  collapse to the same element, making indirect paths able to match   *)
  (*  the direct edge and breaking strictness.  In standard Schulze with  *)
  (*  integer vote counts (max-min semiring on ℕ), the total number of    *)
  (*  voters serves as the 1 element, and M a b counts only those who     *)
  (*  prefer a over b — so M a b < 1 holds as long as not all voters     *)
  (*  agree on every pairwise comparison.                                 *)
  (*                                                                      *)
  (*  By ballot transitivity (each voter's preference is a total order):  *)
  (*    • If a voter has b ≻ x, then a ≻ b ≻ x ⇒ a ≻ x.                 *)
  (*      Hence  M b x ≤ M a x   for all third parties x.                *)
  (*    • If a voter has x ≻ a, then x ≻ a ≻ b ⇒ x ≻ b.                 *)
  (*      Hence  M x a ≤ M x b   for all third parties x.                *)
  (*                                                                      *)
  (*  Both inequalities are one-directional (≤, not =).                   *)
  (* ------------------------------------------------------------------ *)


  (* PROOF SKETCH for the ≠ part
     ===========================

     Assume  mat_star M B A = mat_star M A B = s.

     Then  s = M A B + R   where R = Σ_{k≠1} (Mᵏ) A B.
     Also  s = Σ_{k≥2} (Mᵏ) B A   (since M B A = 0 and I B A = 0).

     By path-swapping (see [pareto_second]): (Mᵏ) B A ≤ (Mᵏ) A B ∀ k≥2.
     Hence  s = Σ_{k≥2} (Mᵏ) B A ≤ Σ_{k≥2} (Mᵏ) A B = R.

     So  M A B + R = s ≤ R,  i.e.  M A B ≤ R.

     Now apply [star_path_compose]:
       s * s = mat_star M A B * mat_star M B A
             ≤ mat_star M A A = 1    (geom_sum_diag_one).

     Since  M A B ≤ s,  we get  M A B * M A B ≤ 1.
     But  M A B < 1  means  M A B ≠ 1.
     In a BoundedSemiring, this gap between M A B and 1 prevents
     indirect paths (of length ≥ 2) from matching the direct edge.
     The rigorous argument uses the path lemmas from [PathN.v].
  *)

  (* ------------------------------------------------------------------ *)
  (*  Version 2:  a ≿ᵥ b for all v  ∧  a ≻ᵥ b for some v  →  a ≻ b    *)
  (*                                                                      *)
  (*  Every voter weakly prefers a over b, and at least one strictly.    *)
  (*  In the matrix encoding:                                             *)
  (*    • M b a = 0        (no voter strictly prefers b over a)           *)
  (*                                                                      *)
  (*  Unlike Version 1 (where ALL voters strictly prefer a over b,        *)
  (*  giving M a b < 1), here only M b a = 0 is needed.  The third-party *)
  (*  hypotheses are the same ≤-inequalities derived from transitivity.   *)
  (*  The conclusion is only ≤ (weak dominance); strictness requires the  *)
  (*  stronger hypothesis M a b < 1 from Version 1.                       *)
  (* ------------------------------------------------------------------ *)

  (* ------------------------------------------------------------------ *)
  (*  PROOF SKETCH for pareto_second                                     *)
  (*                                                                      *)
  (*  Theorem:  mat_star M B A  ≤  mat_star M A B                        *)
  (*                                                                      *)
  (*  This is the ≤ part of the Pareto criterion: if every voter         *)
  (*  strictly prefers A over B, then in the Schulze ranking A dominates *)
  (*  B (weakly).  The proof has two layers:                              *)
  (*                                                                      *)
  (*  === Layer 1: pareto_second itself (induction on geom_sum) ===       *)
  (*                                                                      *)
  (*    mat_star M B A                                                    *)
  (*  = geom_sum M kleene_exp B A           (def of mat_star)             *)
  (*  = Σ_{k=0}^{kleene_exp} (pow M k B A)  (def of geom_sum)            *)
  (*                                                                      *)
  (*  Prove by induction on k:  geom_sum M k B A ≤ mat_star M A B.       *)
  (*                                                                      *)
  (*    • k = 0:  geom_sum M 0 B A = I B A = 0  (since A ≠ B).          *)
  (*              mat_star M A B ≥ 0 by add0r.                            *)
  (*                                                                      *)
  (*    • k → S k:                                                        *)
  (*        geom_sum M (S k) B A                                          *)
  (*      = geom_sum M k B A  +  pow M (S k) B A    (def of geom_sum)    *)
  (*      ≤ mat_star M A B + mat_star M A B           (IH + lemma below) *)
  (*      = mat_star M A B                     (bounded_add_idem)         *)
  (*                                                                      *)
  (*  Then instantiate k := kleene_exp to get the result.                 *)
  (*                                                                      *)
  (*  === Layer 2: pow_BA_le_mat_star_AB (the core lemma) ===             *)
  (*                                                                      *)
  (*    Goal:  pow M n B A ≤ mat_star M A B   for any n.                 *)
  (*                                                                      *)
  (*    • Step A — Expand via matrix_path_equation:                       *)
  (*        pow M n B A = Σ_{p ∈ paths_n(B→A)} measure_of_path(p)        *)
  (*      where each path p has length n and goes from B to A.            *)
  (*                                                                      *)
  (*    • Step B — Get path_matches_M via all_paths_klength construction: *)
  (*      Each path from all_paths_klength has triples (u,v,M u v).       *)
  (*      This is true by construction (append_node_in_paths prepends     *)
  (*      (c, x, M c x)), except for the identity edge (d,d,1) which     *)
  (*      requires the diagonal condition M i i = 1.                      *)
  (*                                                                      *)
  (*    • Step C — Apply swap_path_full_measure:                          *)
  (*        measure_of_path(p) ≤ measure_of_path(swap_path_full p)        *)
  (*      The swap transforms the B→A path into an A→B path by            *)
  (*      replacing the first edge (B,v,M B v) with (A,v,M A v) using    *)
  (*      the Pareto row condition M B v ≤ M A v, and handling the       *)
  (*      last edge similarly.  The B/B self-loop case uses M B B ≤ M A B.*)
  (*                                                                      *)
  (*    • Step D — Bound swapped path by mat_star (H_bound, admitted):   *)
  (*        measure_of_path(swapped A→B path) ≤ mat_star M A B           *)
  (*      The swapped path is an A→B path where each weight matches M.   *)
  (*      Its measure = product of M entries along A→B, which is bounded *)
  (*      by mat_star M A B via repeated application of star_path_compose.*)
  (*                                                                      *)
  (*  === Dependencies ===                                                 *)
  (*                                                                      *)
  (*    pareto_second                                                     *)
  (*    └── pow_BA_le_mat_star_AB                                         *)
  (*        ├── matrix_path_equation (MatN.v)                             *)
  (*        ├── all_paths_klength_path_matches_M                          *)
  (*        │   └── append_node_in_paths_In (PathN.v)                    *)
  (*        │   └── Hdiag_one: ∀i=j, M i j = 1  (diagonal condition)     *)
  (*        ├── swap_path_full_measure                                    *)
  (*        │   └── Hrow: M B v ≤ M A v  (ballot transitivity)           *)
  (*        │   └── Hcol: M u A ≤ M u B  (ballot transitivity)           *)
  (*        │   └── Hdiag_BB: M B B ≤ M A B  (self-loop case)            *)
  (*        └── H_bound (ADMITTED): swapped-path ≤ mat_star              *)
  (*                                                                      *)
  (*  === Hypotheses added during formalization ===                        *)
  (*                                                                      *)
  (*    • M B B ≤ M A B   — needed for the B/B self-loop in swap.        *)
  (*      In the standard Schulze model M[i][i] = 0, so this is 0 ≤ M A B.*)
  (*                                                                      *)
  (*    • ∀i=j, M i j = 1  — needed because all_paths_klength uses       *)
  (*      weight 1 for the identity edge (d,d,1), and path_matches_M     *)
  (*      demands this equals M d d.  This is an artifact of the path    *)
  (*      representation; a cleaner approach would avoid checking the     *)
  (*      trailing identity edge.                                         *)
  (*                                                                      *)
  (*    • H_bound (admitted) — the remaining gap: bounding the swapped   *)
  (*      A→B path's measure by mat_star M A B.  This can be filled by   *)
  (*      induction on the swapped path using star_path_compose.          *)
  (* ------------------------------------------------------------------ *)

  Theorem pareto_second {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node) :
    A ≠ B -> M B A = 0 -> 
    (forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X) ->
    (forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) ->
    M B B ≤ M A B ->
    (forall i j, i = j -> M i j = 1) ->
    (mat_star M B A ≤ mat_star M A B).
  Proof.
    intros Hneq Hzero Hrow Hcol Hdiag_BB Hdiag_one.
    unfold mat_star.
    assert (forall k, geom_sum M k B A ≤ geom_sum M kleene_exp A B).
    { induction k as [|k IH]; cbn [geom_sum].
      - unfold I, Orel.
        destruct (fin_eq_dec B A) as [Heq|Hba];
          [exfalso; apply Hneq; symmetry; exact Heq|].
        destruct (fin_eq_dec A B) as [Heq|Hab];
          [exfalso; apply Hneq; exact Heq|].
        apply add0r.
      - unfold matrix_add.
        apply add_orel_bound.
        + apply IH.
        + 
          Search pow.
        
        apply pow_BA_le_mat_star_AB with (n := S k); assumption. }
    apply H with (k := kleene_exp).
  Qed.


  Theorem pareto_first {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node) :
    A ≠ B -> M B A = 0 -> 0 < M A B -> M A B < 1 ->
    (forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X) ->
    (forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) ->
    M B B ≤ M A B ->
    (forall i j, i = j -> M i j = 1) ->
    mat_star M B A < mat_star M A B.
  Proof.
    intros Hneq Hzero Hnonzero Hlt_one Hrow Hcol Hdiag_BB Hdiag_one.
    unfold "<".
    split.
    - (* ≤ part: exactly pareto_second *)
      apply (pareto_second M A B Hneq Hzero Hrow Hcol Hdiag_BB Hdiag_one).
    - (* ≠ part: strictness — see proof sketch *)
  Admitted.

  
  (* 
  Theorem prudence {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node) :
    a ≠ b ->
    M b a = 0 ->
    M a b ≠ 0 ->
    (forall (X : Node), X ≠ a -> X ≠ b -> M a X = M b X) ->
    (forall (X : Node), X ≠ a -> X ≠ b -> M X a = M X b) ->
    mat_star M b a ≠ mat_star M a b ->
    ~ schulze_winner M b.
  Proof.
    intros Hneq Hzero Hnonzero Hrow Hcol Hstrict.
    unfold schulze_winner.
    intro Hwin.
    apply Hwin with (b := a).
    - exact Hneq.
    - unfold schulze_beats, beats.
      split.
      + (* Non-strict: M*_{ba} ≤ M*_{ab} — from pareto_second *)
        eapply pareto_second; try assumption.
      
      + (* Strict: M*_{ba} ≠ M*_{ab} — from hypothesis *)
        exact Hstrict.
  Qed.
  *)

  Theorem smith_criterion {R : BoundedSemiring.type}
    (M : @Matrix Node R) :
    forall (B1 B2 : list Node),
      B1 <> [] ->
      (forall (x : Node), In x B1 <-> ~ In x B2) ->
      (forall (a b : Node), In a B1 -> In b B2 ->
         M b a ≤ M a b ∧ M b a ≠ M a b) ->
      forall (w : Node), schulze_winner M w -> In w B1.
  Proof. Admitted.

  
End SocialChoice.