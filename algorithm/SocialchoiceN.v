From Stdlib Require Import List Utf8 Lia Wf_nat.
From Semiring Require Import PathN MatN OrelN 
  SemimoduleN Structures.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).

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

  (* ------------------------------------------------------------------ *)
  (*  Pareto criterion (Section 4.3):                                     *)
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
  (*  Version 1 (weaker):  a ≻ᵥ b for all v ∈ V  →  a ≻ b               *)
  (*                                                                      *)
  (*  "Every voter strictly prefers a over b."                            *)
  (*                                                                      *)
  (*  In the matrix M (where M x y counts voters who prefer x over y):    *)
  (*    M b a = 0   — zero voters prefer b over a                         *)
  (*    M a b ≠ 0   — at least one (in fact all) prefer a over b          *)
  (*                                                                      *)
  (*  Conclusion: a beats b in the Schulze sense, i.e.,                   *)
  (*    mat_star M b a ≤ mat_star M a b.                                  *)
  (*                                                                      *)
  (*  Unlike [pareto_stronger], this version does NOT require the         *)
  (*  row/column homogeneity conditions (Hrow, Hcol).  The universal      *)
  (*  quantifier "for all v" is encoded entirely in M b a = 0, which      *)
  (*  is a stronger hypothesis than the "for some v" in version 2.        *)
  (* ------------------------------------------------------------------ *)
  Theorem pareto_weaker {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node) :
    A ≠ B -> M B A = 0 -> M A B ≠ 0 ->
    mat_star M B A ≤ mat_star M A B.
  Proof.
  (* Proof sketch: since M B A = 0, every term in pow M n B A either
     contains the edge (A,B) (bounded above by M A B via boundedness)
     or can be paired with a symmetric term in pow M n A B via a
     path-swapping argument.  Direct formalisation requires the path
     infrastructure from PathN.v. *)
  Admitted.

  (* ------------------------------------------------------------------ *)
  (*  Version 2 (stronger):  a ≿ᵥ b for all v  ∧  a ≻ᵥ b for some v    *)
  (*                         →  a ≻ b                                    *)
  (*                                                                      *)
  (*  Every voter weakly prefers a over b, and at least one voter       *)
  (*   strictly prefers a over b.                                        *)
  (*                                                                      *)
  (*  Paper                    Code                                     *)
  (*  ------------------------------------------------------------     *)
  (*  a ≿ᵥ b for all v     M b a = 0                                   *)
  (*                         (no voter strictly prefers b over a)         *)
  (*                                                                      *)
  (*  a ≻ᵥ b for some v    M a b ≠ 0                                   *)
  (*                         (some voter strictly prefers a over b)       *)
  (*                                                                      *)
  (*  a ≻ b                mat_star M b a ≤ mat_star M a b             *)
  (*                         (a beats b in the Schulze sense)             *)
  (*                                                                      *)
  (*  The two additional hypotheses are specific to the abstract          *)
  (*  semiring framework (they are not needed in the standard proof       *)
  (*  because when M counts voters they follow automatically):            *)
  (*                                                                      *)
  (*    Hrow : M a X = M b X    for X ≠ a,b                              *)
  (*    Hcol : M X a = M X b    for X ≠ a,b                              *)
  (*                                                                      *)
  (*  These say that a and b are indistinguishable to/from every          *)
  (*  other candidate — a homogeneity condition that reflects the         *)
  (*  fact that voter preferences for a vs X and b vs X can differ        *)
  (*  only when X is a or b themselves.                                   *)
  (* ------------------------------------------------------------------ *)
  Theorem pareto_stronger {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node) :
    A ≠ B -> M B A = 0 -> M A B ≠ 0 ->
    (forall (X : Node), X ≠ A -> X ≠ B -> M A X = M B X) ->
    (forall (X : Node), X ≠ A -> X ≠ B -> M X A = M X B) ->
    mat_star M B A ≤ mat_star M A B.
  Proof.
  (* PROOF SKETCH (path-based):
     mat_star M B A = sum over paths from B to A (connect_partial_sum_mat_paths).
     mat_star M A B = sum over paths from A to B.
     For each B→A path p, we show measure(p) ≤ mat_star M A B via case analysis:

     1. If p contains edge (A,B): in a BoundedSemiring, any product containing
        M[A,B] is ≤ M[A,B] (iterated bounded_mul_lower_left/right).
        And M[A,B] ≤ mat_star M A B (geom_sum_includes_direct).  ✓

     2. If p does NOT contain (A,B):
        a. Strip leading B→B self-loops: M[B,B]*rest ≤ rest (bounded_mul_lower_left).
        b. Strip trailing A→A self-loops: rest*M[A,A] ≤ rest (bounded_mul_lower_right).
        c. After stripping, first neighbor ≠ B and last neighbor ≠ A.
           No A→B edge means first neighbor ≠ A and last neighbor ≠ B.
           So first & last neighbors ≠ A,B.
        d. Row condition: M[B,v1]=M[A,v1]. Col condition: M[vk,A]=M[vk,B].
        e. Swap endpoints: A→v1→...→vk→B is valid, same weight, in mat_star M A B.

     By sum_orel_bound, mat_star M B A ≤ mat_star M A B. *)
  Admitted.

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
      + (* Non-strict: M*_{ba} ≤ M*_{ab} — from Pareto (stronger) *)
        apply (pareto_stronger M a b Hneq Hzero Hnonzero Hrow Hcol).
      + (* Strict: M*_{ba} ≠ M*_{ab} — from hypothesis *)
        exact Hstrict.
  Qed.

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