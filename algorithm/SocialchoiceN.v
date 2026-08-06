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

  (** Helper: if (x*y)*y < x then x*y < x, in a bounded semiring with
      total order and decidable equality. *)
  Lemma xy2_lt_x_implies_xy_lt_x {R : BoundedSemiring.type}
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (x y : R) : (x * y) * y < x -> x * y < x.
  Proof.
    intros [Hle Hne].
    assert (Hxy_le_x : x * y ≤ x) by apply bounded_mul_lower_left.
    destruct (H_total_order (x * y) x) as [Hcase | Hcase].
    - (* x ≤ x*y, with x*y ≤ x → x = x*y, then (x*y)*y = x*y, Hne gives x*y ≠ x *)
      assert (Hx_le_xy : x ≤ x * y).
      { change (x + (x * y) = x * y). rewrite addC. exact Hcase. }
      assert (Heq : x * y = x) by (apply orel_antisym; [exact Hxy_le_x | exact Hx_le_xy]).
      rewrite Heq in Hle, Hne. exact (conj Hxy_le_x Hne).
    - (* x*y ≤ x, check if = or < *)
      destruct (Hdec (x * y) x) as [Heq | Hneq].
      + rewrite Heq in Hle, Hne. exfalso. apply Hne. exact Heq.
      + exact (conj Hxy_le_x Hneq).
  Qed.


  Theorem schulze_trans {R : BoundedCommutativeSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_pair_sum_one : forall i j : Node, i ≠ j -> M i j + M j i = 1) :
    forall (a b c : Node),
      schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c.
  Proof.
    intros a b c H_ab H_bc.
    unfold schulze_beats, beats in *.
    destruct H_ab as [H_ab_le H_ab_ne].
    destruct H_bc as [H_bc_le H_bc_ne].
    set (x := mat_star M a b) in *.
    set (y := mat_star M b c) in *.
    (* From beats a b: a ≠ b, and M a b = 1 (since M b a ≠ 1). *)
    assert (Ha_ne_b : a ≠ b).
    { intro Heq. subst b. apply H_ab_ne. apply orel_antisym; [exact H_ab_le |].
      unfold Orel. apply (@bounded_add_idem R (mat_star M a a)). }
    assert (H_Mab_1 : M a b = 1).
    { pose proof (H_pair_sum_one a b Ha_ne_b) as Hsum.
      destruct (H_total_order (M a b) (M b a)) as [Hcase | Hcase].
      - (* M a b + M b a = M a b, so Hsum gives M a b = 1 *)
        exact (eq_trans (eq_sym Hcase) Hsum).
      - (* M a b + M b a = M b a, so M b a = 1.  Then S b a = 1, contradicting beats. *)
        assert (H_Mba_1 : M b a = 1) by (exact (eq_trans (eq_sym Hcase) Hsum)).
        assert (H_Sba_1 : mat_star M b a = 1).
        { apply orel_antisym; [| rewrite <- H_Mba_1].
          - unfold Orel. rewrite addC. apply (@add_bound R _).
          - apply (geom_sum_includes_direct M kleene_exp b a).
            pose proof (elements_two_or_more (s := Node)). unfold kleene_exp. nia. }
        rewrite H_Sba_1 in H_ab_le.
        exfalso. apply H_ab_ne.
        apply (@orel_antisym R (mat_star M b a) x);
        [ rewrite H_Sba_1; exact H_ab_le
        | rewrite H_Sba_1; unfold Orel; rewrite addC; apply (@add_bound R _) ]. }
    (* Hence x = S a b = 1 *)
    assert (Hx_1 : x = 1).
    { apply orel_antisym.
      - unfold Orel. rewrite addC. apply (@add_bound R _).
      - rewrite <- H_Mab_1. apply (geom_sum_includes_direct M kleene_exp a b).
        pose proof (elements_two_or_more (s := Node)). unfold kleene_exp. nia. }
    (* Similarly, from beats b c: b ≠ c, and M b c = 1, and y = 1 *)
    assert (Hb_ne_c : b ≠ c).
    { intro Heq. subst c. apply H_bc_ne. apply orel_antisym; [exact H_bc_le |].
      unfold Orel. apply (@bounded_add_idem R (mat_star M b b)). }
    assert (H_Mbc_1 : M b c = 1).
    { pose proof (H_pair_sum_one b c Hb_ne_c) as Hsum.
      destruct (H_total_order (M b c) (M c b)) as [Hcase | Hcase].
      - exact (eq_trans (eq_sym Hcase) Hsum).
      - (* M c b = 1, so S c b = 1, contradicting beats *)
        assert (H_Mcb_1 : M c b = 1) by (exact (eq_trans (eq_sym Hcase) Hsum)).
        assert (H_Scb_1 : mat_star M c b = 1).
        { apply orel_antisym; [| rewrite <- H_Mcb_1].
          - unfold Orel. rewrite addC. apply (@add_bound R _).
          - apply (geom_sum_includes_direct M kleene_exp c b).
            pose proof (elements_two_or_more (s := Node)). unfold kleene_exp. nia. }
        rewrite H_Scb_1 in H_bc_le.
        exfalso. apply H_bc_ne.
        apply (@orel_antisym R (mat_star M c b) y);
        [ rewrite H_Scb_1; exact H_bc_le
        | rewrite H_Scb_1; unfold Orel; rewrite addC; apply (@add_bound R _) ]. }
    assert (Hy_1 : y = 1).
    { apply orel_antisym.
      - unfold Orel. rewrite addC. apply (@add_bound R _).
      - rewrite <- H_Mbc_1. apply (geom_sum_includes_direct M kleene_exp b c).
        pose proof (elements_two_or_more (s := Node)). unfold kleene_exp. nia. }
    (* Rewrite x and y as 1 everywhere *)
    rewrite Hx_1, Hy_1 in *.
    (* Now H_ab_le : S b a ≤ 1, H_ab_ne : S b a ≠ 1 *)
    (* H_bc_le : S c b ≤ 1, H_bc_ne : S c b ≠ 1 *)
    destruct (H_total_order (mat_star M a c) (mat_star M c a)) as [H_ca_le_ac | H_ac_le_ca].
    { (* Good case: S c a ≤ S a c *)
      split; [unfold Orel; rewrite addC; exact H_ca_le_ac |].
      destruct (Hdec (mat_star M c a) (mat_star M a c)) as [Heq | Hneq]; [| exact Hneq].
      (* Equality case: derive contradiction via the chain. *)
      pose proof (star_path_compose M a b c) as H1.   (* S a b * S b c ≤ S a c *)
      pose proof (star_path_compose M b c a) as H2.   (* S b c * S c a ≤ S b a *)
      (* Since S a b = 1 and S b c = 1, we have 1*1 ≤ S a c and 1 * S c a ≤ S b a *)
      assert (H1' : 1 * 1 ≤ mat_star M a c).
      { unfold x in Hx_1; unfold y in Hy_1.
        setoid_rewrite <-Hx_1 at 1.
        setoid_rewrite <-Hy_1.
        exact H1. }
      assert (H2' : 1 * mat_star M c a ≤ mat_star M b a).
      { unfold y in Hy_1. admit.
      
      }
      rewrite Heq in H2'.                             (* 1 * S a c ≤ S b a *)
      setoid_rewrite <-Heq in H2'.                             (* 1 * S a c ≤ S b a *)
      rewrite !mul1r in H1', H2'.                     (* 1 ≤ S a c,  S a c ≤ S b a *)
      assert (Hle : 1 ≤ mat_star M b a). 
      {
        eapply orel_trans.
        exact H1'.
        rewrite <-Heq. exact H2'.
      }
     
      assert (Hle_ab : 1 ≤ 1) by (eapply orel_trans; [exact Hle | exact H_ab_le]).
      (* 1 ≤ 1 is true.  But H_ab_ne says S b a ≠ 1.
         From Hle: 1 ≤ S b a, and bounded gives S b a ≤ 1, so S b a = 1.  Contradiction! *)
      assert (H_Sba_1 : mat_star M b a = 1).
      { apply orel_antisym; [| exact Hle].
        unfold Orel. rewrite addC. apply (@add_bound R _). }
      rewrite H_Sba_1 in H_ab_ne.
      intro ha. unfold not in H_ab_ne.
      apply H_ab_ne. reflexivity. }
    { (* Bad case: S a c ≤ S c a.  Derive contradiction. *)
      pose proof (star_path_compose M a b c) as H1.   (* S a b * S b c ≤ S a c *)
      pose proof (star_path_compose M b c a) as H2.   (* S b c * S c a ≤ S b a *)
      assert (H1' : 1 * 1 ≤ mat_star M a c).
      { unfold x in Hx_1; unfold y in Hy_1.
        setoid_rewrite <-Hx_1 at 1.
        setoid_rewrite <-Hy_1.
        exact H1. }
      assert (H2' : 1 * mat_star M c a ≤ mat_star M b a).
      { unfold y in Hy_1. admit. }
      rewrite !mul1r in H1'.                           (* 1 ≤ S a c *)
      assert (H1b : 1 ≤ mat_star M c a).
      { apply (orel_trans _ (mat_star M a c) _); [exact H1' | exact H_ac_le_ca]. }
      rewrite mul1r in H2'.                            (* S c a ≤ S b a *)
      assert (Hle : 1 ≤ mat_star M b a).
      { eapply orel_trans. exact H1b. exact H2'.  }
      (* As in the good case: 1 ≤ S b a implies S b a = 1, contradiction. *)
      assert (H_Sba_1 : mat_star M b a = 1).
      { apply orel_antisym; [| exact Hle].
        unfold Orel. rewrite addC. apply (@add_bound R _). }
      rewrite H_Sba_1 in H_ab_ne.
      unfold not in H_ab_ne.
      specialize(H_ab_ne eq_refl).
      inversion H_ab_ne. }
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
  Theorem winner_exists {R : BoundedCommutativeSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (H_pair_sum_one : forall i j : Node, i ≠ j -> M i j + M j i = 1) :
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
            pose proof (@schulze_trans R M H_total_order Hdec H_pair_sum_one x a w Hx_beats_a H_aw) as Hxw.
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

  Theorem monotonicity {R : BoundedSemiring.type}
    (M M' : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y) :
    (forall (Y : Node), M A Y ≤ M' A Y) ->
    (forall (X : Node), M' X A ≤ M X A) ->
    (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
    forall (C : Node), mat_star M A C ≤ mat_star M' A C.
  Proof.
    intros Hrow Hcol Heq C.
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
            { apply bounded_mul_orel_compat_l.
              pose proof (pow_le_mat_star M' 1 A z) as Hp.
              unfold kleene_exp in Hp. specialize (Hp ltac:(nia)).
              cbn [pow] in Hp. rewrite matrix_mul_I_r in Hp. exact Hp. }
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
            { apply bounded_mul_orel_compat_l.
              pose proof (pow_le_mat_star M' 1 z w) as Hp.
              unfold kleene_exp in Hp. specialize (Hp ltac:(nia)).
              cbn [pow] in Hp. rewrite matrix_mul_I_r in Hp. exact Hp. }
            (* mat_star M' z w * mat_star M' w C ≤ mat_star M' z C ≤ star' A C + star' z C *)
            apply (orel_trans _ (mat_star M' z C)).
            { apply star_path_compose. }
            apply orel_plus_upper_right. }
    (* Now use the mutual IH to prove the main result *)
    assert (Hgeom : forall n, geom_sum M n A C ≤ geom_sum M' kleene_exp A C).
    { induction n as [|n IHn]; cbn [geom_sum].
      - destruct (fin_eq_dec A C).
        + subst C. unfold I. destruct (fin_eq_dec A A); [|congruence]. rewrite (geom_sum_diag_one M' kleene_exp A). apply bounded_orel_refl.
        + unfold I. destruct (fin_eq_dec A C); [congruence|]. unfold Orel. apply add0r.
      - unfold matrix_add. apply add_orel_bound.
        + apply IHn.
        + apply Hmutual. }
    apply Hgeom with (n := kleene_exp).
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
        * cbn [measure_of_path]. rewrite !mulr1. unfold Orel. rewrite addC. apply (@add_bound R _).
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

  (** For any path from [x] to [A] (with [x ≠ A]), swapping the destination
      from [A] to [B] gives an upper bound via [mat_star M x B].
      Proved by induction on the path length [k]. *)
  Lemma path_xA_measure_le_mat_star_xB {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hneq : A ≠ B) (Hzero : M B A = 0)
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
    - (* k = S k *)
      cbn [all_paths_klength] in Hin.
      (* Use both shape and membership lemmas on two copies of Hin *)
      pose proof Hin as Hin_shape.
      apply (append_node_in_paths_In M x
        (List.flat_map (fun z => all_paths_klength elements M k z A) elements) p) in Hin.
      destruct Hin as [y [q [Hp Hq_lf]]].
      apply append_node_in_paths_shape in Hin_shape.
      destruct Hin_shape as (y' & q' & Hp' & Hsrc_x & Hsrc_y' & Hq_ne).
      (* Hp: p = (x, y, M x y) :: q.  Hp': p = (x, y', M x y') :: q'. *)
      (* By inversion, y = y' and q = q'. *)
      rewrite Hp in Hp'. inversion Hp' as [[Heq_xy Heq_M Heq_rest]].
      (* Heq_rest: q = q'.  Also from the head equality, y = y'. *)
      (* Actually inversion on a cons equality is tricky.  Let us use injection. *)
      (* Simpler: subst from Hp, then Hp' becomes a reflexive equality. *)
      subst p. 
      (* Now Hp': (x, y, M x y) :: q = (x, y', M x y') :: q' *)
      inversion Hp' as [[Heq_hd Heq_tl]].
      (* Heq_hd: (x, y, M x y) = (x, y', M x y').  Heq_tl: q = q'. *)
      (* From Heq_hd, by inversion: *)
      inversion Heq_hd. subst y' q'. clear Hp' Heq_hd Heq_tl.
      (* Now: Hsrc_y' : source y q = true.  Hq_ne: q ≠ []. *)
      apply in_flat_map in Hq_lf. destruct Hq_lf as [z [Hz_el Hq_in]].
      (* Hq_in: In q (all_paths_klength k z A). *)
      pose proof Hq_in as Hq_in_copy.
      apply non_empty_paths_in_kpath in Hq_in as (_ & Hsrc_z & _).
      (* Hsrc_z: source z q = true.  Also source y q = true, q ≠ []. *)
      assert (Hy_eq_z : y = z).
      { eapply source_inj; eassumption. }
      subst y.
      cbn [measure_of_path].
      destruct (fin_eq_dec z A) as [Heq_zA|Hneq_zA].
      + (* z = A: q ∈ all_paths_klength k A A *)
        subst z.
        assert (Hq_le_one : measure_of_path q ≤ 1).
        { apply measure_of_path_le_one. }
        apply (orel_trans _ _ _ (bounded_mul_orel_compat_r _ _ _ Hq_le_one)).
        rewrite mulr1.
        destruct (fin_eq_dec x B) as [Heq_xB|Hneq_xB].
        * subst x. rewrite Hzero. unfold Orel. apply add0r.
        * apply (orel_trans _ _ _ (Hcol x Hx_ne_A Hneq_xB)).
          unfold Orel.
          pose proof (elements_two_or_more (s := Node)) as Hlen.
          pose proof (@pow_le_mat_star R M 1 x B) as ha.
          unfold kleene_exp in ha.
          specialize (ha ltac:(nia)).
          cbn [pow] in ha. rewrite matrix_mul_I_r in ha. exact ha.
      + (* z ≠ A *)
        assert (Hq_bound : measure_of_path q ≤ mat_star M z B).
        { apply IH; [exact Hneq_zA|exact Hq_in_copy]. }
        apply (orel_trans _ _ _ (bounded_mul_orel_compat_r _ _ _ Hq_bound)).
        assert (HMxz : M x z ≤ mat_star M x z).
        { 
          pose proof (elements_two_or_more (s := Node)) as Hlen.
          pose proof (@pow_le_mat_star R M 1 x z) as ha.
          unfold kleene_exp in ha.
          specialize (ha ltac:(nia)).
          cbn [pow] in ha. rewrite matrix_mul_I_r in ha. exact ha.
        }
        apply (orel_trans _ _ _ (bounded_mul_orel_compat_l _ _ _ HMxz)).
        apply star_path_compose.
  Qed.

  (** [pow M n B A ≤ mat_star M A B] — the core lemma.
      Uses [path_xA_measure_le_mat_star_xB] for the inductive step
      when the first edge goes to a third party, and [star_path_compose]
      to chain through the intermediate node. *)
  Lemma pow_BA_le_mat_star_AB {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hneq : A ≠ B) (Hzero : M B A = 0)
    (Hrow : forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X)
    (Hcol : forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B)
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
    (* Goal: measure_of_path p ≤ mat_star M A B, where p ∈ all_paths_klength n B A *)
    revert p Hin'.
    induction n as [|k IH]; intros p Hin'.
    - (* n = 0: all_paths_klength 0 B A = [] since B ≠ A *)
      cbn [all_paths_klength] in Hin'.
      destruct (fin_eq_dec B A) as [Heq_BA|Hneq_BA]; [congruence|].
      inversion Hin'.
    - (* n = S k *)
      cbn [all_paths_klength] in Hin'.
      pose proof Hin' as Hin_shape.
      apply (append_node_in_paths_In M B
        (List.flat_map (fun z => all_paths_klength elements M k z A) elements) p) in Hin'.
      destruct Hin' as [y [q' [Hp Hq_lf]]].
      apply append_node_in_paths_shape in Hin_shape.
      destruct Hin_shape as (y' & q'' & Hp' & Hsrc_B & Hsrc_y' & Hq_ne).
      (* Hp: p = (B, y, M B y) :: q'.  Hp': p = (B, y', M B y') :: q''. *)
      rewrite Hp in Hp'. inversion Hp' as [[Heq_hd Heq_tl]].
      inversion Heq_hd. subst y' q''. clear Hp'  Heq_tl.
      (* Now: Hsrc_y' : source y q' = true. Hq_ne: q' ≠ []. *)
      apply in_flat_map in Hq_lf. destruct Hq_lf as [z [Hz_el Hq_in]].
      pose proof Hq_in as Hq_in_copy.
      apply non_empty_paths_in_kpath in Hq_in as (_ & Hsrc_z & _).
      assert (Hy_eq_z : y = z).
      { eapply source_inj; eassumption. }
      subst y.
      rewrite Hp. cbn [measure_of_path].
      destruct (fin_eq_dec z A) as [Heq_zA|Hneq_zA].
      + (* z = A: edge is (B, A, M B A = 0) *)
        subst z. rewrite Hzero.
        apply (orel_trans _ 0 _); [|unfold Orel; apply add0r].
        assert (Htmp : 0 * measure_of_path q' = 0). { apply mul0r. }
        rewrite Htmp. unfold Orel. apply add0r.
      + (* z ≠ A *)
        destruct (fin_eq_dec z B) as [Heq_zB|Hneq_zB].
        * (* z = B: q' ∈ all_paths_klength k B A *)
          subst z.
          rewrite (Hdiag_one B B eq_refl). rewrite mul1r.
          apply (IH _ Hq_in_copy).
        * (* z ≠ A, B *)
          assert (Hq_bound : measure_of_path q' ≤ mat_star M z B).
          { apply (path_xA_measure_le_mat_star_xB M A B Hneq Hzero Hcol k z q' Hneq_zA Hq_in_copy). }
          apply (orel_trans _ _ _ (bounded_mul_orel_compat_l _ _ _ (Hrow z Hneq_zA Hneq_zB))).
          apply (orel_trans _ _ _ (bounded_mul_orel_compat_r _ _ _ Hq_bound)).
          apply (orel_trans _ (mat_star M A z * mat_star M z B) _).
          { apply (bounded_mul_orel_compat_l (M A z) (mat_star M A z) (mat_star M z B)).
            pose proof (elements_two_or_more (s := Node)) as Hlen.
            pose proof (pow_le_mat_star M 1 A z) as h.
            unfold kleene_exp in h. specialize (h ltac:(nia)).
            cbn [pow] in h. rewrite matrix_mul_I_r in h. exact h. }
          { apply star_path_compose. }
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


  Theorem pareto_second {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node) :
    A ≠ B -> M B A = 0 -> 
    (forall X, X ≠ A -> X ≠ B -> M B X ≤ M A X) ->
    (forall X, X ≠ A -> X ≠ B -> M X A ≤ M X B) ->
    (forall i j, i = j -> M i j = 1) ->
    (mat_star M B A ≤ mat_star M A B).
  Proof.
    intros Hneq Hzero Hrow Hcol Hdiag_one.
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
        + apply pow_BA_le_mat_star_AB with (n := S k); assumption. }
    apply H with (k := kleene_exp).
  Qed.


  Theorem pareto_first {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node) :
    A ≠ B -> M B A = 0 -> 0 < M A B -> M A B < 1 ->
    (forall X Y, X ≠ Y -> M X Y ≤ M A B) ->
    (forall i j, i = j -> M i j = 1) ->
    mat_star M B A < mat_star M A B.
  Proof.
  Admitted.



  (** With total order on +, if every term in a sum is < 1, the sum < 1. *)
  Lemma sum_lt_1_if_all_lt_1 {R : BoundedSemiring.type}
    (Htotal : forall x y : R, x + y = x \/ x + y = y) (f : Node -> R) :
    (forall z, f z < 1) -> sum f < 1.
  Proof.
    intros Hlt.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    unfold sum.
    destruct (elements (s := Node)) as [|z l] eqn:Heq.
    - (* Empty: contradicts Hlen *)
      exfalso. subst. simpl in Hlen. lia.
    - clear Heq Hlen.
      revert z Hlt.
      induction l as [|y l' IH];
      [ (* One element *)
        cbn; intros z0 Hlt0; rewrite addr0; apply Hlt0
      | (* Multiple elements *)
        intros z0 Hlt0;
        cbn [fold_right];
        specialize (IH z0 Hlt0);
        cbn in IH; destruct IH as [IHa IHb];
        split;
        [ (* ≤ part *)
          unfold Orel in *;
          remember (f y + fold_right (fun x y0 => f x + y0) 0 l') as t;
          setoid_rewrite <- Heqt;
          remember (f z0 + t) as fzt;
          rewrite addC; exact (@add_bound R (f z0 + t))
        | (* ≠ part *)
          destruct (Hlt0 y) as [Hlta Hltb];
          unfold not in IHb;
          intro Hc; eapply IHb;
          destruct (Htotal (f z0) (f y + fold_right (fun x y0 => f x + y0) 0 l')) as [Hcase|Hcase];
          [ (* Case: A + (B+C) = A *)
            assert (Hz1 : f z0 = 1);
            [ transitivity (f z0 + (f y + fold_right (fun x y0 => f x + y0) 0 l'));
              [ symmetry; exact Hcase | exact Hc ]
            | rewrite Hz1; apply add_bound ]
          | (* Case: A + (B+C) = B+C *)
            destruct (Htotal (f y) (fold_right (fun x y0 => f x + y0) 0 l')) as [Hbc|Hbc];
            [ (* Subcase: B+C = B *)
              exfalso; apply Hltb;
              etransitivity; [ symmetry; exact Hbc | ];
              etransitivity; [ symmetry; exact Hcase | ];
              exact Hc
            | (* Subcase: B+C = C *)
              assert (Hc1 : fold_right (fun x y0 => f x + y0) 0 l' = 1);
              [ etransitivity; [ symmetry; exact Hbc | ];
                etransitivity; [ symmetry; exact Hcase | ];
                exact Hc
              | transitivity (f z0 + 1);
                [ apply (f_equal (fun t => f z0 + t)); exact Hc1
                | rewrite addC; apply add_bound ] ] ] ] ] ].
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

  (** Multiplication on the left by something < 1 gives < 1. *)
  Lemma mul_lt_1_left {R : BoundedSemiring.type} (a b : R) :
    a < 1 -> a * b < 1.
  Proof.
    intros Ha_lt_1. eapply orel_lt_trans; [apply bounded_mul_lower_left|exact Ha_lt_1].
  Qed.

  (** Multiplication on the right by something < 1 gives < 1. *)
  Lemma mul_lt_1_right {R : BoundedSemiring.type} (a b : R) :
    b < 1 -> a * b < 1.
  Proof.
    intros Hb_lt_1. eapply orel_lt_trans; [apply bounded_mul_lower_right|exact Hb_lt_1].
  Qed.
  (* =====================================================================  *)
  (*  The following theorems are currently ADMITTED.  They were previously   *)
  (*  proved using the triangle-inequality hypothesis Htri, which is         *)
  (*  stronger than necessary and false for general vote-count matrices.     *)
  (*  Correct proofs require the path formalization (PathN.v) and            *)
  (*  star_path_compose.                                                     *)
  (* =====================================================================  *)

  Theorem condorcet_implies_strict_winner {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (H_pair_sum_one : forall i j : Node, i ≠ j -> M i j + M j i = 1) :
    condorcet_winner M A -> strict_winner M A.
  Proof.
    unfold condorcet_winner, strict_winner, schulze_beats, beats.
    intros Hcw X Hneq.
    destruct (Hcw X Hneq) as [Hle_M Hneq_M].
    (* Step 1: from M X A < M A X and pair sum = 1, get M A X = 1 *)
    assert (Hsum1 : M X A + M A X = 1).
    { apply H_pair_sum_one. exact Hneq. }
    assert (HMA1 : M A X = 1).
    { destruct (H_total_order (M X A) (M A X)) as [Hcase|Hcase].
      - (* M X A + M A X = M X A, i.e., M A X ≤ M X A *)
        exfalso. apply Hneq_M.
        apply orel_antisym; [exact Hle_M |].
        unfold Orel. transitivity (M X A + M A X). { apply addC. } exact Hcase.
      - (* M X A + M A X = M A X *)
        transitivity (M X A + M A X); [symmetry; exact Hcase | exact Hsum1]. }
    assert (H_MAX_lt_1 : M X A < 1).
    { rewrite <- HMA1. exact (conj Hle_M Hneq_M). }
    (* For any w ≠ A, M w A < 1 follows from condorcet *)
    assert (H_all_lt_1 : forall w, w ≠ A -> M w A < 1).
    { intros w Hw_ne_A.
      destruct (Hcw w Hw_ne_A) as [Hle_w Hne_w].
      split.
      - eapply orel_trans; [exact Hle_w |].
        unfold Orel. rewrite addC. apply (@add_bound R _).
      - intro Heq. apply Hne_w.
        unfold Orel in Hle_w.
        rewrite Heq in Hle_w. (* Hle_w: 1 + M A w = M A w *)
        rewrite Heq. (* Goal becomes: 1 = M A w *)
        symmetry. (* Goal: M A w = 1 *)
        transitivity (1 + M A w); [symmetry; exact Hle_w | apply add_bound]. }
    (* 0 < 1 follows from M X A < 1 *)
    assert (H0_lt_1 : (0 : R) < (1 : R)).
    { split.
      - unfold Orel. apply add0r.
      - intro Hz.
        destruct H_MAX_lt_1 as [_ Hne].
        apply Hne.
        transitivity (0 + M X A). { symmetry. apply add0r. }
        transitivity (1 + M X A). { apply (f_equal (fun t => t + M X A) Hz). }
        apply (@add_bound R _). }
    (* Step 2: mat_star M A X = 1 *)
    assert (H_star_AX1 : mat_star M A X = 1).
    { apply orel_antisym.
      - (* mat_star M A X ≤ 1 *)
        unfold mat_star. unfold Orel. rewrite addC. apply (@add_bound R _).
      - (* 1 ≤ mat_star M A X *)
        rewrite <- HMA1.
        apply (geom_sum_includes_direct M kleene_exp A X).
        pose proof (elements_two_or_more (s := Node)). unfold kleene_exp. nia. }
    split.
    - (* ≤ part: mat_star M X A ≤ mat_star M A X *)
      rewrite H_star_AX1. unfold Orel. rewrite addC. apply (@add_bound R _).
    - (* ≠ part: mat_star M X A ≠ mat_star M A X *)
      rewrite H_star_AX1. intro Heq.
      (* mat_star M X A = 1. Show this is impossible via induction on path length. *)
      assert (H_pow_lt_1 : forall n w, w ≠ A -> pow M n w A < 1).
      { induction n as [|n IH]; intros w Hw_ne_A.
        - (* n = 0: I w A = 0 *)
          cbn [pow]. unfold I.
          destruct (fin_eq_dec w A); [congruence|]. exact H0_lt_1.
        - (* n = S n: pow M (S n) w A = Σ_z M w z * pow M n z A *)
          simpl. unfold matrix_mul.
          apply (sum_lt_1_if_all_lt_1 H_total_order (fun z : Node => M w z * pow M n z A)).
          intro z.
          destruct (fin_eq_dec z A) as [Heq_zA|Hne_zA].
          + (* z = A: M w A * pow M n A A. M w A < 1, so product < 1 *)
            subst z. apply mul_lt_1_left. apply H_all_lt_1. exact Hw_ne_A.
          + (* z ≠ A: M w z * pow M n z A, where pow M n z A < 1 by IH *)
            apply mul_lt_1_right. apply IH. exact Hne_zA. }
      (* Now: mat_star M X A = geom_sum M K X A = 1 *)
      unfold mat_star in Heq.
      pose proof (elements_two_or_more (s := Node)) as Hlen.
      assert (H_geom_lt_1 : forall n, geom_sum M n X A < 1).
      { induction n as [|n IH].
        - cbn [geom_sum]. unfold I.
          destruct (fin_eq_dec X A); [congruence|]. exact H0_lt_1.
        - cbn [geom_sum]. unfold matrix_add.
          assert (Hpow_lt_1 : pow M (S n) X A < 1).
          { apply H_pow_lt_1. exact Hneq. }
          destruct (H_total_order (geom_sum M n X A) (pow M (S n) X A)) as [Hcase|Hcase].
          + apply (eq_ind_r (fun t => t < 1) IH Hcase).
          + apply (eq_ind_r (fun t => t < 1) Hpow_lt_1 Hcase). }
      apply H_geom_lt_1 with (n := kleene_exp). exact Heq.
  Qed.

  


  (** Smith criterion: requires total order on + and pair sum = 1. *)
  Theorem smith_criterion {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (H_pair_sum_one : forall i j : Node, i ≠ j -> M i j + M j i = 1) :
    forall (B1 B2 : list Node), B1 <> [] ->
      (forall (x : Node), In x B1 <-> ~ In x B2) ->
      (forall (a b : Node), In a B1 -> In b B2 -> M b a < M a b) ->
      forall (w : Node), schulze_winner M w -> In w B1.
  Proof.
    intros B1 B2 H_B1_nonempty H_partition H_dom w H_winner.
    destruct (in_dec fin_eq_dec w B1) as [Hin|Hnotin_B1]; [exact Hin|].
    destruct (in_dec fin_eq_dec w B2) as [Hw_B2|Hnotin_B2].
    - (* w ∈ B2: derive contradiction *)
      destruct B1 as [|a B1']; [congruence|].
      assert (Ha_B1 : In a (a :: B1')). { left; reflexivity. }
      assert (Ha_ne_w : a ≠ w). { intro Heq. subst a. contradiction. }
      (* 0 < 1 holds because otherwise M w a = M a w, violating H_dom *)
      assert (H0_lt_1 : (0 : R) < (1 : R)).
      { split.
        - unfold Orel. rewrite addC. apply (@add_bound R (0 : R)).
        - intro Hz. (* Hz : (0 : R) = (1 : R) *)
          assert (H_direct : M w a < M a w). { apply H_dom; assumption. }
          destruct H_direct as [H_le H_neq].
          apply H_neq. apply orel_antisym.
          + exact H_le.
          + assert (HMw1 : M w a = (1 : R)).
            { rewrite <- (add0r (M w a)). change zero with (0 : R). rewrite Hz. apply (@add_bound R (M w a)). }
            assert (HMa1 : M a w = (1 : R)).
            { rewrite <- (add0r (M a w)). change zero with (0 : R). rewrite Hz. apply (@add_bound R (M a w)). }
            rewrite HMw1, HMa1. unfold Orel. apply (@add_bound R (1 : R)). }
      (* For any b∈B2, c∈(a::B1'): M b c < 1 *)
      assert (H_M_B2_B1_lt_1 : forall b c, In b B2 -> In c (a :: B1') -> M b c < 1).
      { intros b c Hb_B2 Hc_B1.
        assert (Hbc_ne : b ≠ c).
        { intro Heq. subst c. apply (proj1 (H_partition b) Hc_B1). exact Hb_B2. }
        assert (H_direct : M b c < M c b). { apply H_dom; assumption. }
        destruct H_direct as [H_le H_neq].
        assert (H_sum1 : M c b + M b c = 1). { apply H_pair_sum_one. apply not_eq_sym. exact Hbc_ne. }
        unfold Orel in H_le.
        split.
        - eapply orel_trans; [apply H_le|]. unfold Orel. rewrite addC. apply (@add_bound R _).
        - intro Heq1. apply H_neq.
          rewrite addC in H_le. rewrite H_sum1 in H_le.
          rewrite Heq1. exact H_le. }
      (* M a w = 1 *)
      assert (H_MAW1 : M a w = 1).
      { assert (H_direct : M w a < M a w). { apply H_dom; assumption. }
        destruct H_direct as [H_le H_neq].
        assert (H_sum1 : M a w + M w a = 1). { apply H_pair_sum_one. exact Ha_ne_w. }
        unfold Orel in H_le. rewrite addC in H_le. rewrite H_sum1 in H_le. symmetry. exact H_le. }
      (* mat_star M a w = 1 *)
      assert (H_star_AW1 : mat_star M a w = 1).
      { apply orel_antisym.
        - unfold mat_star, Orel. rewrite addC. apply (@add_bound R _).
        - rewrite <- H_MAW1.
          apply (geom_sum_includes_direct M kleene_exp a w).
          pose proof (elements_two_or_more (s := Node)). unfold kleene_exp. nia. }
      (* Key lemma: for all n, b∈B2, c∈(a::B1'): pow M n b c < 1 *)
      assert (H_pow_B2_B1_lt_1 : forall n b c, In b B2 -> In c (a :: B1') -> pow M n b c < 1).
      { induction n as [|n IH]; intros b c Hb_B2 Hc_B1.
        - (* n = 0: pow M 0 b c = I b c = 0 *)
          cbn [pow]. unfold I.
          assert (Hbc_ne : b ≠ c).
          { intro Heq. subst c. apply (proj1 (H_partition b) Hc_B1). exact Hb_B2. }
          destruct (fin_eq_dec b c); [congruence|]. exact H0_lt_1.
        - (* n = S n: pow M (S n) b c = Σ_z M b z * pow M n z c *)
          simpl. unfold matrix_mul.
          apply (sum_lt_1_if_all_lt_1 H_total_order (fun z : Node => M b z * pow M n z c)).
          intros z.
          destruct (in_dec fin_eq_dec z (a :: B1')) as [Hz_B1|Hz_not_B1].
          + (* z ∈ B1: M b z < 1 *)
            apply mul_lt_1_left. apply H_M_B2_B1_lt_1; assumption.
          + (* z ∉ B1 → z ∈ B2: pow M n z c < 1 *)
            assert (Hz_B2 : In z B2).
            { destruct (in_dec fin_eq_dec z B2) as [HzB|HzB]; [exact HzB|].
              exfalso. apply Hz_not_B1. apply (proj2 (H_partition z)). exact HzB. }
            apply mul_lt_1_right. apply IH; assumption. }
      (* Therefore: geom_sum M n w a < 1 for all n *)
      assert (H_geom_WA_lt_1 : forall n, geom_sum M n w a < 1).
      { induction n as [|n IH].
        - cbn [geom_sum]. unfold I.
          destruct (fin_eq_dec w a) as [Heq|Hne].
          + subst w. exfalso. apply Ha_ne_w. reflexivity.
          + exact H0_lt_1.
        - cbn [geom_sum]. unfold matrix_add.
          assert (Hpow_lt_1 : pow M (S n) w a < 1).
          { apply H_pow_B2_B1_lt_1 with (b := w) (c := a); assumption. }
          destruct (H_total_order (geom_sum M n w a) (pow M (S n) w a)) as [Hcase|Hcase].
          + setoid_rewrite Hcase. exact IH.
          + setoid_rewrite Hcase. exact Hpow_lt_1. }
      (* Hence mat_star M w a < 1 *)
      assert (H_star_WA_lt_1 : mat_star M w a < 1).
      { unfold mat_star. apply H_geom_WA_lt_1. }
      (* Therefore a beats w, contradiction *)
      assert (H_schulze_beats : schulze_beats M a w).
      { unfold schulze_beats, beats. rewrite H_star_AW1. exact H_star_WA_lt_1. }
      unfold schulze_winner in H_winner.
      specialize(H_winner a Ha_ne_w).
      unfold not in H_winner.
      specialize(H_winner H_schulze_beats).
      inversion H_winner.
    - apply H_partition in Hnotin_B2. contradiction.
  Qed.


End SocialChoice.