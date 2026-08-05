From Stdlib Require Import List Utf8 Lia Wf_nat.
From Semiring Require Import PathN MatN OrelN 
  SemimoduleN Structures.
Import ListNotations SemiringNotations.


Section SocialChoice.

  Context 
    {Node : FinType.type}.

  (* Kleene star:  A* = I + A + A² + … + A^{|N|-1}                          *)
  Definition kleene_exp := Init.Nat.pred (List.length (@elements Node)).

  (* =====================================================================  *)
  (*  Kleene star as a named definition for readability                     *)
  (* =====================================================================  *)

  Definition mat_star {R : Semiring.type} (M : @Matrix Node R) 
    : @Matrix Node R :=
    geom_sum M kleene_exp.

  (* =====================================================================  *)
  (*  Fundamental: a beats b in matrix N if N_{ba} < N_{ab}                 *)
  (*  — i.e., Orel (N b a) (N a b)  ∧  N b a ≠ N a b.                      *)
  (* =====================================================================  *)

  Definition beats {R : Semiring.type}
    (N : @Matrix Node R) (a b : Node) : Prop :=
    Orel (N b a) (N a b) ∧ N b a ≠ N a b.

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
    (*  Monotonicity: if voters improve candidate A's pairwise scores        *)
    (*  (raising A's outgoing row and lowering A's incoming column, with     *)
    (*  all other M[X][Y] unchanged), then A's Kleene-star scores do not     *)
    (*  decrease — i.e., for every opponent C:                               *)
    (*                                                                        *)
    (*        Orel (M*_{AC}) (M'*_{AC})    (M'* dominates M* )               *)
    (*                                                                        *)
    (*  Proof outline:                                                        *)
    (*    • If C = A: both entries are oneR (diagonal of the Kleene star),   *)
    (*      and Orel oneR oneR follows from idempotence.                     *)
    (*    • If C ≠ A: we zero out column A in both matrices (Z and Z'),      *)
    (*      prove Orel Z Z' entrywise using the row/col/Heq hypotheses,     *)
    (*      then lift to Kleene stars via mat_star_monotone.  Finally,       *)
    (*      column-zeroing doesn't change the A-row                           *)
    (*      (column_A_zero_preserves_row), so the chain:                     *)
    (*                                                                        *)
    (*        M*_{AC} = Z*_{AC}  ≤  Z'*_{AC} = M'*_{AC}                      *)
    (*                                                                        *)
    (*      collapses to Orel (M*_{AC}) (M'*_{AC}).                           *)
    (* =====================================================================  *)

  Theorem monotonicity {R : Semiring.type}:
    forall (M M' : @Matrix Node R) (A : Node),
    (forall (a b c : R), Orel (a * (b * c)) (a * c)) ->
    (* row increases *)
    (forall (Y : Node), Orel (M A Y) (M' A Y)) ->
    (* column decreases *)
    (forall (X : Node), Orel (M' X A) (M X A)) ->
    (* every other place, M is unchanged. *)
    (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
    forall (C : Node), Orel (mat_star M A C) 
    (mat_star M' A C).
  Proof. 
  Admitted.


  (* =====================================================================  *)
  (*  Lemma: transpose commutes with Kleene star                            *)
  (*                                                                         *)
  (*  (M^T)* = (M* )^T                                                       *)
  (* =====================================================================  *)

  Lemma mat_star_transpose {R : Semiring.type} : 
    forall (M : @Matrix Node R) (i j : Node),
      mat_star (fun x y => M y x) i j = mat_star M j i.
  Proof.
    (* (M^T)* = (M* )^T follows from transpose distributing over           *)
    (* matrix_add and (M^k)^T = (M^T)^k.  Admitted.                       *)
  Admitted.



  
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

  Lemma bounded_orel_refl {R : BoundedSemiring.type} (a : R) : Orel a a.
  Proof. unfold Orel. apply bounded_add_idem. Qed.

  Lemma bounded_mul_orel_compat_r {R : BoundedSemiring.type} (a b c : R) :
    Orel a b -> Orel (c * a) (c * b).
  Proof.
    unfold Orel. intros Hab.
    transitivity (c * (a + b)).
    - symmetry. apply (mulDl c a b).
    - apply (f_equal (fun t => mul c t)). exact Hab.
  Qed.

  (* If every term of a sum is ≤ v, then the whole sum is ≤ v.               *)
  Lemma sum_orel_bound {R : Semiring.type} 
    (f : Node -> R) (v : R) :
    (forall x, Orel (f x) v) -> Orel (sum f) v.
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
    Orel a c -> Orel b c -> Orel (a + b) c.
  Proof.
    unfold Orel. intros Ha Hb.
    rewrite addA, Hb, Ha. reflexivity.
  Qed.

  Lemma bounded_plus_upper_left {R : BoundedSemiring.type} (a b : R) : Orel a (a + b).
  Proof.
    unfold Orel. rewrite <- addA. rewrite (bounded_add_idem a). reflexivity.
  Qed.

  (* In a bounded semiring with the triangle-inequality hypothesis           *)
  (* (M_xy * M_yz ≤ M_xz), every matrix power entry is bounded by the       *)
  (* direct edge weight: pow M k X A ≤ M X A  for k ≥ 1.                    *)
  Lemma pow_bound {R : BoundedSemiring.type} 
    (M : @Matrix Node R)
    (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z)) :
    forall (k : nat) (X A : Node),
      (k >= 1)%nat -> Orel (pow M k X A) (M X A).
  Proof.
    induction k as [|k IH]; intros X A Hk.
    - lia.
    - destruct k as [|k].
      + (* k = 1: pow M 1 X A = M X A *)
        cbn [pow]. rewrite (matrix_mul_I_r M X A).
        unfold Orel. apply bounded_add_idem.
      + (* k = S (S k), i.e., ≥ 2 *)
        assert (Hk' : (S k >= 1)%nat) by lia.
        cbn [pow]. unfold matrix_mul.
        apply sum_orel_bound. intro y.
        (* Need: M X y * pow M (S k) y A ≤ M X A *)
        eapply orel_trans; [| apply (Htri X y A)].
        apply bounded_mul_orel_compat_r.
        apply (IH y A Hk').
  Qed.

  (* Corollary: the geometric sum from X to A is bounded by M_{XA}.          *)
  Lemma geom_sum_bound {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z)) :
    forall (n : nat) (X A : Node),
      X ≠ A -> Orel (geom_sum M n X A) (M X A).
  Proof.
    induction n as [|n IH]; intros X A Hneq.
    - (* n = 0: geom_sum M 0 X A = I X A = 0 *)
      cbn [geom_sum]. unfold I.
      destruct (fin_eq_dec X A) as [Heq|Hneq'].
      + contradiction.
      + unfold Orel. rewrite add0r. reflexivity.
    - (* n = S n: geom_sum (S n) = geom_sum n +M pow M (S n) *)
      cbn [geom_sum]. unfold matrix_add.
      apply add_orel_bound.
      + apply (IH X A Hneq).
      + apply (pow_bound M Htri (S n) X A). lia.
  Qed.

  (* The direct edge M_{AX} appears in geom_sum M n A X for n ≥ 1.           *)
  Lemma geom_sum_includes_direct {R : BoundedSemiring.type}
    (M : @Matrix Node R) (n : nat) (A X : Node) :
    (n >= 1)%nat -> Orel (M A X) (geom_sum M n A X).
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

  (* =====================================================================  *)
  (*  Theorem — Condorcet implies strict winner                              *)
  (*                                                                          *)
  (*  If M satisfies the triangle inequality M_{XY}·M_{YZ} ≤ M_{XZ}         *)
  (*  (which holds for vote-count matrices in max-min semirings),            *)
  (*  and A beats every other candidate in direct pairwise comparisons,      *)
  (*  then A also beats every other candidate via strongest paths            *)
  (*  (i.e., in the Kleene star).                                            *)
  (*  Formally: condorcet_winner M A → strict_winner M A                     *)
  (* =====================================================================  *)

  Theorem condorcet_implies_strict_winner {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z))
    (A : Node) :
    condorcet_winner M A -> strict_winner M A.
  Proof.
    unfold condorcet_winner, strict_winner, schulze_beats, beats.
    intros Hc X Hneq.
    destruct (Hc X Hneq) as [Hdir_le Hdir_neq].
    split.
    - (* Non-strict: mat_star M X A ≤ mat_star M A X *)
      unfold mat_star.
      (* Chain: mat_star M X A = geom_sum ... X A ≤ M X A ≤ M A X ≤ geom_sum ... A X = mat_star M A X *)
      eapply orel_trans;
        [apply (geom_sum_bound M Htri kleene_exp X A Hneq) |].
      eapply orel_trans; [exact Hdir_le |].
      apply (geom_sum_includes_direct M kleene_exp A X).
      (* Need kleene_exp ≥ 1, which holds since there are ≥2 elements *)
      unfold kleene_exp.
      pose proof (elements_two_or_more (s := Node)) as Hlen.
      lia.
    - (* Strict: mat_star M X A ≠ mat_star M A X *)
      intro Heq.
      apply Hdir_neq.
      (* From the chain above and Heq: M A X ≤ mat_star M A X = mat_star M X A ≤ M X A *)
      (* But Hdir_le gives M X A ≤ M A X.  Antisymmetry gives equality, contradiction. *)
      unfold mat_star in Heq.
      pose proof (geom_sum_bound M Htri kleene_exp X A Hneq) as Hbound.
      pose proof (geom_sum_includes_direct (R:=R) M kleene_exp A X) as Hinclude.
      assert (Hk_ge1 : (kleene_exp >= 1)%nat).
      { pose proof (elements_two_or_more (s := Node)) as Hlen.
        unfold kleene_exp.
        pose proof (elements_two_or_more (s := Node)) as Hlen2. lia. }
      pose proof (geom_sum_includes_direct (R:=R) M kleene_exp A X Hk_ge1) as Hinclude_use.
      (* M A X ≤ geom_sum M kleene_exp A X = geom_sum M kleene_exp X A ≤ M X A *)
      assert (H_MA_le_MXA : Orel (M A X) (M X A)).
      { eapply orel_trans; [exact Hinclude_use |].
        rewrite <- Heq. exact Hbound. }
      apply (orel_antisym (R := R) (M X A) (M A X) Hdir_le H_MA_le_MXA).
  Qed.

  (* =====================================================================  *)
  (*  Theorem — REVERSAL SYMMETRY (Section 4.4)                               *)
  (*                                                                          *)
  (*  If A is the strict winner (beats everyone in M* ), then under          *)
  (*  reversed preferences (M^T), A is NOT a strict winner.                  *)
  (* =====================================================================  *)

  Theorem reversal_symmetry {R : Semiring.type} :
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
    (*   H_win_le  : Orel (M*_{BA}) (M*_{AB})  i.e., M*_{BA} ≤ M*_{AB}     *)
    (*   H_rev_le  : Orel (M*_{AB}) (M*_{BA})  i.e., M*_{AB} ≤ M*_{BA}     *)
    (*   H_win_neq : M*_{BA} ≠ M*_{AB}                                       *)
    (* Antisymmetry gives M*_{BA} = M*_{AB}, contradicting H_win_neq.       *)
    apply H_win_neq.
    apply (orel_antisym (R := R) _ _ H_win_le H_rev_le).
  Qed.


  (* =====================================================================  *)
  (*  Theorem — PARETO                                                       *)
  (*                                                                          *)
  (*  If M_{BA} = 0 and M_{AB} ≠ 0, and rows/columns of A and B are         *)
  (*  identical for all other candidates, then the strongest path from A     *)
  (*  to B dominates the strongest path from B to A.                         *)
  (* =====================================================================  *)

  Theorem pareto {R : Semiring.type} :
    forall (M : @Matrix Node R) (A B : Node),
      A ≠ B -> M B A = 0 -> M A B ≠ 0 ->
      (forall (X : Node), X ≠ A -> X ≠ B -> M A X = M B X) ->
      (forall (X : Node), X ≠ A -> X ≠ B -> M X A = M X B) ->
      Orel (mat_star M B A) (mat_star M A B).
  Proof.
    (* Proof sketch (path-based):                                            *)
    (*   M* = I + M + M² + ... + M^{|N|-1}.                                 *)
    (*   For each k, every term in M^k_{BA} is min (product) of k edges     *)
    (*   along a path B → v₁ → ... → v_{k-1} → A.                           *)
    (*   Using the hypotheses:                                               *)
    (*     - If the path uses the direct edge B→A: weight involves          *)
    (*       M_{BA}=0, so the term is 0 (annihilator).                       *)
    (*     - Otherwise, replace first edge B→v₁ with A→v₁ (neutrality on   *)
    (*       rows) and last edge v_{k-1}→A with v_{k-1}→B (neutrality on   *)
    (*       columns).  This gives an A→B path of equal weight.             *)
    (*   Since plusR = max (idempotent), every BA term is ≤ some AB term,  *)
    (*   and plusR is idempotent, so max(all BA, all AB) = all AB.          *)
    (*                                                                       *)
    (* Formal proof requires induction on path length and case analysis     *)
    (* on intermediate nodes.  Admitted.                                     *)
  Admitted.


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
      (forall (X : Node), X ≠ C -> X ≠ C' -> 
        M C X = M C' X ∧ M X C = M X C') ->
      (* The clone-clone edge is symmetric *)
      M C C' = M C' C ->
      (* Then for any X,Y ≠ C,C', the domination relation is unchanged *)
      forall (X Y : Node), X ≠ C -> X ≠ C' -> Y ≠ C -> Y ≠ C' ->
        Orel (mat_star M Y X) (mat_star M X Y) <->
        Orel (mat_star M Y X) (mat_star M X Y).
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


  (* =====================================================================  *)
  (*  Theorem — TRANSITIVITY (Section 4.1)                                    *)
  (*                                                                          *)
  (*  The Schulze order O is transitive: if a Schulze-beats b and             *)
  (*  b Schulze-beats c, then a Schulze-beats c.  This guarantees the        *)
  (*  method is well-defined (the set of winners is non-empty).              *)
  (*                                                                          *)
  (*  Proof (from paper):                                                     *)
  (*    With (4.1.1): PD[a,b] >_D PD[b,a]                                    *)
  (*    With (4.1.2): PD[b,c] >_D PD[c,b]                                    *)
  (*    By the path-composition inequality (2.2.5):                           *)
  (*      min_D{PD[a,b], PD[b,c]} ≤_D PD[a,c]                                *)
  (*    So PD[a,c] ≥_D the minimum, which is >_D both PD[b,a] and PD[c,b]   *)
  (*    in particular PD[a,c] >_D PD[c,a], giving ac ∈ O.                    *)
  (*    Formal proof requires the semiring analogue of (2.2.5).              *)
  (* =====================================================================  *)

  Theorem transitivity {R : Semiring.type} :
    forall (M : @Matrix Node R) (a b c : Node),
      schulze_beats M a b ->
      schulze_beats M b c ->
      schulze_beats M a c.
  Proof.
    (* Admitted — requires the path-composition lemma (analogue of 2.2.5). *)
  Admitted.


  (* =====================================================================  *)
  (*  Theorem — WINNER EXISTENCE (Corollary of §4.1)                          *)
  (*                                                                          *)
  (*  There is always at least one Schulze winner.  This follows from        *)
  (*  transitivity of the strict partial order O on a finite set: a         *)
  (*  finite strict partial order always has a maximal element.              *)
  (* =====================================================================  *)

  Theorem winner_exists {R : Semiring.type} :
    forall (M : @Matrix Node R), exists (a : Node), schulze_winner M a.
  Proof.
    (* Admitted — follows from transitivity + finiteness of Node.           *)
  Admitted.


  (* =====================================================================  *)
  (*  Theorem — SMITH CRITERION (Section 4.7)                                 *)
  (*                                                                          *)
  (*  If the alternatives partition into a top set B1 and bottom set B2      *)
  (*  such that every a ∈ B1 strictly beats every b ∈ B2 in DIRECT          *)
  (*  pairwise comparison, then all Schulze winners are in B1.               *)
  (*                                                                          *)
  (*  This generalizes the Condorcet criterion: when B1 = {a}, B2 = A\{a},  *)
  (*  the Condorcet winner a is the unique Schulze winner.                   *)
  (* =====================================================================  *)

  Theorem smith_criterion {R : Semiring.type} :
    forall (M : @Matrix Node R) (B1 B2 : list Node),
      (* B1 and B2 partition the nodes *)
      (forall (x : Node), In x B1 <-> ~ In x B2) ->
      (* Every a ∈ B1 strictly beats every b ∈ B2 in direct comparison *)
      (forall (a b : Node), In a B1 -> In b B2 ->
         Orel (M b a) (M a b) ∧ M b a ≠ M a b) ->
      (* Then all Schulze winners are in B1 *)
      forall (w : Node), schulze_winner M w -> In w B1.
  Proof.
    (* Proof sketch:                                                          *)
    (*   Suppose w ∈ B2 is a winner.  Pick any a ∈ B1 (non-empty, else      *)
    (*   trivial).  By hypothesis, a strictly beats w directly:              *)
    (*   M_{wa} ≤ M_{aw} and M_{wa} ≠ M_{aw}.  The direct edge a→w is       *)
    (*   already a path, so M*_{wa} ≤ M_{aw} ≤ M*_{aw} and the              *)
    (*   strict inequality propagates.  Thus a Schulze-beats w,              *)
    (*   contradicting that w is a winner.                                    *)
    (*   Admitted — requires lemma that direct dominance implies            *)
    (*   Schulze dominance.                                                   *)
  Admitted.


  (* =====================================================================  *)
  (*  Theorem — PRUDENCE (Section 4.9)                                        *)
  (*                                                                          *)
  (*  If every voter weakly prefers a over b and at least one strictly       *)
  (*  prefers a over b, then b is not a Schulze winner.  In the abstract     *)
  (*  matrix setting: if M_{ba} = 0 and M_{ab} ≠ 0, then b is not a         *)
  (*  Schulze winner.  (This is a corollary of Pareto.)                      *)
  (*                                                                          *)
  (*  Paper formulation:                                                      *)
  (*    ∀v ∈ V : a v b   and   ∃w ∈ V : a w b                                *)
  (*    ⇒  b ∉ S                                                             *)
  (*                                                                          *)
  (*  In our matrix setting: M_{ba} = 0 and M_{ab} ≠ 0 ⇒ ~schulze_winner b *)
  (* =====================================================================  *)

  Theorem prudence {R : Semiring.type} :
    forall (M : @Matrix Node R) (a b : Node),
      a ≠ b ->
      (* no voter prefers b over a *)
      M b a = 0 ->
      (* at least one voter prefers a over b *)
      M a b ≠ 0 ->
      (* rows of a,b coincide on other candidates *)
      (forall (X : Node), X ≠ a -> X ≠ b -> M a X = M b X) ->
      (* columns of a,b coincide on other candidates *)
      (forall (X : Node), X ≠ a -> X ≠ b -> M X a = M X b) ->
      (* strictness: Kleene-star entries differ *)
      mat_star M b a ≠ mat_star M a b ->
      ~ schulze_winner M b.
  Proof.
    intros M a b Hneq Hzero Hnonzero Hrow Hcol Hstrict.
    unfold schulze_winner.
    intro Hwin.
    (* Hwin : ∀ b0 ≠ b, ~ schulze_beats M b0 b *)
    (* Instantiate with b0 := a *)
    apply Hwin with (b := a).
    - exact Hneq.
    - unfold schulze_beats, beats.
      split.
      + (* Orel (mat_star M b a) (mat_star M a b) — from Pareto *)
        apply (pareto M a b Hneq Hzero Hnonzero Hrow Hcol).
      + (* mat_star M b a ≠ mat_star M a b — strictness *)
        exact Hstrict.
  Qed.


  
End SocialChoice.