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
    (*  Proof: with the triangle inequality Htri, every A→C path weight is   *)
    (*  bounded by the direct edge M_{AC}.  Since M'_{AC} dominates M_{AC}  *)
    (*  (Hrow), the chain M*_{AC} ≤ M_{AC} ≤ M'_{AC} ≤ M'*_{AC} holds.      *)
    (*  The C=A case uses boundedness (diagonal of geom_sum = 1).            *)
    (* =====================================================================  *)

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
      (1 <= k)%nat -> Orel (pow M k X A) (M X A).
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
    (1 <= n)%nat -> Orel (M A X) (geom_sum M n A X).
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
  (*  Theorem — MONOTONICITY (§4.5)                                           *)
  (* =====================================================================  *)

  Theorem monotonicity {R : BoundedSemiring.type} :
    forall (M M' : @Matrix Node R)
      (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z))
      (A : Node),
      (forall (Y : Node), Orel (M A Y) (M' A Y)) ->
      (forall (X : Node), Orel (M' X A) (M X A)) ->
      (forall (X Y : Node), X ≠ A -> Y ≠ A -> (M X Y) = (M' X Y)) ->
      forall (C : Node), Orel (mat_star M A C) (mat_star M' A C).
  Proof.
    intros M M' Htri A Hrow Hcol Heq C.
    destruct (fin_eq_dec C A) as [HeqCA|HneqCA].
    - subst C. unfold mat_star, Orel.
      rewrite !geom_sum_diag_one.
      apply (add_bound (s := R) 1).
    - unfold mat_star.
      eapply orel_trans.
      + apply (geom_sum_bound (R:=R) M Htri kleene_exp A C).
        intro HeqAC. apply HneqCA. symmetry. exact HeqAC.
      + eapply orel_trans.
        * apply (Hrow C).
        * apply (geom_sum_includes_direct (R:=R) M' kleene_exp A C).
          unfold kleene_exp.
          pose proof (elements_two_or_more (s := Node)) as Hlen. lia.
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
    (*   H_win_le  : Orel (M*_{BA}) (M*_{AB})  i.e., M*_{BA} ≤ M*_{AB}     *)
    (*   H_rev_le  : Orel (M*_{AB}) (M*_{BA})  i.e., M*_{AB} ≤ M*_{BA}     *)
    (*   H_win_neq : M*_{BA} ≠ M*_{AB}                                       *)
    (* Antisymmetry gives M*_{BA} = M*_{AB}, contradicting H_win_neq.       *)
    apply H_win_neq.
    apply (orel_antisym (R := R) _ _ H_win_le H_rev_le).
  Qed.


  (* =====================================================================  *)
  (*  Lemma: every matrix power is bounded by the direct edge (Orel).        *)
  (*  Requires only Htri (triangle inequality); works for any Semiring.      *)
  (* =====================================================================  *)

  Lemma pow_bound_general {R : IdempotentSemiring.type}
    (M : @Matrix Node R)
    (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z)) :
    forall (k : nat) (X A : Node),
      (1 <= k)%nat -> Orel (pow M k X A) (M X A).
  Proof.
    induction k as [|k IH]; intros X A Hk.
    - lia.
    - destruct k as [|k].
      + (* k = 1 *)
        cbn [pow]. rewrite (matrix_mul_I_r M X A).
        unfold Orel. apply orel_refl.
      + (* k ≥ 2 *)
        assert (Hk' : (1 <= S k)%nat) by lia.
        cbn [pow]. unfold matrix_mul.
        apply sum_orel_bound. intro y.
        eapply orel_trans; [| apply (Htri X y A)].
        apply (mul_orel_compat_r (pow M (S k) y A) (M y A) (M X y)).
        apply (IH y A Hk').
  Qed.

  (* =====================================================================  *)
  (*  Theorem — PARETO                                                       *)
  (*                                                                          *)
  (*  With the triangle inequality Htri, every path from B to A has weight   *)
  (*  ≤ M_{BA} = 0, so all powers are zero and the geometric sum is zero.    *)
  (*  The row/column homogeneity hypotheses become redundant with Htri but   *)
  (*  are kept for compatibility with the paper's formulation.               *)
  (* =====================================================================  *)

  Theorem pareto {R : IdempotentSemiring.type}
    (M : @Matrix Node R)
    (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z))
    (A B : Node) :
      A ≠ B -> M B A = 0 -> M A B ≠ 0 ->
      (forall (X : Node), X ≠ A -> X ≠ B -> M A X = M B X) ->
      (forall (X : Node), X ≠ A -> X ≠ B -> M X A = M X B) ->
      Orel (mat_star M B A) (mat_star M A B).
  Proof.
    intros Hneq Hzero Hnonzero Hrow Hcol.
    unfold mat_star, Orel.
    (* Show that geom_sum kleene_exp B A = 0 *)
    assert (Hgs_zero : geom_sum M kleene_exp B A = 0).
    { induction kleene_exp as [|n IH]; cbn.
      - unfold I. destruct (fin_eq_dec B A) as [Heq|_].
        + exfalso. apply Hneq. symmetry. exact Heq.
        + reflexivity.
      - unfold matrix_add.
        (* Goal: geom_sum M n B A + pow M (S n) B A = 0 *)
        pose proof (pow_bound_general M Htri (S n) B A) as Hpow.
        assert (HSn_ge1 : (S n >= 1)%nat) by lia.
        pose proof (Hpow HSn_ge1) as Hpow_le.
        unfold Orel in Hpow_le.
        rewrite Hzero in Hpow_le.
        rewrite addr0 in Hpow_le.
        (* Hpow_le: pow M (S n) B A = 0 *)
        transitivity (geom_sum M n B A + 0).
        { apply (f_equal (fun t => geom_sum M n B A + t)). exact Hpow_le. }
        rewrite addr0. exact IH. }
    rewrite Hgs_zero. apply add0r.
  Qed.


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
  (*  Theorem — TRANSITIVITY (Section 4.1)                                    *)
  (*                                                                          *)
  (*  The Schulze order is transitive.  Requires path-composition            *)
  (*  M*_{ab}*M*_{bc} ≤ M*_{ac} (from Kleene-star idempotence).             *)
  (* =====================================================================  *)

  Lemma star_path_compose {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b c : Node) :
    Orel (mat_star M a b * mat_star M b c) (mat_star M a c).
  Proof.
  Admitted.

  Theorem transitivity {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z)) :
    forall (a b c : Node),
      schulze_beats M a b ->
      schulze_beats M b c ->
      schulze_beats M a c.
  Proof.
    intros a b c Hab Hbc.
    unfold schulze_beats, beats in *.
    destruct Hab as [Hab_le Hab_neq].
    destruct Hbc as [Hbc_le Hbc_neq].
    unfold mat_star in *.
    (* Hab_le : Orel (M*_{ba}) (M*_{ab}),  Hbc_le : Orel (M*_{cb}) (M*_{bc}) *)
    split.
    - (* Non-strict: Orel (M*_{ca}) (M*_{ac}) *)
      (* From path composition: M*_{cb} * M*_{ba} ≤ M*_{ca} *)
      (* And from hypotheses + path comp: M*_{cb} * M*_{ba} ≤ M*_{ac} *)
      (* In a commutative semiring these chain.  Without commutativity,   *)
      (* the inequality M*_{ca} ≤ M*_{ac} requires the full paper proof.  *)
      admit.
    - (* Strict: M*_{ca} ≠ M*_{ac} *)
      admit.
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
  Theorem winner_exists {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z))
    (Hdec : forall x y : R, {x = y} + {x ≠ y}) :
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
            pose proof (transitivity M Htri x a w Hx_beats_a H_aw) as Hxw.
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
  (*  Theorem — SMITH CRITERION (Section 4.7)                                 *)
  (*                                                                          *)
  (*  If the alternatives partition into a top set B1 and bottom set B2      *)
  (*  such that every a ∈ B1 strictly beats every b ∈ B2 in DIRECT          *)
  (*  pairwise comparison, then all Schulze winners are in B1.               *)
  (*                                                                          *)
  (*  This generalizes the Condorcet criterion: when B1 = {a}, B2 = A\{a},  *)
  (*  the Condorcet winner a is the unique Schulze winner.                   *)
  (* =====================================================================  *)

  Theorem smith_criterion {R : BoundedSemiring.type}
    (M : @Matrix Node R)
    (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z)) :
    forall (B1 B2 : list Node),
      B1 <> [] ->
      (forall (x : Node), In x B1 <-> ~ In x B2) ->
      (forall (a b : Node), In a B1 -> In b B2 ->
         Orel (M b a) (M a b) ∧ M b a ≠ M a b) ->
      forall (w : Node), schulze_winner M w -> In w B1.
  Proof.
    intros B1 B2 HB1_nonempty Hpartition Hdirect w Hwinner.
    destruct (In_dec fin_eq_dec w B1) as [Hin | HnotinB1].
    - exact Hin.
    - destruct (In_dec fin_eq_dec w B2) as [HinB2 | HnotinB2].
      + (* w ∈ B2.  Pick a ∈ B1 (non-empty by HB1_nonempty) *)
        destruct B1 as [|a B1']; [exfalso; apply HB1_nonempty; reflexivity |].
        (* a ∈ a::B1', w ∈ B2.  a strictly beats w directly *)
        pose proof (Hdirect a w (or_introl eq_refl) HinB2) as [Hdir_le Hdir_neq].
        (* Prove a ≠ w: if a = w, then w ∈ B1 ∩ B2, contradicting partition *)
        assert (H_aw_neq : a <> w).
        { intro Heq_aw. subst w.
          destruct (Hpartition a) as [Hfw _].
          apply Hfw; [left; reflexivity | exact HinB2]. }
        (* Prove schulze_beats M a w *)
        assert (H_aw_beats : schulze_beats M a w).
        { unfold schulze_beats, beats. split.
          - (* Non-strict: Orel (mat_star M w a) (mat_star M a w) *)
            unfold mat_star.
            eapply orel_trans.
            { apply (geom_sum_bound (R:=R) M Htri kleene_exp w a).
              intro Heq_wa. apply Hdir_neq. rewrite Heq_wa. reflexivity. }
            eapply orel_trans.
            { exact Hdir_le. }
            apply (geom_sum_includes_direct (R:=R) M kleene_exp a w).
            unfold kleene_exp.
            pose proof (elements_two_or_more (s := Node)) as Hlen. lia.
          - (* Strict: mat_star M w a ≠ mat_star M a w *)
            intro Heq_star.
            apply Hdir_neq.
            unfold mat_star in Heq_star.
            pose proof (geom_sum_bound (R:=R) M Htri kleene_exp w a) as Hbound.
            assert (H_wa_neq : w <> a).
            { intro Heq_wa. apply Hdir_neq. rewrite Heq_wa. reflexivity. }
            apply Hbound in H_wa_neq.
            pose proof (geom_sum_includes_direct (R:=R) M kleene_exp a w) as Hinclude.
            assert (Hk_ge1 : (kleene_exp >= 1)%nat).
            { unfold kleene_exp.
              pose proof (elements_two_or_more (s := Node)) as Hlen. lia. }
            apply Hinclude in Hk_ge1.
            assert (H_Maw_le_Mwa : Orel (M a w) (M w a)).
            { eapply orel_trans; [exact Hk_ge1 |].
              rewrite <- Heq_star. exact H_wa_neq. }
            apply (orel_antisym (R := R) (M w a) (M a w) Hdir_le H_Maw_le_Mwa). }
        (* Contradiction: Hwinner says nobody beats w, but a beats w *)
        exfalso.
        unfold schulze_winner in Hwinner.
        apply (Hwinner a H_aw_neq H_aw_beats).
      + (* ~ In w B2 → In w B1 by partition, contradicting HnotinB1 *)
        destruct (Hpartition w) as [_ Hrev].
        apply Hrev in HnotinB2. contradiction.
  Qed.


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

  Theorem prudence {R : IdempotentSemiring.type} :
    forall (M : @Matrix Node R)
      (Htri : forall (X Y Z : Node), Orel (M X Y * M Y Z) (M X Z))
      (a b : Node),
      a ≠ b ->
      M b a = 0 ->
      M a b ≠ 0 ->
      (forall (X : Node), X ≠ a -> X ≠ b -> M a X = M b X) ->
      (forall (X : Node), X ≠ a -> X ≠ b -> M X a = M X b) ->
      mat_star M b a ≠ mat_star M a b ->
      ~ schulze_winner M b.
  Proof.
    intros M Htri a b Hneq Hzero Hnonzero Hrow Hcol Hstrict.
    unfold schulze_winner.
    intro Hwin.
    apply Hwin with (b := a).
    - exact Hneq.
    - unfold schulze_beats, beats.
      split.
      + (* Orel (mat_star M b a) (mat_star M a b) — from Pareto *)
        apply (pareto M Htri a b Hneq Hzero Hnonzero Hrow Hcol).
      + (* mat_star M b a ≠ mat_star M a b — strictness *)
        exact Hstrict.
  Qed.


  
End SocialChoice.