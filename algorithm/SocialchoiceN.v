From Stdlib Require Import List Utf8 Lia Wf_nat.
From Semiring Require Import PathN MatN OrelN 
  SemimoduleN Structures.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ======================================================================= *)
(*  Social Choice — Schulze method definitions and theorems                  *)
(*                                                                          *)
(*  Status:                                                                 *)
(*    schulze_trans                    — Qed                               *)
(*    condorcet_implies_strict_winner  — Qed                               *)
(*    monotonicity                     — Qed                               *)
(*    smith_criterion                  — Qed                               *)
(*    pareto_weaker                    — Qed                               *)
(*    pareto_stronger                  — Qed                               *)
(*    pareto_stronger_iff              — Qed                               *)
(*    prudence          (§4.9)         — Qed                               *)
(*    minmax_beats      (§4.8)         — Qed                               *)
(*    reversal_symmetry_O (4.4.2)      — Qed                               *)
(*                                                                          *)
(*  WHICH VARIANT TO USE.  Four theorems below — schulze_trans,             *)
(*  winner_exists, condorcet_implies_strict_winner, smith_criterion —       *)
(*  assume H_pair_sum_one (M i j + M j i = 1).  Combined with a total       *)
(*  order that forces one direction of every pair to be the top, i.e. a     *)
(*  STRICT BALLOT such as A > B > C; it does not hold of a profile with     *)
(*  genuine disagreement.  Prefer the [_weaker] variants, which are the     *)
(*  general statements.  For a carrier built by NormalizedOrder their       *)
(*  remaining algebraic hypotheses are discharged outright — see            *)
(*  SchulzeOnNT.v, where transitivity and winner existence come out with    *)
(*  no hypotheses at all.                                                    *)
(*    schulze_beats_asym, strict_winner_unique, condorcet_winner_unique,   *)
(*    strict_winner_is_schulze_winner  — Qed                               *)
(*    reversal_symmetry                — Qed                               *)
(*    winner_exists                    — Qed                               *)
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


  (** * Transitivity of Schulze beats — meet-semiring proof

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

  (** A link is a path of length one. *)
  Lemma link_le_mat_star {R : BoundedSemiring.type}
    (M : @Matrix Node R) (x y : Node) : M x y ≤ mat_star M x y.
  Proof.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    pose proof (@pow_le_mat_star R M 1 x y) as h.
    unfold kleene_exp in h. specialize (h ltac:(nia)).
    cbn [pow] in h. rewrite matrix_mul_I_r in h. exact h.
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


  (** * Winner existence — meet-semiring version

      Same statement as [winner_exists] but using [schulze_trans_weaker]
      (which requires [H_meet_lower_bound]) instead of [schulze_trans]
      (which requires [H_pair_sum_one]).

      The proof is identical to [winner_exists]: a Schulze winner is a
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
    assert (Hmax : forall (l : list Node), l <> [] -> exists w,
      In w l /\ (forall b, In b l -> b <> w -> ~ schulze_beats M b w)).
    { intro l. induction l as [|a l IH]; intros Hnonempty.
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
              H_total_order H_meet_lower_bound
              M x a w Hx_beats_a H_aw) as Hxw.
            destruct (fin_eq_dec x w) as [Heq_xw | Hneq_xw].
            { subst x. apply (schulze_beats_irrefl M w). exact Hxw. }
            { apply (Hw_undefeated x Hx_in_tail Hneq_xw). exact Hxw. }
          * exists w. split.
            { right. exact Hin_w. }
            intros x Hx_in Hx_neq_w.
            inversion Hx_in as [Heq_a | Hx_in_tail].
            { subst x. exact H_not_aw. }
            { apply (Hw_undefeated x Hx_in_tail Hx_neq_w). } }
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

 

  (** * Monotonicity (Section 4.2 of the Schulze paper)

      If we strengthen candidate [A] — increasing [A]'s wins over other
      candidates and decreasing other candidates' wins over [A], while
      leaving all other pairwise comparisons unchanged — then [A]'s
      Kleene-star strength to any candidate [C] does not decrease:
        mat_star M A C ≤ mat_star M' A C.

      Hypotheses:
        [Hrow]:  M A Y  ≤ M' A Y   (A's outgoing edges increase)
        [Hcol]:  M' X A ≤ M X A    (A's incoming edges decrease)
        [Heq]:   M X Y  = M' X Y   for X≠A, Y≠A (everything else unchanged)
  *)
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
  (*  Version 1 — pareto_weaker (weaker form):  a ≻ᵥ b ∀v  →  a ≽ b    *)
  (*                                                                      *)
  (*  If every voter strictly prefers A over B, then A is at least as    *)
  (*  strong as B in the Schulze ranking: mat_star M B A ≤ mat_star M A B.*)
  (*                                                                      *)
  (*  The stronger form (strict <) is [pareto_stronger] below; it needs   *)
  (*  two extra hypotheses, see the comment there.                        *)
  (*                                                                      *)
  (*  Hypotheses:                                                          *)
  (*    A ≠ B            — distinct candidates                            *)
  (*    M B A = 0         — zero voters prefer B over A                   *)
  (*    M B X ≤ M A X    — ballot transitivity: viewers who have B≻X      *)
  (*                        also have A≻X (since A≻B)                     *)
  (*    M X A ≤ M X B    — ballot transitivity: viewers who have X≻A      *)
  (*                        also have X≻B (since A≻B)                     *)
  (*    M i i = 1         — diagonal is the multiplicative identity       *)
  (*                                                                      *)
  

  Theorem pareto_weaker {R : BoundedSemiring.type}
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

  (** [x < y] and [y ≤ z] give [x < z]. *)
  Lemma orel_lt_le_trans {R : CommutativeMonoid.type} (x y z : R) :
    x < y -> y ≤ z -> x < z.
  Proof.
    intros [Hxy_le Hxy_neq] Hyz. split.
    - exact (orel_trans _ _ _ Hxy_le Hyz).
    - intro Heq. apply Hxy_neq.
      apply orel_antisym; [exact Hxy_le | rewrite Heq; exact Hyz].
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
      cbn [all_paths_klength] in Hin.
      pose proof Hin as Hin_shape.
      apply (append_node_in_paths_In M x
        (List.flat_map (fun z => all_paths_klength elements M k z A) elements) p) in Hin.
      destruct Hin as [y [q [Hp Hq_lf]]].
      apply append_node_in_paths_shape in Hin_shape.
      destruct Hin_shape as (y' & q' & Hp' & Hsrc_x & Hsrc_y' & Hq_ne).
      subst p.
      inversion Hp' as [[Heq_hd Heq_tl]].
      inversion Heq_hd. subst y' q'. clear Hp'.
      apply in_flat_map in Hq_lf. destruct Hq_lf as [z [Hz_el Hq_in]].
      pose proof Hq_in as Hq_in_copy.
      apply non_empty_paths_in_kpath in Hq_in as (_ & Hsrc_z & _).
      assert (Hy_eq_z : y = z). { eapply source_inj; eassumption. }
      subst y.
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
        destruct (IH z q Hneq_zA Hq_in_copy) as [Hq_le Hq_top].
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
    rewrite (matrix_path_equation n M B A).
    unfold sum_all_rvalues, get_all_rvalues.
    apply (fold_right_lt_bound Htotal); [exact Hpos |].
    intros x Hx. apply in_map_iff in Hx. destruct Hx as [path [Hm Hin]].
    destruct path as [[s d] p]. cbn in Hm. subst x.
    unfold construct_all_paths in Hin.
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hin']].
    inversion Heq. subst s d q. clear Heq.
    exact (path_BA_measure_lt M A B Htop_trans Hmax Hdiag_one
      Hneq Hne_top n p Hin').
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
    unfold mat_star.
    assert (Hgen : forall k, geom_sum M k B A < M A B).
    { induction k as [|k IHk]; cbn [geom_sum].
      - unfold I.
        destruct (fin_eq_dec B A) as [Heq|_];
          [exfalso; apply Hneq; symmetry; exact Heq | exact Hpos].
      - unfold matrix_add.
        apply (add_lt_bound Htotal); [exact IHk |].
        exact (pow_BA_lt_link M A B Htotal Htop_trans Hmax Hdiag_one
          Hneq Hne_top Hpos (S k)). }
    apply Hgen.
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
    eapply orel_lt_le_trans.
    - exact (mat_star_BA_lt_link M A B Htotal Htop_trans Hmax Hdiag_one
        Hneq Hne_top Hpos).
    - (* M A B ≤ mat_star M A B: the link itself is a path of length one *)
      pose proof (elements_two_or_more (s := Node)) as Hlen.
      pose proof (@pow_le_mat_star R M 1 A B) as h.
      unfold kleene_exp in h. specialize (h ltac:(nia)).
      cbn [pow] in h. rewrite matrix_mul_I_r in h. exact h.
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
    - cbn [all_paths_klength] in Hin.
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
      cbn [measure_of_path].
      destruct (fin_eq_dec x z) as [Hxz|Hxz].
      + (* self-loop of weight 1: the tail is still a path from x to y *)
        subst z. rewrite (Hdiag_one x x eq_refl), mul1r.
        exact (IH x y q Hxy Hq_in_copy).
      + exact (orel_trans _ _ _ (bounded_mul_lower_left _ _) (Hmax x z Hxz)).
  Qed.

  Lemma pow_xy_le_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (n : nat) (x y : Node) : x ≠ y -> pow M n x y ≤ M A B.
  Proof.
    intros Hxy.
    rewrite (matrix_path_equation n M x y).
    unfold sum_all_rvalues, get_all_rvalues.
    apply fold_right_orel_bound.
    intros v Hv. apply in_map_iff in Hv. destruct Hv as [path [Hm Hin]].
    destruct path as [[s d] p]. cbn in Hm. subst v.
    unfold construct_all_paths in Hin.
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hin']].
    inversion Heq. subst s d q. clear Heq.
    exact (path_measure_le_link M A B Hmax Hdiag_one n x y p Hxy Hin').
  Qed.

  Lemma mat_star_le_link {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A B : Node)
    (Hmax : forall X Y, X ≠ Y -> M X Y ≤ M A B)
    (Hdiag_one : forall i j, i = j -> M i j = 1)
    (x y : Node) : x ≠ y -> mat_star M x y ≤ M A B.
  Proof.
    intros Hxy. unfold mat_star.
    assert (Hgen : forall k, geom_sum M k x y ≤ M A B).
    { induction k as [|k IHk]; cbn [geom_sum].
      - unfold I.
        destruct (fin_eq_dec x y) as [Heq|_];
          [congruence | apply zero_is_bottom].
      - unfold matrix_add. apply add_orel_bound; [exact IHk |].
        exact (pow_xy_le_link M A B Hmax Hdiag_one (S k) x y Hxy). }
    apply Hgen.
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
    - pose proof (elements_two_or_more (s := Node)) as Hlen.
      pose proof (@pow_le_mat_star R M 1 A B) as h.
      unfold kleene_exp in h. specialize (h ltac:(nia)).
      cbn [pow] in h. rewrite matrix_mul_I_r in h. exact h.
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
      pose proof (elements_two_or_more (s := Node)) as Hlen.
      pose proof (@pow_le_mat_star R M 1 B A) as h.
      unfold kleene_exp in h. specialize (h ltac:(nia)).
      cbn [pow] in h. rewrite matrix_mul_I_r in h. exact h.
    - intros Hne_top.
      eapply orel_lt_le_trans.
      + exact (mat_star_BA_lt_link M A B Htotal Htop_trans Hmax Hdiag_one
          Hneq Hne_top Hpos).
      + rewrite Hstar_AB. apply bounded_orel_refl.
  Qed.



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
      (generalizes [sum_lt_1_if_all_lt_1] from the fixed bound [1] to an
      arbitrary [c]; only needs totality, not boundedness at [c]). *)
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

  (* Mixed transitivity ([orel_lt_le_trans]) is proved above, with the
     helper lemmas for [pareto_stronger]. *)

  (** * [condorcet_implies_strict_winner], with [H_pair_sum_one] replaced by
      [H_dominance] — every edge *into* the Condorcet winner [A] is strictly
      below every edge *out of* [A], rather than forcing every outgoing edge
      to equal the semiring's top [1].  
  *)
  Theorem condorcet_implies_strict_winner_weaker  {R : BoundedSemiring.type}
    (M : @Matrix Node R) (A : Node)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (H_dominance : forall Z X, Z <> A -> X <> A -> M Z A < M A X) :
    condorcet_winner M A -> strict_winner M A.
  Proof.
    intros Hcw X0 HX0.
    unfold schulze_beats, beats.
    (* Every walk of length n into A, from any w <> A, stays strictly below
       the fixed target margin M A X0. *)
    assert (H_pow_lt : forall n w, w <> A -> pow M n w A < M A X0).
    { induction n as [|n IH]; intros w Hw.
      - (* n = 0: pow M 0 w A = I w A = 0, since w <> A *)
        cbn [pow]. unfold I.
        destruct (fin_eq_dec w A) as [Heq|Hneq]; [congruence|].
        split.
        + apply zero_is_bottom.
        + intro Heq0.
          destruct (H_dominance X0 X0 HX0 HX0) as [Hd_le Hd_ne].
          apply Hd_ne. unfold Orel in Hd_le.
          rewrite <- Heq0 in Hd_le. rewrite addr0 in Hd_le.
          rewrite Hd_le. exact Heq0.
      - (* n = S n: pow M (S n) w A = sum_z M w z * pow M n z A *)
        simpl. unfold matrix_mul.
        apply sum_lt_bound_if_all_lt; [exact H_total_order |].
        intro z.
        destruct (fin_eq_dec z A) as [Heqz|Hneqz].
        + (* z = A: bound via the first factor, M w A < M A X0 directly *)
          subst z.
          apply (orel_lt_trans (M w A * pow M n A A) (M w A) (M A X0)).
          * apply bounded_mul_lower_left.
          * apply H_dominance; assumption.
        + (* z <> A: bound via the second factor, IH gives pow M n z A < M A X0 *)
          apply (orel_lt_trans (M w z * pow M n z A) (pow M n z A) (M A X0)).
          * apply bounded_mul_lower_right.
          * apply IH. exact Hneqz. }
    assert (H_geom_lt : forall n, geom_sum M n X0 A < M A X0).
    { induction n as [|n IH].
      - change (geom_sum M 0 X0 A) with (pow M 0 X0 A).
        apply H_pow_lt. exact HX0.
      - cbn [geom_sum]. unfold matrix_add.
        apply orel_lt_add_lt; [exact H_total_order | exact IH | apply H_pow_lt; exact HX0]. }
    unfold mat_star.
    apply (orel_lt_le_trans (geom_sum M kleene_exp X0 A) (M A X0)
      (geom_sum M kleene_exp A X0)).
    - apply H_geom_lt.
    - apply (geom_sum_includes_direct M kleene_exp A X0).
      pose proof (elements_two_or_more (s := Node)) as Hlen. unfold kleene_exp. nia.
  Qed.


  
  (** [smith_criterion], with the global [H_pair_sum_one] normalization
      replaced by a single shared threshold [c0] separating the two sides
      of the cut, rather than forcing every B1-to-B2 edge to equal the
      literal top [1]. This subsumes the theorem's own per-pair cut
      hypothesis (["forall a b, In a B1 -> In b B2 -> M b a < M a b"]),
      which follows immediately by chaining [M b a < c0 <= M a b] — so it
      is dropped as a separate premise here.
  *)
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
    intros B1 B2 H_B1_nonempty H_partition (c & H_lt & H_ge) w H_winner.
    destruct (in_dec fin_eq_dec w B1) as [Hin|Hnotin_B1]; [exact Hin|].
    destruct (in_dec fin_eq_dec w B2) as [Hw_B2|Hnotin_B2];
      [| apply H_partition in Hnotin_B2; contradiction].
    exfalso.
    destruct B1 as [|a0 B1']; [congruence|].
    assert (Ha0_B1 : In a0 (a0 :: B1')) by (left; reflexivity).
    assert (H0_lt_c0 : (0 : R) < c).
    { apply (orel_lt_trans 0 (M w a0) c).
      - apply zero_is_bottom.
      - apply H_lt; assumption. }
    assert (H_pow_lt : forall n b, In b B2 ->
      forall a, In a (a0 :: B1') -> pow M n b a < c).
    { induction n as [|n IH]; intros b Hb a Ha.
      - (* n = 0: pow M 0 b a = I b a. b <> a since b in B2, a in B1. *)
        cbn [pow]. unfold I.
        destruct (fin_eq_dec b a) as [Heq|Hneq].
        + subst a. exfalso. apply (proj1 (H_partition b) Ha). exact Hb.
        + exact H0_lt_c0.
      - (* n = S n: pow M (S n) b a = sum_z M b z * pow M n z a *)
        simpl. unfold matrix_mul.
        apply sum_lt_bound_if_all_lt; [exact H_total_order |].
        intro z.
        destruct (in_dec fin_eq_dec z (a0 :: B1')) as [HzB1|HzB1'].
        + (* z in B1: bound via the first factor, M b z < c0 directly *)
          apply (orel_lt_trans (M b z * pow M n z a) (M b z) c).
          * apply bounded_mul_lower_left.
          * apply H_lt; assumption.
        + (* z in B2: bound via the second factor, IH gives pow M n z a < c0 *)
          assert (HzB2 : In z B2).
          { destruct (in_dec fin_eq_dec z B2) as [Hz|Hz]; [exact Hz|].
            exfalso. apply HzB1'. apply (proj2 (H_partition z)). exact Hz. }
          apply (orel_lt_trans (M b z * pow M n z a) (pow M n z a) c).
          * apply bounded_mul_lower_right.
          * apply IH; assumption. }
    assert (H_geom_lt : forall n, geom_sum M n w a0 < c).
    { induction n as [|n IH].
      - change (geom_sum M 0 w a0) with (pow M 0 w a0).
        apply H_pow_lt; assumption.
      - cbn [geom_sum]. unfold matrix_add.
        apply orel_lt_add_lt; [exact H_total_order | exact IH | apply H_pow_lt; assumption]. }
    assert (H_star_lt : mat_star M w a0 < mat_star M a0 w).
    { unfold mat_star.
      apply (orel_lt_le_trans (geom_sum M kleene_exp w a0) c (geom_sum M kleene_exp a0 w)).
      - apply H_geom_lt.
      - apply (orel_trans c (M a0 w) (geom_sum M kleene_exp a0 w)).
        + apply H_ge; assumption.
        + apply (geom_sum_includes_direct M kleene_exp a0 w).
          pose proof (elements_two_or_more (s := Node)) as Hlen. unfold kleene_exp. nia. }
    assert (H_a0_ne_w : a0 <> w).
    { intro Heq. subst w. apply (proj1 (H_partition a0) Ha0_B1). exact Hw_B2. }
    apply (H_winner a0 H_a0_ne_w).
    unfold schulze_beats, beats. exact H_star_lt.
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
      the link itself. *)
  Theorem prudence_local {R : BoundedSemiring.type}
    (M : @Matrix Node R) (a b : Node)
    (* Htotal and Hmeet are both satisfied by max-min semiring 
    but not in general *)
    (Htotal : forall x y : R, x + y = x \/ x + y = y)
    (Hmeet : forall x y : R, x ≤ y -> x * y = x /\ y * x = x) :
    a ≠ b -> M a b * mat_star M b a < M a b -> schulze_beats M a b.
  Proof.
    intros Hab Hlam.
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
    unfold schulze_beats, beats.
    apply (orel_lt_le_trans (mat_star M b a) (M a b) (mat_star M a b)).
    - split; [exact Hstar_le | exact Hstar_ne].
    - apply link_le_mat_star.
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
    apply (prudence_local M a b Htotal Hmeet Hab).
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
    - cbn [all_paths_klength] in Hin.
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
      cbn [measure_of_path].
      destruct (B z) eqn:Hz.
      + (* the head edge already crosses the boundary *)
        exact (orel_trans _ _ _ (bounded_mul_lower_left _ _)
          (cut_in_ge M B x z Hx Hz)).
      + (* still outside [B]: the tail crosses it *)
        exact (orel_trans _ _ _ (bounded_mul_lower_right _ _)
          (IH z y q Hz Hy Hq_in_copy)).
  Qed.

  Lemma pow_into_B_le_cut {R : BoundedSemiring.type}
    (M : @Matrix Node R) (B : Node -> bool) (n : nat) (x y : Node) :
    B x = false -> B y = true -> pow M n x y ≤ cut_in M B.
  Proof.
    intros Hx Hy.
    rewrite (matrix_path_equation n M x y).
    unfold sum_all_rvalues, get_all_rvalues.
    apply fold_right_orel_bound.
    intros v Hv. apply in_map_iff in Hv. destruct Hv as [path [Hm Hin]].
    destruct path as [[s d] p]. cbn in Hm. subst v.
    unfold construct_all_paths in Hin.
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hin']].
    inversion Heq. subst s d q. clear Heq.
    exact (path_into_B_le_cut M B n x y p Hx Hy Hin').
  Qed.

  Lemma mat_star_into_B_le_cut {R : BoundedSemiring.type}
    (M : @Matrix Node R) (B : Node -> bool) (x y : Node) :
    B x = false -> B y = true -> mat_star M x y ≤ cut_in M B.
  Proof.
    intros Hx Hy. unfold mat_star.
    assert (Hgen : forall k, geom_sum M k x y ≤ cut_in M B).
    { induction k as [|k IHk]; cbn [geom_sum].
      - unfold I.
        destruct (fin_eq_dec x y) as [Heq|_];
          [subst y; congruence | apply zero_is_bottom].
      - unfold matrix_add. apply add_orel_bound; [exact IHk |].
        exact (pow_into_B_le_cut M B (S k) x y Hx Hy). }
    apply Hgen.
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

