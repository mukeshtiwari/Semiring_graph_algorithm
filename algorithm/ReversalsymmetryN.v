From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: reversal symmetry (4.4)
    Split out of the former monolithic SocialchoiceN.v. *)

Section ReversalsymmetryN.

  Context {Node : FinType.type}.


  (** * Reversal symmetry (Section 4.4) *)

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

  (** The same statement over a bounded semiring, with no commutativity
      assumption: the meet property supplies it by [mul_comm_of_meet].  This
      is what places the winner-level reversal-symmetry results below at the
      level of selectivity and the meet property rather than above it. *)
  Theorem reversal_symmetry_O_level2 {R : BoundedSemiring.type}
    (H_meet_lower_bound : forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b)
    (M : @Matrix Node R) (a b : Node) :
    schulze_beats M a b <-> schulze_beats (fun i j => M j i) b a.
  Proof.
    unfold schulze_beats, beats.
    rewrite (mat_star_transpose_hyp (mul_comm_of_meet H_meet_lower_bound) M a b),
            (mat_star_transpose_hyp (mul_comm_of_meet H_meet_lower_bound) M b a).
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
    (** [A] beats [B] originally, and beating [B] in the reversed profile is
        exactly being beaten by [B] in the original one *)
    exact (schulze_beats_asym M A B
      (H_win B H_BA)
      (proj2 (reversal_symmetry_O M B A) (H_win_rev B H_BA))).
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

  (** The same theorem over a bounded semiring.  Commutativity is not assumed,
      because the meet property already supplies it (mul_comm_of_meet), so
      Schulze's (4.4.3) needs nothing beyond selectivity and the meet
      property.  In the classification this moves the winner-level reversal
      symmetry down onto the level of the two structural guarantees; only the
      relation-level form (4.4.2, reversal_symmetry_O) genuinely requires
      commutativity, and it is also the only one that does not require
      boundedness. *)
  Theorem reversal_symmetry_S_level2 {R : BoundedSemiring.type}
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
        by (apply (reversal_symmetry_O_level2 H_meet_lower_bound M i j); exact Hj_beats).
      destruct (fin_eq_dec i j) as [Heq|Hne].
      + subst j. exact (schulze_beats_irrefl M i Hij).
      + exact (Hj_old i Hne Hij).
    - intros [j [Hj_old Hj_new]].
      destruct (winner_beats_nonwinner H_total_order Hdec H_meet_lower_bound
                  M j Hj_old) as [i [Hi_old Hi_beats]].
      exists i. split; [exact Hi_old |].
      intro Hi_new.
      assert (Hji : schulze_beats (fun x y => M y x) j i)
        by (apply (reversal_symmetry_O_level2 H_meet_lower_bound M i j); exact Hi_beats).
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

  (** Schulze's (4.4.4) over a bounded semiring, for the same reason. *)
  Theorem reversal_symmetry_all_tied_level2 {R : BoundedSemiring.type}
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
        by (apply (reversal_symmetry_O_level2 H_meet_lower_bound M i x); exact Hi_beats).
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
      exact (Hno x b (proj2 (reversal_symmetry_O_level2 H_meet_lower_bound M x b) Hbeats)).
  Qed.

End ReversalsymmetryN.
