From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ================================================================================= *)
(*  Schulze over a semiring: facts about the Kleene star, powers, and path measures *)
(*  Split out of the former monolithic SocialchoiceN.v.                             *)
(* ================================================================================= *)

Section SchulzeClosureN.

  Context {Node : FinType.type}.


  (* =====================================================================  *)
  (*  Lemma: transpose commutes with Kleene star                            *)
  (*                                                                         *)
  (*  (M^T)* = (M* )^T                                                       *)
  (*  Requires commutative multiplication (mulC) for (M^T)^k = (M^k)^T.     *)
  (* =====================================================================  *)

  (*  Commutativity is needed pointwise only, so we take it as a hypothesis *)
  (*  rather than as a structure.  That matters downstream: on a carrier    *)
  (*  with the meet property commutativity is free (mul_comm_of_meet), so   *)
  (*  the reversal-symmetry results can be stated over a bounded semiring   *)
  (*  with no commutativity assumption of their own.  The named lemmas at   *)
  (*  the end of the block are the CommutativeSemiring instances, unchanged.*)

  Lemma pow_transpose_hyp {R : Semiring.type}
    (Hcomm : forall x y : R, x * y = y * x)
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
        * intro X. apply Hcomm.
      + intro X. rewrite (IH X j). reflexivity.
  Qed.

  Lemma geom_sum_transpose_hyp {R : Semiring.type}
    (Hcomm : forall x y : R, x * y = y * x)
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
      rewrite (pow_transpose_hyp Hcomm M (S n) i j).
      reflexivity.
  Qed.

  Lemma mat_star_transpose_hyp {R : Semiring.type}
    (Hcomm : forall x y : R, x * y = y * x)
    (M : @Matrix Node R) (i j : Node) :
    mat_star (fun x y => M y x) i j = mat_star M j i.
  Proof.
    unfold mat_star. apply geom_sum_transpose_hyp. exact Hcomm.
  Qed.

  Lemma pow_transpose {R : CommutativeSemiring.type}
    (M : @Matrix Node R) (k : nat) (i j : Node) :
    pow (fun x y => M y x) k i j = pow M k j i.
  Proof. apply pow_transpose_hyp. intros x y. apply mulC. Qed.

  Lemma geom_sum_transpose {R : CommutativeSemiring.type}
    (M : @Matrix Node R) (n : nat) (i j : Node) :
    geom_sum (fun x y => M y x) n i j = geom_sum M n j i.
  Proof. apply geom_sum_transpose_hyp. intros x y. apply mulC. Qed.

  Lemma mat_star_transpose {R : CommutativeSemiring.type} :
    forall (M : @Matrix Node R) (i j : Node),
      mat_star (fun x y => M y x) i j = mat_star M j i.
  Proof. intros M i j. apply mat_star_transpose_hyp. intros x y. apply mulC. Qed.

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
    induction (@kleene_exp Node) as [|K IH]; cbn [geom_sum].
    - unfold I. destruct (fin_eq_dec a b);
        [right; left; reflexivity | left; reflexivity].
    - unfold matrix_add.
      destruct (Htotal (geom_sum M K a b) (pow M (S K) a b)) as [Hc | Hc];
        setoid_rewrite Hc.
      + exact IH.
      + apply pow_link_or_extreme; assumption.
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
    pow (matrix_add M (I : @Matrix Node R)) ((@kleene_exp Node) + n) a c =
    pow (matrix_add M (I : @Matrix Node R)) (@kleene_exp Node) a c.
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
    set (K := (@kleene_exp Node)).
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
      rewrite <- (pow_add (matrix_add M (I : @Matrix Node R)) (@kleene_exp Node) (@kleene_exp Node) a c).
      rewrite (pow_MplusI_stable M (@kleene_exp Node) a c).
      reflexivity. }
    rewrite Hpow in Hmul.
    exact Hmul.
  Qed.



  
  


  (** Each power term is ≤ the full mat_star (idempotent addition). *)
  Lemma pow_le_mat_star {R : BoundedSemiring.type} (M : @Matrix Node R) (m : nat) 
    (A B : Node) :
    (m <= (@kleene_exp Node))%nat -> pow M m A B ≤ mat_star M A B.
  Proof.
    unfold mat_star. revert m.
    induction (@kleene_exp Node) as [|K IH]; intros m Hle; cbn [geom_sum].
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
      (@kleene_exp Node)].  The diagonal condition is what makes that stabilisation
      hold. *)
  Lemma pow_le_mat_star_any {R : BoundedSemiring.type}
    (M : @Matrix Node R) (Hdiag : forall u v : Node, u = v -> M u v = 1)
    (k : nat) (a b : Node) :
    pow M k a b ≤ mat_star M a b.
  Proof.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    destruct (Compare_dec.le_lt_dec k (@kleene_exp Node)) as [Hle | Hgt].
    - exact (pow_le_mat_star M k a b Hle).
    - assert (Hstep : pow M k a b ≤ pow (matrix_add M (I : @Matrix Node R)) k a b).
      { apply pow_monotone. intros i j.
        rewrite matrix_add_unfold. apply bounded_plus_upper_left. }
      assert (Heq1 : pow (matrix_add M (I : @Matrix Node R)) k a b
                     = geom_sum M k a b)
        by apply matrix_pow_idempotence_bounded.
      assert (Heq2 : geom_sum M k a b = geom_sum M (@kleene_exp Node) a b).
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

  

  

  (** Retained name for [mul_comm_of_meet]: commutativity is not an assumption
      of the characterisation but a consequence of the right-hand side.  The
      two were proved separately at different times; the proof now lives once,
      in SchulzeOrderN. *)
  Corollary meet_lower_bound_implies_comm {R : BoundedSemiring.type} :
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b) ->
    forall a b : R, a * b = b * a.
  Proof. exact (@mul_comm_of_meet R). Qed.
  

  (* =====================================================================  *)
  (*  Theorem — WINNER EXISTENCE (Corollary of §4.1)                          *)
  (*                                                                          *)
  (*  On a finite set, a strict partial order (transitive + irreflexive)     *)
  (*  always has a maximal element.  schulze_beats is transitive (Qed)       *)
  (*  and irreflexive, so a winner exists.                                   *)
  (* =====================================================================  *)

  (* ===================================================================== *)
  (*  Generic closure bounds.                                               *)
  (*                                                                        *)
  (*  These say how far a value can travel out of a node whose whole row is  *)
  (*  bounded, and are what make a sparse witness matrix computable: a path  *)
  (*  leaving such a node is capped by the row bound, and a path through a   *)
  (*  dead end contributes nothing at all.                                   *)
  (* ===================================================================== *)

  (** If every out-edge of [x] is below [v], then so is every power entry
      out of [x], provided the target is not [x] itself. *)
  Lemma pow_row_bound {R : BoundedSemiring.type} (M : @Matrix Node R)
    (x : Node) (v : R) (Hrow : forall u, M x u ≤ v) :
    forall (k : nat) (y : Node), x <> y -> pow M k x y ≤ v.
  Proof.
    induction k as [|k IH]; intros y Hxy.
    - cbn [pow]. unfold I.
      destruct (fin_eq_dec x y) as [C|_]; [congruence|]. apply zero_is_bottom.
    - cbn [pow]. unfold matrix_mul. apply sum_orel_bound. intro z.
      eapply orel_trans; [apply bounded_mul_lower_left | apply Hrow].
  Qed.

  Lemma mat_star_row_bound {R : BoundedSemiring.type} (M : @Matrix Node R)
    (x : Node) (v : R) (y : Node) :
    (forall u, M x u ≤ v) -> x <> y -> mat_star M x y ≤ v.
  Proof.
    intros Hrow Hxy. apply mat_star_bound. intro k.
    exact (pow_row_bound M x v Hrow k y Hxy).
  Qed.

  (** If the only out-edge of [a] that can begin a path to [c] is [a -> b],
      every other target being either unreachable from [a] or a dead end,
      and every out-edge of [b] is below [v], then the whole closure from
      [a] to [c] is capped by that first step followed by [v]. *)
  Lemma mat_star_two_step {R : BoundedSemiring.type} (M : @Matrix Node R)
    (a b c : Node) (v : R) :
    a <> c -> b <> c ->
    (forall w, w <> b -> M a w = 0 \/ (w <> c /\ forall u, M w u = 0)) ->
    (forall w, M b w ≤ v) ->
    mat_star M a c ≤ M a b * v.
  Proof.
    intros Hac Hbc Hout Hrowb.
    apply mat_star_bound. intro k. destruct k as [|k].
    - cbn [pow]. unfold I.
      destruct (fin_eq_dec a c) as [C|_]; [congruence|]. apply zero_is_bottom.
    - cbn [pow]. unfold matrix_mul. apply sum_orel_bound. intro z.
      destruct (fin_eq_dec z b) as [Hzb|Hzb].
      + subst z. apply bounded_mul_orel_compat_r.
        exact (pow_row_bound M b v Hrowb k c Hbc).
      + destruct (Hout z Hzb) as [Hz0 | (Hzc & Hdead)].
        * rewrite Hz0. rewrite (@mul0r R). apply zero_is_bottom.
        * assert (Hp0 : pow M k z c = 0).
          { apply orel_antisym; [| apply zero_is_bottom].
            apply (pow_row_bound M z 0);
              [ intro u; rewrite Hdead; apply (@bounded_orel_refl R 0)
              | exact Hzc ]. }
          rewrite Hp0. rewrite (@mulr0 R). apply zero_is_bottom.
  Qed.

  (** Sandwiching both closure directions between two strictly ordered
      values is enough to establish a Schulze victory. *)
  Lemma beats_of_bounds {R : BoundedSemiring.type} (M : @Matrix Node R)
    (a b : Node) (u v : R) :
    mat_star M b a ≤ u -> v ≤ mat_star M a b -> u ≤ v -> u <> v ->
    schulze_beats M a b.
  Proof.
    intros Hba Hab Huv Hne. unfold schulze_beats, beats. split.
    - exact (orel_trans _ _ _ Hba (orel_trans _ _ _ Huv Hab)).
    - intro Heq. apply Hne. apply orel_antisym; [exact Huv |].
      rewrite <- Heq in Hab. exact (orel_trans _ _ _ Hab Hba).
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

  (** The diagonal of the closure is the top. *)
  Lemma mat_star_diag_one {R : BoundedSemiring.type}
    (M : @Matrix Node R) (x : Node) : mat_star M x x = 1.
  Proof. unfold mat_star. apply geom_sum_diag_one. Qed.

End SchulzeClosureN.
