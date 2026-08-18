From Stdlib Require Import List Utf8 Lia.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures SocialchoiceN
  ClosureTransportN BeatsOnN CloneN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).

(* ====================================================================== *)
(*  Independence of clones characterises the bottleneck semirings.       *)
(*                                                                       *)
(*  Selectivity and the meet property are not merely sufficient for the  *)
(*  clone criterion but necessary, so it sits in the same class as       *)
(*  transitivity and winner existence, and is in fact EQUIVALENT to      *)
(*  winner existence rather than merely implied by the same conditions.  *)
(*                                                                       *)
(*  The leverage is that the clone hypotheses constrain nothing about    *)
(*  the links among the clones, and go vacuous when the old alternative  *)
(*  set is the singleton [[d]].  There the criterion says exactly that   *)
(*  an arbitrary matrix on an arbitrary nonempty set of clones admits an *)
(*  undefeated element, so the winner-existence witnesses apply with the *)
(*  replaced alternative parked outside as a node no link leaves.        *)
(* ====================================================================== *)

Section CloneCharacterisation.

  Context {Node : FinType.type}.
  Context {R : BoundedSemiring.type}.


  (** The clone criterion as a property of the semiring: it holds of every
      pair of elections related by a clone replacement.  Quantifying over the
      configuration is what makes the converse direction available; for a
      single fixed configuration the criterion can hold accidentally, for
      instance when every path strength ties, and then it says nothing about
      the semiring at all. *)
  Definition clone_independence : Prop :=
    forall (A_old K : list Node) (d : Node) (M_old M_new : @OrelN.Matrix Node R),
      List.In d A_old -> K <> [] ->
      (forall x, List.In x K -> ~ List.In x A_old) ->
      (forall u v : Node, u = v -> M_old u v = 1) ->
      (forall u v : Node, u = v -> M_new u v = 1) ->
      (forall a g, List.In a A_old -> a <> d -> List.In g K ->
         M_new g a = M_old d a) ->
      (forall a g, List.In a A_old -> a <> d -> List.In g K ->
         M_new a g = M_old a d) ->
      (forall a b, List.In a A_old -> a <> d -> List.In b A_old -> b <> d ->
         M_new a b = M_old a b) ->
      (forall a, List.In a A_old -> a <> d ->
         (winner_on A_old M_old a <-> winner_on (A_new A_old K d) M_new a))
      /\ (winner_on A_old M_old d <->
          exists g, List.In g K /\ winner_on (A_new A_old K d) M_new g).

  (** A short list cannot exhaust the alternatives. *)
  Lemma exists_outside (c : list Node) :
    (List.length c < List.length (@elements Node))%nat ->
    exists z, ~ List.In z c.
  Proof.
    intros Hlen.
    destruct (List.existsb
                (fun z => if List.in_dec fin_eq_dec z c then false else true)
                (@elements Node)) eqn:Hex.
    - apply List.existsb_exists in Hex. destruct Hex as (z & _ & Hz).
      exists z. destruct (List.in_dec fin_eq_dec z c); [discriminate | assumption].
    - exfalso.
      assert (Hcov : covers (@elements Node) c).
      { intros z _.
        destruct (List.in_dec fin_eq_dec z c) as [Hin | Hnin]; [exact Hin |].
        exfalso.
        assert (Htrue : List.existsb
                  (fun z0 => if List.in_dec fin_eq_dec z0 c then false else true)
                  (@elements Node) = true).
        { apply List.existsb_exists. exists z.
          split; [apply elements_complete |].
          destruct (List.in_dec fin_eq_dec z c); [contradiction | reflexivity]. }
        rewrite Htrue in Hex. discriminate. }
      destruct (@covers_pigenhole Node fin_eq_dec (@elements Node) c Hcov Hlen)
        as (a & l1 & l2 & l3 & Heq).
      pose proof (@elements_nodup Node) as Hnd.
      rewrite Heq in Hnd. cbn in Hnd.
      eapply NoDup_remove_2 in Hnd. apply Hnd.
      rewrite app_assoc. apply in_elt.
  Qed.

  (** Replacing the only original alternative leaves exactly the clones. *)
  Lemma A_new_singleton (K : list Node) (d : Node) :
    A_new [d] K d = K.
  Proof.
    unfold A_new. cbn.
    destruct (fin_eq_dec d d) as [_ | Hc];
      [reflexivity | exfalso; apply Hc; reflexivity].
  Qed.

  (** The clone criterion yields a Schulze winner for any matrix in which
      everything outside a chosen nonempty set [K] is dead.  Take [A_old] to
      be the singleton [[d]]: the three clone hypotheses are then vacuous,
      [A_new] is [K], and [winner_on [d] M_old d] holds for want of a rival,
      so the criterion hands back an undefeated clone.  That clone is a
      winner over the whole alternative set, because the closure over [K]
      agrees with [mat_star] there and because a dead alternative reaches
      nothing and so defeats nobody. *)
  Lemma winner_of_dead_outside (Hclone : clone_independence)
    (K : list Node) (d : Node) (M : @OrelN.Matrix Node R) :
    K <> [] -> ~ List.In d K ->
    (forall u v, ~ List.In u K -> u <> v -> M u v = 0) ->
    exists w, schulze_winner M w.
  Proof.
    intros HK Hd Hdead.
    set (M' := matrix_add M (I : @OrelN.Matrix Node R)).
    assert (Hdiag' : forall u v : Node, u = v -> M' u v = 1).
    { intros u v H. unfold M'. apply matrix_add_I_diag. exact H. }
    assert (Hdiag1 : forall u v : Node, u = v -> (fun _ _ : Node => (1 : R)) u v = 1).
    { intros. reflexivity. }
    assert (Hfresh : forall x, List.In x K -> ~ List.In x [d]).
    { intros x Hx Habs. destruct Habs as [Habs | []]. subst x. contradiction. }
    assert (Hvac1 : forall a g, List.In a [d] -> a <> d -> List.In g K ->
              M' g a = (fun _ _ : Node => (1 : R)) d a).
    { intros a g Ha Hne _. destruct Ha as [Ha | []]. subst a. contradiction. }
    assert (Hvac2 : forall a g, List.In a [d] -> a <> d -> List.In g K ->
              M' a g = (fun _ _ : Node => (1 : R)) a d).
    { intros a g Ha Hne _. destruct Ha as [Ha | []]. subst a. contradiction. }
    assert (Hvac3 : forall a b, List.In a [d] -> a <> d -> List.In b [d] -> b <> d ->
              M' a b = (fun _ _ : Node => (1 : R)) a b).
    { intros a b Ha Hne _ _. destruct Ha as [Ha | []]. subst a. contradiction. }
    destruct (Hclone [d] K d (fun _ _ : Node => (1 : R)) M'
                (or_introl eq_refl) HK Hfresh Hdiag1 Hdiag' Hvac1 Hvac2 Hvac3)
      as [_ Hiff].
    assert (Hwin_d : winner_on [d] (fun _ _ : Node => (1 : R)) d).
    { intros b Hb Hne. destruct Hb as [Hb | []]. subst b. contradiction. }
    destruct (proj1 Hiff Hwin_d) as [g [Hg Hwg]].
    rewrite A_new_singleton in Hwg.
    assert (Hdead' : forall u v, ~ List.In u K -> List.In v K -> M' u v = 0).
    { intros u v Hu Hv.
      assert (Huv : u <> v) by (intro h; subst v; contradiction).
      unfold M'. rewrite (matrix_add_I_off M u v Huv). exact (Hdead u v Hu Huv). }
    assert (Hid : forall x y, List.In x K -> List.In y K ->
              path_star K M' x y = mat_star M x y).
    { intros x y Hx Hy.
      rewrite <- (path_star_restrict K (@elements Node) M' HK
                    (fun z _ => elements_complete z) Hdead' Hdiag' x y Hx Hy).
      rewrite path_star_elements_is_mat_star.
      apply mat_star_add_I. }
    exists g. intros b Hbg Hbeats.
    destruct (List.in_dec fin_eq_dec b K) as [HbK | HbK].
    - apply (Hwg b HbK Hbg).
      unfold schulze_beats, beats in Hbeats. unfold beats_on.
      rewrite (Hid g b Hg HbK), (Hid b g HbK Hg).
      exact Hbeats.
    - assert (Hbg' : b <> g) by (intro h; subst b; contradiction).
      assert (Hzero : mat_star M b g = 0).
      { rewrite <- (mat_star_add_I M b g).
        rewrite <- path_star_elements_is_mat_star.
        apply (path_star_dead (@elements Node) M' b g Hdiag').
        - intros v Hbv. unfold M'. rewrite (matrix_add_I_off M b v Hbv).
          exact (Hdead b v HbK Hbv).
        - exact Hbg'. }
      unfold schulze_beats, beats in Hbeats.
      destruct Hbeats as [Hle Hne].
      rewrite Hzero in Hle, Hne.
      apply Hne. unfold Orel in Hle. rewrite addr0 in Hle. exact Hle.
  Qed.

  (** The four-cycle witness, read off the clone criterion.  Its unnamed
      nodes have no outgoing edges, so one of them can play the replaced
      alternative. *)
  Lemma clone_winner_sq (Hclone : clone_independence)
    (Hlen : (5 <= List.length (@elements Node))%nat) :
    forall (A B C D : Node) (x y : R),
      exists a, schulze_winner (sq_matrix A B C D x y) a.
  Proof.
    intros A B C D x y.
    assert (Hlt : (List.length [A; B; C; D] < List.length (@elements Node))%nat)
      by (cbn; lia).
    destruct (exists_outside [A; B; C; D] Hlt) as [z Hz].
    apply (winner_of_dead_outside Hclone [A; B; C; D] z).
    - discriminate.
    - exact Hz.
    - intros u v Hu Huv.
      assert (HuA : A <> u) by (intro h; apply Hu; left; exact h).
      assert (HuB : B <> u) by (intro h; apply Hu; right; left; exact h).
      assert (HuC : C <> u) by (intro h; apply Hu; right; right; left; exact h).
      assert (HuD : D <> u) by (intro h; apply Hu; right; right; right; left; exact h).
      rewrite sq_matrix_unfold.
      destruct (fin_eq_dec u A) as [h|_]; [exfalso; exact (HuA (eq_sym h)) |].
      destruct (fin_eq_dec u B) as [h|_]; [exfalso; exact (HuB (eq_sym h)) |].
      destruct (fin_eq_dec u C) as [h|_]; [exfalso; exact (HuC (eq_sym h)) |].
      destruct (fin_eq_dec u D) as [h|_]; [exfalso; exact (HuD (eq_sym h)) |].
      reflexivity.
  Qed.

  (** The three-cycle witness, likewise. *)
  Lemma clone_winner_tri (Hclone : clone_independence)
    (Hlen : (4 <= List.length (@elements Node))%nat) :
    forall (X Y Z : Node) (p q r : R),
      exists a, schulze_winner (tri_matrix X Y Z p q r) a.
  Proof.
    intros X Y Z p q r.
    assert (Hlt : (List.length [X; Y; Z] < List.length (@elements Node))%nat)
      by (cbn; lia).
    destruct (exists_outside [X; Y; Z] Hlt) as [z Hz].
    apply (winner_of_dead_outside Hclone [X; Y; Z] z).
    - discriminate.
    - exact Hz.
    - intros u v Hu Huv.
      assert (HuX : X <> u) by (intro h; apply Hu; left; exact h).
      assert (HuY : Y <> u) by (intro h; apply Hu; right; left; exact h).
      assert (HuZ : Z <> u) by (intro h; apply Hu; right; right; left; exact h).
      rewrite tri_matrix_unfold.
      destruct (fin_eq_dec u X) as [h|_]; [exfalso; exact (HuX (eq_sym h)) |].
      destruct (fin_eq_dec u Y) as [h|_]; [exfalso; exact (HuY (eq_sym h)) |].
      destruct (fin_eq_dec u Z) as [h|_]; [exfalso; exact (HuZ (eq_sym h)) |].
      reflexivity.
  Qed.

  (** Independence of clones characterises the bottleneck semirings, exactly
      as transitivity and winner existence do.  Five alternatives are needed:
      four to carry the alternating cycle that refutes selectivity, and one
      more to be the replaced alternative. *)
  Theorem clone_characterisation
    (Hlen : (5 <= List.length (@elements Node))%nat)
    (Hdec : forall x y : R, {x = y} + {x <> y}) :
    clone_independence <->
    (forall x y : R, x + y = x \/ x + y = y) /\
    (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    assert (Hlen4 : (4 <= List.length (@elements Node))%nat) by lia.
    assert (Hlen3 : (3 <= List.length (@elements Node))%nat) by lia.
    split.
    - intro Hclone.
      assert (Hsel : forall x y : R, x + y = x \/ x + y = y)
        by exact (selectivity_from_winner_exists Hlen4 Hdec
                    (clone_winner_sq Hclone Hlen)).
      split; [exact Hsel |].
      exact (meet_from_winner_exists Hlen3 Hdec Hsel
               (clone_winner_tri Hclone Hlen4)).
    - intros [Hsel Hmeet] A_old K d M_old M_new H1 H2 H3 H4 H5 H6 H7 H8.
      exact (independence_of_clones_selective A_old K d M_old M_new
               H1 H2 H3 H4 H5 H6 H7 H8 Hsel Hdec Hmeet).
  Qed.

  (** The sharper classification statement: over this framework independence
      of clones and winner existence are the same condition, not merely two
      criteria that happen to hold under the same hypotheses. *)
  Corollary clone_iff_winner_exists
    (Hlen : (5 <= List.length (@elements Node))%nat)
    (Hdec : forall x y : R, {x = y} + {x <> y}) :
    clone_independence <->
    (forall M : @OrelN.Matrix Node R, exists a : Node, schulze_winner M a).
  Proof.
    assert (Hlen4 : (4 <= List.length (@elements Node))%nat) by lia.
    pose proof (clone_characterisation Hlen Hdec) as H1.
    pose proof (winner_exists_characterisation Hlen4 Hdec) as H2.
    split; intro H.
    - apply (proj2 H2). apply (proj1 H1). exact H.
    - apply (proj2 H1). apply (proj1 H2). exact H.
  Qed.

End CloneCharacterisation.
