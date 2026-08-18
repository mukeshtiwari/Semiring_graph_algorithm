From Stdlib Require Import List Utf8 Lia.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures SocialchoiceN CloneN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ===================================================================== *)
(*  Smith-IIA in its genuine removal form (Schulze 4.7.5a)               *)
(*                                                                        *)
(*  SocialchoiceN proves the isolation surrogate: zeroing out a weak      *)
(*  alternative's row and column leaves the beat relation on the strong   *)
(*  set unchanged.  The criterion Schulze states is about REMOVING the    *)
(*  alternative, which changes the size of the alternative set and so     *)
(*  needs the list-indexed closure of PathN.                              *)
(*                                                                        *)
(*  The two forms turn out to be the same object.  [isolate M d] gives    *)
(*  [d] no links at all, which is exactly the hypothesis under which      *)
(*  [path_star_restrict] identifies a closure over a sublist with the     *)
(*  closure over everything.  So the removal form is the isolation form   *)
(*  composed with a bridge, and the mathematical content, that no walk    *)
(*  out of the weak block reaches the threshold, is already carried by    *)
(*  [pow_from_B2_lt].                                                     *)
(* ===================================================================== *)

Section SmithIIA.

  Context {Node : FinType.type}.
  Context {R : BoundedSemiring.type}.

  (** The list-indexed closure depends on the matrix only through the entries
      at pairs of candidates.  Both directions are [path_star_transport] at
      the identity map. *)
  Lemma path_star_ext (ns : list Node)
    (m1 m2 : @OrelN.Matrix Node R) (c d : Node) :
    ns <> [] -> List.In c ns -> List.In d ns ->
    (forall u v : Node, u = v -> m1 u v = 1) ->
    (forall u v : Node, u = v -> m2 u v = 1) ->
    (forall u v, List.In u ns -> List.In v ns -> m1 u v = m2 u v) ->
    path_star ns m1 c d = path_star ns m2 c d.
  Proof.
    intros Hns Hc Hd Hd1 Hd2 Hext.
    assert (Hsub : forall z, List.In z (c :: d :: ns) -> List.In z ns).
    { intros z Hz. destruct Hz as [Hz | [Hz | Hz]];
        [rewrite <- Hz; exact Hc | rewrite <- Hz; exact Hd | exact Hz]. }
    apply orel_antisym.
    - apply (path_star_transport (fun z => z) m1 m2 ns ns c d Hns Hd1 Hd2 Hsub).
      intros a b Ha Hb. rewrite (Hext a b (Hsub a Ha) (Hsub b Hb)).
      unfold Orel. apply bounded_add_idem.
    - apply (path_star_transport (fun z => z) m2 m1 ns ns c d Hns Hd2 Hd1 Hsub).
      intros a b Ha Hb. rewrite <- (Hext a b (Hsub a Ha) (Hsub b Hb)).
      unfold Orel. apply bounded_add_idem.
  Qed.

  (** The alternative set with [d] removed. *)
  Definition drop (d : Node) : list Node :=
    List.remove fin_eq_dec d (@elements Node).

  Lemma in_drop (d x : Node) : List.In x (drop d) <-> x <> d.
  Proof.
    unfold drop. split.
    - intros Hx. exact (proj2 (in_remove fin_eq_dec _ x d Hx)).
    - intros Hne. apply in_in_remove; [exact Hne | apply elements_complete].
  Qed.

  Lemma drop_nonempty (d : Node) : drop d <> [].
  Proof.
    destruct (exists_other d) as [y Hy].
    intro Hnil. pose proof (proj2 (in_drop d y) Hy) as Hin.
    rewrite Hnil in Hin. inversion Hin.
  Qed.

  Lemma drop_sub (d x : Node) : List.In x (drop d) -> List.In x (@elements Node).
  Proof. intros _. apply elements_complete. Qed.

  (* =================================================================== *)
  (*  The removal theorem                                                 *)
  (*                                                                      *)
  (*  The hypotheses are those of [smith_iia_isolate] in SocialchoiceN,   *)
  (*  with one addition: [M] must carry [1] on its diagonal.  The         *)
  (*  isolation form does not need this, because [mat_star] supplies the  *)
  (*  identity separately, whereas the list-indexed closure enumerates    *)
  (*  paths that may take a self-loop and so reads the diagonal.  It      *)
  (*  costs nothing in substance, since [M] and [M + I] have the same     *)
  (*  star, but it is a genuine difference between the two statements.    *)
  (* =================================================================== *)

  Section Removal.

  Context (M : @OrelN.Matrix Node R).
  Hypothesis Htotal : forall x y : R, x + y = x \/ x + y = y.
  Hypothesis Hdiag : forall u v : Node, u = v -> M u v = 1.
  Context (B1 B2 : list Node) (c : R) (d : Node).
  Hypothesis H_partition : forall x : Node, List.In x B1 <-> ~ List.In x B2.
  Hypothesis H_lt : forall a b, List.In a B1 -> List.In b B2 -> M b a < c.
  Hypothesis H0 : (0 : R) < c.
  Hypothesis Hd : List.In d B2.
  Hypothesis Hsep : forall x y : Node, x <> y -> c ≤ M x y + M y x.

  Lemma B1_not_d (x : Node) : List.In x B1 -> x <> d.
  Proof.
    intros Hx Heq. subst x. exact (proj1 (H_partition d) Hx Hd).
  Qed.

  (** The bridge, and the reason the removal form is now within reach:
      deleting [d] from the candidate list computes the same closure as
      isolating it in the matrix.  [isolate M d] gives [d] no links at all,
      which is exactly the hypothesis [path_star_restrict] needs, and the
      unit diagonal is restored by adding [I], which leaves the star alone.
      No Smith hypothesis is used here. *)
  Lemma path_star_drop_is_isolate (x y : Node) :
    x <> d -> y <> d ->
    path_star (drop d) M x y = mat_star (isolate M d) x y.
  Proof.
    intros Hx Hy.
    set (M' := matrix_add (isolate M d) (I : @OrelN.Matrix Node R)).
    assert (Hdiag' : forall u v : Node, u = v -> M' u v = 1).
    { intros u v H. unfold M'. apply matrix_add_I_diag. exact H. }
    assert (Hxd : List.In x (drop d)) by (apply in_drop; exact Hx).
    assert (Hyd : List.In y (drop d)) by (apply in_drop; exact Hy).
    assert (Hstep1 : path_star (drop d) M x y = path_star (drop d) M' x y).
    { apply path_star_ext.
      - apply drop_nonempty.
      - exact Hxd.
      - exact Hyd.
      - exact Hdiag.
      - exact Hdiag'.
      - intros u v Hu Hv.
        pose proof (proj1 (in_drop d u) Hu) as Hu'.
        pose proof (proj1 (in_drop d v) Hv) as Hv'.
        destruct (fin_eq_dec u v) as [Heq | Hne].
        + rewrite (Hdiag u v Heq). symmetry. apply matrix_add_I_diag. exact Heq.
        + unfold M'. rewrite (matrix_add_I_off (isolate M d) u v Hne).
          symmetry. apply isolate_off; assumption. }
    assert (Hstep2 : path_star (drop d) M' x y = path_star (@elements Node) M' x y).
    { symmetry. apply path_star_restrict.
      - apply drop_nonempty.
      - apply drop_sub.
      - intros u v Hu Hv.
        assert (Hud : u = d).
        { destruct (fin_eq_dec u d) as [Heq | Hne]; [exact Heq |].
          exfalso. apply Hu. apply in_drop. exact Hne. }
        assert (Huv : u <> v).
        { subst u. intro Heq. subst v.
          exact ((proj1 (in_drop d d) Hv) eq_refl). }
        unfold M'. rewrite (matrix_add_I_off (isolate M d) u v Huv).
        subst u. unfold isolate.
        destruct (fin_eq_dec d d) as [_ | Hc']; [reflexivity | contradiction].
      - exact Hdiag'.
      - exact Hxd.
      - exact Hyd. }
    rewrite Hstep1, Hstep2.
    rewrite path_star_elements_is_mat_star.
    apply mat_star_add_I.
  Qed.

  Lemma orel_le_lt_trans (x y z : R) : x ≤ y -> y < z -> x < z.
  Proof.
    intros Hxy [Hyz Hyz_ne]. split.
    - exact (orel_trans _ _ _ Hxy Hyz).
    - intro Heq. subst z. apply Hyz_ne.
      apply orel_antisym; [exact Hyz | exact Hxy].
  Qed.

  (** The separation hypothesis and the cut together force the strong side to
      clear the threshold outright, which is what [smith_beats] asks for. *)
  Lemma c_le_link (a b : Node) :
    List.In a B1 -> List.In b B2 -> c ≤ M a b.
  Proof.
    intros Ha Hb.
    assert (Hab : a <> b).
    { intro Heq. subst b. exact (proj1 (H_partition a) Ha Hb). }
    pose proof (Hsep a b Hab) as Hs.
    destruct (Htotal (M a b) (M b a)) as [Hc1 | Hc1]; setoid_rewrite Hc1 in Hs.
    - exact Hs.
    - exfalso. destruct (H_lt a b Ha Hb) as [Hle Hne].
      apply Hne. apply orel_antisym; [exact Hle | exact Hs].
  Qed.

  Lemma strong_beats_weak (a b : Node) :
    List.In a B1 -> List.In b B2 -> schulze_beats M a b.
  Proof.
    intros Ha Hb.
    apply (smith_beats M Htotal B1 B2 H_partition).
    - exists c. split; [exact H_lt | exact c_le_link].
    - exact Ha.
    - exact Hb.
  Qed.

  (** No beatpath out of the weak block reaches the threshold.  This is the
      engine of the criterion, and it is already carried by [pow_from_B2_lt]. *)
  Lemma mat_star_from_B2_lt (b a : Node) :
    List.In b B2 -> List.In a B1 -> mat_star M b a < c.
  Proof.
    intros Hb Ha.
    apply (mat_star_lt_bound Htotal). intro n.
    exact (pow_from_B2_lt M Htotal B1 B2 c H_partition H_lt H0 n b Hb a Ha).
  Qed.

  (** Schulze (4.7.5a) at the level of the beat relation.  Given the bridge,
      this is the isolation theorem of SocialchoiceN read through it. *)
  Theorem smith_iia_removal_beats (e f : Node) :
    List.In e B1 -> List.In f B1 ->
    (schulze_beats M e f <-> beats_on (drop d) M e f).
  Proof.
    intros He Hf.
    unfold beats_on.
    rewrite (path_star_drop_is_isolate f e (B1_not_d f Hf) (B1_not_d e He)).
    rewrite (path_star_drop_is_isolate e f (B1_not_d e He) (B1_not_d f Hf)).
    exact (smith_iia_isolate M Htotal B1 B2 c d H_partition H_lt H0 Hd Hsep
             e f He Hf).
  Qed.

  (** A strong alternative still beats every surviving weak one, so deleting
      [d] removes no beater of a strong alternative. *)
  Lemma strong_beats_weak_on_drop (a b : Node) :
    List.In a B1 -> List.In b B2 -> b <> d -> beats_on (drop d) M a b.
  Proof.
    intros Ha Hb Hbd.
    pose proof (B1_not_d a Ha) as Had.
    unfold beats_on.
    rewrite (path_star_drop_is_isolate b a Hbd Had).
    rewrite (path_star_drop_is_isolate a b Had Hbd).
    apply (orel_lt_le_trans _ c _).
    - apply (orel_le_lt_trans _ (mat_star M b a) _).
      + apply mat_star_isolate_le.
      + exact (mat_star_from_B2_lt b a Hb Ha).
    - eapply orel_trans; [| apply link_le_mat_star ].
      rewrite (isolate_off M d a b Had Hbd).
      exact (c_le_link a b Ha Hb).
  Qed.

  Lemma in_B2_of_not_B1 (b : Node) : ~ List.In b B1 -> List.In b B2.
  Proof.
    intros Hb.
    destruct (in_dec fin_eq_dec b B2) as [h | h]; [exact h |].
    exfalso. apply Hb. apply (proj2 (H_partition b)). exact h.
  Qed.

  (** Schulze (4.7.5a).  Deleting a weak alternative from the ballot leaves
      the winner status of every strong alternative untouched.  Unlike
      [smith_iia_isolate] this compares two elections over different
      alternative sets, which is the form Schulze states. *)
  Theorem smith_iia_removal (a : Node) :
    List.In a B1 ->
    (schulze_winner M a <-> winner_on (drop d) M a).
  Proof.
    intros Ha. split.
    - intros Hwin b Hb Hne Hbeats.
      destruct (in_dec fin_eq_dec b B1) as [HbB1 | HbB1].
      + exact (Hwin b Hne (proj2 (smith_iia_removal_beats b a HbB1 Ha) Hbeats)).
      + pose proof (in_B2_of_not_B1 b HbB1) as HbB2.
        pose proof (proj1 (in_drop d b) Hb) as Hbd.
        exact (beats_on_asym (drop d) M a b
                 (strong_beats_weak_on_drop a b Ha HbB2 Hbd) Hbeats).
    - intros Hwin b Hne Hbeats.
      destruct (in_dec fin_eq_dec b B1) as [HbB1 | HbB1].
      + pose proof (B1_not_d b HbB1) as Hbd.
        exact (Hwin b (proj2 (in_drop d b) Hbd) Hne
                 (proj1 (smith_iia_removal_beats b a HbB1 Ha) Hbeats)).
      + pose proof (in_B2_of_not_B1 b HbB1) as HbB2.
        exact (schulze_beats_asym M a b (strong_beats_weak a b Ha HbB2) Hbeats).
  Qed.

  (** The winner set itself is unchanged.  Every winner lies in the strong
      block by the Smith criterion, and there the two elections agree, so
      deleting a weak alternative is invisible to the outcome. *)
  Corollary smith_iia_winner_set (HB1 : B1 <> []) (a : Node) :
    schulze_winner M a <-> (List.In a B1 /\ winner_on (drop d) M a).
  Proof.
    split.
    - intros Hwin.
      assert (Ha : List.In a B1).
      { apply (smith_criterion_weaker M Htotal B1 B2 HB1 H_partition).
        - exists c. split; [exact H_lt | exact c_le_link].
        - exact Hwin. }
      split; [exact Ha | exact (proj1 (smith_iia_removal a Ha) Hwin)].
    - intros [Ha Hwin]. exact (proj2 (smith_iia_removal a Ha) Hwin).
  Qed.

  End Removal.

End SmithIIA.
