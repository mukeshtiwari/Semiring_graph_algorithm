From Stdlib Require Import List Utf8 Lia.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures SocialchoiceN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).

(* ===================================================================== *)
(*  Transporting the list-indexed closure along a node map.             *)
(*                                                                      *)
(*  Generic machinery, with nothing specific to clones or to Smith-IIA. *)
(*  A path is carried from one election to another by renaming its      *)
(*  nodes and recomputing its link strengths in the target matrix,      *)
(*  which makes well-formedness hold by construction.  Two consumers:   *)
(*  CloneN and SmithiiaN, each comparing two elections whose            *)
(*  alternative sets differ.                                            *)
(* ===================================================================== *)

Section ClosureTransportN.

  Context {Node : FinType.type}.

  Let Matrix {R : Semiring.type} := @OrelN.Matrix Node R.

  (* =================================================================== *)
  (*  Relabelling a path along a node map                                 *)
  (*                                                                      *)
  (*  Both directions of the clone argument move a path from one election *)
  (*  to the other by renaming its nodes and recomputing its edge weights *)
  (*  in the target matrix.  Recomputing rather than transporting the     *)
  (*  weights makes well-formedness hold by construction and turns the    *)
  (*  measure comparison into a purely edgewise question, which is what   *)
  (*  replaces Schulze's informal first-entry / last-exit surgery on the  *)
  (*  strongest path.                                                     *)
  (* =================================================================== *)

  Definition remap_path {R : Semiring.type} (f : Node -> Node)
    (m : @Matrix R) (p : list (Node * Node * R)) : list (Node * Node * R) :=
    List.map (fun '(a, b, _) => (f a, f b, m (f a) (f b))) p.

  Lemma remap_path_app {R : Semiring.type} (f : Node -> Node)
    (m : @Matrix R) (p q : list (Node * Node * R)) :
    remap_path f m (p ++ q) = remap_path f m p ++ remap_path f m q.
  Proof. unfold remap_path. apply map_app. Qed.

  Lemma remap_path_length {R : Semiring.type} (f : Node -> Node)
    (m : @Matrix R) (p : list (Node * Node * R)) :
    List.length (remap_path f m p) = List.length p.
  Proof. unfold remap_path. apply length_map. Qed.

  Lemma remap_path_cons {R : Semiring.type} (f : Node -> Node)
    (m : @Matrix R) (a b : Node) (w : R) (t : list (Node * Node * R)) :
    remap_path f m ((a, b, w) :: t) =
    (f a, f b, m (f a) (f b)) :: remap_path f m t.
  Proof. reflexivity. Qed.

  (** Well-formedness of the image is free: the weights were read off [m2]. *)
  Lemma remap_well_formed {R : Semiring.type} (f : Node -> Node)
    (m1 m2 : @Matrix R) (p : list (Node * Node * R)) :
    well_formed_path_aux m1 p ->
    well_formed_path_aux m2 (remap_path f m2 p).
  Proof.
    induction p as [|((a, b), w) t IH]; intros Hwf.
    - exact Logic.I.
    - cbn in Hwf. destruct Hwf as [Hw Hrest].
      rewrite remap_path_cons. cbn.
      split; [reflexivity |].
      destruct t as [|((b', c), w') t'].
      + exact Logic.I.
      + destruct Hrest as [Heq Hwf_t].
        rewrite remap_path_cons.
        split; [rewrite Heq; reflexivity |].
        exact (IH Hwf_t).
  Qed.

  (** An edgewise bound lifts to the measure, by monotonicity of [*]. *)
  Lemma remap_measure {R : BoundedSemiring.type} (f : Node -> Node)
    (m2 : @Matrix R) (p : list (Node * Node * R)) :
    (forall a b w, List.In (a, b, w) p -> w ≤ m2 (f a) (f b)) ->
    measure_of_path p ≤ measure_of_path (remap_path f m2 p).
  Proof.
    induction p as [|((a, b), w) t IH]; intros Hedge.
    - cbn. unfold Orel. apply bounded_add_idem.
    - rewrite remap_path_cons. cbn [measure_of_path].
      eapply orel_trans.
      + apply bounded_mul_orel_compat_r.
        apply IH. intros x y u Hin. exact (Hedge x y u (or_intror Hin)).
      + apply bounded_mul_orel_compat_l.
        exact (Hedge a b w (or_introl eq_refl)).
  Qed.

  Lemma remap_source {R : Semiring.type} (f : Node -> Node)
    (m : @Matrix R) (c : Node) (p : list (Node * Node * R)) :
    source c p = true -> source (f c) (remap_path f m p) = true.
  Proof.
    intros Hsrc.
    destruct p as [|((x, y), w) t]; [discriminate Hsrc |].
    cbn in Hsrc. destruct (fin_eq_dec c x) as [Heq | Hne]; [| discriminate Hsrc].
    subst x. rewrite remap_path_cons. cbn.
    destruct (fin_eq_dec (f c) (f c)) as [_ | Hc];
      [reflexivity | exfalso; apply Hc; reflexivity].
  Qed.

  Lemma remap_target {R : Semiring.type} (f : Node -> Node)
    (m : @Matrix R) (d : Node) (p : list (Node * Node * R)) :
    target d p = true -> target (f d) (remap_path f m p) = true.
  Proof.
    induction p as [|((x, y), w) t IH]; intros Htgt.
    - discriminate Htgt.
    - rewrite remap_path_cons.
      destruct t as [|((x', y'), w') t'].
      + cbn in Htgt. destruct (fin_eq_dec d y) as [Heq | Hne]; [| discriminate Htgt].
        subst y. cbn.
        destruct (fin_eq_dec (f d) (f d)) as [_ | Hc];
          [reflexivity | exfalso; apply Hc; reflexivity].
      + cbn [target] in Htgt |- *.
        rewrite remap_path_cons in IH |- *.
        exact (IH Htgt).
  Qed.

  Lemma remap_nodes_in {R : Semiring.type} (f : Node -> Node)
    (m : @Matrix R) (ns1 ns2 : list Node) (p : list (Node * Node * R)) :
    path_nodes_in ns1 p ->
    (forall x, List.In x ns1 -> List.In (f x) ns2) ->
    path_nodes_in ns2 (remap_path f m p).
  Proof.
    intros Hp Hf x y u Hin.
    unfold remap_path in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (((a, b), w) & Heq & Hab).
    inversion Heq. subst x y.
    destruct (Hp a b w Hab) as [Ha Hb].
    split; [exact (Hf a Ha) | exact (Hf b Hb)].
  Qed.

  (* =================================================================== *)
  (*  Transporting the closure along a node map                           *)
  (*                                                                      *)
  (*  This is the single workhorse of the clone argument.  Note that no   *)
  (*  control is needed on the length of the transported path: the image  *)
  (*  is shortened by [reduce_path_into_simpl_path_gen] at the target     *)
  (*  candidate list, which is what removes the need to track loop        *)
  (*  freeness through the surgery.                                       *)
  (* =================================================================== *)

  Lemma path_star_transport {R : BoundedSemiring.type}
    (f : Node -> Node) (m1 m2 : @Matrix R) (ns1 ns2 : list Node) (c d : Node) :
    ns2 <> [] ->
    (forall u v : Node, u = v -> m1 u v = 1) ->
    (forall u v : Node, u = v -> m2 u v = 1) ->
    (forall x, List.In x (c :: d :: ns1) -> List.In (f x) ns2) ->
    (forall a b, List.In a (c :: d :: ns1) -> List.In b (c :: d :: ns1) ->
       m1 a b ≤ m2 (f a) (f b)) ->
    path_star ns1 m1 c d ≤ path_star ns2 m2 (f c) (f d).
  Proof.
    intros Hns2 Hdiag1 Hdiag2 Hf Hedge.
    apply path_star_upper.
    intros k p Hk Hin.
    pose proof (all_paths_well_formed_in_kpaths_gen ns1 k m1 c d p Hdiag1 Hin) as Hwf_p.
    pose proof (all_paths_klength_nodes ns1 k m1 c d p Hin) as Hcov_p.
    pose proof (covers_path_nodes_in m1 (c :: d :: ns1) p Hwf_p Hcov_p) as Hnodes_p.
    destruct (non_empty_paths_in_kpath_gen ns1 k m1 c d p Hin)
      as (Hne_p & Hsrc_p & Htgt_p).
    destruct (path_end_unit_loop_gen ns1 k p m1 c d Hin) as [p' Hp'].
    assert (Hwf_q : well_formed_path_aux m2 (remap_path f m2 p))
      by exact (remap_well_formed f m1 m2 p Hwf_p).
    assert (Hsrc_q : source (f c) (remap_path f m2 p) = true)
      by exact (remap_source f m2 c p Hsrc_p).
    assert (Htgt_q : target (f d) (remap_path f m2 p) = true)
      by exact (remap_target f m2 d p Htgt_p).
    assert (Hnodes_q : path_nodes_in ns2 (remap_path f m2 p))
      by exact (remap_nodes_in f m2 (c :: d :: ns1) ns2 p Hnodes_p Hf).
    assert (Hmeas_q : measure_of_path p ≤ measure_of_path (remap_path f m2 p)).
    { apply remap_measure. intros a b w Hin_e.
      destruct (Hnodes_p a b w Hin_e) as [Ha Hb].
      rewrite <- (well_formed_edge m1 p a b w Hwf_p Hin_e).
      exact (Hedge a b Ha Hb). }
    assert (Hfd : List.In (f d) ns2)
      by (apply Hf; right; left; reflexivity).
    assert (Hq_shape : remap_path f m2 p = remap_path f m2 p' ++ [(f d, f d, 1)]).
    { rewrite Hp'. rewrite remap_path_app.
      rewrite remap_path_cons.
      rewrite (Hdiag2 (f d) (f d) eq_refl). reflexivity. }
    rewrite Hq_shape in Hwf_q, Hsrc_q, Htgt_q, Hnodes_q, Hmeas_q.
    destruct (path_nodes_in_app_inv ns2 (remap_path f m2 p') [(f d, f d, 1)] Hnodes_q)
      as [Hnodes_xs _].
    destruct (reduce_path_into_simpl_path_gen ns2 (remap_path f m2 p') m2 (f c) (f d)
                Hns2 Hnodes_xs Hwf_q Hsrc_q Htgt_q)
      as (ys & Hlen_ys & Hnodes_ys & Hwf_ys & Hsrc_ys & Htgt_ys & Horel_ys).
    assert (Hnodes_full : path_nodes_in ns2 (ys ++ [(f d, f d, 1)])).
    { apply path_nodes_in_app; [exact Hnodes_ys |].
      intros a b w Hin_e. destruct Hin_e as [Heq | []].
      inversion Heq. subst. split; exact Hfd. }
    assert (Hlen_bound : (List.length ys <= List.length ns2 - 1)%nat) by lia.
    pose proof (path_star_lower_of_path ns2 m2 (f c) (f d) ys
                  Hnodes_full Hlen_bound Hsrc_ys Htgt_ys Hwf_ys) as Hlow.
    rewrite measure_snoc_unit in Hmeas_q, Hlow.
    eapply orel_trans; [exact Hmeas_q |].
    eapply orel_trans; [exact Horel_ys | exact Hlow].
  Qed.

  (* =================================================================== *)
  (*  Restricting the closure to a sublist                                *)
  (*                                                                      *)
  (*  If everything outside [ns] is dead, in the sense of having no edge  *)
  (*  back into [ns], then the closure over any larger list agrees with   *)
  (*  the closure over [ns] on [ns] itself.  A path that leaves [ns] can  *)
  (*  only return through a zero edge, so it contributes nothing.  This   *)
  (*  is what lets the winner-existence witnesses of SocialchoiceN, which *)
  (*  live over the whole alternative set, be read as statements about a  *)
  (*  chosen sublist.                                                     *)
  (* =================================================================== *)

  Lemma path_star_restrict {R : BoundedSemiring.type} (ns ns' : list Node)
    (m : @Matrix R) :
    ns <> [] ->
    (forall x, List.In x ns -> List.In x ns') ->
    (forall u v, ~ List.In u ns -> List.In v ns -> m u v = 0) ->
    (forall a b : Node, a = b -> m a b = 1) ->
    forall x y, List.In x ns -> List.In y ns ->
      path_star ns' m x y = path_star ns m x y.
  Proof.
    intros Hns Hsub Hdead Hdiag x y Hx Hy.
    assert (Hns' : ns' <> []).
    { intro h. pose proof (Hsub x Hx) as Hx'. rewrite h in Hx'. inversion Hx'. }
    apply orel_antisym.
    - apply path_star_upper. intros k p Hk Hin.
      pose proof (all_paths_well_formed_in_kpaths_gen ns' k m x y p Hdiag Hin) as Hwf.
      destruct (non_empty_paths_in_kpath_gen ns' k m x y p Hin) as (Hne & Hsrc & Htgt).
      destruct (path_inside_or_exits m ns p y Hwf Htgt Hy) as [Hin_ns | Hex].
      + destruct (path_end_unit_loop_gen ns' k p m x y Hin) as [p' Hp'].
        rewrite Hp' in Hwf, Hsrc, Htgt, Hin_ns.
        destruct (path_nodes_in_app_inv ns p' [(y, y, 1)] Hin_ns) as [Hn_p' _].
        destruct (reduce_path_into_simpl_path_gen ns p' m x y Hns Hn_p' Hwf Hsrc Htgt)
          as (ys & Hlen & Hnodes & Hwf2 & Hsrc2 & Htgt2 & Horel).
        assert (Hfull : path_nodes_in ns (ys ++ [(y, y, 1)])).
        { apply path_nodes_in_app; [exact Hnodes |].
          intros a b w Hin_e. destruct Hin_e as [Heq | []].
          inversion Heq. subst. split; exact Hy. }
        assert (Hlb : (List.length ys <= List.length ns - 1)%nat) by lia.
        pose proof (path_star_lower_of_path ns m x y ys Hfull Hlb Hsrc2 Htgt2 Hwf2)
          as Hlow.
        rewrite measure_snoc_unit in Hlow.
        rewrite Hp'. rewrite measure_snoc_unit.
        eapply orel_trans; [exact Horel | exact Hlow].
      + destruct Hex as (a & b & w & Hin_e & Ha & Hb).
        assert (Hw : w = 0).
        { rewrite <- (well_formed_edge m p a b w Hwf Hin_e). exact (Hdead a b Ha Hb). }
        rewrite (measure_zero_edge p a b w Hin_e Hw).
        apply zero_is_bottom.
    - assert (Hin_ns' : forall z, List.In z (x :: y :: ns) -> List.In z ns').
      { intros z Hz. destruct Hz as [Hz | [Hz | Hz]];
          [rewrite <- Hz; exact (Hsub x Hx)
          | rewrite <- Hz; exact (Hsub y Hy)
          | exact (Hsub z Hz)]. }
      assert (Hedge : forall a b, List.In a (x :: y :: ns) ->
                List.In b (x :: y :: ns) -> Orel (m a b) (m a b)).
      { intros a b _ _. unfold Orel. apply bounded_add_idem. }
      exact (path_star_transport (fun z => z) m m ns ns' x y Hns' Hdiag Hdiag
               Hin_ns' Hedge).
  Qed.

  (* =================================================================== *)
  (*  Forcing [1] onto the diagonal                                       *)
  (*                                                                      *)
  (*  The clone development assumes [1] on the diagonal, because the path *)
  (*  enumeration hard-codes the terminal loop weight as [1].  The        *)
  (*  witness matrices of SocialchoiceN do not carry that, so they are    *)
  (*  used through [matrix_add M I], which changes only the diagonal and  *)
  (*  leaves the Kleene star alone.                                       *)
  (* =================================================================== *)

  Lemma mat_star_add_I {R : BoundedSemiring.type} (M : @Matrix R) (c d : Node) :
    mat_star (matrix_add M I) c d = mat_star M c d.
  Proof.
    unfold mat_star.
    rewrite <- (matrix_pow_idempotence_bounded kleene_exp (matrix_add M I) c d).
    rewrite <- (matrix_pow_idempotence_bounded kleene_exp M c d).
    apply pow_pointwise.
    intros i j. rewrite !matrix_add_unfold.
    rewrite addA. f_equal. apply bounded_add_idem.
  Qed.

  Lemma matrix_add_I_diag {R : BoundedSemiring.type} (M : @Matrix R) (u v : Node) :
    u = v -> matrix_add M I u v = 1.
  Proof.
    intros Huv. rewrite matrix_add_unfold. unfold I.
    destruct (fin_eq_dec u v) as [_ | Hc]; [| contradiction].
    rewrite addC. apply add_bound.
  Qed.

  Lemma matrix_add_I_off {R : BoundedSemiring.type} (M : @Matrix R) (u v : Node) :
    u <> v -> matrix_add M I u v = M u v.
  Proof.
    intros Huv. rewrite matrix_add_unfold. unfold I.
    destruct (fin_eq_dec u v) as [Hc | _]; [contradiction |].
    apply addr0.
  Qed.

End ClosureTransportN.
