From Stdlib Require Import List Utf8 Lia.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures SocialchoiceN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).

(* ===================================================================== *)
(*  Independence of clones (Schulze, Section 4.6)                         *)
(*                                                                        *)
(*  The criterion compares two elections whose alternative sets differ:   *)
(*  one alternative [d] is replaced by a set of clones [K].  Both         *)
(*  elections run here over a single ambient [Node] type and differ only  *)
(*  in which candidate list the closure [path_star] folds over, which is  *)
(*  what makes the comparison statable at all.  At [elements] the closure *)
(*  agrees with [mat_star] by [path_star_elements_is_mat_star], so the    *)
(*  results below speak about the same Schulze relation as SocialchoiceN. *)
(*                                                                        *)
(*  Both matrices are assumed to carry [1] on the diagonal, the standing  *)
(*  hypothesis [∀ u v, u = v -> m u v = 1] used throughout SemimoduleN.   *)
(* ===================================================================== *)

Section Clone.

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

  Lemma orel_le_one {R : BoundedSemiring.type} (a : R) : a ≤ 1.
  Proof. unfold Orel. rewrite addC. apply add_bound. Qed.

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

End Clone.


Section CloneReplacement.

  Context {Node : FinType.type}.
  Context {R : BoundedSemiring.type}.

  (** [A_old] is the original list of alternatives, [d] one of them, and [K]
      a nonempty set of fresh alternatives that replaces it. *)
  Context (A_old K : list Node) (d : Node)
          (M_old M_new : @OrelN.Matrix Node R).

  Hypothesis Hd_old : List.In d A_old.
  Hypothesis HK_nonempty : K <> [].
  Hypothesis HK_fresh : forall x, List.In x K -> ~ List.In x A_old.

  Hypothesis Hdiag_old : forall u v : Node, u = v -> M_old u v = 1.
  Hypothesis Hdiag_new : forall u v : Node, u = v -> M_new u v = 1.

  (** Schulze's (4.6.12): every clone inherits the outgoing edges of [d]. *)
  Hypothesis Hclone_out : forall a g, List.In a A_old -> a <> d ->
    List.In g K -> M_new g a = M_old d a.
  (** Schulze's (4.6.13): every clone inherits the incoming edges of [d]. *)
  Hypothesis Hclone_in : forall a g, List.In a A_old -> a <> d ->
    List.In g K -> M_new a g = M_old a d.
  (** Schulze's (4.6.14): edges between surviving alternatives are untouched.
      Nothing at all is assumed about edges *between* clones. *)
  Hypothesis Hclone_ext : forall a b, List.In a A_old -> a <> d ->
    List.In b A_old -> b <> d -> M_new a b = M_old a b.

  (** [A_new = (A_old ∪ K) \ {d}]. *)
  Definition A_new : list Node := List.remove fin_eq_dec d A_old ++ K.

  (** Sending [d] to a chosen clone [g] carries an old path to a new one. *)
  Definition expand (g : Node) : Node -> Node :=
    fun x => if fin_eq_dec x d then g else x.

  (** Sending every clone back to [d] carries a new path to an old one. *)
  Definition collapse : Node -> Node :=
    fun x => if List.in_dec fin_eq_dec x K then d else x.

  (* ------------------------------------------------------------------ *)
  (*  Membership bookkeeping                                             *)
  (* ------------------------------------------------------------------ *)

  Lemma A_new_nonempty : A_new <> [].
  Proof.
    unfold A_new. intro Hnil.
    apply app_eq_nil in Hnil. destruct Hnil as [_ HK].
    exact (HK_nonempty HK).
  Qed.

  Lemma A_old_nonempty : A_old <> [].
  Proof.
    intro Hnil. rewrite Hnil in Hd_old. inversion Hd_old.
  Qed.

  Lemma in_A_new_intro_old (x : Node) :
    List.In x A_old -> x <> d -> List.In x A_new.
  Proof.
    intros Hx Hne. unfold A_new. apply in_or_app. left.
    apply in_in_remove; assumption.
  Qed.

  Lemma in_A_new_intro_clone (g : Node) :
    List.In g K -> List.In g A_new.
  Proof.
    intros Hg. unfold A_new. apply in_or_app. right. exact Hg.
  Qed.

  Lemma in_A_new_inv (x : Node) :
    List.In x A_new ->
    (List.In x A_old /\ x <> d /\ ~ List.In x K) \/ List.In x K.
  Proof.
    intros Hx. unfold A_new in Hx. apply in_app_or in Hx.
    destruct Hx as [Hx | Hx].
    - apply in_remove in Hx. destruct Hx as [Hx_old Hx_ne].
      left. split; [exact Hx_old | split; [exact Hx_ne |]].
      intro Hx_K. exact (HK_fresh x Hx_K Hx_old).
    - right. exact Hx.
  Qed.

  (** An original alternative is never a clone. *)
  Lemma old_not_clone (x : Node) : List.In x A_old -> ~ List.In x K.
  Proof.
    intros Hx Hx_K. exact (HK_fresh x Hx_K Hx).
  Qed.

  Lemma collapse_old (x : Node) : List.In x A_old -> collapse x = x.
  Proof.
    intros Hx. unfold collapse.
    destruct (List.in_dec fin_eq_dec x K) as [Hin | Hnin];
      [exfalso; exact (old_not_clone x Hx Hin) | reflexivity].
  Qed.

  Lemma collapse_clone (g : Node) : List.In g K -> collapse g = d.
  Proof.
    intros Hg. unfold collapse.
    destruct (List.in_dec fin_eq_dec g K) as [Hin | Hnin];
      [reflexivity | contradiction].
  Qed.

  Lemma expand_other (g x : Node) : x <> d -> expand g x = x.
  Proof.
    intros Hne. unfold expand.
    destruct (fin_eq_dec x d) as [Heq | _]; [contradiction | reflexivity].
  Qed.

  Lemma expand_d (g : Node) : expand g d = g.
  Proof.
    unfold expand.
    destruct (fin_eq_dec d d) as [_ | Hc];
      [reflexivity | exfalso; apply Hc; reflexivity].
  Qed.

  Lemma in_cons2 (c e x : Node) (l : list Node) :
    List.In c l -> List.In e l -> List.In x (c :: e :: l) -> List.In x l.
  Proof.
    intros Hc He Hx.
    destruct Hx as [Hx | [Hx | Hx]]; [subst x; exact Hc | subst x; exact He | exact Hx].
  Qed.

  Lemma bounded_orel_refl' (a : R) : a ≤ a.
  Proof. unfold Orel. apply bounded_add_idem. Qed.

  Lemma nonempty_has_member {A : Type} (l : list A) :
    l <> [] -> exists x, List.In x l.
  Proof.
    destruct l as [|x t]; intros Hne.
    - exfalso. apply Hne. reflexivity.
    - exists x. left. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The two transports                                                 *)
  (* ------------------------------------------------------------------ *)

  (** Expansion: replacing [d] by a chosen clone [g] carries the old closure
      below the new one.  Every edge of the image has exactly the weight the
      original edge had, by the three clone hypotheses. *)
  Lemma expand_transport (g c e : Node) :
    List.In g K -> List.In c A_old -> List.In e A_old ->
    path_star A_old M_old c e ≤ path_star A_new M_new (expand g c) (expand g e).
  Proof.
    intros Hg Hc He.
    apply path_star_transport.
    - exact A_new_nonempty.
    - exact Hdiag_old.
    - exact Hdiag_new.
    - intros x Hx.
      pose proof (in_cons2 c e x A_old Hc He Hx) as Hx_old.
      destruct (fin_eq_dec x d) as [Heq | Hne].
      + subst x. rewrite expand_d. exact (in_A_new_intro_clone g Hg).
      + rewrite (expand_other g x Hne). exact (in_A_new_intro_old x Hx_old Hne).
    - intros a b Ha Hb.
      pose proof (in_cons2 c e a A_old Hc He Ha) as Ha_old.
      pose proof (in_cons2 c e b A_old Hc He Hb) as Hb_old.
      destruct (fin_eq_dec a d) as [Had | Han];
        destruct (fin_eq_dec b d) as [Hbd | Hbn].
      + subst a b. rewrite !expand_d.
        rewrite (Hdiag_old d d eq_refl), (Hdiag_new g g eq_refl).
        apply bounded_orel_refl'.
      + subst a. rewrite expand_d, (expand_other g b Hbn).
        rewrite (Hclone_out b g Hb_old Hbn Hg).
        apply bounded_orel_refl'.
      + subst b. rewrite (expand_other g a Han), expand_d.
        rewrite (Hclone_in a g Ha_old Han Hg).
        apply bounded_orel_refl'.
      + rewrite (expand_other g a Han), (expand_other g b Hbn).
        rewrite (Hclone_ext a b Ha_old Han Hb_old Hbn).
        apply bounded_orel_refl'.
  Qed.

  (** Collapse: sending every clone back to [d] carries the new closure below
      the old one.  The three boundary cases are equalities again; only the
      clone-to-clone edges lose information, and there the bound is [1].  This
      is the one step where boundedness of the semiring is genuinely used, and
      it is why independence of clones sits with transitivity and winner
      existence rather than with neutrality and monotonicity. *)
  Lemma collapse_transport (c e : Node) :
    List.In c A_new -> List.In e A_new ->
    path_star A_new M_new c e ≤ path_star A_old M_old (collapse c) (collapse e).
  Proof.
    intros Hc He.
    apply path_star_transport.
    - exact A_old_nonempty.
    - exact Hdiag_new.
    - exact Hdiag_old.
    - intros x Hx.
      pose proof (in_cons2 c e x A_new Hc He Hx) as Hx_new.
      destruct (in_A_new_inv x Hx_new) as [[Hx_old [Hx_ne _]] | Hx_K].
      + rewrite (collapse_old x Hx_old). exact Hx_old.
      + rewrite (collapse_clone x Hx_K). exact Hd_old.
    - intros a b Ha Hb.
      pose proof (in_cons2 c e a A_new Hc He Ha) as Ha_new.
      pose proof (in_cons2 c e b A_new Hc He Hb) as Hb_new.
      destruct (in_A_new_inv a Ha_new) as [[Ha_old [Ha_ne _]] | Ha_K];
        destruct (in_A_new_inv b Hb_new) as [[Hb_old [Hb_ne _]] | Hb_K].
      + rewrite (collapse_old a Ha_old), (collapse_old b Hb_old).
        rewrite (Hclone_ext a b Ha_old Ha_ne Hb_old Hb_ne).
        apply bounded_orel_refl'.
      + rewrite (collapse_old a Ha_old), (collapse_clone b Hb_K).
        rewrite (Hclone_in a b Ha_old Ha_ne Hb_K).
        apply bounded_orel_refl'.
      + rewrite (collapse_clone a Ha_K), (collapse_old b Hb_old).
        rewrite (Hclone_out b a Hb_old Hb_ne Ha_K).
        apply bounded_orel_refl'.
      + rewrite (collapse_clone a Ha_K), (collapse_clone b Hb_K).
        rewrite (Hdiag_old d d eq_refl).
        apply orel_le_one.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Path strengths are preserved (Schulze 4.6.4 to 4.6.6)              *)
  (* ------------------------------------------------------------------ *)

  (** (4.6.4) Strengths between surviving alternatives are unchanged. *)
  Theorem clone_strength_survivors (a b : Node) :
    List.In a A_old -> a <> d -> List.In b A_old -> b <> d ->
    path_star A_new M_new a b = path_star A_old M_old a b.
  Proof.
    intros Ha Ha_ne Hb Hb_ne.
    destruct (nonempty_has_member K HK_nonempty) as [g Hg].
    apply orel_antisym.
    - pose proof (collapse_transport a b
        (in_A_new_intro_old a Ha Ha_ne) (in_A_new_intro_old b Hb Hb_ne)) as H.
      rewrite (collapse_old a Ha), (collapse_old b Hb) in H. exact H.
    - pose proof (expand_transport g a b Hg Ha Hb) as H.
      rewrite (expand_other g a Ha_ne), (expand_other g b Hb_ne) in H. exact H.
  Qed.

  (** (4.6.5) The strength into any clone equals the old strength into [d]. *)
  Theorem clone_strength_to_clone (a g : Node) :
    List.In a A_old -> a <> d -> List.In g K ->
    path_star A_new M_new a g = path_star A_old M_old a d.
  Proof.
    intros Ha Ha_ne Hg.
    apply orel_antisym.
    - pose proof (collapse_transport a g
        (in_A_new_intro_old a Ha Ha_ne) (in_A_new_intro_clone g Hg)) as H.
      rewrite (collapse_old a Ha), (collapse_clone g Hg) in H. exact H.
    - pose proof (expand_transport g a d Hg Ha Hd_old) as H.
      rewrite (expand_other g a Ha_ne), expand_d in H. exact H.
  Qed.

  (** (4.6.6) The strength out of any clone equals the old strength out of
      [d].  In particular all clones are pairwise indistinguishable from the
      outside, however they compare among themselves. *)
  Theorem clone_strength_from_clone (a g : Node) :
    List.In a A_old -> a <> d -> List.In g K ->
    path_star A_new M_new g a = path_star A_old M_old d a.
  Proof.
    intros Ha Ha_ne Hg.
    apply orel_antisym.
    - pose proof (collapse_transport g a
        (in_A_new_intro_clone g Hg) (in_A_new_intro_old a Ha Ha_ne)) as H.
      rewrite (collapse_clone g Hg), (collapse_old a Ha) in H. exact H.
    - pose proof (expand_transport g d a Hg Hd_old Ha) as H.
      rewrite expand_d, (expand_other g a Ha_ne) in H. exact H.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Beating and winning over a candidate list                          *)
  (*                                                                     *)
  (*  [beats_on] and [winner_on] are [schulze_beats] and [schulze_winner] *)
  (*  of SocialchoiceN with [mat_star] replaced by the list-indexed       *)
  (*  closure, and with the quantifier ranging over the candidate list    *)
  (*  rather than over the whole [Node] type.  At [ns := elements] they   *)
  (*  agree with the originals via [path_star_elements_is_mat_star].      *)
  (* ------------------------------------------------------------------ *)

  Definition beats_on (ns : list Node) (m : @OrelN.Matrix Node R)
    (a b : Node) : Prop :=
    path_star ns m b a ≤ path_star ns m a b /\
    path_star ns m b a <> path_star ns m a b.

  Definition winner_on (ns : list Node) (m : @OrelN.Matrix Node R)
    (a : Node) : Prop :=
    forall b, List.In b ns -> b <> a -> ~ beats_on ns m b a.

  Lemma beats_on_asym (ns : list Node) (m : @OrelN.Matrix Node R) (a b : Node) :
    beats_on ns m a b -> ~ beats_on ns m b a.
  Proof.
    intros [Hab_le Hab_ne] [Hba_le _].
    apply Hab_ne. apply orel_antisym; assumption.
  Qed.

  Lemma beats_on_irrefl (ns : list Node) (m : @OrelN.Matrix Node R) (a : Node) :
    ~ beats_on ns m a a.
  Proof. intros H. exact (beats_on_asym ns m a a H H). Qed.

  (** Beating depends only on the two strengths, so the strength equalities
      above transfer the whole beat relation. *)
  Lemma beats_on_congr (ns1 : list Node) (m1 : @OrelN.Matrix Node R)
    (ns2 : list Node) (m2 : @OrelN.Matrix Node R) (a b a' b' : Node) :
    path_star ns1 m1 a b = path_star ns2 m2 a' b' ->
    path_star ns1 m1 b a = path_star ns2 m2 b' a' ->
    beats_on ns1 m1 a b -> beats_on ns2 m2 a' b'.
  Proof.
    unfold beats_on. intros Hab Hba [Hle Hne].
    rewrite Hab, Hba in Hle, Hne. split; assumption.
  Qed.

  (** A clone beats a survivor exactly when [d] used to. *)
  Lemma clone_beats_survivor (g a : Node) :
    List.In g K -> List.In a A_old -> a <> d ->
    beats_on A_new M_new g a -> beats_on A_old M_old d a.
  Proof.
    intros Hg Ha Ha_ne Hbeats.
    apply (beats_on_congr A_new M_new A_old M_old g a d a);
      [ exact (clone_strength_from_clone a g Ha Ha_ne Hg)
      | exact (clone_strength_to_clone a g Ha Ha_ne Hg)
      | exact Hbeats ].
  Qed.

  Lemma d_beats_survivor (g a : Node) :
    List.In g K -> List.In a A_old -> a <> d ->
    beats_on A_old M_old d a -> beats_on A_new M_new g a.
  Proof.
    intros Hg Ha Ha_ne Hbeats.
    apply (beats_on_congr A_old M_old A_new M_new d a g a);
      [ exact (eq_sym (clone_strength_from_clone a g Ha Ha_ne Hg))
      | exact (eq_sym (clone_strength_to_clone a g Ha Ha_ne Hg))
      | exact Hbeats ].
  Qed.

  (** A survivor beats a clone exactly when it used to beat [d]. *)
  Lemma survivor_beats_clone (b g : Node) :
    List.In g K -> List.In b A_old -> b <> d ->
    beats_on A_new M_new b g -> beats_on A_old M_old b d.
  Proof.
    intros Hg Hb Hb_ne Hbeats.
    apply (beats_on_congr A_new M_new A_old M_old b g b d);
      [ exact (clone_strength_to_clone b g Hb Hb_ne Hg)
      | exact (clone_strength_from_clone b g Hb Hb_ne Hg)
      | exact Hbeats ].
  Qed.

  Lemma survivor_beats_d (b g : Node) :
    List.In g K -> List.In b A_old -> b <> d ->
    beats_on A_old M_old b d -> beats_on A_new M_new b g.
  Proof.
    intros Hg Hb Hb_ne Hbeats.
    apply (beats_on_congr A_old M_old A_new M_new b d b g);
      [ exact (eq_sym (clone_strength_to_clone b g Hb Hb_ne Hg))
      | exact (eq_sym (clone_strength_from_clone b g Hb Hb_ne Hg))
      | exact Hbeats ].
  Qed.

  (** Survivors beat each other exactly as before. *)
  Lemma survivors_beat_new_old (a b : Node) :
    List.In a A_old -> a <> d -> List.In b A_old -> b <> d ->
    beats_on A_new M_new a b -> beats_on A_old M_old a b.
  Proof.
    intros Ha Ha_ne Hb Hb_ne Hbeats.
    apply (beats_on_congr A_new M_new A_old M_old a b a b);
      [ exact (clone_strength_survivors a b Ha Ha_ne Hb Hb_ne)
      | exact (clone_strength_survivors b a Hb Hb_ne Ha Ha_ne)
      | exact Hbeats ].
  Qed.

  Lemma survivors_beat_old_new (a b : Node) :
    List.In a A_old -> a <> d -> List.In b A_old -> b <> d ->
    beats_on A_old M_old a b -> beats_on A_new M_new a b.
  Proof.
    intros Ha Ha_ne Hb Hb_ne Hbeats.
    apply (beats_on_congr A_old M_old A_new M_new a b a b);
      [ exact (eq_sym (clone_strength_survivors a b Ha Ha_ne Hb Hb_ne))
      | exact (eq_sym (clone_strength_survivors b a Hb Hb_ne Ha Ha_ne))
      | exact Hbeats ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Decidability and transitivity of the list-indexed beat relation     *)
  (* ------------------------------------------------------------------ *)

  Lemma orel_dec (Hdec : forall x y : R, {x = y} + {x <> y}) (x y : R) :
    {x ≤ y} + {~ (x ≤ y)}.
  Proof. unfold Orel. exact (Hdec (x + y) y). Qed.

  Lemma beats_on_dec (Hdec : forall x y : R, {x = y} + {x <> y})
    (ns : list Node) (m : @OrelN.Matrix Node R) (a b : Node) :
    {beats_on ns m a b} + {~ beats_on ns m a b}.
  Proof.
    unfold beats_on.
    destruct (orel_dec Hdec (path_star ns m b a) (path_star ns m a b)) as [Hle | Hle].
    - destruct (Hdec (path_star ns m b a) (path_star ns m a b)) as [Heq | Hne].
      + right. intros [_ Hne']. exact (Hne' Heq).
      + left. split; assumption.
    - right. intros [Hle' _]. exact (Hle Hle').
  Qed.

  (** Transitivity of the list-indexed beat relation.  This is
      [schulze_trans_weaker_necessary] of SocialchoiceN with [mat_star]
      replaced by [path_star] and [star_path_compose] replaced by
      [path_star_compose]; the argument is otherwise the same, and needs the
      same two selectivity hypotheses. *)
  Lemma beats_on_trans (ns : list Node) (m : @OrelN.Matrix Node R)
    (Hns : ns <> [])
    (Hdiag : forall u v : Node, u = v -> m u v = 1)
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (H_meet_lower_bound : forall u v w : R, u ≤ v -> u ≤ w -> u ≤ v * w) :
    forall a b c, List.In a ns -> List.In b ns -> List.In c ns ->
      beats_on ns m a b -> beats_on ns m b c -> beats_on ns m a c.
  Proof.
    intros a b c Ha Hb Hc H_ab H_bc.
    destruct H_ab as [H_ab_le H_ab_ne].
    destruct H_bc as [H_bc_le H_bc_ne].
    pose proof (path_star_compose ns m a b c Hns Hdiag Ha Hb Hc) as Hm_Sac.
    assert (H_total_orel : forall x y : R, x ≤ y \/ y ≤ x).
    { intros x y.
      destruct (H_total_order x y) as [Hcase | Hcase].
      - right. unfold Orel. rewrite addC. exact Hcase.
      - left. unfold Orel. exact Hcase. }
    assert (H_not_ac_le_ca : ~ (path_star ns m a c ≤ path_star ns m c a)).
    { intro H_ac_le_ca.
      assert (Hm_Sca : path_star ns m a b * path_star ns m b c ≤ path_star ns m c a).
      { eapply orel_trans; [exact Hm_Sac | exact H_ac_le_ca]. }
      destruct (H_total_orel (path_star ns m a b) (path_star ns m b c))
        as [Hab_le_Hbc | Hbc_le_Hab].
      - assert (Hm_eq_Sab : path_star ns m a b * path_star ns m b c
                            = path_star ns m a b).
        { apply orel_antisym.
          - apply (@bounded_mul_lower_left R (path_star ns m a b) (path_star ns m b c)).
          - apply H_meet_lower_bound.
            + apply (@bounded_orel_refl R (path_star ns m a b)).
            + exact Hab_le_Hbc. }
        rewrite Hm_eq_Sab in Hm_Sca.
        assert (H_Sbc_ge_m : path_star ns m a b ≤ path_star ns m b c).
        { rewrite <- Hm_eq_Sab.
          apply (@bounded_mul_lower_right R (path_star ns m a b) (path_star ns m b c)). }
        assert (Hm_Sbc_Sca : path_star ns m a b
                             ≤ path_star ns m b c * path_star ns m c a).
        { apply H_meet_lower_bound; [exact H_Sbc_ge_m | exact Hm_Sca]. }
        pose proof (path_star_compose ns m b c a Hns Hdiag Hb Hc Ha) as H_comp.
        assert (Hm_Sba : path_star ns m a b ≤ path_star ns m b a).
        { eapply orel_trans; [exact Hm_Sbc_Sca | exact H_comp]. }
        assert (Heq : path_star ns m b a = path_star ns m a b).
        { apply orel_antisym; [exact H_ab_le | exact Hm_Sba]. }
        exact (H_ab_ne Heq).
      - assert (Hm_eq_Sbc : path_star ns m a b * path_star ns m b c
                            = path_star ns m b c).
        { apply orel_antisym.
          - apply (@bounded_mul_lower_right R (path_star ns m a b) (path_star ns m b c)).
          - apply H_meet_lower_bound.
            + exact Hbc_le_Hab.
            + apply (@bounded_orel_refl R (path_star ns m b c)). }
        rewrite Hm_eq_Sbc in Hm_Sca.
        assert (H_Sab_ge_m : path_star ns m b c ≤ path_star ns m a b).
        { rewrite <- Hm_eq_Sbc.
          apply (@bounded_mul_lower_left R (path_star ns m a b) (path_star ns m b c)). }
        assert (Hm_Sca_Sab : path_star ns m b c
                             ≤ path_star ns m c a * path_star ns m a b).
        { apply H_meet_lower_bound; [exact Hm_Sca | exact H_Sab_ge_m]. }
        pose proof (path_star_compose ns m c a b Hns Hdiag Hc Ha Hb) as H_comp.
        assert (Hm_Scb : path_star ns m b c ≤ path_star ns m c b).
        { eapply orel_trans; [exact Hm_Sca_Sab | exact H_comp]. }
        assert (Heq : path_star ns m c b = path_star ns m b c).
        { apply orel_antisym; [exact H_bc_le | exact Hm_Scb]. }
        exact (H_bc_ne Heq). }
    destruct (H_total_orel (path_star ns m a c) (path_star ns m c a))
      as [Hac_le_Sca | Hca_le_Sac].
    - exfalso. exact (H_not_ac_le_ca Hac_le_Sca).
    - split; [exact Hca_le_Sac |].
      intro Heq. apply H_not_ac_le_ca. rewrite Heq.
      apply (@bounded_orel_refl R (path_star ns m a c)).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Winner sets (Schulze 4.6.7 and 4.6.8)                              *)
  (* ------------------------------------------------------------------ *)

  (** A nonempty list has a maximal element under any decidable relation that
      is transitive and irreflexive on its members.  Restricting the two
      order hypotheses to members of the list is what lets [beats_on_trans],
      which needs its arguments to be candidates, be used here. *)
  Lemma exists_maximal_in (Rel : Node -> Node -> Prop) :
    forall (l : list Node),
    (forall x y z, List.In x l -> List.In y l -> List.In z l ->
       Rel x y -> Rel y z -> Rel x z) ->
    (forall x, List.In x l -> ~ Rel x x) ->
    (forall x y, {Rel x y} + {~ Rel x y}) ->
    l <> [] ->
    exists w, List.In w l /\ forall y, List.In y l -> ~ Rel y w.
  Proof.
    induction l as [|x t IH]; intros Htrans Hirr Hdecb Hne.
    - exfalso. apply Hne. reflexivity.
    - destruct t as [|z t'].
      + exists x. split; [left; reflexivity |].
        intros y Hy. destruct Hy as [Hy | []]. subst y.
        apply Hirr. left. reflexivity.
      + assert (Ht_ne : z :: t' <> []) by discriminate.
        assert (Htrans' : forall u v w, List.In u (z :: t') -> List.In v (z :: t') ->
                  List.In w (z :: t') -> Rel u v -> Rel v w -> Rel u w).
        { intros u v w Hu Hv Hw. apply Htrans; right; assumption. }
        assert (Hirr' : forall u, List.In u (z :: t') -> ~ Rel u u).
        { intros u Hu. apply Hirr. right. exact Hu. }
        destruct (IH Htrans' Hirr' Hdecb Ht_ne) as [w [Hw Hwmax]].
        destruct (Hdecb x w) as [Hxw | Hxw].
        * exists x. split; [left; reflexivity |].
          intros y Hy. destruct Hy as [Hy | Hy].
          -- subst y. apply Hirr. left. reflexivity.
          -- intros Hyx. apply (Hwmax y Hy).
             apply (Htrans y x w);
               [right; exact Hy | left; reflexivity | right; exact Hw
               | exact Hyx | exact Hxw].
        * exists w. split; [right; exact Hw |].
          intros y Hy. destruct Hy as [Hy | Hy].
          -- subst y. exact Hxw.
          -- exact (Hwmax y Hy).
  Qed.

  (** (4.6.8) A surviving alternative wins the new election exactly when it
      won the old one.  This needs nothing beyond the three strength
      equalities, so no selectivity assumption on the semiring appears. *)
  Theorem clone_winner_survivors (a : Node) :
    List.In a A_old -> a <> d ->
    (winner_on A_old M_old a <-> winner_on A_new M_new a).
  Proof.
    intros Ha Ha_ne. split.
    - intros Hwin b Hb_new Hb_ne Hbeats.
      destruct (in_A_new_inv b Hb_new) as [[Hb_old [Hb_d _]] | Hb_K].
      + exact (Hwin b Hb_old Hb_ne
                 (survivors_beat_new_old b a Hb_old Hb_d Ha Ha_ne Hbeats)).
      + apply (Hwin d Hd_old (fun h => Ha_ne (eq_sym h))).
        exact (clone_beats_survivor b a Hb_K Ha Ha_ne Hbeats).
    - intros Hwin b Hb_old Hb_ne Hbeats.
      destruct (fin_eq_dec b d) as [Hbd | Hbn].
      + subst b.
        destruct (nonempty_has_member K HK_nonempty) as [g Hg].
        assert (Hg_ne : g <> a).
        { intro Heq. subst g. exact (old_not_clone a Ha Hg). }
        exact (Hwin g (in_A_new_intro_clone g Hg) Hg_ne
                 (d_beats_survivor g a Hg Ha Ha_ne Hbeats)).
      + exact (Hwin b (in_A_new_intro_old b Hb_old Hbn) Hb_ne
                 (survivors_beat_old_new b a Hb_old Hbn Ha Ha_ne Hbeats)).
  Qed.

  (** Half of (4.6.7): if any clone wins the new election then [d] won the old
      one.  Contrapositively, a beaten [d] leaves every clone beaten. *)
  Theorem clone_winner_implies_d_winner (g : Node) :
    List.In g K -> winner_on A_new M_new g -> winner_on A_old M_old d.
  Proof.
    intros Hg Hwin b Hb_old Hb_ne Hbeats.
    assert (Hb_ne_g : b <> g).
    { intro Heq. subst b. exact (HK_fresh g Hg Hb_old). }
    exact (Hwin b (in_A_new_intro_old b Hb_old Hb_ne) Hb_ne_g
             (survivor_beats_d b g Hg Hb_old Hb_ne Hbeats)).
  Qed.

  (** The other half.  No survivor can beat a clone, so the only obstacle is
      the clones beating one another, and a maximal clone under the new beat
      relation is therefore a winner.  This is the one step that needs the
      beat relation to be transitive and decidable, exactly as Schulze's own
      proof invokes asymmetry and transitivity of [O_new].  Both are supplied
      by [beats_on_trans] and [beats_on_dec] below; they are left as
      hypotheses here so that the statement stays independent of which
      selectivity assumptions one is willing to make. *)
  Theorem d_winner_implies_clone_winner
    (Htrans : forall x y z, List.In x A_new -> List.In y A_new -> List.In z A_new ->
                beats_on A_new M_new x y -> beats_on A_new M_new y z ->
                beats_on A_new M_new x z)
    (Hdecb : forall x y, {beats_on A_new M_new x y} + {~ beats_on A_new M_new x y}) :
    winner_on A_old M_old d ->
    exists g, List.In g K /\ winner_on A_new M_new g.
  Proof.
    intros Hwin_d.
    destruct (exists_maximal_in (beats_on A_new M_new) K
                (fun x y z Hx Hy Hz => Htrans x y z
                   (in_A_new_intro_clone x Hx) (in_A_new_intro_clone y Hy)
                   (in_A_new_intro_clone z Hz))
                (fun x _ => beats_on_irrefl A_new M_new x)
                Hdecb HK_nonempty) as [w [Hw Hwmax]].
    exists w. split; [exact Hw |].
    intros b Hb_new Hb_ne Hbeats.
    destruct (in_A_new_inv b Hb_new) as [[Hb_old [Hb_d _]] | Hb_K].
    - exact (Hwin_d b Hb_old Hb_d
               (survivor_beats_clone b w Hw Hb_old Hb_d Hbeats)).
    - exact (Hwmax b Hb_K Hbeats).
  Qed.

  (** Independence of clones (4.6.7 and 4.6.8 together): replacing an
      alternative by a set of clones leaves the winner status of every other
      alternative untouched, and puts a clone in the winner set exactly when
      the replaced alternative was in it. *)
  Theorem independence_of_clones
    (Htrans : forall x y z, List.In x A_new -> List.In y A_new -> List.In z A_new ->
                beats_on A_new M_new x y -> beats_on A_new M_new y z ->
                beats_on A_new M_new x z)
    (Hdecb : forall x y, {beats_on A_new M_new x y} + {~ beats_on A_new M_new x y}) :
    (forall a, List.In a A_old -> a <> d ->
       (winner_on A_old M_old a <-> winner_on A_new M_new a))
    /\ (winner_on A_old M_old d <-> exists g, List.In g K /\ winner_on A_new M_new g).
  Proof.
    split.
    - exact clone_winner_survivors.
    - split.
      + exact (d_winner_implies_clone_winner Htrans Hdecb).
      + intros [g [Hg Hwin]]. exact (clone_winner_implies_d_winner g Hg Hwin).
  Qed.

  (** Independence of clones with the two order hypotheses discharged.  The
      three assumptions are exactly the ones SocialchoiceN carries for the
      corresponding results about [mat_star]: the order on path strengths is
      total, equality on strengths is decidable, and multiplication is a
      greatest lower bound.  Nothing about clones is assumed beyond the three
      hypotheses of this section. *)
  Theorem independence_of_clones_selective
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (HdecR : forall x y : R, {x = y} + {x <> y})
    (H_meet_lower_bound : forall u v w : R, u ≤ v -> u ≤ w -> u ≤ v * w) :
    (forall a, List.In a A_old -> a <> d ->
       (winner_on A_old M_old a <-> winner_on A_new M_new a))
    /\ (winner_on A_old M_old d <-> exists g, List.In g K /\ winner_on A_new M_new g).
  Proof.
    apply independence_of_clones.
    - exact (beats_on_trans A_new M_new A_new_nonempty Hdiag_new
               H_total_order H_meet_lower_bound).
    - exact (beats_on_dec HdecR A_new M_new).
  Qed.

End CloneReplacement.


(* ===================================================================== *)
(*  The clone development speaks about the Schulze winner set            *)
(*                                                                        *)
(*  [beats_on] and [winner_on] were introduced over a candidate list so   *)
(*  that two elections with different alternative sets could be compared. *)
(*  At [elements] they are literally the relations of SocialchoiceN, so   *)
(*  the theorems above are about the same notion of winner as the rest of *)
(*  the development and not a parallel one.                               *)
(* ===================================================================== *)

Section CloneAtElements.

  Context {Node : FinType.type}.
  Context {R : BoundedSemiring.type}.

  Lemma beats_on_elements_is_schulze_beats
    (m : @OrelN.Matrix Node R) (a b : Node) :
    beats_on (@elements Node) m a b <-> schulze_beats m a b.
  Proof.
    unfold beats_on, schulze_beats, beats.
    rewrite !path_star_elements_is_mat_star.
    reflexivity.
  Qed.

  Lemma winner_on_elements_is_schulze_winner
    (m : @OrelN.Matrix Node R) (a : Node) :
    winner_on (@elements Node) m a <-> schulze_winner m a.
  Proof.
    unfold winner_on, schulze_winner. split.
    - intros Hwin b Hb_ne Hbeats.
      apply (Hwin b (elements_complete b) Hb_ne).
      exact (proj2 (beats_on_elements_is_schulze_beats m b a) Hbeats).
    - intros Hwin b _ Hb_ne Hbeats.
      apply (Hwin b Hb_ne).
      exact (proj1 (beats_on_elements_is_schulze_beats m b a) Hbeats).
  Qed.

End CloneAtElements.
