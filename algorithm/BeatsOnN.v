From Stdlib Require Import List Utf8 Lia.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures SocialchoiceN
  ClosureTransportN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).

(** * Beating and winning over a candidate list.

    [beats_on] and [winner_on] are [schulze_beats] and [schulze_winner]
    with [mat_star] replaced by the list-indexed closure, and with the
    quantifier ranging over a candidate list rather than over the whole
    [Node] type.  At [elements] they are the originals, which is what
    the two bridge lemmas at the end of the file record. *)

Section BeatsOnN.

  Context {Node : FinType.type}.
  Context {R : BoundedSemiring.type}.

  (** ** Beating and winning over a candidate list

      [beats_on] and [winner_on] are [schulze_beats] and [schulze_winner]
      of SocialchoiceN with [mat_star] replaced by the list-indexed
      closure, and with the quantifier ranging over the candidate list
      rather than over the whole [Node] type.  At [ns := elements] they
      agree with the originals via [path_star_elements_is_mat_star]. *)

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
  (** ** Decidability and transitivity of the list-indexed beat relation *)

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

  (** ** Three-cycles in the beat relation

      A three-cycle forces a CYCLIC TRIPLE in the carrier: three values,
      each strictly above the product of the other two.  This is the
      triangle core of the transitivity argument read contrapositively,
      and it needs no selectivity and no meet property — only the
      composition bound.  A carrier with no cyclic triple, such as the
      diamond lattice, therefore admits no beat three-cycle over any
      candidate list, which is what the clone criterion at four
      alternatives turns on. *)

  Lemma beats_on_cycle3_cyclic_triple (ns : list Node)
    (m : @OrelN.Matrix Node R)
    (Hns : ns <> [])
    (Hdiag : forall u v : Node, u = v -> m u v = 1)
    (x y z : Node)
    (Hx : List.In x ns) (Hy : List.In y ns) (Hz : List.In z ns) :
    beats_on ns m x y -> beats_on ns m y z -> beats_on ns m z x ->
    exists F1 F2 F3 : R,
      (F1 * F2 ≤ F3 /\ F1 * F2 <> F3) /\
      (F2 * F3 ≤ F1 /\ F2 * F3 <> F1) /\
      (F3 * F1 ≤ F2 /\ F3 * F1 <> F2).
  Proof.
    intros [B1le B1ne] [B2le B2ne] [B3le B3ne].
    exists (path_star ns m x y), (path_star ns m y z), (path_star ns m z x).
    pose proof (path_star_compose ns m x y z Hns Hdiag Hx Hy Hz) as C1.
    pose proof (path_star_compose ns m y z x Hns Hdiag Hy Hz Hx) as C2.
    pose proof (path_star_compose ns m z x y Hns Hdiag Hz Hx Hy) as C3.
    split; [| split]; split.
    - exact (orel_trans _ _ _ C1 B3le).
    - intro Heq. apply B3ne. apply orel_antisym; [exact B3le |].
      rewrite <- Heq. exact C1.
    - exact (orel_trans _ _ _ C2 B1le).
    - intro Heq. apply B1ne. apply orel_antisym; [exact B1le |].
      rewrite <- Heq. exact C2.
    - exact (orel_trans _ _ _ C3 B2le).
    - intro Heq. apply B2ne. apply orel_antisym; [exact B2le |].
      rewrite <- Heq. exact C3.
  Qed.

  (** Four values drawn from a three-element set must collide somewhere. *)
  Lemma four_in_three_collide (a b c u0 u1 u2 u3 : Node) :
    (u0 = a \/ u0 = b \/ u0 = c) ->
    (u1 = a \/ u1 = b \/ u1 = c) ->
    (u2 = a \/ u2 = b \/ u2 = c) ->
    (u3 = a \/ u3 = b \/ u3 = c) ->
    u1 = u0 \/ u2 = u1 \/ u3 = u2 \/ u2 = u0 \/ u3 = u1 \/ u3 = u0.
  Proof.
    intros H0 H1 H2 H3.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; tauto.
  Qed.

  (** On a list drawn from at most three values, an asymmetric decidable
      relation with no three-cycle leaves some member unbeaten.  Every
      beaten-by-beaten chain of length three must collide, and each
      collision is either an asymmetry violation or a three-cycle. *)
  Lemma exists_unbeaten_small (Rel : Node -> Node -> Prop)
    (Hdec : forall u v : Node, {Rel u v} + {~ Rel u v})
    (Hasym : forall u v : Node, Rel u v -> ~ Rel v u)
    (a b c : Node) (l : list Node)
    (Hsmall : forall u, List.In u l -> u = a \/ u = b \/ u = c)
    (Hnc : forall u v w, List.In u l -> List.In v l -> List.In w l ->
             Rel u v -> Rel v w -> Rel w u -> False)
    (Hne : l <> []) :
    exists w, List.In w l /\ forall u, List.In u l -> ~ Rel u w.
  Proof.
    set (beatenb := fun u : Node =>
      existsb (fun v => if Hdec v u then true else false) l).
    assert (Hbeaten : forall u, beatenb u = true ->
              exists v, List.In v l /\ Rel v u).
    { intros u Hu. unfold beatenb in Hu.
      destruct (proj1 (existsb_exists _ _) Hu) as (v & Hv & Hif).
      exists v. split; [exact Hv |].
      destruct (Hdec v u) as [HR | HR]; [exact HR | discriminate]. }
    destruct (existsb (fun u => negb (beatenb u)) l) eqn:E.
    - (* some member is unbeaten *)
      destruct (proj1 (existsb_exists _ _) E) as (w & Hw & Hnb).
      exists w. split; [exact Hw |].
      intros u Hu HR.
      assert (Hb : beatenb w = true).
      { unfold beatenb. apply existsb_exists. exists u. split; [exact Hu |].
        destruct (Hdec u w) as [_ | Habs]; [reflexivity | contradiction]. }
      rewrite Hb in Hnb. discriminate.
    - (* every member is beaten: build a chain of three beaters and collide *)
      exfalso.
      assert (Hallb : forall u, List.In u l ->
                exists v, List.In v l /\ Rel v u).
      { intros u Hu. apply Hbeaten.
        destruct (beatenb u) eqn:Eb; [reflexivity | exfalso].
        assert (Htrue : existsb (fun u0 => negb (beatenb u0)) l = true).
        { apply existsb_exists. exists u. split; [exact Hu |].
          rewrite Eb. reflexivity. }
        rewrite E in Htrue. discriminate. }
      destruct l as [| u0 t] eqn:El; [exact (Hne eq_refl) |].
      rewrite <- El in *.
      assert (Hu0 : List.In u0 l) by (rewrite El; left; reflexivity).
      destruct (Hallb u0 Hu0) as (v1 & Hv1 & R1).
      destruct (Hallb v1 Hv1) as (v2 & Hv2 & R2).
      destruct (Hallb v2 Hv2) as (v3 & Hv3 & R3).
      destruct (four_in_three_collide a b c u0 v1 v2 v3
                  (Hsmall u0 Hu0) (Hsmall v1 Hv1) (Hsmall v2 Hv2)
                  (Hsmall v3 Hv3))
        as [Hc1 | [Hc2 | [Hc3 | [Hc4 | [Hc5 | Hc6]]]]].
      + subst v1. exact (Hasym u0 u0 R1 R1).
      + subst v2. exact (Hasym v1 v1 R2 R2).
      + subst v3. exact (Hasym v2 v2 R3 R3).
      + subst v2. exact (Hasym v1 u0 R1 R2).
      + subst v3. exact (Hasym v2 v1 R2 R3).
      + subst v3. exact (Hnc u0 v2 v1 Hu0 Hv2 Hv1 R3 R2 R1).
  Qed.

  (** ** Winner sets (Schulze 4.6.7 and 4.6.8) *)

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
End BeatsOnN.
