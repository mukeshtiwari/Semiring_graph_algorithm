(** * Independence of clones over the diamond at FOUR alternatives.

    [clone_characterisation] states the equivalence between the clone
    criterion and the two bottleneck axioms at five or more alternatives.
    This file shows that five is optimal: over the diamond lattice D4,
    which is bounded, has the meet property, and is NOT selective, the
    clone criterion holds at four ambient alternatives, so no
    four-alternative configuration can derive selectivity from it.

    The reason is a triangle argument, not an exhaustive search.  The
    survivor clause and one direction of the clone clause hold over any
    bounded semiring (CloneN).  The remaining direction needs an
    unbeaten clone, and with four ambient alternatives the clone set has
    at most three distinct members, so the only obstruction would be a
    beat three-cycle among the clones.  A three-cycle forces a cyclic
    triple in the carrier (beats_on_cycle3_cyclic_triple), and the
    diamond has no cyclic triple (diamond_no_cyclic_triple): its width
    is two, and a cyclic triple needs three values that pairwise meet
    strictly below each of them. *)

From Stdlib Require Import List Utf8 Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN SocialchoiceN
  ClosureTransportN BeatsOnN CloneN CloneCharacterisationN.
From Examples Require Import SharpnessWitness.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).

Section CloneFour.

  Lemma D4_eq_dec : forall x y : D4, {x = y} + {x <> y}.
  Proof. decide equality. Qed.

  (** The three alternatives other than [d]. *)
  Lemma node4_rest (d : Node4) :
    exists a b c : Node4, forall x : Node4, x <> d -> x = a \/ x = b \/ x = c.
  Proof.
    destruct d;
      [ exists W2, W3, W4 | exists W1, W3, W4
      | exists W1, W2, W4 | exists W1, W2, W3 ];
      intros [| | |] Hx; try congruence; auto.
  Qed.

  (** Over the diamond, four ambient alternatives satisfy independence of
      clones. *)
  Theorem diamond_clone_independence_at_four :
    @clone_independence Node4 D4.
  Proof.
    unfold clone_independence.
    intros A_old K d M_old M_new Hd HK Hfresh Hdiag_old Hdiag_new
      Hout Hin Hext.
    split.
    - (* the survivor clause holds over any bounded semiring *)
      exact (clone_winner_survivors A_old K d M_old M_new Hd HK Hfresh
               Hdiag_old Hdiag_new Hout Hin Hext).
    - split.
      + (* d wins the old election: an unbeaten clone wins the new one *)
        intro Hwin_d.
        destruct (node4_rest d) as (a & b & c & Hrest).
        (** the clones avoid [d], so they draw on at most three values *)
        assert (Hsmall : forall u, List.In u K -> u = a \/ u = b \/ u = c).
        { intros u Hu. apply Hrest. intro Heq. subst u.
          exact (Hfresh d Hu Hd). }
        (** no beat three-cycle among the clones: a cycle would force a
            cyclic triple, and the diamond has none *)
        assert (Hnc : forall u v w,
                  List.In u K -> List.In v K -> List.In w K ->
                  beats_on (A_new A_old K d) M_new u v ->
                  beats_on (A_new A_old K d) M_new v w ->
                  beats_on (A_new A_old K d) M_new w u -> False).
        { intros u v w Hu Hv Hw R1 R2 R3.
          destruct (beats_on_cycle3_cyclic_triple (A_new A_old K d) M_new
                      (A_new_nonempty A_old K d HK) Hdiag_new u v w
                      (in_A_new_intro_clone A_old K d u Hu)
                      (in_A_new_intro_clone A_old K d v Hv)
                      (in_A_new_intro_clone A_old K d w Hw) R1 R2 R3)
            as (F1 & F2 & F3 & H1 & H2 & H3).
          exact (diamond_no_cyclic_triple F1 F2 F3 H1 H2 H3). }
        destruct (exists_unbeaten_small (beats_on (A_new A_old K d) M_new)
                    (beats_on_dec D4_eq_dec (A_new A_old K d) M_new)
                    (beats_on_asym (A_new A_old K d) M_new)
                    a b c K Hsmall Hnc HK) as (w & Hw & Hunb).
        exists w. split; [exact Hw |].
        intros b0 Hb0_in Hb0_ne Hbeats.
        destruct (in_A_new_inv A_old K d Hfresh b0 Hb0_in)
          as [(Hb_old & Hb_d & _) | Hb_K].
        * (* a survivor beating the clone would have beaten [d] before *)
          exact (Hwin_d b0 Hb_old Hb_d
                   (survivor_beats_clone A_old K d M_old M_new Hd HK Hfresh
                      Hdiag_old Hdiag_new Hout Hin Hext b0 w Hw Hb_old Hb_d
                      Hbeats)).
        * exact (Hunb b0 Hb_K Hbeats).
      + intros (g & Hg & Hwg).
        exact (clone_winner_implies_d_winner A_old K d M_old M_new Hd HK
                 Hfresh Hdiag_old Hdiag_new Hout Hin Hext g Hg Hwg).
  Qed.

  (** Five alternatives are optimal in [clone_characterisation]: at four,
      the clone criterion holds over a carrier that is not selective, so the
      equivalence of the characterisation fails and its hypothesis
      [5 <= length elements] cannot be weakened to four. *)
  Theorem clone_characterisation_four_insufficient :
    @clone_independence Node4 D4 /\
    ~ (forall x y : D4, x + y = x \/ x + y = y).
  Proof.
    split.
    - exact diamond_clone_independence_at_four.
    - intro Hsel.
      destruct diamond_not_selective as (x & y & Hx & Hy).
      destruct (Hsel x y) as [H | H]; [exact (Hx H) | exact (Hy H)].
  Qed.

End CloneFour.
