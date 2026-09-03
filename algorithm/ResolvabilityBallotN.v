(** * Resolvability from the ballots (Schulze 4.2.1 and 4.2.2)

    Both formulations of resolvability are statements about profiles, so
    they need the ballot layer of BallotN.v.  Two results:

      - 4.2.1, combinatorial core: if no two distinct links of the profile
        have the same strength, there is at most one winner.  This is the
        matrix theorem of CriticalLinkN.v applied to [matrix_of m P].

      - 4.2.2: for every winner [a] there is a single ballot [w] whose
        addition makes [a] the unique winner.  Schulze's [w] ranks [a] first
        and orders the other alternatives by their closure strength into [a],
        breaking ties along the predecessor tree of the strongest paths.  The
        ballot used here ranks [a] first and orders the others by [P[.,a]]
        descending, leaving ties as ties; the tree is not needed, because the
        claim it serves (the strongest paths out of [a] are not weakened) is
        proved by a threshold argument instead:

          a link [xe] with [M x e >= t] that [w] weakens has [P[x,a] < P[e,a]]
          and therefore [P[x,a] >= t] and [P[a,e] > t]; so the walk can be
          rerouted to [e] through the closure at the strictly higher level
          [P[a,e]], and an induction on the number of levels above [t]
          closes the argument ([reach_level]).

        Claim 3 of the paper (the closure into [a] drops strictly) is the
        cut lemma of CriticalLinkN.v applied to Schulze's set [T(g)].

    A note on the proofs.  The generic closure lemmas are stated over an
    arbitrary bounded semiring, and applying them to goals over the concrete
    carrier [Strength m] leaves Hierarchy Builder unable to infer the
    structure path.  The block of one-line wrappers below restates the
    lemmas needed at the concrete carrier, so that [apply] and [rewrite] work
    syntactically.  Where a hypothesis and a goal still meet along different
    paths, the proof transports with [eq_ind] instead of rewriting. *)

From Stdlib Require Import Utf8 List Arith Lia Bool Wf_nat.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN OrderSemiring
  NormalizedOrder ExtendOrder MeasureN SocialchoiceN SchulzeOnNT SmithN
  BeatsOnN BallotN CriticalLinkN.
Import ListNotations.

Section ResolvabilityBallotN.

  Context {Node : FinType.type} (m : Measure).

  (** The standing hypotheses of the selective results hold on any [Strength m]. *)
  Let Htot := NT_selective (spec m).
  Let Hmeet := NT_meet_lower_bound (spec m).
  Let Hdec := NT_eq_dec (spec m).

  (** ** 4.2.1: pairwise distinct link strengths give a unique winner *)

  Theorem distinct_links_unique_winner_from_profile (P : @Profile Node) :
    (forall e f g h, e <> f -> g <> h ->
       matrix_of m P e f = matrix_of m P g h -> e = g /\ f = h) ->
    forall a b, schulze_winner (matrix_of m P) a -> schulze_winner (matrix_of m P) b -> a = b.
  Proof.
    intro Hd.
    exact (distinct_links_unique_winner Htot Hmeet Hdec (matrix_of m P)
             (matrix_of_diag m P) (matrix_of_ne_one m P) Hd).
  Qed.

  (** ** Boolean comparison on strengths, and adding one ballot *)

  (** [sgt u v]: [u] is strictly above [v]. *)
  Definition sgt (u v : Strength m) : bool := negb (leN (spec m) u v).

  Lemma sgt_true : forall u v, sgt u v = true <-> (Orel v u /\ v <> u).
  Proof.
    intros u v. unfold sgt. split.
    - intro H. destruct (leN (spec m) u v) eqn:E; [discriminate |].
      assert (Hn : ~ Orel u v).
      { intro Ho. apply (Orel_iff_leN (spec m)) in Ho. congruence. }
      destruct (leN_total (spec m) u v) as [Ht | Ht]; [congruence |].
      split; [apply (Orel_iff_leN (spec m)); exact Ht |].
      intro Heq. subst. apply Hn. apply (Orel_iff_leN (spec m)). apply leN_refl.
    - intros [Hvu Hne]. destruct (leN (spec m) u v) eqn:E; [| reflexivity].
      exfalso. apply Hne. apply orel_antisym; [exact Hvu | apply (Orel_iff_leN (spec m)); exact E].
  Qed.

  Lemma sgt_false : forall u v, sgt u v = false <-> Orel u v.
  Proof.
    intros u v. unfold sgt. rewrite (Orel_iff_leN (spec m)).
    destruct (leN (spec m) u v); cbn; split; intros H; congruence.
  Qed.

  Lemma count_cons : forall (w : @Ballot Node) (P : @Profile Node) i j,
    count (w :: P) i j = (if prefers w i j then S (count P i j) else count P i j).
  Proof. intros w P i j. unfold count. cbn [filter]. destruct (prefers w i j); reflexivity. Qed.

  (** ** The closure lemmas at the concrete carrier *)

  Lemma orefl (u : Strength m) : Orel u u.
  Proof. exact (bounded_orel_refl u). Qed.
  Lemma ole_one (u : Strength m) : Orel u one.
  Proof. exact (le_one u). Qed.
  Lemma ozero (u : Strength m) : Orel zero u.
  Proof. exact (zero_is_bottom u). Qed.
  Lemma mul_le_l (u v : Strength m) : Orel (mul u v) u.
  Proof. exact (bounded_mul_lower_left u v). Qed.
  Lemma mul_le_r (u v : Strength m) : Orel (mul u v) v.
  Proof. exact (bounded_mul_lower_right u v). Qed.
  Lemma mul_compat_l (u v c : Strength m) : Orel u v -> Orel (mul u c) (mul v c).
  Proof. exact (bounded_mul_orel_compat_l u v c). Qed.
  Lemma mul_compat_r (u v c : Strength m) : Orel u v -> Orel (mul c u) (mul c v).
  Proof. exact (bounded_mul_orel_compat_r u v c). Qed.
  Lemma mul_min' (u v : Strength m) : mul u v = u \/ mul u v = v.
  Proof. exact (mul_min Htot Hmeet u v). Qed.
  Lemma mul_gt' (c u v : Strength m) :
    Orel c u /\ c <> u -> Orel c v /\ c <> v -> Orel c (mul u v) /\ c <> mul u v.
  Proof. exact (mul_gt Htot Hmeet c u v). Qed.
  Lemma mstar_diag (N : @Matrix Node (Strength m)) (x : Node) : mat_star N x x = one.
  Proof. exact (mat_star_diag_one N x). Qed.
  Lemma mstar_link (N : @Matrix Node (Strength m)) (i j : Node) : Orel (N i j) (mat_star N i j).
  Proof. exact (link_le_mat_star N i j). Qed.
  Lemma mstar_compose (N : @Matrix Node (Strength m)) (i j k : Node) :
    Orel (mul (mat_star N i j) (mat_star N j k)) (mat_star N i k).
  Proof. exact (star_path_compose N i j k). Qed.
  Lemma mstar_mono (N1 N2 : @Matrix Node (Strength m)) :
    (forall i j, Orel (N1 i j) (N2 i j)) -> forall c d, Orel (mat_star N1 c d) (mat_star N2 c d).
  Proof. intros H c d. exact (geom_sum_monotone N1 N2 (@kleene_exp Node) H c d). Qed.
  Lemma mstar_attained (N : @Matrix Node (Strength m)) (x y : Node) :
    exists k, mat_star N x y = pow N k x y.
  Proof.
    destruct (geom_sum_selective Htot N (@kleene_exp Node) x y) as [k [_ Hk]]. exists k. exact Hk.
  Qed.
  Lemma sum_sel (f : Node -> Strength m) : sum f = zero \/ exists z, sum f = f z.
  Proof. exact (sum_selective Htot f). Qed.
  Lemma pow_0 (N : @Matrix Node (Strength m)) (x g : Node) :
    pow N 0 x g = (if fin_eq_dec x g then one else zero).
  Proof. reflexivity. Qed.
  Lemma pow_S (N : @Matrix Node (Strength m)) (k : nat) (x g : Node) :
    pow N (S k) x g = sum (fun e => mul (N x e) (pow N k e g)).
  Proof. reflexivity. Qed.
  Lemma mstar_cut (N : @Matrix Node (Strength m)) (Bp : Node -> bool) (c : Strength m) :
    Orel zero c /\ zero <> c ->
    (forall i j, Bp i = false -> Bp j = true -> Orel (N i j) c /\ N i j <> c) ->
    forall y x, Bp y = false -> Bp x = true -> Orel (mat_star N y x) c /\ mat_star N y x <> c.
  Proof. exact (mat_star_lt_of_cut Htot N Bp c). Qed.

  (** * 4.2.2: one added ballot makes a winner the unique winner *)

  Section AddBallot.

    Variable P : @Profile Node.
    Variable a : Node.
    Hypothesis Hwin : schulze_winner (matrix_of m P) a.

    Notation M := (matrix_of m P).

    (** ** The ballot: [a] first, then by closure strength into [a] *)

    (** The alternatives whose closure strength into [a] exceeds that of [x]. *)
    Definition above (x : Node) : list Node :=
      filter (fun y => sgt (mat_star M y a) (mat_star M x a)) elements.

    (** Rank 0 for [a]; otherwise one more than the number of alternatives
        strictly stronger into [a].  Equal strengths get equal ranks. *)
    Definition w : @Ballot Node :=
      fun x => if fin_eq_dec x a then 0 else S (length (above x)).

    Lemma w_a : w a = 0.
    Proof. unfold w. destruct (fin_eq_dec a a) as [_ | Hn]; [reflexivity | contradiction]. Qed.

    Lemma w_other : forall x, x <> a -> w x = S (length (above x)).
    Proof.
      intros x Hx. unfold w. destruct (fin_eq_dec x a) as [E | _]; [contradiction | reflexivity].
    Qed.

    (** (4.2.2.4): [w] ranks [a] above everybody. *)
    Lemma prefers_w_a : forall f, f <> a -> prefers w a f = true.
    Proof. intros f Hf. unfold prefers. rewrite w_a, (w_other f Hf). apply Nat.ltb_lt. lia. Qed.

    Lemma prefers_w_into_a : forall e, prefers w e a = false.
    Proof. intro e. unfold prefers. rewrite w_a. apply Nat.ltb_nlt. lia. Qed.

    Lemma above_incl : forall e f, Orel (mat_star M e a) (mat_star M f a) ->
      forall y, In y elements ->
        sgt (mat_star M y a) (mat_star M f a) = true ->
        sgt (mat_star M y a) (mat_star M e a) = true.
    Proof.
      intros e f Hef y _ Hy. apply sgt_true in Hy. apply sgt_true.
      exact (orel_le_lt_trans' _ _ _ Hef Hy).
    Qed.

    (** (4.2.2.3): among the others, [w] prefers [e] to [f] exactly when [e]
        is strictly stronger into [a]. *)
    Lemma prefers_w_order : forall e f, e <> a -> f <> a ->
      (prefers w e f = true <->
       (Orel (mat_star M f a) (mat_star M e a) /\ mat_star M f a <> mat_star M e a)).
    Proof.
      intros e f He Hf. unfold prefers. rewrite (w_other e He), (w_other f Hf).
      split.
      - intro H. apply Nat.ltb_lt in H.
        destruct (orel_total Htot (mat_star M e a) (mat_star M f a)) as [Hle | Hge].
        + exfalso.
          pose proof (filter_length_le_of_impl _ _ elements (above_incl e f Hle)) as Hlen.
          unfold above in H. lia.
        + split; [exact Hge |]. intro Heq.
          unfold above in H. rewrite Heq in H. lia.
      - intros [Hle Hne]. apply Nat.ltb_lt. apply Nat.succ_lt_mono. unfold above.
        pose proof (filter_length_lt_of_strict
                      (fun y => sgt (mat_star M y a) (mat_star M e a))
                      (fun y => sgt (mat_star M y a) (mat_star M f a)) elements e
                      (above_incl f e Hle) (elements_complete e)
                      (proj2 (sgt_true _ _) (conj Hle Hne))
                      (proj2 (sgt_false _ _) (bounded_orel_refl _))) as H.
        lia.
    Qed.

    (** ** How the links move *)

    Notation M' := (matrix_of m (w :: P)).

    (** A link [w] does not oppose keeps or gains strength… *)
    Lemma link_up : forall i j, i <> j -> prefers w j i = false -> Orel (M i j) (M' i j).
    Proof.
      intros i j Hij Hw. rewrite (matrix_of_off m P i j Hij), (matrix_of_off m (w :: P) i j Hij).
      rewrite !count_cons. rewrite Hw. destruct (prefers w i j); apply strength_mono_weak; lia.
    Qed.

    (** …and a link [w] opposes loses strength strictly, by (2.1.1). *)
    Lemma link_down : forall i j, i <> j -> prefers w j i = true ->
      Orel (M' i j) (M i j) /\ M' i j <> M i j.
    Proof.
      intros i j Hij Hw. rewrite (matrix_of_off m P i j Hij), (matrix_of_off m (w :: P) i j Hij).
      rewrite !count_cons. rewrite Hw, (prefers_asym w j i Hw).
      apply strength_211. right. lia.
    Qed.

    (** Closure strengths out of [a] are positive. *)
    Lemma d_pos : forall g, g <> a -> Orel zero (mat_star M a g) /\ zero <> mat_star M a g.
    Proof.
      intros g Hg. split; [apply ozero |]. intro H0.
      apply (strength_ne_zero m (count P a g, count P g a)).
      rewrite <- (matrix_of_off m P a g (not_eq_sym Hg)).
      apply orel_antisym; [| apply ozero].
      exact (orel_trans _ _ _ (mstar_link M a g)
               (eq_ind _ (fun z => Orel (mat_star M a g) z) (orefl _) _ (eq_sym H0))).
    Qed.

    (** ** Claim 3: the closure into [a] drops strictly *)

    (** Schulze's [T(g)]: [a] together with everything strictly stronger into
        [a] than [a] is into [g]. *)
    Definition Tg (g : Node) (x : Node) : bool :=
      if fin_eq_dec x a then true else sgt (mat_star M x a) (mat_star M a g).

    Lemma Tg_a : forall g, Tg g a = true.
    Proof. intro g. unfold Tg. destruct (fin_eq_dec a a) as [_ | Hn]; [reflexivity | contradiction]. Qed.

    Lemma Tg_other : forall g x, x <> a -> Tg g x = sgt (mat_star M x a) (mat_star M a g).
    Proof.
      intros g x Hx. unfold Tg. destruct (fin_eq_dec x a) as [E | _]; [contradiction | reflexivity].
    Qed.

    (** (4.2.2.18): every link entering [T(g)] was at most [P[a,g]] (else its
        source would be in [T(g)]) and is weakened by [w], so the cut lemma
        bounds the new closure from [g] into [a] strictly below [P[a,g]]. *)
    Lemma claim3 : forall g, g <> a ->
      Orel (mat_star M' g a) (mat_star M a g) /\ mat_star M' g a <> mat_star M a g.
    Proof.
      intros g Hg.
      apply (mstar_cut M' (Tg g) (mat_star M a g) (d_pos g Hg)).
      - intros i j Hi Hj.
        assert (Hij : i <> j). { intro E. subst. congruence. }
        assert (Hia : i <> a). { intro E. rewrite E, Tg_a in Hi. discriminate. }
        rewrite (Tg_other g i Hia) in Hi. apply sgt_false in Hi.
        (** (4.2.2.14): the old link is at most P[a,g] *)
        assert (Hle : Orel (M i j) (mat_star M a g)).
        { destruct (fin_eq_dec j a) as [-> | Hja].
          - exact (orel_trans _ _ _ (mstar_link M i a) Hi).
          - rewrite (Tg_other g j Hja) in Hj. apply sgt_true in Hj.
            destruct (sgt (M i j) (mat_star M a g)) eqn:E; [exfalso | apply sgt_false; exact E].
            apply sgt_true in E.
            pose proof (mul_gt' _ _ _ E Hj) as Hprod.
            pose proof (orel_trans _ _ _ (mul_compat_l _ _ _ (mstar_link M i j))
                          (mstar_compose M i j a)) as Hchain.
            destruct (orel_lt_le_trans _ _ _ Hprod Hchain) as [Hle' Hne].
            apply Hne. apply orel_antisym; [exact Hle' | exact Hi]. }
        (** (4.2.2.15): w ranks the target above the source *)
        assert (Hw : prefers w j i = true).
        { destruct (fin_eq_dec j a) as [-> | Hja]; [exact (prefers_w_a i Hia) |].
          rewrite (Tg_other g j Hja) in Hj. apply sgt_true in Hj.
          apply (prefers_w_order j i Hja Hia). exact (orel_le_lt_trans' _ _ _ Hi Hj). }
        (** (4.2.2.17): so the new link is strictly below P[a,g] *)
        exact (orel_lt_le_trans _ _ _ (link_down i j Hij Hw) Hle).
      - (* (4.2.2.13): g is outside T(g), because a is a winner *)
        rewrite (Tg_other g g Hg). apply sgt_false. apply (not_lt_le Htot Hdec). exact (Hwin g Hg).
      - apply Tg_a.
    Qed.

    (** ** Claim 2: the closure out of [a] does not drop *)

    (** The links at least [t] strong that [w] does not weaken. *)
    Definition keep (t : Strength m) (i j : Node) : bool :=
      leN (spec m) t (M i j) && negb (prefers w j i).

    (** [M] restricted to those links, typed at the concrete carrier. *)
    Definition Rk (t : Strength m) : @Matrix Node (Strength m) := restrict M (keep t).

    Lemma Rk_keep : forall t i j, keep t i j = true -> Rk t i j = M i j.
    Proof. intros t i j H. unfold Rk. exact (restrict_keep M (keep t) i j H). Qed.

    Lemma Rk_zero : forall t i j, keep t i j = false -> Rk t i j = zero.
    Proof. intros t i j H. unfold Rk, restrict. rewrite H. reflexivity. Qed.

    (** Every kept link survives into the new matrix. *)
    Lemma keep_le_new : forall t i j, Orel (Rk t i j) (M' i j).
    Proof.
      intros t i j. destruct (keep t i j) eqn:E.
      - rewrite (Rk_keep t i j E). unfold keep in E. apply andb_true_iff in E. destruct E as [_ E].
        destruct (fin_eq_dec i j) as [-> | Hij].
        + rewrite (matrix_of_diag m P j j eq_refl), (matrix_of_diag m (w :: P) j j eq_refl).
          apply orefl.
        + apply link_up; [exact Hij |]. destruct (prefers w j i); [discriminate | reflexivity].
      - rewrite (Rk_zero t i j E). apply ozero.
    Qed.

    (** A higher threshold keeps fewer links. *)
    Lemma keep_mono : forall t t', Orel t t' -> forall i j, Orel (Rk t' i j) (Rk t i j).
    Proof.
      intros t t' Htt' i j. destruct (keep t' i j) eqn:E.
      - rewrite (Rk_keep t' i j E). unfold keep in E. apply andb_true_iff in E.
        destruct E as [E1 E2].
        assert (Hk : keep t i j = true).
        { unfold keep. rewrite E2. apply andb_true_iff. split; [| reflexivity].
          apply (Orel_iff_leN (spec m)). eapply orel_trans; [exact Htt' |].
          apply (Orel_iff_leN (spec m)). exact E1. }
        rewrite (Rk_keep t i j Hk). apply orefl.
      - rewrite (Rk_zero t' i j E). apply ozero.
    Qed.

    (** The number of alternatives whose closure strength out of [a] is
        strictly above [t]: the induction measure. *)
    Definition mu (t : Strength m) : nat :=
      length (filter (fun x => sgt (mat_star M a x) t) elements).

    (** The heart of claim 2.  If [x] is reachable from [a] at level [t]
        through kept links and a walk of strength at least [t] leads from [x]
        to [g], then [g] is reachable from [a] at level [t] through kept links.
        Induction on the walk; a weakened link [xe] on it forces [P[a,e] > t],
        and the outer induction on [mu] reroutes through level [P[a,e]]. *)
    Lemma reach_level : forall n (t : Strength m), mu t = n -> Orel zero t /\ zero <> t ->
      forall k x g, Orel t (mat_star (Rk t) a x) -> Orel t (pow M k x g) ->
        Orel t (mat_star (Rk t) a g).
    Proof.
      induction n as [n IHn] using lt_wf_ind. intros t Hmu Ht0 k.
      induction k as [|k IHk]; intros x g Hx Hg.
      - rewrite pow_0 in Hg. destruct (fin_eq_dec x g) as [-> | Hxg]; [exact Hx |].
        exfalso. destruct Ht0 as [_ Hne]. apply Hne.
        apply orel_antisym; [apply ozero | exact Hg].
      - rewrite pow_S in Hg.
        destruct (sum_sel (fun e => mul (M x e) (pow M k e g))) as [H0 | [e He]].
        + exfalso. destruct Ht0 as [_ Hne]. apply Hne.
          apply orel_antisym; [apply ozero | exact (eq_ind _ (fun s => Orel t s) Hg _ H0)].
        + pose proof (eq_ind _ (fun s => Orel t s) Hg _ He) as Hg'. cbv beta in Hg'.
          pose proof (orel_trans _ _ _ Hg' (mul_le_l (M x e) (pow M k e g))) as Hxe.
          pose proof (orel_trans _ _ _ Hg' (mul_le_r (M x e) (pow M k e g))) as Heg.
          apply (IHk e g); [| exact Heg].
          destruct (prefers w e x) eqn:Hw.
          * (* the link x → e is weakened by w *)
            destruct (fin_eq_dec e a) as [-> | Hea].
            { rewrite mstar_diag. apply ole_one. }
            assert (Hxa : x <> a).
            { intro E. subst x. rewrite prefers_w_into_a in Hw. discriminate. }
            apply (prefers_w_order e x Hea Hxa) in Hw.
            (** P[x,a] ≥ min(M x e, P[e,a]) and P[x,a] < P[e,a], so P[x,a] ≥ t *)
            pose proof (orel_trans _ _ _ (mul_compat_l _ _ _ (mstar_link M x e))
                          (mstar_compose M x e a)) as Hchain.
            assert (Htxa : Orel t (mat_star M x a)).
            { destruct (mul_min' (M x e) (mat_star M e a)) as [E | E].
              - exact (orel_trans _ _ _ Hxe (eq_ind _ (fun z => Orel z (mat_star M x a)) Hchain _ E)).
              - exfalso. destruct Hw as [Hle Hne]. apply Hne. apply orel_antisym; [exact Hle |].
                exact (eq_ind _ (fun z => Orel z (mat_star M x a)) Hchain _ E). }
            (** a is a winner, so P[e,a] ≤ P[a,e]; hence t < P[a,e] *)
            assert (Hea_le : Orel (mat_star M e a) (mat_star M a e)).
            { apply (not_lt_le Htot Hdec). exact (Hwin e Hea). }
            assert (Hlt : Orel t (mat_star M a e) /\ t <> mat_star M a e).
            { exact (orel_lt_le_trans _ _ _ (orel_le_lt_trans' _ _ _ Htxa Hw) Hea_le). }
            (** fewer alternatives lie above the higher level *)
            assert (Hmu' : mu (mat_star M a e) < n).
            { rewrite <- Hmu. unfold mu.
              apply (filter_length_lt_of_strict _ _ elements e).
              - intros y _ Hy. apply sgt_true in Hy. apply sgt_true.
                exact (orel_lt_trans _ _ _ (proj1 Hlt) Hy).
              - apply elements_complete.
              - apply sgt_true. exact Hlt.
              - apply sgt_false. apply orefl. }
            destruct (mstar_attained M a e) as [k' Hk'].
            assert (Ht2pos : Orel zero (mat_star M a e) /\ zero <> mat_star M a e).
            { split; [apply ozero |]. intro E. destruct Hlt as [Hle Hne]. apply Hne.
              exact (orel_antisym _ _ Hle (eq_ind _ (fun z => Orel z t) (ozero t) _ E)). }
            pose proof (IHn (mu (mat_star M a e)) Hmu' (mat_star M a e) eq_refl Ht2pos k' a e)
              as IH2.
            assert (Hreach2 : Orel (mat_star M a e) (mat_star (Rk (mat_star M a e)) a e)).
            { apply IH2; [rewrite mstar_diag; apply ole_one |].
              exact (eq_ind _ (fun z => Orel (mat_star M a e) z) (orefl _) _ Hk'). }
            eapply orel_trans; [exact (proj1 Hlt) |].
            eapply orel_trans; [exact Hreach2 |].
            apply mstar_mono. apply keep_mono. exact (proj1 Hlt).
          * (* the link x → e is kept *)
            assert (Hkeep : keep t x e = true).
            { unfold keep. rewrite Hw. apply andb_true_iff. split; [| reflexivity].
              apply (Orel_iff_leN (spec m)). exact Hxe. }
            eapply orel_trans; [| apply (mstar_compose (Rk t) a x e)].
            eapply orel_trans; [| apply (mul_compat_r _ _ _ (mstar_link (Rk t) x e))].
            rewrite (Rk_keep t x e Hkeep).
            apply Hmeet; assumption.
    Qed.

    (** (4.2.2.11): the closure out of [a] does not drop. *)
    Lemma claim2 : forall g, Orel (mat_star M a g) (mat_star M' a g).
    Proof.
      intro g. destruct (fin_eq_dec g a) as [-> | Hga].
      - exact (eq_ind _ (fun z => Orel (mat_star M a a) z) (ole_one _) _ (eq_sym (mstar_diag M' a))).
      - destruct (mstar_attained M a g) as [k Hk].
        eapply orel_trans.
        + apply (reach_level (mu (mat_star M a g)) (mat_star M a g) eq_refl (d_pos g Hga) k a g).
          * rewrite mstar_diag. apply ole_one.
          * exact (eq_ind _ (fun z => Orel (mat_star M a g) z) (orefl _) _ Hk).
        + apply mstar_mono. apply keep_le_new.
    Qed.

    (** ** Conclusion *)

    (** With the ballot added, [a] beats everyone. *)
    Theorem add_ballot_strict_winner : strict_winner M' a.
    Proof.
      intros g Hga. unfold schulze_beats, beats.
      exact (orel_lt_le_trans _ _ _ (claim3 g Hga) (claim2 g)).
    Qed.

    (** …so [S_new = {a}]. *)
    Theorem add_ballot_unique_winner : forall x, schulze_winner M' x <-> x = a.
    Proof.
      intro x. split.
      - intro Hx. destruct (fin_eq_dec x a) as [E | Hne]; [exact E | exfalso].
        exact (strict_winner_excludes_others M' a x add_ballot_strict_winner Hne Hx).
      - intros ->. intros b Hb Hbeat.
        exact (schulze_beats_asym M' a b (add_ballot_strict_winner b Hb) Hbeat).
    Qed.

  End AddBallot.

  (** Schulze 4.2.2: for every winner there is one ballot whose addition makes
      it the unique winner. *)
  Theorem resolvability_from_profile : forall (P : @Profile Node) (a : Node),
    schulze_winner (matrix_of m P) a ->
    exists w : @Ballot Node,
      strict_winner (matrix_of m (w :: P)) a /\
      forall x, schulze_winner (matrix_of m (w :: P)) x <-> x = a.
  Proof.
    intros P a Hwin. exists (w P a).
    split; [exact (add_ballot_strict_winner P a Hwin) | exact (add_ballot_unique_winner P a Hwin)].
  Qed.

End ResolvabilityBallotN.
