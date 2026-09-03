(* ========================================================================= *)
(*  Thresholds, cuts, and the critical link (Schulze 4.2.1, second half)      *)
(*                                                                           *)
(*  Several of Schulze's arguments locate the weakest link of a strongest     *)
(*  path and split the path there.  This development has no path witnesses    *)
(*  for closure entries, so the same reasoning is done with two algebraic     *)
(*  tools instead, both valid over a selective bounded semiring whose          *)
(*  multiplication is the meet of the natural order:                          *)
(*                                                                           *)
(*    - THRESHOLDS.  Zeroing every link that is not strictly above [c] does   *)
(*      not lower any closure entry that was strictly above [c]               *)
(*      ([mat_star_above_restrict]).  So the statement that the strongest    *)
(*      path from [a] to [b] uses only links above [c] is expressed without   *)
(*      naming the path.                                                      *)
(*    - CUTS.  If every link entering a set of nodes is strictly below [c],   *)
(*      no closure entry from outside the set into it reaches [c]             *)
(*      ([mat_star_lt_of_cut], a packaging of SmithN's [pow_from_B2_lt]).     *)
(*                                                                           *)
(*  With these, the second half of 4.2.1 goes through: when no two distinct   *)
(*  links have the same strength, two winners [a ≠ b] force a tie             *)
(*  [P[a,b] = P[b,a] = c], and [c] is the strength of exactly one link [ef].  *)
(*  The set of nodes reachable from [a] above [c] must be left through a link  *)
(*  of strength exactly [c] (else, by the cut lemma, [P[a,b] < c]), which is   *)
(*  [ef]; likewise the set of nodes reaching [a] above [c] must be entered     *)
(*  through [ef].  Hence [P[a,f] ≤ c < P[f,a]]: [f] beats [a], contradicting   *)
(*  that [a] is a winner.  This is the paper's (4.2.1.4) to (4.2.1.9), with    *)
(*  reachability sets in place of path prefixes and suffixes.                 *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 List Arith Lia Bool.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN
  SocialchoiceN SmithN BeatsOnN.
Import ListNotations SemiringNotations.

(* ------------------------------------------------------------------ *)
(*  Counting with filters                                              *)
(* ------------------------------------------------------------------ *)

Lemma filter_length_le_of_impl {A : Type} (f g : A -> bool) (l : list A) :
  (forall x, In x l -> f x = true -> g x = true) ->
  length (filter f l) <= length (filter g l).
Proof.
  induction l as [|x l IH]; intro H; cbn [filter]; [lia |].
  assert (IH' : length (filter f l) <= length (filter g l)).
  { apply IH. intros y Hy Hf. apply H; [right; exact Hy | exact Hf]. }
  destruct (f x) eqn:Ef.
  - rewrite (H x (or_introl eq_refl) Ef). cbn [length]. lia.
  - destruct (g x); cbn [length]; lia.
Qed.

(** A filter that is pointwise implied by another, and misses an element the
    other keeps, is strictly shorter. *)
Lemma filter_length_lt_of_strict {A : Type} (f g : A -> bool) (l : list A) (x0 : A) :
  (forall x, In x l -> f x = true -> g x = true) ->
  In x0 l -> g x0 = true -> f x0 = false ->
  length (filter f l) < length (filter g l).
Proof.
  induction l as [|x l IH]; intros H Hin Hg Hf; [destruct Hin |].
  cbn [filter].
  assert (Hle : length (filter f l) <= length (filter g l)).
  { apply filter_length_le_of_impl. intros y Hy Hfy. apply H; [right; exact Hy | exact Hfy]. }
  destruct Hin as [Heq | Hin].
  - subst x. rewrite Hf, Hg. cbn [length]. lia.
  - assert (Hlt : length (filter f l) < length (filter g l)).
    { apply IH; try assumption. intros y Hy Hfy. apply H; [right; exact Hy | exact Hfy]. }
    destruct (f x) eqn:Ef.
    + rewrite (H x (or_introl eq_refl) Ef). cbn [length]. lia.
    + destruct (g x); cbn [length]; lia.
Qed.

Section CriticalLinkN.

  Context {Node : FinType.type}.
  Context {R : BoundedSemiring.type}.

  (** The standing hypotheses of the selective results: [+] returns one of its
      arguments, and [*] is the meet of the natural order. *)
  Hypothesis Htotal : forall x y : R, x + y = x \/ x + y = y.
  Hypothesis Hmeet : forall m a b : R, Orel m a -> Orel m b -> Orel m (a * b).

  (* ---------------------------------------------------------------- *)
  (*  Order facts                                                      *)
  (* ---------------------------------------------------------------- *)

  (** Multiplication is the minimum. *)
  Lemma mul_min : forall u v : R, u * v = u \/ u * v = v.
  Proof.
    intros u v. destruct (Htotal u v) as [H | H].
    - right. apply orel_antisym; [apply bounded_mul_lower_right |].
      apply Hmeet; [| apply bounded_orel_refl]. unfold Orel. rewrite addC. exact H.
    - left. apply orel_antisym; [apply bounded_mul_lower_left |].
      apply Hmeet; [apply bounded_orel_refl | exact H].
  Qed.

  (** The form of the meet property used by [mat_star_link_or_extreme]. *)
  Lemma meet_of_le : forall x y : R, Orel x y -> x * y = x /\ y * x = x.
  Proof.
    intros x y Hxy. split; apply orel_antisym.
    - apply bounded_mul_lower_left.
    - apply Hmeet; [apply bounded_orel_refl | exact Hxy].
    - apply bounded_mul_lower_right.
    - apply Hmeet; [exact Hxy | apply bounded_orel_refl].
  Qed.

  Lemma orel_le_lt_trans' : forall x y z : R,
    Orel x y -> Orel y z /\ y <> z -> Orel x z /\ x <> z.
  Proof.
    intros x y z Hxy [Hyz Hne]. split; [exact (orel_trans _ _ _ Hxy Hyz) |].
    intro Heq. subst z. apply Hne. apply orel_antisym; assumption.
  Qed.

  (** The minimum of two values strictly above [c] is strictly above [c]. *)
  Lemma mul_gt : forall c u v : R,
    Orel c u /\ c <> u -> Orel c v /\ c <> v -> Orel c (u * v) /\ c <> u * v.
  Proof.
    intros c u v [Hcu Hneu] [Hcv Hnev]. split; [apply Hmeet; assumption |].
    intro Heq. destruct (mul_min u v) as [E | E]; rewrite E in Heq; congruence.
  Qed.

  Lemma orel_total : forall x y : R, Orel x y \/ Orel y x.
  Proof.
    intros x y. destruct (Htotal x y) as [H | H].
    - right. unfold Orel. rewrite addC. exact H.
    - left. exact H.
  Qed.

  Lemma not_le_lt : forall x y : R, ~ Orel x y -> Orel y x /\ y <> x.
  Proof.
    intros x y Hn. destruct (orel_total x y) as [H | H]; [contradiction |].
    split; [exact H |]. intro E. subst. apply Hn. apply bounded_orel_refl.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  Restricting a matrix to a set of links                           *)
  (* ---------------------------------------------------------------- *)

  Definition restrict (M : @Matrix Node R) (keep : Node -> Node -> bool)
    : @Matrix Node R :=
    fun i j => if keep i j then M i j else 0.

  Lemma restrict_le : forall M keep i j, Orel (restrict M keep i j) (M i j).
  Proof.
    intros M keep i j. unfold restrict.
    destruct (keep i j); [apply bounded_orel_refl | apply zero_is_bottom].
  Qed.

  Lemma restrict_keep : forall M keep i j, keep i j = true -> restrict M keep i j = M i j.
  Proof. intros M keep i j H. unfold restrict. rewrite H. reflexivity. Qed.

  Lemma mat_star_restrict_le : forall M keep a b,
    Orel (mat_star (restrict M keep) a b) (mat_star M a b).
  Proof.
    intros M keep a b. unfold mat_star. apply geom_sum_monotone.
    intros i j. apply restrict_le.
  Qed.

  (** THRESHOLDS.  A walk whose strength is strictly above [c] uses only links
      strictly above [c], so it survives in any restriction that keeps those. *)
  Lemma pow_above_restrict (M : @Matrix Node R) (keep : Node -> Node -> bool) (c : R)
    (Hkeep : forall i j, Orel c (M i j) /\ c <> M i j -> keep i j = true) :
    forall n x y, Orel c (pow M n x y) /\ c <> pow M n x y ->
      Orel (pow M n x y) (pow (restrict M keep) n x y).
  Proof.
    induction n as [|n IH]; intros x y Hc.
    - cbn [pow]. apply bounded_orel_refl.
    - cbn [pow] in *. unfold matrix_mul in *.
      destruct (sum_selective Htotal (fun e => M x e * pow M n e y)) as [H0 | [e He]].
      + exfalso. rewrite H0 in Hc. destruct Hc as [Hle Hne]. apply Hne.
        apply orel_antisym; [exact Hle | apply zero_is_bottom].
      + rewrite He in *. cbv beta in *.
        pose proof (orel_lt_le_trans _ _ _ Hc
                      (bounded_mul_lower_left (M x e) (pow M n e y))) as Hxe.
        pose proof (orel_lt_le_trans _ _ _ Hc
                      (bounded_mul_lower_right (M x e) (pow M n e y))) as Hey.
        eapply orel_trans;
          [| apply (le_sum (fun e' => restrict M keep x e' * pow (restrict M keep) n e' y) e)].
        cbv beta. rewrite (restrict_keep M keep x e (Hkeep x e Hxe)).
        apply bounded_mul_orel_compat_r. exact (IH e y Hey).
  Qed.

  Lemma mat_star_above_restrict (M : @Matrix Node R) (keep : Node -> Node -> bool) (c : R)
    (Hkeep : forall i j, Orel c (M i j) /\ c <> M i j -> keep i j = true) (a b : Node) :
    Orel c (mat_star M a b) /\ c <> mat_star M a b ->
    Orel (mat_star M a b) (mat_star (restrict M keep) a b).
  Proof.
    intro Hc. destruct (geom_sum_selective Htotal M (@kleene_exp Node) a b) as [k [Hk Heq]].
    unfold mat_star in *. rewrite Heq in *.
    eapply orel_trans; [apply (pow_above_restrict M keep c Hkeep k a b Hc) |].
    apply pow_le_mat_star. exact Hk.
  Qed.

  (** CUTS.  If every link entering the set [Bp] is strictly below [c], no
      closure entry from outside [Bp] into it reaches [c]. *)
  Lemma mat_star_lt_of_cut (M : @Matrix Node R) (Bp : Node -> bool) (c : R)
    (H0 : Orel 0 c /\ 0 <> c)
    (Hcross : forall i j, Bp i = false -> Bp j = true -> Orel (M i j) c /\ M i j <> c) :
    forall y x, Bp y = false -> Bp x = true ->
      Orel (mat_star M y x) c /\ mat_star M y x <> c.
  Proof.
    intros y x Hy Hx.
    apply (mat_star_lt_bound Htotal). intro n.
    apply (pow_from_B2_lt M Htotal (filter Bp elements)
             (filter (fun z => negb (Bp z)) elements) c).
    - intro z. rewrite !filter_In. split.
      + intros [_ Hz] [_ Hnz]. rewrite Hz in Hnz. discriminate.
      + intro Hn. split; [apply elements_complete |].
        destruct (Bp z) eqn:E; [reflexivity |].
        exfalso. apply Hn. split; [apply elements_complete | reflexivity].
    - intros a b Ha Hb. rewrite filter_In in Ha, Hb.
      destruct Ha as [_ Ha]. destruct Hb as [_ Hb].
      apply Hcross; [| exact Ha].
      destruct (Bp b) eqn:E; [cbn in Hb; discriminate | reflexivity].
    - exact H0.
    - rewrite filter_In. split; [apply elements_complete | rewrite Hy; reflexivity].
    - rewrite filter_In. split; [apply elements_complete | exact Hx].
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  Off-diagonal closure entries stay below the top                  *)
  (* ---------------------------------------------------------------- *)

  Lemma zero_ne_one_of_link : forall (M : @Matrix Node R) x y,
    x <> y -> M x y <> 1 -> (0 : R) <> 1.
  Proof.
    intros M x y Hxy Hne H01. apply Hne.
    rewrite <- (mulr1 (M x y)). rewrite <- H01. exact (mulr0 (M x y)).
  Qed.

  Lemma pow_off_diag_lt_one (M : @Matrix Node R)
    (Hne_one : forall i j, i <> j -> M i j <> 1) :
    forall n x y, x <> y -> Orel (pow M n x y) 1 /\ pow M n x y <> 1.
  Proof.
    intros n. induction n as [|n IH]; intros x y Hxy.
    - cbn [pow]. unfold I. destruct (fin_eq_dec x y) as [E|_]; [contradiction |].
      split; [apply zero_is_bottom | exact (zero_ne_one_of_link M x y Hxy (Hne_one x y Hxy))].
    - cbn [pow]. unfold matrix_mul. apply sum_lt_bound_if_all_lt; [exact Htotal |].
      intro e. destruct (fin_eq_dec e y) as [-> | Hey].
      + apply (orel_le_lt_trans' _ (M x y) _); [apply bounded_mul_lower_left |].
        split; [apply le_one | exact (Hne_one x y Hxy)].
      + apply (orel_le_lt_trans' _ (pow M n e y) _);
          [apply bounded_mul_lower_right | exact (IH e y Hey)].
  Qed.

  Lemma mat_star_off_diag_lt_one (M : @Matrix Node R)
    (Hne_one : forall i j, i <> j -> M i j <> 1) (x y : Node) :
    x <> y -> Orel (mat_star M x y) 1 /\ mat_star M x y <> 1.
  Proof.
    intro Hxy. apply (mat_star_lt_bound Htotal). intro n.
    exact (pow_off_diag_lt_one M Hne_one n x y Hxy).
  Qed.

  (* ================================================================ *)
  (*  Pairwise distinct link strengths force a unique winner           *)
  (*  (Schulze 4.2.1, the combinatorial statement behind Formulation 1)*)
  (* ================================================================ *)

  Section DistinctLinks.

    Context (Hdec : forall x y : R, {x = y} + {x <> y}).

    Lemma not_lt_le : forall x y : R, ~ (Orel x y /\ x <> y) -> Orel y x.
    Proof.
      intros x y Hn. destruct (orel_total x y) as [H | H]; [| exact H].
      destruct (Hdec x y) as [E | Hne].
      - subst. apply bounded_orel_refl.
      - exfalso. apply Hn. split; assumption.
    Qed.

    (** Boolean strictly-above test. *)
    Definition gtb (u c : R) : bool := if orel_dec Hdec u c then false else true.

    Lemma gtb_true : forall u c, gtb u c = true <-> (Orel c u /\ c <> u).
    Proof.
      intros u c. unfold gtb. destruct (orel_dec Hdec u c) as [H | H]; split; intro K.
      - discriminate.
      - exfalso. destruct K as [K1 K2]. apply K2. apply orel_antisym; assumption.
      - exact (not_le_lt u c H).
      - reflexivity.
    Qed.

    Lemma gtb_false : forall u c, gtb u c = false <-> Orel u c.
    Proof.
      intros u c. unfold gtb. destruct (orel_dec Hdec u c) as [H | H]; split; intro K;
        [exact H | reflexivity | discriminate | contradiction].
    Qed.

    Variable M : @Matrix Node R.
    Hypothesis Hdiag : forall i j, i = j -> M i j = 1.
    Hypothesis Hne_one : forall i j, i <> j -> M i j <> 1.
    (** No two distinct links have the same strength. *)
    Hypothesis Hdistinct : forall e f g h, e <> f -> g <> h -> M e f = M g h -> e = g /\ f = h.

    (** Two winners [a ≠ b], the common value [c] of [P[a,b]] and [P[b,a]],
        and the unique link [ef] of strength [c]. *)
    Section TwoWinners.

      Variable a b : Node.
      Hypothesis Hab : a <> b.
      Hypothesis Hwa : schulze_winner M a.
      Variable c : R.
      Hypothesis Hc_ab : mat_star M a b = c.
      Hypothesis Hc_ba : mat_star M b a = c.
      Hypothesis Hc0 : c <> 0.
      Hypothesis Hc1 : c <> 1.
      Variable e f : Node.
      Hypothesis Hef : e <> f.
      Hypothesis Hc_ef : M e f = c.

      (** The links strictly above [c]. *)
      Definition Rgt : @Matrix Node R := restrict M (fun i j => gtb (M i j) c).
      (** Reachable from [a] above [c]; reaches [a] above [c]. *)
      Definition U (x : Node) : bool := gtb (mat_star Rgt a x) c.
      Definition V (x : Node) : bool := gtb (mat_star Rgt x a) c.

      Lemma Rgt_keep : forall i j, Orel c (M i j) /\ c <> M i j -> Rgt i j = M i j.
      Proof. intros i j H. apply restrict_keep. apply gtb_true. exact H. Qed.

      Lemma c_pos : Orel 0 c /\ 0 <> c.
      Proof. split; [apply zero_is_bottom | intro H; apply Hc0; symmetry; exact H]. Qed.

      Lemma c_lt_one : Orel c 1 /\ c <> 1.
      Proof. split; [apply le_one | exact Hc1]. Qed.

      (* --- the set reachable from [a] --- *)

      Lemma U_a : U a = true.
      Proof. unfold U. apply gtb_true. rewrite mat_star_diag_one. exact c_lt_one. Qed.

      Lemma U_b : U b = false.
      Proof. unfold U. apply gtb_false. rewrite <- Hc_ab. unfold Rgt. apply mat_star_restrict_le. Qed.

      Lemma U_closed : forall x y, U x = true -> Orel c (M x y) /\ c <> M x y -> U y = true.
      Proof.
        intros x y Hx Hxy. unfold U in *. apply gtb_true. apply gtb_true in Hx.
        apply (orel_lt_le_trans c (mat_star Rgt a x * Rgt x y) (mat_star Rgt a y)).
        - rewrite (Rgt_keep x y Hxy). apply mul_gt; assumption.
        - eapply orel_trans; [| apply star_path_compose].
          apply bounded_mul_orel_compat_r. apply link_le_mat_star.
      Qed.

      Lemma U_cross_le : forall x y, U x = true -> U y = false -> Orel (M x y) c.
      Proof.
        intros x y Hx Hy. destruct (gtb (M x y) c) eqn:E.
        - exfalso. apply gtb_true in E. rewrite (U_closed x y Hx E) in Hy. discriminate.
        - apply gtb_false. exact E.
      Qed.

      Definition crossU (p : Node * Node) : bool :=
        U (fst p) && negb (U (snd p)) && (if Hdec (M (fst p) (snd p)) c then true else false).

      (** Some link of strength exactly [c] leaves the reachable set: otherwise
          every leaving link is strictly below [c] and the cut lemma gives
          [P[a,b] < c]. *)
      Lemma U_link : exists x y, U x = true /\ U y = false /\ M x y = c.
      Proof.
        destruct (existsb crossU (list_prod elements elements)) eqn:E.
        - apply existsb_exists in E. destruct E as [[x y] [_ Hp]].
          unfold crossU in Hp. cbn [fst snd] in Hp.
          destruct (U x) eqn:Hx; destruct (U y) eqn:Hy;
            destruct (Hdec (M x y) c) as [Heq | Hne]; cbn in Hp; try discriminate.
          exists x, y. repeat split; assumption.
        - exfalso.
          assert (Hcross : forall i j, negb (U i) = false -> negb (U j) = true ->
                    Orel (M i j) c /\ M i j <> c).
          { intros i j Hi Hj.
            assert (Hi' : U i = true) by (destruct (U i); [reflexivity | discriminate]).
            assert (Hj' : U j = false) by (destruct (U j); [discriminate | reflexivity]).
            split; [exact (U_cross_le i j Hi' Hj') |].
            intro Heq.
            assert (Hex : existsb crossU (list_prod elements elements) = true).
            { apply existsb_exists. exists (i, j).
              split; [apply in_prod; apply elements_complete |].
              unfold crossU. cbn [fst snd]. rewrite Hi', Hj'. cbn.
              destruct (Hdec (M i j) c); [reflexivity | contradiction]. }
            congruence. }
          pose proof (mat_star_lt_of_cut M (fun z => negb (U z)) c c_pos Hcross a b) as Hlt.
          assert (Ha' : negb (U a) = false) by (rewrite U_a; reflexivity).
          assert (Hb' : negb (U b) = true) by (rewrite U_b; reflexivity).
          destruct (Hlt Ha' Hb') as [_ Hne]. apply Hne. exact Hc_ab.
      Qed.

      (** …and by distinctness that link is [ef]. *)
      Lemma U_ef : U e = true /\ U f = false.
      Proof.
        destruct U_link as [x [y [Hx [Hy Hxy]]]].
        assert (Hne : x <> y) by (intro E; subst; congruence).
        destruct (Hdistinct x y e f Hne Hef (eq_trans Hxy (eq_sym Hc_ef))) as [-> ->].
        split; assumption.
      Qed.

      (** (4.2.1.4): [P[a,f] ≤ c], since [f] is not reachable above [c]. *)
      Lemma P_af_le : Orel (mat_star M a f) c.
      Proof.
        destruct (gtb (mat_star M a f) c) eqn:E.
        - exfalso. apply gtb_true in E.
          pose proof (mat_star_above_restrict M (fun i j => gtb (M i j) c) c
                        (fun i j H => proj2 (gtb_true _ _) H) a f E) as Hle.
          destruct U_ef as [_ Hf]. unfold U, Rgt in Hf.
          pose proof (orel_lt_le_trans _ _ _ E Hle) as Hgt.
          apply gtb_true in Hgt. congruence.
        - apply gtb_false. exact E.
      Qed.

      Lemma f_ne_a : f <> a.
      Proof. intro E. destruct U_ef as [_ Hf]. rewrite E, U_a in Hf. discriminate. Qed.

      (* --- the set reaching [a] --- *)

      Lemma V_a : V a = true.
      Proof. unfold V. apply gtb_true. rewrite mat_star_diag_one. exact c_lt_one. Qed.

      Lemma V_b : V b = false.
      Proof. unfold V. apply gtb_false. rewrite <- Hc_ba. unfold Rgt. apply mat_star_restrict_le. Qed.

      Lemma V_closed : forall x y, V y = true -> Orel c (M x y) /\ c <> M x y -> V x = true.
      Proof.
        intros x y Hy Hxy. unfold V in *. apply gtb_true. apply gtb_true in Hy.
        apply (orel_lt_le_trans c (Rgt x y * mat_star Rgt y a) (mat_star Rgt x a)).
        - rewrite (Rgt_keep x y Hxy). apply mul_gt; assumption.
        - eapply orel_trans; [| apply star_path_compose].
          apply bounded_mul_orel_compat_l. apply link_le_mat_star.
      Qed.

      Lemma V_cross_le : forall x y, V x = false -> V y = true -> Orel (M x y) c.
      Proof.
        intros x y Hx Hy. destruct (gtb (M x y) c) eqn:E.
        - exfalso. apply gtb_true in E. rewrite (V_closed x y Hy E) in Hx. discriminate.
        - apply gtb_false. exact E.
      Qed.

      Definition crossV (p : Node * Node) : bool :=
        negb (V (fst p)) && V (snd p) && (if Hdec (M (fst p) (snd p)) c then true else false).

      Lemma V_link : exists x y, V x = false /\ V y = true /\ M x y = c.
      Proof.
        destruct (existsb crossV (list_prod elements elements)) eqn:E.
        - apply existsb_exists in E. destruct E as [[x y] [_ Hp]].
          unfold crossV in Hp. cbn [fst snd] in Hp.
          destruct (V x) eqn:Hx; destruct (V y) eqn:Hy;
            destruct (Hdec (M x y) c) as [Heq | Hne]; cbn in Hp; try discriminate.
          exists x, y. repeat split; assumption.
        - exfalso.
          assert (Hcross : forall i j, V i = false -> V j = true -> Orel (M i j) c /\ M i j <> c).
          { intros i j Hi Hj.
            split; [exact (V_cross_le i j Hi Hj) |].
            intro Heq.
            assert (Hex : existsb crossV (list_prod elements elements) = true).
            { apply existsb_exists. exists (i, j).
              split; [apply in_prod; apply elements_complete |].
              unfold crossV. cbn [fst snd]. rewrite Hi, Hj. cbn.
              destruct (Hdec (M i j) c); [reflexivity | contradiction]. }
            congruence. }
          pose proof (mat_star_lt_of_cut M V c c_pos Hcross b a V_b V_a) as [_ Hne].
          apply Hne. exact Hc_ba.
      Qed.

      Lemma V_ef : V e = false /\ V f = true.
      Proof.
        destruct V_link as [x [y [Hx [Hy Hxy]]]].
        assert (Hne : x <> y) by (intro E; subst; congruence).
        destruct (Hdistinct x y e f Hne Hef (eq_trans Hxy (eq_sym Hc_ef))) as [-> ->].
        split; assumption.
      Qed.

      (** (4.2.1.7): [c < P[f,a]], since [f] reaches [a] above [c]. *)
      Lemma P_fa_gt : Orel c (mat_star M f a) /\ c <> mat_star M f a.
      Proof.
        destruct V_ef as [_ Hf]. unfold V in Hf. apply gtb_true in Hf.
        exact (orel_lt_le_trans _ _ _ Hf (mat_star_restrict_le M _ f a)).
      Qed.

      (** (4.2.1.8): [f] beats [a], which a winner does not allow. *)
      Lemma two_winners_absurd : False.
      Proof.
        apply (Hwa f f_ne_a). unfold schulze_beats, beats.
        exact (orel_le_lt_trans' _ _ _ P_af_le P_fa_gt).
      Qed.

    End TwoWinners.

    (** Schulze 4.2.1, the combinatorial core: with pairwise distinct link
        strengths there is at most one winner. *)
    Theorem distinct_links_unique_winner :
      forall a b, schulze_winner M a -> schulze_winner M b -> a = b.
    Proof.
      intros a b Hwa Hwb. destruct (fin_eq_dec a b) as [E | Hab]; [exact E | exfalso].
      (* two winners tie *)
      assert (Hba : mat_star M b a = mat_star M a b).
      { apply orel_antisym.
        - apply not_lt_le. exact (Hwa b (not_eq_sym Hab)).
        - apply not_lt_le. exact (Hwb a Hab). }
      (* the tie value is neither extreme *)
      assert (Hc0 : mat_star M a b <> 0).
      { intro H0.
        assert (Hab0 : M a b = 0).
        { apply orel_antisym; [| apply zero_is_bottom]. rewrite <- H0. apply link_le_mat_star. }
        assert (Hba0 : M b a = 0).
        { apply orel_antisym; [| apply zero_is_bottom]. rewrite <- H0, <- Hba. apply link_le_mat_star. }
        destruct (Hdistinct a b b a Hab (not_eq_sym Hab) (eq_trans Hab0 (eq_sym Hba0))) as [E _].
        exact (Hab E). }
      assert (Hc1 : mat_star M a b <> 1).
      { exact (proj2 (mat_star_off_diag_lt_one M Hne_one a b Hab)). }
      (* …so it is the strength of a link, and that link is off-diagonal *)
      destruct (mat_star_link_or_extreme Htotal meet_of_le M a b) as [H0 | [H1 | [x [y Hxy]]]];
        [exact (Hc0 H0) | exact (Hc1 H1) |].
      destruct (fin_eq_dec x y) as [Exy | Hxy_ne].
      { apply Hc1. rewrite Hxy. apply Hdiag. exact Exy. }
      exact (two_winners_absurd a b Hwa (mat_star M a b) eq_refl Hba Hc0 Hc1
               x y Hxy_ne (eq_sym Hxy)).
    Qed.

  End DistinctLinks.

End CriticalLinkN.
