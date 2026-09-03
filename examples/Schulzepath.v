(** * Schulzepath.v — the language (trace) semiring for the Schulze method

    Unlike the value+witness pair (which is NOT a semiring), the pure
    LANGUAGE semiring below IS a genuine semiring: every axiom of the
    HB [Semiring] is proved, exactly as [Schulze.v] proves its max-min
    semiring.

    Carrier :  Lang := Edge -> bool
               a predicate on edge-paths (the "set" of paths)
    add     :  pointwise boolean OR (set union)
    mul     :  concatenation product: L⊗M is the set of all p1++p2 with
               L p1 and M p2 (pairwise concatenation)
    0       :  the empty language (constant false)
    1       :  the singleton {[]} (the empty path)

    Union and pairwise concatenation distribute EXACTLY (no witness is
    ever discarded), so distributivity holds — the property that failed
    for the single-witness and value+set constructions.  The only price
    is that [add] equality needs functional extensionality (functions
    are compared pointwise).

    The Schulze fixed point [geom_sum (lift M) K i j] then denotes the
    set of all paths from i to j of length ≤ K, from which the value
    M*[i,j] = max measure is recovered. *)

From Stdlib Require Import List Utf8 Bool PeanoNat Lia BinNatDef
  Logic.FunctionalExtensionality.
From HB Require Import structures.
From Semiring Require Import PathN MatN OrelN SemimoduleN Structures.
From Examples Require Import Schulze.
Import ListNotations SemiringNotations.

(** * The language semiring over the max-min semiring R (from Schulze.v) *)

Section LanguageSemiring.

  (** A path is an edge list; a language is a predicate on paths. *)
  Definition Edge : Type := list (Node * Node * R).
  Definition Lang : Type := Edge -> bool.

  (** The empty language. *)
  Definition lang_zero : Lang := fun _ => false.

  (** The singleton language { [] } (the empty path). *)
  Definition lang_one : Lang := fun p => match p with [] => true | _ => false end.

  (** Set union as pointwise boolean OR. *)
  Definition lang_add (L M : Lang) : Lang := fun p => L p || M p.

  (** All decompositions p = p1 ++ p2 of a path into two parts. *)
  Fixpoint split_path (p : Edge) : list (Edge * Edge) :=
    match p with
    | [] => (nil, nil) :: nil
    | x :: rest =>
        (nil, x :: rest) :: List.map (fun '(p1, p2) => (x :: p1, p2)) (split_path rest)
    end.

  (** Concatenation product: all pairwise concatenations. *)
  Definition lang_mul (L M : Lang) : Lang :=
    fun p => List.existsb (fun '(p1, p2) => L p1 && M p2) (split_path p).

  (** Every split of [p] is exactly a pair [p1 p2] with [p1 ++ p2 = p]. *)
  Lemma split_path_spec (p : Edge) (p1 p2 : Edge) :
    List.In (p1, p2) (split_path p) <-> p1 ++ p2 = p.
  Proof.
    revert p1 p2. induction p as [|e p IH]; intros p1 p2.
    - cbn. split; intro H.
      + destruct H as [Hpair | Hfalse]; [| inversion Hfalse].
        inversion Hpair; subst; reflexivity.
      + destruct p1 as [|e1 p1']; [| cbn in H; discriminate].
        destruct p2 as [|e2 p2']; [| cbn in H; discriminate].
        cbn. left. reflexivity.
    - cbn. split; intro H.
      + destruct H as [Hpair | Hmap].
        * injection Hpair as Hp1 Hp2. subst p1 p2. cbn. reflexivity.
        * apply in_map_iff in Hmap.
          destruct Hmap as [[p1' p2'] [Hpair Hin]].
          injection Hpair as Hp1 Hp2. subst p1 p2.
          apply (proj1 (IH p1' p2')) in Hin.
          cbn. f_equal. exact Hin.
      + destruct p1 as [|e1 p1'].
        * cbn in H. subst p2. cbn. left. reflexivity.
        * cbn in H. injection H as He Hpp. subst e1.
          right. apply in_map_iff.
          exists (p1', p2). split.
          reflexivity.
          apply (proj2 (IH p1' p2)). exact Hpp.
  Qed.

  (** [lang_mul] is the concatenation product: [p] is in [L⊗M] iff it
      factors as [p1 ++ p2] with [p1] in [L] and [p2] in [M]. *)
  Lemma mul_exists (L M : Lang) (p : Edge) :
    lang_mul L M p = true <-> exists p1 p2, p1 ++ p2 = p /\ L p1 = true /\ M p2 = true.
  Proof.
    unfold lang_mul.
    rewrite List.existsb_exists.
    split.
    - intros [x [Hin Hx]].
      destruct x as [p1 p2]. cbn in Hx.
      apply (proj1 (split_path_spec p p1 p2)) in Hin.
      rewrite andb_true_iff in Hx. destruct Hx as [HL HM].
      exists p1, p2. split; [exact Hin | split; [exact HL | exact HM]].
    - intros [p1 [p2 [Happ [HL HM]]]].
      exists (p1, p2). split.
      + apply (proj2 (split_path_spec p p1 p2)). exact Happ.
      + cbn. rewrite andb_true_iff. split; [exact HL | exact HM].
  Qed.

  (** [lang_one] is exactly the singleton of the empty path. *)
  Lemma lang_one_spec (p : Edge) : lang_one p = true <-> p = [].
  Proof.
    destruct p as [|e rest]; cbn.
    - split; intros _; reflexivity.
    - split; intro H; [discriminate | inversion H].
  Qed.

  (** ** Pointwise algebraic laws *)

  Lemma lang_mul_one_l_point (L : Lang) (p : Edge) : lang_mul lang_one L p = L p.
  Proof.
    destruct (L p) eqn:HL.
    - apply (proj2 (mul_exists lang_one L p)).
      exists nil, p. split; [reflexivity | split].
      + apply lang_one_spec. reflexivity.
      + exact HL.
    - destruct (lang_mul lang_one L p) eqn:Hm; [| reflexivity].
      apply (proj1 (mul_exists lang_one L p)) in Hm.
      destruct Hm as [p1 [p2 [Happ [Hone HL']]]].
      apply lang_one_spec in Hone. subst p1.
      rewrite app_nil_l in Happ. subst p2.
      rewrite HL' in HL. discriminate.
  Qed.

  Lemma lang_mul_one_r_point (L : Lang) (p : Edge) : lang_mul L lang_one p = L p.
  Proof.
    destruct (L p) eqn:HL.
    - apply (proj2 (mul_exists L lang_one p)).
      exists p, nil. split; [rewrite app_nil_r; reflexivity | split; [exact HL |]].
      apply lang_one_spec. reflexivity.
    - destruct (lang_mul L lang_one p) eqn:Hm; [| reflexivity].
      apply (proj1 (mul_exists L lang_one p)) in Hm.
      destruct Hm as [p1 [p2 [Happ [HL' Hone]]]].
      apply lang_one_spec in Hone. subst p2.
      rewrite app_nil_r in Happ. subst p1.
      rewrite HL' in HL. discriminate.
  Qed.

  Lemma lang_mul_zero_l_point (M : Lang) (p : Edge) : lang_mul lang_zero M p = false.
  Proof.
    destruct (lang_mul lang_zero M p) eqn:Hm; [| reflexivity].
    apply (proj1 (mul_exists lang_zero M p)) in Hm.
    destruct Hm as [p1 [p2 [Happ [Hz _]]]]. cbn in Hz. discriminate.
  Qed.

  Lemma lang_mul_zero_r_point (L : Lang) (p : Edge) : lang_mul L lang_zero p = false.
  Proof.
    destruct (lang_mul L lang_zero p) eqn:Hm; [| reflexivity].
    apply (proj1 (mul_exists L lang_zero p)) in Hm.
    destruct Hm as [p1 [p2 [Happ [Hl Hz]]]]. cbn in Hz. discriminate.
  Qed.

  (** Associativity of concatenation product. *)
  Lemma lang_mul_assoc_point (L M N : Lang) (p : Edge) :
    lang_mul (lang_mul L M) N p = lang_mul L (lang_mul M N) p.
  Proof.
    destruct (lang_mul (lang_mul L M) N p) eqn:Hl;
    destruct (lang_mul L (lang_mul M N) p) eqn:Hr; try reflexivity.
    - (* Hl = true, Hr = false *)
      apply (proj1 (mul_exists (lang_mul L M) N p)) in Hl.
      destruct Hl as [p1 [p3 [Happ [Hlm Hn]]]].
      apply (proj1 (mul_exists L M p1)) in Hlm.
      destruct Hlm as [p11 [p12 [Happ1 [Hl' Hm]]]].
      assert (Htrue : lang_mul L (lang_mul M N) p = true).
      { apply (proj2 (mul_exists L (lang_mul M N) p)).
        exists p11, (p12 ++ p3). split.
        { transitivity ((p11 ++ p12) ++ p3).
          - rewrite app_assoc. reflexivity.
          - rewrite Happ1. exact Happ. }
        split; [exact Hl' |].
        apply (proj2 (mul_exists M N (p12 ++ p3))).
        exists p12, p3. split; [reflexivity | split; [exact Hm | exact Hn]]. }
      rewrite Htrue in Hr. discriminate.
    - (* Hl = false, Hr = true *)
      apply (proj1 (mul_exists L (lang_mul M N) p)) in Hr.
      destruct Hr as [p1 [p3 [Happ [HL Hmn]]]].
      apply (proj1 (mul_exists M N p3)) in Hmn.
      destruct Hmn as [p21 [p22 [Happ2 [Hm' Hn]]]].
      assert (Htrue : lang_mul (lang_mul L M) N p = true).
      { apply (proj2 (mul_exists (lang_mul L M) N p)).
        exists (p1 ++ p21), p22. split.
        { rewrite <- app_assoc. rewrite Happ2. exact Happ. }
        split; [| exact Hn].
        apply (proj2 (mul_exists L M (p1 ++ p21))).
        exists p1, p21. split; [reflexivity | split; [exact HL | exact Hm']]. }
      rewrite Htrue in Hl. discriminate.
  Qed.

  (** Right distributivity: L ⊗ (M ⊕ N) = (L⊗M) ⊕ (L⊗N). *)
  Lemma lang_mul_add_distr_point (L M N : Lang) (p : Edge) :
    lang_mul L (lang_add M N) p = lang_add (lang_mul L M) (lang_mul L N) p.
  Proof.
    apply eq_true_iff_eq.
    unfold lang_add.
    rewrite !mul_exists.
    split.
    - intros Hl.
      destruct Hl as [p1 [p2 [Happ [HL Hmn]]]].
      apply orb_true_iff in Hmn.
      destruct Hmn as [HM2 | HN2].
      + apply (proj2 (orb_true_iff (lang_mul L M p) (lang_mul L N p))).
        left. apply (proj2 (mul_exists L M p)).
        exists p1, p2. split; [exact Happ | split; [exact HL | exact HM2]].
      + apply (proj2 (orb_true_iff (lang_mul L M p) (lang_mul L N p))).
        right. apply (proj2 (mul_exists L N p)).
        exists p1, p2. split; [exact Happ | split; [exact HL | exact HN2]].
    - intros Hr.
      apply orb_true_iff in Hr.
      destruct Hr as [HM2 | HN2].
      + apply (proj1 (mul_exists L M p)) in HM2.
        destruct HM2 as [p1 [p2 [Happ [HL HMp]]]].
        exists p1, p2. split; [exact Happ | split; [exact HL |]].
        apply (proj2 (orb_true_iff (M p2) (N p2))). left. exact HMp.
      + apply (proj1 (mul_exists L N p)) in HN2.
        destruct HN2 as [p1 [p2 [Happ [HL HNp]]]].
        exists p1, p2. split; [exact Happ | split; [exact HL |]].
        apply (proj2 (orb_true_iff (M p2) (N p2))). right. exact HNp.
  Qed.

  (** Left distributivity: (L ⊕ M) ⊗ N = (L⊗N) ⊕ (M⊗N). *)
  Lemma lang_mul_add_distl_point (L M N : Lang) (p : Edge) :
    lang_mul (lang_add L M) N p = lang_add (lang_mul L N) (lang_mul M N) p.
  Proof.
    apply eq_true_iff_eq.
    unfold lang_add.
    rewrite !mul_exists.
    split.
    - intros Hl.
      destruct Hl as [p1 [p2 [Happ [Hlm Hn]]]].
      apply orb_true_iff in Hlm.
      destruct Hlm as [HL2 | HM2].
      + apply (proj2 (orb_true_iff (lang_mul L N p) (lang_mul M N p))).
        left. apply (proj2 (mul_exists L N p)).
        exists p1, p2. split; [exact Happ | split; [exact HL2 | exact Hn]].
      + apply (proj2 (orb_true_iff (lang_mul L N p) (lang_mul M N p))).
        right. apply (proj2 (mul_exists M N p)).
        exists p1, p2. split; [exact Happ | split; [exact HM2 | exact Hn]].
    - intros Hr.
      apply orb_true_iff in Hr.
      destruct Hr as [HL2 | HM2].
      + apply (proj1 (mul_exists L N p)) in HL2.
        destruct HL2 as [p1 [p2 [Happ [HLp Hn]]]].
        exists p1, p2. split; [exact Happ | split; [| exact Hn]].
        apply (proj2 (orb_true_iff (L p1) (M p1))). left. exact HLp.
      + apply (proj1 (mul_exists M N p)) in HM2.
        destruct HM2 as [p1 [p2 [Happ [HMp Hn]]]].
        exists p1, p2. split; [exact Happ | split; [| exact Hn]].
        apply (proj2 (orb_true_iff (L p1) (M p1))). right. exact HMp.
  Qed.

End LanguageSemiring.

(** * Bridging [Lang] back to the numeric Schulze fixed point

    [lift m i j] is the singleton language of exactly the one direct
    edge (i,j,m i j).  Kleene-closing [lift m] therefore denotes, at
    [i,j], the set of every walk of a given length from i to j (every
    witness kept -- see the header comment on why the value+witness
    pairing could not do this).  [pow_lift_sound]/[pow_lift_complete]
    show the numeric [pow m n i j] is exactly the max measure over that
    set: no counted walk exceeds it, and whenever the value is not the
    bottom [0] (i.e. some walk really exists), some counted walk attains
    it exactly. *)

Section LangInstances.

  (** ---- additive commutative monoid (union) ---- *)

  Lemma addA_proof : forall x y z : Lang, lang_add (lang_add x y) z = lang_add x (lang_add y z).
  Proof. intros x y z. apply functional_extensionality. intro p. unfold lang_add. symmetry. exact (orb_assoc (x p) (y p) (z p)). Qed.

  Lemma addC_proof : forall x y : Lang, lang_add x y = lang_add y x.
  Proof. intros x y. apply functional_extensionality. intro p. unfold lang_add. exact (orb_comm (x p) (y p)). Qed.

  Lemma add0r_proof : forall x : Lang, lang_add lang_zero x = x.
  Proof. intro x. apply functional_extensionality. intro p. unfold lang_add, lang_zero. exact (orb_false_l (x p)). Qed.

  Lemma addr0_proof : forall x : Lang, lang_add x lang_zero = x.
  Proof. intro x. apply functional_extensionality. intro p. unfold lang_add, lang_zero. exact (orb_false_r (x p)). Qed.

  HB.instance Definition _ := IsCommutativeMonoid.Build Lang
    lang_zero lang_add addA_proof addC_proof add0r_proof addr0_proof.

  (** ---- multiplicative semiring (concatenation product) ---- *)

  Lemma mulA_proof : forall a b c : Lang, lang_mul (lang_mul a b) c = lang_mul a (lang_mul b c).
  Proof. intros a b c. apply functional_extensionality. intro p. apply lang_mul_assoc_point. Qed.

  Lemma mul1r_proof : forall a : Lang, lang_mul lang_one a = a.
  Proof. intro a. apply functional_extensionality. intro p. apply lang_mul_one_l_point. Qed.

  Lemma mulr1_proof : forall a : Lang, lang_mul a lang_one = a.
  Proof. intro a. apply functional_extensionality. intro p. apply lang_mul_one_r_point. Qed.

  Lemma mulDr_proof : forall a b c : Lang,
    lang_mul (lang_add a b) c = lang_add (lang_mul a c) (lang_mul b c).
  Proof. intros a b c. apply functional_extensionality. intro p. apply lang_mul_add_distl_point. Qed.

  Lemma mulDl_proof : forall a b c : Lang,
    lang_mul a (lang_add b c) = lang_add (lang_mul a b) (lang_mul a c).
  Proof. intros a b c. apply functional_extensionality. intro p. apply lang_mul_add_distr_point. Qed.

  Lemma mul0r_proof : forall a : Lang, lang_mul lang_zero a = lang_zero.
  Proof. intro a. apply functional_extensionality. intro p. apply lang_mul_zero_l_point. Qed.

  Lemma mulr0_proof : forall a : Lang, lang_mul a lang_zero = lang_zero.
  Proof. intro a. apply functional_extensionality. intro p. apply lang_mul_zero_r_point. Qed.

  HB.instance Definition _ := IsSemiring.Build Lang
    lang_one lang_mul mulA_proof mul1r_proof mulr1_proof
    mulDr_proof mulDl_proof mul0r_proof mulr0_proof.

  (** * Lang is now a genuine Semiring (not bounded, not commutative),
      so the generic [pow] / [geom_sum] / [matrix_mul] machinery from
      [MatN] applies to Lang-valued matrices.

      Deliberately NOT [BoundedSemiring]: there is no single "biggest
      language" for [1 + L = 1] to hold against. 
 *)

End LangInstances.

Section LiftBridge.

  
  Fixpoint nat_eqb (n k : nat) : bool :=
    match n, k with
    | O, O => true
    | S n', S k' => nat_eqb n' k'
    | _, _ => false
    end.

  Lemma nat_eqb_eq (n k : nat) : nat_eqb n k = true <-> n = k.
  Proof.
    revert k. induction n as [|n IH]; intros [|k]; cbn; split; intro H;
      try discriminate; try reflexivity.
    - f_equal. apply IH. exact H.
    - apply IH. injection H as H. exact H.
  Qed.

  Definition R_eqb (x y : R) : bool :=
    match x, y with
    | Left n, Left k => nat_eqb n k
    | Infinity, Infinity => true
    | _, _ => false
    end.

  Lemma R_eqb_eq (x y : R) : R_eqb x y = true <-> x = y.
  Proof.
    destruct x as [n|], y as [k|]; cbn; split; intro H; try discriminate.
    - f_equal. apply nat_eqb_eq. exact H.
    - apply nat_eqb_eq. injection H as H. exact H.
    - reflexivity.
    - reflexivity.
  Qed.

  Definition Node_eqb (x y : Node) : bool :=
    if fin_eq_dec x y then true else false.

  Lemma Node_eqb_eq (x y : Node) : Node_eqb x y = true <-> x = y.
  Proof.
    unfold Node_eqb. destruct (fin_eq_dec x y) as [Heq | Hneq]; split; intro H.
    - exact Heq.
    - reflexivity.
    - discriminate.
    - congruence.
  Qed.

  (** The language of exactly one path: the direct edge [(i,j,m i j)]. *)
  Definition lift (m : Node -> Node -> R) (i j : Node) : Lang :=
    fun p => match p with
      | (i', j', w) :: nil => Node_eqb i i' && Node_eqb j j' && R_eqb w (m i j)
      | _ => false
      end.

  Lemma lift_spec (m : Node -> Node -> R) (i j : Node) (p : Edge) :
    lift m i j p = true <-> p = [(i, j, m i j)].
  Proof.
    unfold lift.
    destruct p as [|[[i' j'] w] [|e p']]; cbn; split; intro H; try discriminate.
    - apply andb_true_iff in H; destruct H as [H1 H2].
      apply andb_true_iff in H1; destruct H1 as [H1 H1'].
      apply Node_eqb_eq in H1; apply Node_eqb_eq in H1'; apply R_eqb_eq in H2.
      subst. reflexivity.
    - injection H as Hi Hj Hw. subst i' j' w.
      rewrite (proj2 (Node_eqb_eq i i) eq_refl).
      rewrite (proj2 (Node_eqb_eq j j) eq_refl).
      rewrite (proj2 (R_eqb_eq (m i j) (m i j)) eq_refl).
      reflexivity.
  Qed.

  (** [*] is monotone in its right argument w.r.t. [Orel] -- this only
      needs distributivity, not idempotence, so it holds for any
      [Semiring], not just [IdempotentSemiring] as in [OrelN.v]. *)
  Lemma mul_orel_compat_r_gen {S : Semiring.type} (a b c : S) :
    Orel a b -> Orel (c * a) (c * b).
  Proof.
    unfold Orel. intro H.
    transitivity (c * (a + b)).
    - symmetry. apply mulDl.
    - rewrite H. reflexivity.
  Qed.

  (** Membership in a [fold_right lang_add] is membership in some branch. *)
  Lemma sum_lang_mem (f : Node -> Lang) (l : list Node) (p : Edge) :
    (List.fold_right (fun x acc => lang_add (f x) acc) lang_zero l) p = true <->
    exists x, In x l /\ f x p = true.
  Proof.
    induction l as [|a l' IH]; cbn.
    - split; [discriminate | intros [x [[] _]]].
    - unfold lang_add at 1. rewrite orb_true_iff. split.
      + intros [H | H].
        * exists a. split; [left; reflexivity | exact H].
        * apply IH in H. destruct H as [x [Hin Hfx]].
          exists x. split; [right; exact Hin | exact Hfx].
      + intros [x [[Heq | Hin] Hfx]].
        * subst. left. exact Hfx.
        * right. apply IH. exists x. split; [exact Hin | exact Hfx].
  Qed.

  (** Every term of a [BoundedSemiring] fold-sum is [Orel]-below the sum
      (proved for an abstract list first, then specialised to
      [elements] -- specialising directly runs into an HB canonical-
      structure diamond for [Node]'s concrete, closed [elements] list). *)
  Lemma sum_ge_term_list {S : BoundedSemiring.type} (f : Node -> S) (y : Node) (l : list Node) :
    In y l -> Orel (f y) (List.fold_right (fun x acc => f x + acc) 0 l).
  Proof.
    unfold Orel.
    induction l as [|a l' IH]; intro Hin.
    - contradiction.
    - cbn. destruct Hin as [Heq | Hin].
      + subst. transitivity ((f y + f y) + List.fold_right (fun x acc => f x + acc) 0 l').
        * symmetry; apply addA.
        * apply (f_equal (fun t => t + List.fold_right (fun x acc => f x + acc) 0 l')).
          apply bounded_add_idem.
      + transitivity (f a + (f y + List.fold_right (fun x acc => f x + acc) 0 l')).
        * transitivity ((f y + f a) + List.fold_right (fun x acc => f x + acc) 0 l').
          -- symmetry; apply addA.
          -- transitivity ((f a + f y) + List.fold_right (fun x acc => f x + acc) 0 l').
             ++ apply (f_equal (fun t => t + List.fold_right (fun x acc => f x + acc) 0 l')).
                apply addC.
             ++ apply addA.
        * apply (f_equal (fun t => f a + t)); apply (IH Hin).
  Qed.

  Lemma sum_ge_term {S : BoundedSemiring.type} (f : Node -> S) (y : Node) :
    In y elements -> Orel (f y) (sum f).
  Proof. unfold sum. apply sum_ge_term_list. Qed.

  (** Unfolds one [S n] step of [pow (lift m)] into: [p] is counted iff
      it starts with a direct edge [(i,y,m i y)] into some [y] followed
      by a walk counted at [n] from [y] to [j]. *)
  Lemma pow_lift_S_spec (m : Node -> Node -> R) (n : nat) (i j : Node) (p : Edge) :
    pow (lift m) (S n) i j p = true <->
    exists y p2, p = (i, y, m i y) :: p2 /\ pow (lift m) n y j p2 = true.
  Proof.
    cbn [pow]. unfold matrix_mul.
    rewrite (sum_lang_mem (fun y => lang_mul (lift m i y) (pow (lift m) n y j)) elements p).
    split.
    - intros [y [_ Hy]]. apply mul_exists in Hy.
      destruct Hy as [p1 [p2 [Happ [Hp1 Hp2]]]].
      apply lift_spec in Hp1. subst p1. exists y, p2. split; [| exact Hp2].
      rewrite <- Happ. reflexivity.
    - intros [y [p2 [Heq Hp2]]]. exists y.
      split; [apply elements_complete |].
      apply mul_exists. exists [(i, y, m i y)], p2.
      split; [symmetry; exact Heq | split; [apply lift_spec; reflexivity | exact Hp2]].
  Qed.

  (** SOUNDNESS: no walk counted by [pow (lift m) n] exceeds the numeric
      Schulze fixed point. *)
  Theorem pow_lift_sound (m : Node -> Node -> R) :
    forall n i j p, pow (lift m) n i j p = true -> Orel (measure_of_path p) (pow m n i j).
  Proof.
    induction n as [|n IH]; intros i j p Hp.
    - cbn [pow] in Hp |- *. unfold I in Hp.
      destruct (Structures.fin_eq_dec i j) as [Heq | Hneq].
      + apply lang_one_spec in Hp. subst p. cbn [measure_of_path].
        unfold I. destruct (Structures.fin_eq_dec i j) as [_ | Hc]; [| congruence].
        unfold Orel. apply (add_bound (s := R) 1).
      + cbn in Hp. discriminate.
    - apply pow_lift_S_spec in Hp.
      destruct Hp as [y [p2 [Heq Hp2]]]. subst p.
      cbn [measure_of_path].
      cbn [pow]. unfold matrix_mul.
      apply (orel_trans (m i y * measure_of_path p2) (m i y * pow m n y j)).
      + apply mul_orel_compat_r_gen. apply (IH y j p2 Hp2).
      + apply (sum_ge_term (fun l => m i l * pow m n l j) y (elements_complete y)).
  Qed.

  (** The numeric max is total for this concrete [R] -- [+] always
      returns one of its two arguments. Needed only for completeness. *)
  Lemma R_total_order (x y : R) : x + y = x \/ x + y = y.
  Proof.
    destruct x as [n|], y as [k|]; cbn; auto.
    destruct (Nat.le_ge_cases n k) as [Hle | Hge].
    - right. f_equal. apply Nat.max_r. exact Hle.
    - left. f_equal. apply Nat.max_l. exact Hge.
  Qed.

  (** A [BoundedSemiring] fold-sum over a total order equals one of its
      own terms, or -- if the index list is empty -- the bottom [0]. *)
  Lemma sum_attained (f : Node -> R) (l : list Node) :
    (exists x, In x l /\ f x = List.fold_right (fun x y => f x + y) 0 l) \/
    List.fold_right (fun x y => f x + y) 0 l = 0.
  Proof.
    induction l as [|a l' IH]; cbn.
    - right. reflexivity.
    - destruct (R_total_order (f a) (List.fold_right (fun x y => f x + y) 0 l'))
        as [Heq | Heq].
      + left. exists a. split; [left; reflexivity | symmetry; exact Heq].
      + destruct IH as [[x [Hin Hx]] | Hz].
        * left. exists x. split; [right; exact Hin |].
          rewrite Hx. symmetry. exact Heq.
        * right. transitivity (List.fold_right (fun x y => f x + y) 0 l').
          exact Heq. exact Hz.
  Qed.

  (** COMPLETENESS: whenever the numeric value at [i,j,n] is not the
      bottom [0] (i.e. some walk of length [n] genuinely exists), it is
      attained exactly by some walk counted in [pow (lift m) n]. *)
  Theorem pow_lift_complete (m : Node -> Node -> R) :
    forall n i j, pow m n i j = 0 \/
      exists p, pow (lift m) n i j p = true /\ measure_of_path p = pow m n i j.
  Proof.
    induction n as [|n IH]; intros i j.
    - cbn [pow]. unfold I. destruct (Structures.fin_eq_dec i j) as [Heq | Hneq].
      + right. exists []. split.
        * cbn [pow]. unfold I. destruct (Structures.fin_eq_dec i j) as [_ | Hc]; [| congruence].
          apply lang_one_spec. reflexivity.
        * cbn [measure_of_path]. reflexivity.
      + left. reflexivity.
    - cbn [pow]. unfold matrix_mul.
      destruct (sum_attained (fun l => m i l * pow m n l j) elements) as [[y [_ Hy]] | Hz].
      + destruct (IH y j) as [Hz | [p2 [Hp2 Hmeas]]].
        * (* the winning term m i y * pow m n y j collapses to 0 *)
          left. unfold sum. transitivity (m i y * pow m n y j).
          symmetry; exact Hy. rewrite Hz. apply mulr0.
        * right. exists ((i, y, m i y) :: p2). split.
          -- unfold sum.
             apply (sum_lang_mem (fun y0 => lang_mul (lift m i y0) (pow (lift m) n y0 j)) elements).
             exists y. split; [apply elements_complete |].
             apply mul_exists. exists [(i, y, m i y)], p2.
             split; [reflexivity | split; [apply lift_spec; reflexivity | exact Hp2]].
          -- cbn [measure_of_path]. rewrite Hmeas. unfold sum. exact Hy.
      + left. unfold sum. exact Hz.
  Qed.

  (** Computable extraction: an actual witness path, not just a [Prop]-
      level existence proof.  [pow_lift_complete]'s proof term is erased
      by extraction, so [pow_witness] below is a genuine [Fixpoint]
      mirroring the same induction with a real decision procedure
      ([R_leb]) standing in for [R_total_order]'s bare disjunction. *)

  Fixpoint nat_leb (n k : nat) : bool :=
    match n, k with
    | O, _ => true
    | S _, O => false
    | S n', S k' => nat_leb n' k'
    end.

  Lemma nat_leb_le (n k : nat) : nat_leb n k = true <-> n <= k.
  Proof.
    revert k. induction n as [|n IH]; intros k; destruct k; cbn; split; intro H;
      try discriminate; try lia.
    - apply IH in H. lia.
    - apply IH. lia.
  Qed.

  Definition R_leb (x y : R) : bool :=
    match x, y with
    | _, Infinity => true
    | Infinity, Left _ => false
    | Left n, Left k => nat_leb n k
    end.

  Lemma R_leb_spec (x y : R) : R_leb x y = true <-> Orel x y.
  Proof.
    unfold Orel. destruct x as [n|], y as [k|]; cbn; split; intro H;
      try discriminate; try reflexivity.
    - f_equal. apply nat_leb_le in H. lia.
    - f_equal. apply nat_leb_le. injection H as H. lia.
  Qed.

  (** Picks the [val]-maximal element of a list, or [None] for []. *)
  Fixpoint list_argmax_by {A : Type} (val : A -> R) (l : list A) : option A :=
    match l with
    | [] => None
    | x :: rest =>
        match list_argmax_by val rest with
        | None => Some x
        | Some best => if R_leb (val best) (val x) then Some x else Some best
        end
    end.

  Lemma R_leb_total (x y : R) : R_leb x y = false -> Orel y x.
  Proof.
    unfold Orel. destruct x as [n|], y as [k|]; cbn; intro H; try discriminate.
    - f_equal. assert (Hc : ~ n <= k) by (intro Hc'; apply nat_leb_le in Hc'; congruence).
      lia.
    - reflexivity.
  Qed.

  (** The argmax is a member of the list and its value equals the fold
      (the same fold-shape [sum] unfolds to). *)
  Lemma list_argmax_by_spec {A : Type} (val : A -> R) (l : list A) :
    match list_argmax_by val l with
    | Some x => In x l /\ val x = List.fold_right (fun y acc => val y + acc) 0 l
    | None => l = []
    end.
  Proof.
    induction l as [|x rest IH]; cbn.
    - reflexivity.
    - destruct (list_argmax_by val rest) as [best|] eqn:Hbest.
      + destruct IH as [Hin Hval].
        destruct (R_leb (val best) (val x)) eqn:Hcmp.
        * split; [left; reflexivity |].
          apply R_leb_spec in Hcmp.
          transitivity (val x + val best).
          transitivity (val best + val x).
          symmetry; exact Hcmp.
          apply addC.
          apply (f_equal (fun t => val x + t)); exact Hval.
        * split; [right; exact Hin |].
          apply R_leb_total in Hcmp.
          transitivity (val x + val best).
          symmetry.
          exact Hcmp.
          apply (f_equal (fun t => val x + t)).
          exact Hval.
      + subst rest. cbn. split; [left; reflexivity |].
        transitivity (val x + 0). symmetry; apply addr0. reflexivity.
  Qed.

  (** A real, extractable witness-path computation: at each step, pick
      the numerically-best successor via [list_argmax_by] and recurse. *)
  Fixpoint pow_witness (m : Node -> Node -> R) (n : nat) (i j : Node) : option Edge :=
    match n with
    | O => if Structures.fin_eq_dec i j then Some [] else None
    | S n' =>
        match list_argmax_by (fun y => m i y * pow m n' y j) elements with
        | None => None
        | Some y =>
            match pow_witness m n' y j with
            | Some p2 => Some ((i, y, m i y) :: p2)
            | None => None
            end
        end
    end.

  (** CORRECTNESS of the computable extractor: it matches
      [pow_lift_complete] exactly, constructively. *)
  Theorem pow_witness_spec (m : Node -> Node -> R) :
    forall n i j,
      match pow_witness m n i j with
      | Some p => pow (lift m) n i j p = true /\ measure_of_path p = pow m n i j
      | None => pow m n i j = 0
      end.
  Proof.
    induction n as [|n IH]; intros i j.
    - cbn [pow_witness pow]. unfold I.
      destruct (Structures.fin_eq_dec i j) as [Heq | Hneq].
      + split.
        * cbn [pow]. unfold I. destruct (Structures.fin_eq_dec i j) as [_ | Hc]; [| congruence].
          apply lang_one_spec. reflexivity.
        * cbn [measure_of_path]. destruct (Structures.fin_eq_dec i j) as [_ | Hc]; [| congruence].
          reflexivity.
      + reflexivity.
    - cbn [pow_witness pow]. unfold matrix_mul.
      pose proof (list_argmax_by_spec (fun y => m i y * pow m n y j) elements) as Hargmax.
      destruct (list_argmax_by (fun y => m i y * pow m n y j) elements) as [y|] eqn:Hbest.
      + destruct Hargmax as [_ Hval].
        specialize (IH y j).
        destruct (pow_witness m n y j) as [p2|] eqn:Hp2.
        * destruct IH as [Hmem Hmeas].
          split.
          -- apply pow_lift_S_spec. exists y, p2. split; [reflexivity | exact Hmem].
          -- cbn [measure_of_path]. rewrite Hmeas. unfold sum. exact Hval.
        * unfold sum. transitivity (m i y * pow m n y j).
          symmetry; exact Hval.
          transitivity (m i y * 0). apply (f_equal (fun t => m i y * t)); exact IH.
          apply mulr0.
      + exfalso.
        pose proof (elements_complete (s := Node) i) as Hin.
        exact (eq_rect elements (fun l => In i l) Hin [] Hargmax).
  Qed.

End LiftBridge.


(** * Schulze beatpath strengths via the Kleene closure

    The single power [m³] counts only exact length-3 paths; the Schulze
    strongest-path strengths are the geometric closure
        (m + I)³ = I + m + m² + m³
    (paths of up to three hops — with |Node| = 4 candidates, every
    simple path has at most 3 edges, so this is the fixed point). *)

(** Kleene-closure matrix: [(m + I)³] — the strongest-path strengths
    between all candidate pairs (the Schulze beatpath matrix). *)
Definition schulze_star (m : Node -> Node -> R) : Node -> Node -> R :=
  powN_fun (matrix_add m (I : Node -> Node -> R)) 3%N.

(** Efficient matrix-vector action of the beatpath closure (list-based). *)
Definition mva_star_eff_fun (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action_eff_fun (schulze_star m) v.

(** Functional matrix-vector action of the beatpath closure. *)
Definition mva_star_func (m : Node -> Node -> R) (v : Node -> R) : Node -> R :=
  SemimoduleN.matrix_vector_action (schulze_star m) v.

(** A real, computable witness path -- not just the strength value.
    [pow_witness_spec] guarantees [schulze_witness_value m i j] equals
    [pow (matrix_add m I) 3 i j], which -- since a beatpath closure of
    up to 3 hops over 4 candidates has already stabilised -- coincides
    with [schulze_star m i j] above. *)

(** An actual strongest beatpath from [i] to [j] (up to 3 hops), or
    [None] if [i] cannot reach [j] within that bound. *)
Definition schulze_witness (m : Node -> Node -> R) (i j : Node) : option Edge :=
  pow_witness (matrix_add m (I : Node -> Node -> R)) 3 i j.

(** The strength of that witness path -- [0] when there is none. *)
Definition schulze_witness_value (m : Node -> Node -> R) (i j : Node) : R :=
  match schulze_witness m i j with
  | Some p => measure_of_path p
  | None => 0
  end.
