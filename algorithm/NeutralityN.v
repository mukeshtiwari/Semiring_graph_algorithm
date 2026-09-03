From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN
  SchulzeWitnessN ResolvabilityN TransitivityN WinnerexistenceN
  ReversalsymmetryN MonotonicityN ParetoN CondorcetN
  SmithN PrudenceN MinMaxN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(** Schulze over a semiring: neutrality (2.1)
    Split out of the former monolithic SocialchoiceN.v. *)

Section NeutralityN.

  Context {Node : FinType.type}.


  (** * Neutrality (§2.1)

      Schulze notes in §2.1 that making the strength of a link depend only
      on N[e,f] and N[f,e] guarantees that the proposed method satisfies
      anonymity and neutrality, without proving it.  Neutrality is the
      claim that the method treats the alternatives symmetrically: rename
      them and the outcome is renamed to match.

      Here a renaming is a bijection [s] of [Node] with inverse [t], and
      the relabelled profile is [permute_matrix M s].  The whole content
      is that [sum] does not notice a permutation of its index — the
      closure is then equivariant termwise. *)

  (** Relabelling the alternatives by [s]. *)
  Definition permute_matrix {R : Semiring.type}
    (M : @Matrix Node R) (s : Node -> Node) : @Matrix Node R :=
    fun x y => M (s x) (s y).

  Lemma permute_matrix_unfold {R : Semiring.type}
    (M : @Matrix Node R) (s : Node -> Node) (x y : Node) :
    permute_matrix M s x y = M (s x) (s y).
  Proof. reflexivity. Qed.

  Lemma NoDup_map_inj {A B : Type} (f : A -> B) (l : list A) :
    (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
  Proof.
    intros Hinj Hnd. induction Hnd as [|a l Ha Hnd IH]; cbn [map].
    - constructor.
    - constructor; [| exact IH].
      intro Hin. apply in_map_iff in Hin as [z [Heq Hz]].
      apply Hinj in Heq. subst z. contradiction.
  Qed.

  Section Neutrality.
    Context (s t : Node -> Node)
            (Hst : forall x, s (t x) = x)
            (Hts : forall x, t (s x) = x).

    Lemma s_inj : forall x y, s x = s y -> x = y.
    Proof. intros x y H. rewrite <- (Hts x), <- (Hts y), H. reflexivity. Qed.

    (** [s] permutes the enumeration: it is injective, and surjective by [t]. *)
    Lemma map_s_perm : Permutation (map s (@elements Node)) (@elements Node).
    Proof.
      apply NoDup_Permutation.
      - apply NoDup_map_inj; [exact s_inj | apply elements_nodup].
      - apply elements_nodup.
      - intro x. split; intro Hin.
        + apply elements_complete.
        + apply in_map_iff. exists (t x).
          split; [apply Hst | apply elements_complete].
    Qed.

    (** A commutative-monoid fold does not notice the order of its list. *)
    Lemma fold_right_perm {R : Semiring.type} (f : Node -> R) :
      forall l l', Permutation l l' ->
        fold_right (fun x acc => f x + acc) 0 l
        = fold_right (fun x acc => f x + acc) 0 l'.
    Proof.
      intros l l' Hp.
      induction Hp as [| x l l' Hp IH | x y l | l l' l'' Hp1 IH1 Hp2 IH2].
      - reflexivity.
      - cbn [fold_right]. rewrite IH. reflexivity.
      - cbn [fold_right].
        rewrite <- (addA (f y) (f x) (fold_right (fun z acc => f z + acc) 0 l)).
        rewrite <- (addA (f x) (f y) (fold_right (fun z acc => f z + acc) 0 l)).
        rewrite (addC (f y) (f x)). reflexivity.
      - rewrite IH1. exact IH2.
    Qed.

    Lemma fold_right_map_s {R : Semiring.type} (g : Node -> R) :
      forall l, fold_right (fun x acc => g x + acc) 0 (map s l)
                = fold_right (fun x acc => g (s x) + acc) 0 l.
    Proof.
      induction l as [|a l IH]; cbn [map fold_right]; [reflexivity |].
      rewrite IH. reflexivity.
    Qed.

    (** The one fact everything below rests on. *)
    Lemma sum_permute {R : Semiring.type} (g : Node -> R) :
      sum (fun z => g (s z)) = sum g.
    Proof.
      unfold sum.
      rewrite <- (fold_right_map_s g (@elements Node)).
      apply fold_right_perm. exact map_s_perm.
    Qed.

    Lemma pow_permute {R : Semiring.type} (M : @Matrix Node R) :
      forall n a b, pow (permute_matrix M s) n a b = pow M n (s a) (s b).
    Proof.
      induction n as [|n IH]; intros a b.
      - cbn [pow]. unfold I.
        destruct (fin_eq_dec a b) as [Hab|Hab];
          destruct (fin_eq_dec (s a) (s b)) as [Hsab|Hsab]; try reflexivity.
        + exfalso. apply Hsab. rewrite Hab. reflexivity.
        + exfalso. apply Hab. exact (s_inj a b Hsab).
      - cbn [pow]. unfold matrix_mul.
        transitivity (sum (fun z => M (s a) (s z) * pow M n (s z) (s b))).
        + apply sum_ext. intro z. rewrite permute_matrix_unfold, IH. reflexivity.
        + exact (sum_permute (fun w => M (s a) w * pow M n w (s b))).
    Qed.

    Lemma geom_sum_permute {R : Semiring.type} (M : @Matrix Node R) :
      forall n a b, geom_sum (permute_matrix M s) n a b = geom_sum M n (s a) (s b).
    Proof.
      induction n as [|n IH]; intros a b.
      - cbn [geom_sum]. unfold I.
        destruct (fin_eq_dec a b) as [Hab|Hab];
          destruct (fin_eq_dec (s a) (s b)) as [Hsab|Hsab]; try reflexivity.
        + exfalso. apply Hsab. rewrite Hab. reflexivity.
        + exfalso. apply Hab. exact (s_inj a b Hsab).
      - cbn [geom_sum]. unfold matrix_add.
        rewrite IH, pow_permute. reflexivity.
    Qed.

    Lemma mat_star_permute {R : Semiring.type} (M : @Matrix Node R) (a b : Node) :
      mat_star (permute_matrix M s) a b = mat_star M (s a) (s b).
    Proof. unfold mat_star. apply geom_sum_permute. Qed.

    (** Neutrality for the relation O. *)
    Theorem neutrality_beats {R : Semiring.type} (M : @Matrix Node R) (a b : Node) :
      schulze_beats (permute_matrix M s) a b <-> schulze_beats M (s a) (s b).
    Proof.
      unfold schulze_beats, beats.
      rewrite (mat_star_permute M b a), (mat_star_permute M a b). reflexivity.
    Qed.

    (** …and for the winner set. *)
    Theorem neutrality_winner {R : Semiring.type} (M : @Matrix Node R) (a : Node) :
      schulze_winner (permute_matrix M s) a <-> schulze_winner M (s a).
    Proof.
      split.
      - intros Hw c Hc Hbeats.
        apply (Hw (t c)).
        + intro Heq. apply Hc. rewrite <- (Hst c), Heq. reflexivity.
        + apply (neutrality_beats M (t c) a). rewrite Hst. exact Hbeats.
      - intros Hw b Hb Hbeats.
        apply (Hw (s b)).
        + intro Heq. apply Hb. exact (s_inj b a Heq).
        + exact (proj1 (neutrality_beats M b a) Hbeats).
    Qed.

    (** The same equivalence read from the original election's side: [a]
        wins [M] exactly when the alternative playing [a]'s role in the
        relabelled election, its inverse image [t a], wins there.  Note
        that [s a] in place of [t a] would be false for a non-involutive
        [s]: it would say that [a] wins iff [s (s a)] wins. *)
    Corollary neutrality_winner_inv {R : Semiring.type}
      (M : @Matrix Node R) (a : Node) :
      schulze_winner M a <-> schulze_winner (permute_matrix M s) (t a).
    Proof.
      rewrite (neutrality_winner M (t a)). rewrite (Hst a). reflexivity.
    Qed.
  End Neutrality.

  (** The passive view of neutrality.  [neutrality_winner] and its inverse
      corollary read [permute_matrix M s] actively: the matrix is pulled
      along [s] and the winner moves along the inverse [t].  The passive
      reading keeps every entry of [M] in place and renames each
      alternative [a] to [s a]; written as a matrix over the new names,
      the renamed election is [permute_matrix M t], and the winner now
      moves forward along [s] itself.  The proof is [neutrality_winner]
      with the roles of [s] and [t] exchanged, which the symmetric
      hypotheses permit. *)
  Corollary neutrality_winner_relabel
    (s t : Node -> Node)
    (Hst : forall x, s (t x) = x)
    (Hts : forall x, t (s x) = x)
    {R : Semiring.type} (M : @Matrix Node R) (a : Node) :
    schulze_winner M a <-> schulze_winner (permute_matrix M t) (s a).
  Proof.
    rewrite (neutrality_winner t s Hts Hst M (s a)).
    rewrite (Hts a). reflexivity.
  Qed.


End NeutralityN.
