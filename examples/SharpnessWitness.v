(** * Machine-checked sharpness witnesses for the two characterisations.

    Two carriers isolate the axioms of the transitivity and winner
    characterisations in SocialchoiceN.v:

      - the TROPICAL semiring (min-plus, from Shortestpath.v) is bounded
        and selective but lacks the meet property, and admits a 3x3
        matrix whose beat relation is a 3-cycle with no winner at all;

      - the DIAMOND lattice D4 = {bot, p, q, top} with join/meet has the
        meet property but is not selective, and yet EVERY matrix on
        three alternatives admits a winner — checked by enumerating all
        4^9 matrices — which is why the winner characterisation needs a
        fourth alternative and why four is optimal.

    The exhaustive facts are established by reflection: a boolean
    winner-checker is proved sound against schulze_winner, and a single
    vm_compute discharges the quantification over all tabulated matrices. *)

From Stdlib Require Import List Psatz Utf8.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN SocialchoiceN.
(** Schulze is imported first so that Shortestpath's [Node], [R], and
    constructor names shadow its homonyms; the max-min carrier of the worked
    example below is referred to by its qualified name [Schulze.R]. *)
From Examples Require Import Schulze Shortestpath.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).

(** * Part 1: the tropical semiring breaks winner existence at three.

    Forward hops cost 1, backward hops cost 2.  Being closer is better
    (the natural order of min-plus is REVERSED numeric order), so every
    alternative beats its successor round the triangle. *)

Section Tropical.

  (** The rock-paper-scissors profile.  Each alternative reaches its successor
      round the triangle in one hop and its predecessor in two, and the diagonal
      is [oneR], which is distance zero. *)
  Definition M0 : Node -> Node -> R :=
    fun x y =>
      match x, y with
      | A, A => oneR | B, B => oneR | C, C => oneR
      | A, B => Left 1 | B, C => Left 1 | C, A => Left 1
      | B, A => Left 2 | C, B => Left 2 | A, C => Left 2
      end.

  (** The tropical semiring is selective... *)
  Lemma tropical_selective : forall x y : R, x + y = x \/ x + y = y.
  Proof.
    intros [x|] [y|]; cbn; auto.
    destruct (PeanoNat.Nat.min_dec x y) as [E|E];
      [left | right]; cbn; rewrite E; reflexivity.
  Qed.

  (** ...but it does not have the meet property: 1 ≤ 1 twice over, yet
      1 * 1 = 2 and 1 ≤ 2 fails in the reversed order. *)
  Lemma tropical_no_meet :
    ~ (forall m a b : R, m ≤ a -> m ≤ b -> m ≤ a * b).
  Proof.
    intro Hmeet.
    specialize (Hmeet (Left 1) (Left 1) (Left 1)).
    assert (H1 : Left 1 ≤ Left 1) by (unfold Orel; reflexivity).
    specialize (Hmeet H1 H1).
    unfold Orel in Hmeet. vm_compute in Hmeet. discriminate.
  Qed.

  (** The first edge of the cycle: the one-hop route from [A] to [B] is strictly
      shorter than the two-hop route back, so [A] beats [B]. *)
  Lemma trop_beats_AB : schulze_beats M0 A B.
  Proof. split; vm_compute; [reflexivity | discriminate]. Qed.

  (** The second edge, [B] beats [C], by the same computation. *)
  Lemma trop_beats_BC : schulze_beats M0 B C.
  Proof. split; vm_compute; [reflexivity | discriminate]. Qed.

  (** The third edge, [C] beats [A], closing the cycle. *)
  Lemma trop_beats_CA : schulze_beats M0 C A.
  Proof. split; vm_compute; [reflexivity | discriminate]. Qed.

  (** The beat relation of M0 is the 3-cycle A ≻ B ≻ C ≻ A: everyone is
      beaten, so the winner set is empty already at three alternatives. *)
  Theorem tropical_no_winner_at_three :
    forall w : Node, ~ schulze_winner M0 w.
  Proof.
    intros w Hw. destruct w.
    - exact (Hw C ltac:(discriminate) trop_beats_CA).
    - exact (Hw A ltac:(discriminate) trop_beats_AB).
    - exact (Hw B ltac:(discriminate) trop_beats_BC).
  Qed.

End Tropical.

(** * Part 2: the diamond lattice. *)

(** The diamond lattice D4: a bottom, two incomparable atoms [Dp] and [Dq], and
    a top.  It is the smallest lattice that is distributive and yet not a chain,
    which is exactly what is needed here: a chain would be selective, and
    selectivity is the axiom under test. *)
Inductive D4 : Type := Dbot | Dp | Dq | Dtop.

(** Join, the least upper bound and the additive operation of the semiring.
    [Dbot] is neutral and [Dtop] absorbing; the two incomparable atoms join to
    [Dtop], which is where non-selectivity comes from. *)
Definition joinD (x y : D4) : D4 :=
  match x, y with
  | Dbot, z => z
  | z, Dbot => z
  | Dtop, _ => Dtop
  | _, Dtop => Dtop
  | Dp, Dp => Dp
  | Dq, Dq => Dq
  | Dp, Dq => Dtop
  | Dq, Dp => Dtop
  end.

(** Meet, the greatest lower bound and the multiplicative operation.  [Dtop] is
    neutral and [Dbot] absorbing; the two incomparable atoms meet at [Dbot].
    The strength of a path is the meet of its links. *)
Definition meetD (x y : D4) : D4 :=
  match x, y with
  | Dtop, z => z
  | z, Dtop => z
  | Dbot, _ => Dbot
  | _, Dbot => Dbot
  | Dp, Dp => Dp
  | Dq, Dq => Dq
  | Dp, Dq => Dbot
  | Dq, Dp => Dbot
  end.

(** The lattice laws, each by exhaustive case analysis over the four elements,
    and the Hierarchy-Builder instances they feed.  The upshot is that [D4] is a
    bounded semiring under (join, meet), so every result of the development
    applies to it unchanged. *)
Section D4Instances.

  (** Join is associative. *)
  Lemma joinD_assoc : forall x y z, joinD (joinD x y) z = joinD x (joinD y z).
  Proof. intros [| | |] [| | |] [| | |]; reflexivity. Qed.

  (** Join is commutative. *)
  Lemma joinD_comm : forall x y, joinD x y = joinD y x.
  Proof. intros [| | |] [| | |]; reflexivity. Qed.

  (** [Dbot] is a left identity for join, so it is the semiring zero. *)
  Lemma joinD_0l : forall x, joinD Dbot x = x.
  Proof. intros [| | |]; reflexivity. Qed.

  (** [Dbot] is a right identity for join. *)
  Lemma joinD_0r : forall x, joinD x Dbot = x.
  Proof. intros [| | |]; reflexivity. Qed.

  (** The additive structure: [(D4, joinD, Dbot)] is a commutative monoid. *)
  HB.instance Definition _ := IsCommutativeMonoid.Build D4
    Dbot joinD joinD_assoc joinD_comm joinD_0l joinD_0r.

  (** Meet is associative. *)
  Lemma meetD_assoc : forall x y z, meetD (meetD x y) z = meetD x (meetD y z).
  Proof. intros [| | |] [| | |] [| | |]; reflexivity. Qed.

  (** [Dtop] is a left identity for meet, so it is the semiring one. *)
  Lemma meetD_1l : forall x, meetD Dtop x = x.
  Proof. intros [| | |]; reflexivity. Qed.

  (** [Dtop] is a right identity for meet. *)
  Lemma meetD_1r : forall x, meetD x Dtop = x.
  Proof. intros [| | |]; reflexivity. Qed.

  (** Meet distributes over join on the right. *)
  Lemma meetD_joinD_distr_r : forall x y z,
    meetD (joinD x y) z = joinD (meetD x z) (meetD y z).
  Proof. intros [| | |] [| | |] [| | |]; reflexivity. Qed.

  (** Meet distributes over join on the left. *)
  Lemma meetD_joinD_distr_l : forall x y z,
    meetD x (joinD y z) = joinD (meetD x y) (meetD x z).
  Proof. intros [| | |] [| | |] [| | |]; reflexivity. Qed.

  (** [Dbot] annihilates on the left under meet. *)
  Lemma meetD_0l : forall x, meetD Dbot x = Dbot.
  Proof. intros [| | |]; reflexivity. Qed.

  (** [Dbot] annihilates on the right under meet. *)
  Lemma meetD_0r : forall x, meetD x Dbot = Dbot.
  Proof. intros [| | |]; reflexivity. Qed.

  (** The multiplicative structure closes the semiring: meet distributes over
      join in both arguments and [Dbot] annihilates. *)
  HB.instance Definition _ := IsSemiring.Build D4
    Dtop meetD meetD_assoc meetD_1l meetD_1r
    meetD_joinD_distr_r meetD_joinD_distr_l meetD_0l meetD_0r.

  (** [Dtop] is absorbing for join, which is the boundedness axiom.  Its effect
      is that the geometric sum defining the closure stabilises. *)
  Lemma joinD_bound : forall x, joinD Dtop x = Dtop.
  Proof. intros [| | |]; reflexivity. Qed.

  (** [D4] is therefore a bounded semiring, and [mat_star], [schulze_beats] and
      [schulze_winner] are all available on it. *)
  HB.instance Definition _ := IsBoundedSemiring.Build D4 joinD_bound.

End D4Instances.

(** D4 has the meet property: meet really is the greatest lower bound. *)
Lemma diamond_meet_property :
  forall m a b : D4, m ≤ a -> m ≤ b -> m ≤ a * b.
Proof.
  intros [| | |] [| | |] [| | |]; unfold Orel; cbn;
    intros H1 H2; first [reflexivity | discriminate H1 | discriminate H2].
Qed.

(** ...and it is not selective: the two incomparable atoms join to top. *)
Lemma diamond_not_selective :
  exists x y : D4, x + y <> x /\ x + y <> y.
Proof.
  exists Dp, Dq. split; cbn; discriminate.
Qed.

(** The diamond admits no CYCLIC TRIPLE: no three values, each strictly
    above the meet of the other two.  By [beats_on_cycle3_cyclic_triple]
    this means the beat relation over the diamond never contains a
    three-cycle, on any candidate list and for any matrix — the fact that
    lets the clone criterion hold at four alternatives (CloneFour.v), and
    the proof of the computational observation that no order-3 profile over
    the diamond has a cyclic beat relation. *)
Lemma diamond_no_cyclic_triple :
  forall F1 F2 F3 : D4,
    F1 * F2 ≤ F3 /\ F1 * F2 <> F3 ->
    F2 * F3 ≤ F1 /\ F2 * F3 <> F1 ->
    F3 * F1 ≤ F2 /\ F3 * F1 <> F2 -> False.
Proof.
  intros [| | |] [| | |] [| | |]; unfold Orel; cbn;
    intros [H1a H1b] [H2a H2b] [H3a H3b]; congruence.
Qed.

(** * Reflection machinery: a sound boolean winner checker. *)

Section Reflection.

  (** Boolean equality on the diamond, so that the checkers below reduce under
      [vm_compute]. *)
  Definition Deqb (x y : D4) : bool :=
    match x, y with
    | Dbot, Dbot | Dp, Dp | Dq, Dq | Dtop, Dtop => true
    | _, _ => false
    end.

  (** [Deqb] reflects equality. *)
  Lemma Deqb_eq : forall x y, Deqb x y = true <-> x = y.
  Proof.
    intros [| | |] [| | |]; cbn; split; congruence.
  Qed.

  (** Boolean equality on the three alternatives. *)
  Definition node_eqb (x y : Node) : bool :=
    match x, y with
    | A, A | B, B | C, C => true
    | _, _ => false
    end.

  (** [node_eqb] reflects equality. *)
  Lemma node_eqb_eq : forall x y, node_eqb x y = true <-> x = y.
  Proof.
    intros [| |] [| |]; cbn; split; congruence.
  Qed.

  (** The three alternatives, as a list for the checkers to fold over. *)
  Definition nodes : list Node := [A; B; C].

  (** [nodes] enumerates every alternative, which is what lets a [forallb] over
      it stand for a universal quantifier. *)
  Lemma nodes_complete : forall n : Node, In n nodes.
  Proof. intros [| |]; cbn; auto. Qed.

  (** A matrix tabulated as nine nested pairs, row-major. *)
  Definition T9 : Type :=
    ((((((((D4 * D4) * D4) * D4) * D4) * D4) * D4) * D4) * D4).

  (** The matrix denoted by a table: an entry is selected by its two indices. *)
  Definition mtx (t : T9) : Node -> Node -> D4 :=
    fun x y =>
      let '((((((((aa, ab), ac), ba), bb), bc), ca), cb), cc) := t in
      match x, y with
      | A, A => aa | A, B => ab | A, C => ac
      | B, A => ba | B, B => bb | B, C => bc
      | C, A => ca | C, B => cb | C, C => cc
      end.

  (** The table of a matrix, its nine entries evaluated once.  Inverse to [mtx]
      by [mtx_tableof]. *)
  Definition tableof (M : Node -> Node -> D4) : T9 :=
    ((((((((M A A, M A B), M A C), M B A), M B B), M B C),
        M C A), M C B), M C C).

  (** Tabulating a matrix and reading it back returns the original entries, so
      nothing is lost in passing to the finite representation. *)
  Lemma mtx_tableof : forall (M : Node -> Node -> D4) (x y : Node),
    mtx (tableof M) x y = M x y.
  Proof. intros M [| |] [| |]; reflexivity. Qed.

  (** The four elements of the diamond, as a list. *)
  Definition enumD : list D4 := [Dbot; Dp; Dq; Dtop].

  (** [enumD] enumerates the whole carrier. *)
  Lemma enumD_complete : forall d : D4, In d enumD.
  Proof. intros [| | |]; cbn; auto. Qed.

  (** All 4^9 = 262144 tables, as the ninefold product of [enumD] with itself. *)
  Definition all_tabs : list T9 :=
    list_prod (list_prod (list_prod (list_prod (list_prod (list_prod
      (list_prod (list_prod enumD enumD) enumD) enumD) enumD) enumD)
      enumD) enumD) enumD.

  (** Every matrix over the diamond is tabulated somewhere in [all_tabs].  This
      is the step that turns a claim about all matrices into a claim about a
      finite list. *)
  Lemma tableof_in : forall M : Node -> Node -> D4, In (tableof M) all_tabs.
  Proof.
    intro M. unfold tableof, all_tabs.
    repeat apply in_prod; apply enumD_complete.
  Qed.

  (** The closure of a tabulated matrix, computed once per table. *)
  Definition star9 (t : T9) : T9 :=
    let Mf := mtx t in
    ((((((((mat_star Mf A A, mat_star Mf A B), mat_star Mf A C),
           mat_star Mf B A), mat_star Mf B B), mat_star Mf B C),
           mat_star Mf C A), mat_star Mf C B), mat_star Mf C C).

  (** Reading an entry out of a closure table, by the same layout as [mtx]. *)
  Definition getS (s : T9) (x y : Node) : D4 :=
    let '((((((((aa, ab), ac), ba), bb), bc), ca), cb), cc) := s in
    match x, y with
    | A, A => aa | A, B => ab | A, C => ac
    | B, A => ba | B, B => bb | B, C => bc
    | C, A => ca | C, B => cb | C, C => cc
    end.

  (** [star9] does tabulate the closure. *)
  Lemma getS_star9 : forall (t : T9) (x y : Node),
    getS (star9 t) x y = mat_star (mtx t) x y.
  Proof. intros t [| |] [| |]; reflexivity. Qed.

  (** [a] beats [b], read off a closure table. *)
  Definition beatsb (s : T9) (a b : Node) : bool :=
    andb (Deqb (getS s b a + getS s a b) (getS s a b))
         (negb (Deqb (getS s b a) (getS s a b))).

  (** The boolean beat test agrees with [schulze_beats] on the matrix the table
      denotes: the reflection lemma for a single pair. *)
  Lemma beatsb_correct : forall (t : T9) (a b : Node),
    beatsb (star9 t) a b = true <-> schulze_beats (mtx t) a b.
  Proof.
    intros t a b. unfold beatsb, schulze_beats, beats.
    rewrite !getS_star9.
    rewrite Bool.andb_true_iff, Bool.negb_true_iff.
    split.
    - intros (H1 & H2). split.
      + exact (proj1 (Deqb_eq _ _) H1).
      + intro E. rewrite E in H2.
        rewrite (proj2 (Deqb_eq _ _) eq_refl) in H2. discriminate.
    - intros (H1 & H2). split.
      + exact (proj2 (Deqb_eq _ _) H1).
      + destruct (Deqb (mat_star (mtx t) b a) (mat_star (mtx t) a b)) eqn:E;
          [ exfalso; exact (H2 (proj1 (Deqb_eq _ _) E)) | reflexivity ].
  Qed.

  (** [w] is a winner, read off a closure table: no alternative other than [w]
      beats it. *)
  Definition winnerb (t : T9) (w : Node) : bool :=
    let s := star9 t in
    forallb (fun b => orb (node_eqb b w) (negb (beatsb s b w))) nodes.

  (** [winnerb] is sound for [schulze_winner].  Only soundness is needed, since
      the exhaustive check produces [true] and this lemma turns each [true] into
      a genuine winner. *)
  Lemma winnerb_correct : forall (t : T9) (w : Node),
    winnerb t w = true -> schulze_winner (mtx t) w.
  Proof.
    intros t w Hall b Hbw Hbeat.
    pose proof (proj1 (forallb_forall _ _) Hall b (nodes_complete b)) as Hb.
    cbv beta in Hb.
    destruct (node_eqb b w) eqn:Ebw.
    - exact (Hbw (proj1 (node_eqb_eq _ _) Ebw)).
    - rewrite (proj2 (beatsb_correct t b w) Hbeat) in Hb.
      cbn in Hb. discriminate.
  Qed.

  (** Some alternative is a winner of the tabulated matrix. *)
  Definition has_winnerb (t : T9) : bool :=
    existsb (fun w => winnerb t w) nodes.

  (** Soundness of [has_winnerb]: a positive answer yields an actual winner. *)
  Lemma has_winnerb_correct : forall t : T9,
    has_winnerb t = true -> exists w : Node, schulze_winner (mtx t) w.
  Proof.
    intros t H.
    destruct (proj1 (existsb_exists _ _) H) as (w & _ & Hw).
    exact (ex_intro _ w (winnerb_correct t w Hw)).
  Qed.

  (** Pointwise congruence for the closure, to move between a matrix and
      its tabulation.  [mat_star]'s body is built from [sum], so this is a
      straightforward induction. *)
  Lemma pow_ext (M N : @Matrix Node D4)
    (Hpt : forall x y, M x y = N x y) :
    forall (k : nat) (x y : Node), pow M k x y = pow N k x y.
  Proof.
    induction k as [|k IH]; intros x y.
    - reflexivity.
    - cbn [pow]. unfold matrix_mul. apply sum_ext. intro z.
      rewrite (Hpt x z), (IH z y). reflexivity.
  Qed.

  (** The geometric sum is likewise pointwise. *)
  Lemma geom_sum_ext (M N : @Matrix Node D4)
    (Hpt : forall x y, M x y = N x y) :
    forall (n : nat) (x y : Node), geom_sum M n x y = geom_sum N n x y.
  Proof.
    induction n as [|n IH]; intros x y.
    - reflexivity.
    - cbn [geom_sum]. unfold matrix_add.
      f_equal; [apply IH | apply (pow_ext M N Hpt (S n) x y)].
  Qed.

  (** Hence the closure depends only on a matrix's entries, not on how the
      function computing them is written. *)
  Lemma mat_star_ext (M N : @Matrix Node D4)
    (Hpt : forall x y, M x y = N x y) :
    forall x y, mat_star M x y = mat_star N x y.
  Proof. intros x y. unfold mat_star. apply geom_sum_ext. exact Hpt. Qed.

  (** The beat relation transports along a pointwise equality of matrices. *)
  Lemma schulze_beats_ext (M N : @Matrix Node D4)
    (Hpt : forall x y, M x y = N x y) (a b : Node) :
    schulze_beats M a b -> schulze_beats N a b.
  Proof.
    unfold schulze_beats, beats. intros (Hle & Hne).
    setoid_rewrite <- (mat_star_ext M N Hpt b a).
    setoid_rewrite <- (mat_star_ext M N Hpt a b).
    exact (conj Hle Hne).
  Qed.

  (** So does being a winner. *)
  Lemma schulze_winner_ext (M N : @Matrix Node D4)
    (Hpt : forall x y, M x y = N x y) (w : Node) :
    schulze_winner M w -> schulze_winner N w.
  Proof.
    intros Hw b Hb Hbeat.
    exact (Hw b Hb
             (schulze_beats_ext N M (fun x y => eq_sym (Hpt x y)) b w Hbeat)).
  Qed.

  (** A winner of a concrete matrix, certified by the boolean checker. *)
  Lemma winner_by_vm (M : Node -> Node -> D4) (w : Node) :
    winnerb (tableof M) w = true -> schulze_winner M w.
  Proof.
    intro Hc.
    exact (schulze_winner_ext (mtx (tableof M)) M (mtx_tableof M) w
             (winnerb_correct (tableof M) w Hc)).
  Qed.

End Reflection.

(** The exhaustive check: one vm_compute over all 4^9 = 262144 matrices.
    It is taking too much time though. *)

Lemma diamond_all_tabs_have_winner :
  forallb has_winnerb all_tabs = true.
Proof. vm_compute. reflexivity. Qed.

(** Over the diamond, EVERY profile on three alternatives has a winner —
    even though the diamond is not selective.  This is the machine-checked
    form of "four alternatives are optimal" in the winner-existence
    characterisation: no three-alternative witness can exist over D4. *)
Theorem diamond_every_profile_has_winner :
  forall M : @Matrix Node D4, exists w : Node, schulze_winner M w.
Proof.
  intro M.
  pose proof (proj1 (forallb_forall _ _) diamond_all_tabs_have_winner
                (tableof M) (tableof_in M)) as Hc.
  destruct (has_winnerb_correct _ Hc) as (w & Hw).
  exists w.
  intros b Hbw Hbeat.
  apply (Hw b Hbw).
  exact (schulze_beats_ext M (mtx (tableof M))
           (fun x y => eq_sym (mtx_tableof M x y)) b w Hbeat).
Qed.

(** The order-3 counts over the diamond with diagonal top: exactly 36 of
    the 4096 matrices have an intransitive beat relation, and none has a
    cyclic one. *)

Section Counts.

  (** Six off-diagonal entries; diagonal fixed at top. *)
  Definition T6 : Type := (((((D4 * D4) * D4) * D4) * D4) * D4).

  (** A six-entry table embedded into a nine-entry one by filling the diagonal
      with [Dtop], the reflexive strength. *)
  Definition emb6 (t : T6) : T9 :=
    let '(((((ab, ac), ba), bc), ca), cb) := t in
    ((((((((Dtop, ab), ac), ba), Dtop), bc), ca), cb), Dtop).

  (** All 4^6 = 4096 tables with the diagonal fixed. *)
  Definition all_tabs6 : list T6 :=
    list_prod (list_prod (list_prod (list_prod (list_prod
      enumD enumD) enumD) enumD) enumD) enumD.

  (** The six ordered triples of distinct alternatives, over which transitivity
      and cyclicity are tested. *)
  Definition triples : list (Node * Node * Node) :=
    [(A,B,C); (A,C,B); (B,A,C); (B,C,A); (C,A,B); (C,B,A)].

  (** The beat relation of a table is intransitive: some triple has [a] beating
      [b] and [b] beating [c] without [a] beating [c]. *)
  Definition intransb (t : T9) : bool :=
    let s := star9 t in
    existsb (fun '(a,b,c) =>
      andb (andb (beatsb s a b) (beatsb s b c)) (negb (beatsb s a c)))
      triples.

  (** The beat relation of a table contains a three-cycle. *)
  Definition cycleb (t : T9) : bool :=
    let s := star9 t in
    existsb (fun '(a,b,c) =>
      andb (andb (beatsb s a b) (beatsb s b c)) (beatsb s c a)) triples.

  (** Exactly 36 of the 4096 profiles are intransitive, so intransitivity is
      possible over the diamond, but uncommon. *)
  Lemma diamond_order3_intransitive_count :
    List.length (List.filter (fun t => intransb (emb6 t)) all_tabs6) = 36%nat.
  Proof. vm_compute. reflexivity. Qed.

  (** None of them is cyclic: the computational counterpart of
      [diamond_no_cyclic_triple]. *)
  Lemma diamond_order3_no_cycle :
    forallb (fun t => negb (cycleb (emb6 t))) all_tabs6 = true.
  Proof. vm_compute. reflexivity. Qed.

End Counts.

(** * Part 3: the Level-1 rows of the classification are tight.

    Over the diamond, the hypotheses of the Smith criterion, of Condorcet
    consistency and of the resolution step can all hold while their
    conclusions fail.  Each failure is one concrete 3x3 matrix, and each
    works by the same mechanism: two incomparable path strengths join to
    a value that is no link strength, which selectivity would forbid. *)

Section Level1Tight.

  (** ---- Smith: the threshold hypotheses hold, a winner escapes B1. ---- *)

  Definition Msmith : Node -> Node -> D4 :=
    fun x y =>
      match x, y with
      | A, A => Dtop | A, B => Dbot | A, C => Dp
      | B, A => Dp   | B, B => Dtop | B, C => Dq
      | C, A => Dtop | C, B => Dtop | C, C => Dtop
      end.

  (** The Smith hypotheses hold with Smith set [[C]] and threshold [Dtop]:
      nothing outside reaches [C] at that strength, while [C] reaches everything
      at it.  Yet [B], which lies outside the Smith set, is a winner.
      Selectivity is what would rule this out. *)
  Theorem smith_fails_over_diamond :
    (forall x : Node, In x [C] <-> ~ In x [A; B])
    /\ (exists c : D4,
          (forall a b : Node, In a [C] -> In b [A; B] ->
             Msmith b a ≤ c /\ Msmith b a <> c)
       /\ (forall a b : Node, In a [C] -> In b [A; B] -> c ≤ Msmith a b))
    /\ schulze_winner Msmith B
    /\ ~ In B [C].
  Proof.
    split; [| split; [| split]].
    - intro x. destruct x; cbn; intuition congruence.
    - exists Dtop. split.
      + intros a b Ha Hb.
        destruct Ha as [Ea|[]]; subst a.
        destruct Hb as [Eb|[Eb|[]]]; subst b;
          split; vm_compute; first [reflexivity | discriminate].
      + intros a b Ha Hb.
        destruct Ha as [Ea|[]]; subst a.
        destruct Hb as [Eb|[Eb|[]]]; subst b; vm_compute; reflexivity.
    - apply winner_by_vm. vm_compute. reflexivity.
    - cbn. intuition congruence.
  Qed.

  (** ---- Condorcet: a Condorcet winner satisfying the cross-pair
           condition that still fails to be a strict winner. ---- *)

  Definition Mcond : Node -> Node -> D4 :=
    fun x y =>
      match x, y with
      | A, A => Dtop | A, B => Dtop | A, C => Dtop
      | B, A => Dp   | B, B => Dtop | B, C => Dbot
      | C, A => Dq   | C, B => Dp   | C, C => Dtop
      end.

  (** [A] is a Condorcet winner and meets the cross-pair condition, and is still
      not a strict winner: its closure strength against [C] ties instead of
      dominating. *)
  Theorem condorcet_fails_over_diamond :
    condorcet_winner Mcond A
    /\ (forall Z X : Node, Z <> A -> X <> A -> Z <> X ->
          Mcond Z A ≤ mat_star Mcond A X /\ Mcond Z A <> mat_star Mcond A X)
    /\ ~ strict_winner Mcond A.
  Proof.
    split; [| split].
    - intros X HX. destruct X; try congruence;
        split; vm_compute; first [reflexivity | discriminate].
    - intros Z X HZ HX HZX.
      destruct Z, X; try congruence; split; vm_compute;
        first [reflexivity | discriminate].
    - intro Hs.
      destruct (Hs C ltac:(discriminate)) as (_ & Hne).
      apply Hne. vm_compute. reflexivity.
  Qed.

  (** ---- Resolution step: an untied winner that is not unique. ---- *)

  Definition Muntied : Node -> Node -> D4 :=
    fun x y =>
      match x, y with
      | A, A => Dtop | A, B => Dbot | A, C => Dbot
      | B, A => Dbot | B, B => Dtop | B, C => Dp
      | C, A => Dp   | C, B => Dq   | C, C => Dtop
      end.

  (** [B] is a winner and is untied against every other alternative, which is
      the hypothesis of the resolution step, and yet [C] is a winner too.  Being
      untied does not make a winner unique over the diamond. *)
  Theorem resolution_fails_over_diamond :
    schulze_winner Muntied B
    /\ (forall b : Node, b <> B ->
          mat_star Muntied B b <> mat_star Muntied b B)
    /\ schulze_winner Muntied C
    /\ B <> C.
  Proof.
    split; [| split; [| split]].
    - apply winner_by_vm. vm_compute. reflexivity.
    - intros b Hb. destruct b; [| congruence |]; vm_compute; discriminate.
    - apply winner_by_vm. vm_compute. reflexivity.
    - discriminate.
  Qed.

  (** ---- Smith-IIA (isolation form): every hypothesis of
           [smith_iia_isolate] holds, yet isolating the non-Smith
           alternative changes the beat relation on B1: the beat B > C
           travelled through the outside alternative A, its two routes
           joining to top, and dies with it. ---- *)

  Definition Miia : Node -> Node -> D4 :=
    fun x y =>
      match x, y with
      | A, A => Dtop | A, B => Dbot | A, C => Dp
      | B, A => Dtop | B, B => Dtop | B, C => Dq
      | C, A => Dq   | C, B => Dp   | C, C => Dtop
      end.

  (** Every hypothesis of [smith_iia_isolate] is met and its conclusion fails:
      [B] beats [C] before [A] is isolated and no longer does after. *)
  Theorem smith_iia_fails_over_diamond :
    (forall x : Node, In x [B; C] <-> ~ In x [A])
    /\ (forall a b : Node, In a [B; C] -> In b [A] ->
          Miia b a ≤ Dtop /\ Miia b a <> Dtop)
    /\ ((Dbot : D4) ≤ Dtop /\ Dbot <> Dtop)
    /\ In A [A]
    /\ (forall x y : Node, x <> y -> Dtop ≤ Miia x y + Miia y x)
    /\ In B [B; C] /\ In C [B; C]
    /\ schulze_beats Miia B C
    /\ ~ schulze_beats (isolate Miia A) B C.
  Proof.
    split; [| split; [| split; [| split; [| split; [| split; [| split;
      [| split]]]]]]].
    - intro x. destruct x; cbn; intuition congruence.
    - intros a b Ha Hb.
      destruct Hb as [Eb|[]]; subst b.
      destruct Ha as [Ea|[Ea|[]]]; subst a;
        split; vm_compute; first [reflexivity | discriminate].
    - split; vm_compute; first [reflexivity | discriminate].
    - cbn; auto.
    - intros x y Hxy. destruct x, y; try congruence; vm_compute; reflexivity.
    - cbn; auto.
    - cbn; auto.
    - split; vm_compute; first [reflexivity | discriminate].
    - intros (Hle & _). vm_compute in Hle. discriminate.
  Qed.

  (** ---- Smith-IIA, strong-removal form (Schulze 4.7.6): every
           hypothesis of [smith_iia_isolate_strong] holds, yet isolating
           the strong alternative A changes the beat relation on B2: the
           tie between B and C rested on C's route to B through A, whose
           strength q joined with the direct p to top, and dies with A. ---- *)

  Definition Mstrong : Node -> Node -> D4 :=
    fun x y =>
      match x, y with
      | A, A => Dtop | A, B => Dq   | A, C => Dp
      | B, A => Dp   | B, B => Dtop | B, C => Dtop
      | C, A => Dq   | C, B => Dp   | C, C => Dtop
      end.

  (** Every hypothesis of [smith_iia_isolate_strong] is met and its conclusion
      fails in the opposite direction: [B] does not beat [C] until [A] is
      isolated, and then it does. *)
  Theorem smith_iia_strong_fails_over_diamond :
    (forall x : Node, In x [A] <-> ~ In x [B; C])
    /\ (forall a b : Node, In a [A] -> In b [B; C] ->
          Mstrong b a ≤ Dtop /\ Mstrong b a <> Dtop)
    /\ In A [A]
    /\ (forall x y : Node, x <> y -> Dtop ≤ Mstrong x y + Mstrong y x)
    /\ In B [B; C] /\ In C [B; C]
    /\ ~ schulze_beats Mstrong B C
    /\ schulze_beats (isolate Mstrong A) B C.
  Proof.
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    - intro x. destruct x; cbn; intuition congruence.
    - intros a b Ha Hb.
      destruct Ha as [Ea|[]]; subst a.
      destruct Hb as [Eb|[Eb|[]]]; subst b;
        split; vm_compute; first [reflexivity | discriminate].
    - cbn; auto.
    - intros x y Hxy. destruct x, y; try congruence; vm_compute; reflexivity.
    - cbn; auto.
    - cbn; auto.
    - intros (_ & Hne). apply Hne. vm_compute. reflexivity.
    - split; vm_compute; first [reflexivity | discriminate].
  Qed.

End Level1Tight.

(** * Part 4: the worked beatpath example, machine-checked.

    The introductory example of the semiring reading: over the max-min
    carrier (nat extended with infinity, from Schulze.v, whose zero
    [Left 0] plays the bottom), the profile with direct links
    A -> B at 8, B -> C at 6, and C -> A at 4 has closure

        star = [[top, 8, 6], [4, top, 6], [4, 4, top]],

    so the beat relation is the strict order A > B > C and A is the
    unique winner: the beatpaths break the direct cycle. *)

Section WorkedExample.

  (** The worked profile: direct links [A -> B] at 8, [B -> C] at 6 and [C -> A]
      at 4, every other off-diagonal entry at [Left 0], the bottom of the
      max-min carrier, and the diagonal at [Infinity]. *)
  Definition Mw : Node -> Node -> Schulze.R :=
    fun x y =>
      match x, y with
      | A, A => Schulze.Infinity
      | A, B => Schulze.Left 8
      | A, C => Schulze.Left 0
      | B, A => Schulze.Left 0
      | B, B => Schulze.Infinity
      | B, C => Schulze.Left 6
      | C, A => Schulze.Left 4
      | C, B => Schulze.Left 0
      | C, C => Schulze.Infinity
      end.

  (** The six off-diagonal closure entries, exactly as in the paper. *)
  Theorem worked_example_star :
    mat_star Mw A B = Schulze.Left 8 /\ mat_star Mw A C = Schulze.Left 6 /\
    mat_star Mw B C = Schulze.Left 6 /\ mat_star Mw B A = Schulze.Left 4 /\
    mat_star Mw C A = Schulze.Left 4 /\ mat_star Mw C B = Schulze.Left 4.
  Proof.
    repeat split; vm_compute; reflexivity.
  Qed.

  (** The beat relation is the strict order A > B > C. *)
  Theorem worked_example_order :
    schulze_beats Mw A B /\ schulze_beats Mw A C /\ schulze_beats Mw B C.
  Proof.
    repeat split; vm_compute; first [reflexivity | discriminate].
  Qed.

  (** A is the unique winner. *)
  Theorem worked_example_winner :
    schulze_winner Mw A /\ ~ schulze_winner Mw B /\ ~ schulze_winner Mw C.
  Proof.
    split; [| split].
    - intros b Hb [Hle Hne].
      destruct b; [congruence | vm_compute in Hle; discriminate
                  | vm_compute in Hle; discriminate].
    - intro Hw. apply (Hw A ltac:(discriminate)).
      split; vm_compute; first [reflexivity | discriminate].
    - intro Hw. apply (Hw A ltac:(discriminate)).
      split; vm_compute; first [reflexivity | discriminate].
  Qed.

End WorkedExample.

(** * The four-alternative witness over the diamond.

    This is not a new construction.  It is the alternating square of the
    winner-existence characterisation, [sq_no_winner], instantiated at
    x := Dp and y := Dq.  The two facts that construction needs,
    x * y < y and y * x < x, hold over the diamond because Dp and Dq are
    incomparable and their meet is Dbot.  Together with
    [diamond_every_profile_has_winner] this shows four alternatives are
    both sufficient and necessary to refute winner existence over D4. *)

Inductive Node4 := W1 | W2 | W3 | W4.

(** Decidable equality on the four alternatives, required by [IsFinType]. *)
Definition node4_eq_dec : forall x y : Node4, {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** The four alternatives, in the order the alternating square uses them. *)
Definition elements4 : list Node4 := [W1; W2; W3; W4].

(** The enumeration is duplicate-free. *)
Lemma elements4_nodup : NoDup elements4.
Proof. repeat constructor; cbn; intuition discriminate. Qed.

(** The enumeration is complete. *)
Lemma elements4_complete : forall x : Node4, In x elements4.
Proof. intros [| | |]; cbn; auto. Qed.

(** There are at least two alternatives, which the development assumes
    throughout. *)
Lemma elements4_two_or_more : (2 <= List.length elements4)%nat.
Proof. cbn; lia. Qed.

(** [Node4] is therefore a [FinType], so [mat_star] and the beat relation are
    available on it. *)
HB.instance Definition _ := IsFinType.Build Node4
  elements4 elements4_nodup elements4_complete
  elements4_two_or_more node4_eq_dec.

(** Over the diamond, four alternatives admit a profile with no winner:
    the beat relation is the cycle W1 > W4 > W3 > W2 > W1. *)
Theorem diamond_no_winner_at_four :
  forall w : Node4, ~ schulze_winner (sq_matrix W1 W2 W3 W4 Dp Dq) w.
Proof.
  apply (@sq_no_winner Node4 D4 W1 W2 W3 W4);
    unfold Orel; cbn; first [reflexivity | discriminate].
Qed.
