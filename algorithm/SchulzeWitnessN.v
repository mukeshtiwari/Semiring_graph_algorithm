From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN SchulzeBasicsN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ======================================================================= *)
(*  Schulze over a semiring: the triangle and four-cycle witness matrices *)
(*  Split out of the former monolithic SocialchoiceN.v.                   *)
(* ======================================================================= *)

Section SchulzeWitnessN.

  Context {Node : FinType.type}.


  (* ===================================================================== *)
  (*  Converse of schulze_trans_weaker_necessary.                           *)
  (*                                                                        *)
  (*  Three distinct nodes exist as soon as [elements] has length >= 3,      *)
  (*  because [elements] carries a NoDup proof.  They index the witness      *)
  (*  triangle used throughout the refutation arguments below.               *)
  (* ===================================================================== *)

  Lemma three_distinct_nodes :
    (3 <= List.length (@elements Node))%nat ->
    exists a b c : Node, a <> b /\ b <> c /\ a <> c.
  Proof.
    intro Hlen.
    pose proof (@elements_nodup Node) as Hnd.
    destruct (@elements Node) as [|x [|y [|z t]]] eqn:Hel; cbn in Hlen; try lia.
    inversion Hnd as [|u l Hu Hnd1]; subst.
    inversion Hnd1 as [|u2 l2 Hu2 Hnd2]; subst.
    exists x, y, z. repeat split.
    - intro Hxy; subst; apply Hu; left; reflexivity.
    - intro Hyz; subst; apply Hu2; left; reflexivity.
    - intro Hxz; subst; apply Hu; right; left; reflexivity.
  Qed.


(* =====================================================================  *)
  (*  The witness matrix                                                     *)
  (*                                                                         *)
  (*  A directed triangle [X → Y → Z → X] carrying [p], [q], [r].  [Y] and    *)
  (*  [Z] have a single out-link each, so every path leaving them is forced.  *)
  (*  [X] additionally links to every node OUTSIDE the triangle, also with    *)
  (*  strength [p].  Those nodes are dead ends — their whole row is zero — so *)
  (*  they lie on no path between triangle nodes and do not disturb any of    *)
  (*  the closure bounds.  They must nevertheless be reachable: an isolated   *)
  (*  node is beaten by nobody, hence a Schulze winner, which would make the  *)
  (*  matrix useless for refuting winner existence on more than three         *)
  (*  alternatives.                                                          *)
  (* =====================================================================  *)

  Definition tri_matrix {R : Semiring.type} (X Y Z : Node) (p q r : R)
    : @Matrix Node R :=
    fun i j =>
      if fin_eq_dec i X then
        (if fin_eq_dec j X then 0 else if fin_eq_dec j Z then 0 else p)
      else if fin_eq_dec i Y then (if fin_eq_dec j Z then q else 0)
      else if fin_eq_dec i Z then (if fin_eq_dec j X then r else 0)
      else 0.

  (* [tri_matrix]'s body is a lambda, so all reasoning goes through this
     pointwise equation rather than [unfold]. *)
  Lemma tri_matrix_unfold {R : Semiring.type} (X Y Z : Node) (p q r : R)
    (i j : Node) :
    tri_matrix X Y Z p q r i j =
      if fin_eq_dec i X then
        (if fin_eq_dec j X then 0 else if fin_eq_dec j Z then 0 else p)
      else if fin_eq_dec i Y then (if fin_eq_dec j Z then q else 0)
      else if fin_eq_dec i Z then (if fin_eq_dec j X then r else 0)
      else 0.
  Proof. reflexivity. Qed.

  Section TriangleEntries.

    Context {R : Semiring.type} (X Y Z : Node) (p q r : R).

    (** [X] links with strength [p] to everything except itself and [Z]. *)
    Lemma tri_X_out (w : Node) : w <> X -> w <> Z ->
      tri_matrix X Y Z p q r X w = p.
    Proof.
      intros HwX HwZ. rewrite tri_matrix_unfold.
      destruct (fin_eq_dec X X) as [_|h]; [| congruence].
      destruct (fin_eq_dec w X) as [h|_]; [congruence |].
      destruct (fin_eq_dec w Z) as [h|_]; [congruence | reflexivity].
    Qed.

    Lemma tri_YZ : Y <> X -> tri_matrix X Y Z p q r Y Z = q.
    Proof.
      intro HYX. rewrite tri_matrix_unfold.
      destruct (fin_eq_dec Y X) as [h|_]; [congruence |].
      destruct (fin_eq_dec Y Y) as [_|h]; [| congruence].
      destruct (fin_eq_dec Z Z) as [_|h]; [reflexivity | congruence].
    Qed.

    Lemma tri_ZX : Z <> X -> Z <> Y -> tri_matrix X Y Z p q r Z X = r.
    Proof.
      intros HZX HZY. rewrite tri_matrix_unfold.
      destruct (fin_eq_dec Z X) as [h|_]; [congruence |].
      destruct (fin_eq_dec Z Y) as [h|_]; [congruence |].
      destruct (fin_eq_dec Z Z) as [_|h]; [| congruence].
      destruct (fin_eq_dec X X) as [_|h]; [reflexivity | congruence].
    Qed.

    (** Nodes outside the triangle have no outgoing link at all. *)
    Lemma tri_dead_row (w : Node) : w <> X -> w <> Y -> w <> Z ->
      forall u, tri_matrix X Y Z p q r w u = 0.
    Proof.
      intros HwX HwY HwZ u. rewrite tri_matrix_unfold.
      destruct (fin_eq_dec w X) as [h|_]; [congruence |].
      destruct (fin_eq_dec w Y) as [h|_]; [congruence |].
      destruct (fin_eq_dec w Z) as [h|_]; [congruence | reflexivity].
    Qed.

    Lemma tri_Y_only_Z : Y <> X -> forall w, w <> Z ->
      tri_matrix X Y Z p q r Y w = 0.
    Proof.
      intros HYX w Hw. rewrite tri_matrix_unfold.
      destruct (fin_eq_dec Y X) as [h|_]; [congruence |].
      destruct (fin_eq_dec Y Y) as [_|h]; [| congruence].
      destruct (fin_eq_dec w Z) as [h|_]; [congruence | reflexivity].
    Qed.

    Lemma tri_Z_only_X : Z <> X -> Z <> Y -> forall w, w <> X ->
      tri_matrix X Y Z p q r Z w = 0.
    Proof.
      intros HZX HZY w Hw. rewrite tri_matrix_unfold.
      destruct (fin_eq_dec Z X) as [h|_]; [congruence |].
      destruct (fin_eq_dec Z Y) as [h|_]; [congruence |].
      destruct (fin_eq_dec Z Z) as [_|h]; [| congruence].
      destruct (fin_eq_dec w X) as [h|_]; [congruence | reflexivity].
    Qed.

    (** Leaving [X] you either take the [Y] link or fall into a dead end. *)
    Lemma tri_X_out_or_dead : forall w, w <> Y ->
      tri_matrix X Y Z p q r X w = 0 \/
      (w <> Z /\ forall u, tri_matrix X Y Z p q r w u = 0).
    Proof.
      intros w Hw.
      destruct (fin_eq_dec w X) as [HwX|HwX].
      { left. subst w. rewrite tri_matrix_unfold.
        destruct (fin_eq_dec X X) as [_|h]; [reflexivity | congruence]. }
      destruct (fin_eq_dec w Z) as [HwZ|HwZ].
      { left. subst w. rewrite tri_matrix_unfold.
        destruct (fin_eq_dec X X) as [_|h]; [| congruence].
        destruct (fin_eq_dec Z X) as [h|_]; [congruence |].
        destruct (fin_eq_dec Z Z) as [_|h]; [reflexivity | congruence]. }
      right. split; [exact HwZ | exact (tri_dead_row w HwX Hw HwZ)].
    Qed.

  End TriangleEntries.

  Section TriangleRows.

    Context {R : BoundedSemiring.type} (X Y Z : Node) (p q r : R).

    Lemma tri_row_X : forall w, tri_matrix X Y Z p q r X w ≤ p.
    Proof.
      intro w. rewrite tri_matrix_unfold.
      destruct (fin_eq_dec X X) as [_|h]; [| congruence].
      destruct (fin_eq_dec w X) as [_|_]; [apply zero_is_bottom |].
      destruct (fin_eq_dec w Z) as [_|_];
        [apply zero_is_bottom | apply (@bounded_orel_refl R p)].
    Qed.

    Lemma tri_row_Y : Y <> X -> forall w, tri_matrix X Y Z p q r Y w ≤ q.
    Proof.
      intros HYX w. destruct (fin_eq_dec w Z) as [Heq|Hne].
      - subst w. rewrite (tri_YZ X Y Z p q r HYX). apply (@bounded_orel_refl R q).
      - rewrite (tri_Y_only_Z X Y Z p q r HYX w Hne). apply zero_is_bottom.
    Qed.

    Lemma tri_row_Z : Z <> X -> Z <> Y ->
      forall w, tri_matrix X Y Z p q r Z w ≤ r.
    Proof.
      intros HZX HZY w. destruct (fin_eq_dec w X) as [Heq|Hne].
      - subst w. rewrite (tri_ZX X Y Z p q r HZX HZY).
        apply (@bounded_orel_refl R r).
      - rewrite (tri_Z_only_X X Y Z p q r HZX HZY w Hne). apply zero_is_bottom.
    Qed.

  End TriangleRows.

  Section TriangleClosures.

    Context {R : BoundedSemiring.type} (X Y Z : Node)
      (HXY : X <> Y) (HYZ : Y <> Z) (HXZ : X <> Z) (p q r : R).

    (* Every lemma below is generalised over the whole context, so that all
       of them take the same argument list once the section closes. *)
    Set Default Proof Using "All".

    Let HYX : Y <> X := fun h => HXY (eq_sym h).
    Let HZY : Z <> Y := fun h => HYZ (eq_sym h).
    Let HZX : Z <> X := fun h => HXZ (eq_sym h).

    (** The three reverse closures, each pinned by a forced two-step path. *)
    Lemma tri_star_YX : mat_star (tri_matrix X Y Z p q r) Y X ≤ q * r.
    Proof.
      set (M := tri_matrix X Y Z p q r).
      assert (E : M Y Z = q) by exact (tri_YZ X Y Z p q r HYX).
      rewrite <- E.
      apply (mat_star_two_step M Y Z X r HYX HZX).
      - intros w Hw. left. exact (tri_Y_only_Z X Y Z p q r HYX w Hw).
      - exact (tri_row_Z X Y Z p q r HZX HZY).
    Qed.

    Lemma tri_star_ZY : mat_star (tri_matrix X Y Z p q r) Z Y ≤ r * p.
    Proof.
      set (M := tri_matrix X Y Z p q r).
      assert (E : M Z X = r) by exact (tri_ZX X Y Z p q r HZX HZY).
      rewrite <- E.
      apply (mat_star_two_step M Z X Y p HZY HXY).
      - intros w Hw. left. exact (tri_Z_only_X X Y Z p q r HZX HZY w Hw).
      - exact (tri_row_X X Y Z p q r).
    Qed.

    Lemma tri_star_XZ : mat_star (tri_matrix X Y Z p q r) X Z ≤ p * q.
    Proof.
      set (M := tri_matrix X Y Z p q r).
      assert (E : M X Y = p) by exact (tri_X_out X Y Z p q r Y HYX HYZ).
      rewrite <- E.
      apply (mat_star_two_step M X Y Z q HXZ HYZ).
      - exact (tri_X_out_or_dead X Y Z p q r).
      - exact (tri_row_Y X Y Z p q r HYX).
    Qed.

    (** A dead end reaches nothing. *)
    Lemma tri_star_dead (w v : Node) : w <> X -> w <> Y -> w <> Z -> w <> v ->
      mat_star (tri_matrix X Y Z p q r) w v = 0.
    Proof.
      intros HwX HwY HwZ Hwv.
      apply orel_antisym; [| apply zero_is_bottom].
      apply (mat_star_row_bound (tri_matrix X Y Z p q r) w 0); [| exact Hwv].
      intro u. rewrite (tri_dead_row X Y Z p q r w HwX HwY HwZ u).
      apply (@bounded_orel_refl R 0).
    Qed.

    (** Links are paths of length one, so each forward closure dominates its
        link. *)
    Lemma tri_link_XY : p ≤ mat_star (tri_matrix X Y Z p q r) X Y.
    Proof.
      set (M := tri_matrix X Y Z p q r).
      assert (E : M X Y = p) by exact (tri_X_out X Y Z p q r Y HYX HYZ).
      rewrite <- E. exact (@link_le_mat_star Node R M X Y).
    Qed.

    Lemma tri_link_YZ : q ≤ mat_star (tri_matrix X Y Z p q r) Y Z.
    Proof.
      set (M := tri_matrix X Y Z p q r).
      assert (E : M Y Z = q) by exact (tri_YZ X Y Z p q r HYX).
      rewrite <- E. exact (@link_le_mat_star Node R M Y Z).
    Qed.

    Lemma tri_link_ZX : r ≤ mat_star (tri_matrix X Y Z p q r) Z X.
    Proof.
      set (M := tri_matrix X Y Z p q r).
      assert (E : M Z X = r) by exact (tri_ZX X Y Z p q r HZX HZY).
      rewrite <- E. exact (@link_le_mat_star Node R M Z X).
    Qed.

    Lemma tri_link_Xdead (w : Node) : w <> X -> w <> Z ->
      p ≤ mat_star (tri_matrix X Y Z p q r) X w.
    Proof.
      intros HwX HwZ.
      set (M := tri_matrix X Y Z p q r).
      assert (E : M X w = p) by exact (tri_X_out X Y Z p q r w HwX HwZ).
      rewrite <- E. exact (@link_le_mat_star Node R M X w).
    Qed.

    (** The three edges of the cycle, and the links to the dead ends. *)
    Lemma tri_beats_XY : q * r ≤ p -> q * r <> p ->
      schulze_beats (tri_matrix X Y Z p q r) X Y.
    Proof.
      intros H1 H1'.
      exact (beats_of_bounds _ X Y (q * r) p tri_star_YX tri_link_XY H1 H1').
    Qed.

    Lemma tri_beats_YZ : r * p ≤ q -> r * p <> q ->
      schulze_beats (tri_matrix X Y Z p q r) Y Z.
    Proof.
      intros H2 H2'.
      exact (beats_of_bounds _ Y Z (r * p) q tri_star_ZY tri_link_YZ H2 H2').
    Qed.

    Lemma tri_beats_ZX : p * q ≤ r -> p * q <> r ->
      schulze_beats (tri_matrix X Y Z p q r) Z X.
    Proof.
      intros H3 H3'.
      exact (beats_of_bounds _ Z X (p * q) r tri_star_XZ tri_link_ZX H3 H3').
    Qed.

    Lemma tri_beats_dead (w : Node) : p <> 0 ->
      w <> X -> w <> Y -> w <> Z ->
      schulze_beats (tri_matrix X Y Z p q r) X w.
    Proof.
      intros Hp HwX HwY HwZ.
      apply (beats_of_bounds _ X w 0 p).
      - rewrite (tri_star_dead w X HwX HwY HwZ HwX).
        apply (@bounded_orel_refl R 0).
      - exact (tri_link_Xdead w HwX HwZ).
      - apply zero_is_bottom.
      - intro h. apply Hp. symmetry. exact h.
    Qed.

  End TriangleClosures.

  (** Transitivity over the triangle forces [r] strictly below [p * q]:
      [X] beats [Y] and [Y] beats [Z], so [X] must beat [Z]. *)
  Lemma tri_witness {R : BoundedSemiring.type}
    (X Y Z : Node) (HXY : X <> Y) (HYZ : Y <> Z) (HXZ : X <> Z)
    (p q r : R)
    (H1 : q * r ≤ p) (H1' : q * r <> p)
    (H2 : r * p ≤ q) (H2' : r * p <> q) :
    (forall (M : @Matrix Node R) a b c,
       schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c) ->
    r ≤ p * q /\ r <> p * q.
  Proof.
    intro Htrans.
    pose proof (tri_star_XZ X Y Z HXY HYZ HXZ p q r) as UXZ.
    pose proof (tri_link_ZX X Y Z HXY HYZ HXZ p q r) as LZX.
    destruct (Htrans (tri_matrix X Y Z p q r) X Y Z
                (tri_beats_XY X Y Z HXY HYZ HXZ p q r H1 H1')
                (tri_beats_YZ X Y Z HXY HYZ HXZ p q r H2 H2')) as [BZXle BZXne].
    split.
    - exact (orel_trans _ _ _ LZX (orel_trans _ _ _ BZXle UXZ)).
    - intro Heq. apply BZXne. apply orel_antisym; [exact BZXle |].
      rewrite <- Heq in UXZ. exact (orel_trans _ _ _ UXZ LZX).
  Qed.

  (** A strict cycle of strengths leaves nobody unbeaten: [X], [Y], [Z] beat
      one another round the triangle, and [X] beats every remaining node. *)
  Lemma tri_no_winner {R : BoundedSemiring.type}
    (X Y Z : Node) (HXY : X <> Y) (HYZ : Y <> Z) (HXZ : X <> Z)
    (p q r : R) (Hp : p <> 0)
    (H1 : q * r ≤ p) (H1' : q * r <> p)
    (H2 : r * p ≤ q) (H2' : r * p <> q)
    (H3 : p * q ≤ r) (H3' : p * q <> r) :
    forall w : Node, ~ schulze_winner (tri_matrix X Y Z p q r) w.
  Proof.
    intros w Hw.
    destruct (fin_eq_dec w X) as [->|HwX].
    { exact (Hw Z (fun h => HXZ (eq_sym h))
               (tri_beats_ZX X Y Z HXY HYZ HXZ p q r H3 H3')). }
    destruct (fin_eq_dec w Y) as [->|HwY].
    { exact (Hw X HXY (tri_beats_XY X Y Z HXY HYZ HXZ p q r H1 H1')). }
    destruct (fin_eq_dec w Z) as [->|HwZ].
    { exact (Hw Y HYZ (tri_beats_YZ X Y Z HXY HYZ HXZ p q r H2 H2')). }
    exact (Hw X (fun h => HwX (eq_sym h))
             (tri_beats_dead X Y Z HXY HYZ HXZ p q r w Hp HwX HwY HwZ)).
  Qed.

  (* ===================================================================== *)
  (*  A four-cycle witness, for the selectivity half of winner existence.   *)
  (*                                                                        *)
  (*  The three-cycle of [tri_matrix] cannot refute winner existence from    *)
  (*  non-selectivity: with incomparable x, y the only natural choice of      *)
  (*  third weight is x * y, and the third edge then compares x * y against  *)
  (*  itself, a tie rather than a strict victory.  A four-cycle with          *)
  (*  ALTERNATING weights avoids this.  On distinct A, B, C, D carry          *)
  (*                                                                        *)
  (*      A -> D = y,  D -> C = x,  C -> B = y,  B -> A = x,                 *)
  (*                                                                        *)
  (*  with C additionally linked to every node outside {A,B,C,D} at strength *)
  (*  y (those are dead ends, so they carry no path and are beaten by C).     *)
  (*  Each node of the cycle has a single out-edge into the cycle, so every   *)
  (*  reverse closure is pinned by one two-step bound, and the alternation    *)
  (*  makes all four bounds instances of just x * y < y and y * x < x.        *)
  (* ===================================================================== *)

  Definition sq_matrix {R : Semiring.type} (A B C D : Node) (x y : R)
    : @Matrix Node R :=
    fun i j =>
      if fin_eq_dec i A then (if fin_eq_dec j D then y else 0)
      else if fin_eq_dec i B then (if fin_eq_dec j A then x else 0)
      else if fin_eq_dec i C then
        (if fin_eq_dec j A then 0
         else if fin_eq_dec j C then 0
         else if fin_eq_dec j D then 0 else y)
      else if fin_eq_dec i D then (if fin_eq_dec j C then x else 0)
      else 0.

  Lemma sq_matrix_unfold {R : Semiring.type} (A B C D : Node) (x y : R) (i j : Node) :
    sq_matrix A B C D x y i j =
      if fin_eq_dec i A then (if fin_eq_dec j D then y else 0)
      else if fin_eq_dec i B then (if fin_eq_dec j A then x else 0)
      else if fin_eq_dec i C then
        (if fin_eq_dec j A then 0
         else if fin_eq_dec j C then 0
         else if fin_eq_dec j D then 0 else y)
      else if fin_eq_dec i D then (if fin_eq_dec j C then x else 0)
      else 0.
  Proof. reflexivity. Qed.

  Section Square.

    Context {R : BoundedSemiring.type} (A B C D : Node)
      (HAB : A <> B) (HAC : A <> C) (HAD : A <> D)
      (HBC : B <> C) (HBD : B <> D) (HCD : C <> D)
      (x y : R).

    Set Default Proof Using "All".

    Local Notation W := (sq_matrix A B C D x y).

    Ltac sqcase := rewrite sq_matrix_unfold;
      repeat (match goal with
              | |- context [fin_eq_dec ?u ?v] =>
                  destruct (fin_eq_dec u v); try congruence
              end); try reflexivity.

    (* the four carried cycle edges *)
    Lemma sq_AD : W A D = y.  Proof. sqcase. Qed.
    Lemma sq_BA : W B A = x.  Proof. sqcase. Qed.
    Lemma sq_CB : W C B = y.  Proof. sqcase. Qed.
    Lemma sq_DC : W D C = x.  Proof. sqcase. Qed.

    (* rows: each node's out-edges are bounded by its single cycle weight *)
    Lemma sq_row_A : forall w, W A w ≤ y.
    Proof. intro w. sqcase; [apply (@bounded_orel_refl R y) | apply zero_is_bottom]. Qed.

    Lemma sq_row_B : forall w, W B w ≤ x.
    Proof. intro w. sqcase; [apply (@bounded_orel_refl R x) | apply zero_is_bottom]. Qed.

    Lemma sq_row_C : forall w, W C w ≤ y.
    Proof.
      intro w. sqcase;
        try apply zero_is_bottom; apply (@bounded_orel_refl R y).
    Qed.

    Lemma sq_row_D : forall w, W D w ≤ x.
    Proof. intro w. sqcase; [apply (@bounded_orel_refl R x) | apply zero_is_bottom]. Qed.

    (* A, B, D have a single out-edge; C also links to dead ends *)
    Lemma sq_A_only_D : forall w, w <> D -> W A w = 0.
    Proof. intros w Hw. sqcase. Qed.

    Lemma sq_B_only_A : forall w, w <> A -> W B w = 0.
    Proof. intros w Hw. sqcase. Qed.

    Lemma sq_D_only_C : forall w, w <> C -> W D w = 0.
    Proof. intros w Hw. sqcase. Qed.

    Lemma sq_dead_row : forall w, w <> A -> w <> B -> w <> C -> w <> D ->
      forall u, W w u = 0.
    Proof. intros w H1 H2 H3 H4 u. sqcase. Qed.

    (* C's out-edges are B and the dead ends outside the square *)
    Lemma sq_C_out : forall w, w <> B ->
      W C w = 0 \/ (w <> D /\ forall u, W w u = 0).
    Proof.
      intros w Hw.
      destruct (fin_eq_dec w A) as [->|HwA]; [left; sqcase |].
      destruct (fin_eq_dec w C) as [->|HwC]; [left; sqcase |].
      destruct (fin_eq_dec w D) as [->|HwD]; [left; sqcase |].
      right. split; [exact HwD | exact (sq_dead_row w HwA Hw HwC HwD)].
    Qed.

    (* the four reverse closures *)
    Lemma sq_star_DA : mat_star W D A ≤ x * y.
    Proof.
      pose proof (mat_star_two_step W D C A y
                    (fun h => HAD (eq_sym h)) (fun h => HAC (eq_sym h))
                    (fun w Hw => or_introl (sq_D_only_C w Hw)) sq_row_C) as H.
      rewrite sq_DC in H. exact H.
    Qed.

    Lemma sq_star_CD : mat_star W C D ≤ y * x.
    Proof.
      pose proof (mat_star_two_step W C B D x HCD HBD sq_C_out sq_row_B) as H.
      rewrite sq_CB in H. exact H.
    Qed.

    Lemma sq_star_BC : mat_star W B C ≤ x * y.
    Proof.
      pose proof (mat_star_two_step W B A C y HBC HAC
                    (fun w Hw => or_introl (sq_B_only_A w Hw)) sq_row_A) as H.
      rewrite sq_BA in H. exact H.
    Qed.

    Lemma sq_star_AB : mat_star W A B ≤ y * x.
    Proof.
      pose proof (mat_star_two_step W A D B x HAB (fun h => HBD (eq_sym h))
                    (fun w Hw => or_introl (sq_A_only_D w Hw)) sq_row_D) as H.
      rewrite sq_AD in H. exact H.
    Qed.

    (* forward links *)
    Lemma sq_link_AD : y ≤ mat_star W A D.
    Proof. pose proof (@link_le_mat_star Node R W A D) as H. rewrite sq_AD in H. exact H. Qed.
    Lemma sq_link_DC : x ≤ mat_star W D C.
    Proof. pose proof (@link_le_mat_star Node R W D C) as H. rewrite sq_DC in H. exact H. Qed.
    Lemma sq_link_CB : y ≤ mat_star W C B.
    Proof. pose proof (@link_le_mat_star Node R W C B) as H. rewrite sq_CB in H. exact H. Qed.
    Lemma sq_link_BA : x ≤ mat_star W B A.
    Proof. pose proof (@link_le_mat_star Node R W B A) as H. rewrite sq_BA in H. exact H. Qed.

    (* the four victories, from just  x*y < y  and  y*x < x *)
    Lemma sq_beats_AD : x * y ≤ y -> x * y <> y -> schulze_beats W A D.
    Proof. intros H H'. exact (beats_of_bounds W A D (x*y) y sq_star_DA sq_link_AD H H'). Qed.
    Lemma sq_beats_DC : y * x ≤ x -> y * x <> x -> schulze_beats W D C.
    Proof. intros H H'. exact (beats_of_bounds W D C (y*x) x sq_star_CD sq_link_DC H H'). Qed.
    Lemma sq_beats_CB : x * y ≤ y -> x * y <> y -> schulze_beats W C B.
    Proof. intros H H'. exact (beats_of_bounds W C B (x*y) y sq_star_BC sq_link_CB H H'). Qed.
    Lemma sq_beats_BA : y * x ≤ x -> y * x <> x -> schulze_beats W B A.
    Proof. intros H H'. exact (beats_of_bounds W B A (y*x) x sq_star_AB sq_link_BA H H'). Qed.

    (* C beats every node outside the square *)
    Lemma sq_beats_dead (w : Node) : y <> 0 ->
      w <> A -> w <> B -> w <> C -> w <> D -> schulze_beats W C w.
    Proof.
      intros Hy HwA HwB HwC HwD.
      assert (Ecw : W C w = y) by sqcase.
      apply (beats_of_bounds W C w 0 y).
      - apply (mat_star_row_bound W w 0 C); [| exact HwC].
        intro u. rewrite (sq_dead_row w HwA HwB HwC HwD u).
        apply (@bounded_orel_refl R 0).
      - pose proof (@link_le_mat_star Node R W C w) as H. rewrite Ecw in H. exact H.
      - apply zero_is_bottom.
      - intro h. apply Hy. symmetry. exact h.
    Qed.

    Lemma sq_no_winner : y <> 0 ->
      x * y ≤ y -> x * y <> y -> y * x ≤ x -> y * x <> x ->
      forall w : Node, ~ schulze_winner W w.
    Proof.
      intros Hy H1 H1' H2 H2' w Hw.
      destruct (fin_eq_dec w A) as [->|HwA].
      { exact (Hw B (fun h => HAB (eq_sym h)) (sq_beats_BA H2 H2')). }
      destruct (fin_eq_dec w B) as [->|HwB].
      { exact (Hw C (fun h => HBC (eq_sym h)) (sq_beats_CB H1 H1')). }
      destruct (fin_eq_dec w C) as [->|HwC].
      { exact (Hw D (fun h => HCD (eq_sym h)) (sq_beats_DC H2 H2')). }
      destruct (fin_eq_dec w D) as [->|HwD].
      { exact (Hw A HAD (sq_beats_AD H1 H1')). }
      exact (Hw C (fun h => HwC (eq_sym h))
               (sq_beats_dead w Hy HwA HwB HwC HwD)).
    Qed.

  End Square.

  Lemma four_distinct_nodes :
    (4 <= List.length (@elements Node))%nat ->
    exists A B C D : Node,
      A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D /\ C <> D.
  Proof.
    intro Hlen.
    pose proof (@elements_nodup Node) as Hnd.
    destruct (@elements Node) as [|p [|q [|r [|s t]]]] eqn:Hel;
      cbn in Hlen; try lia.
    inversion Hnd as [|u0 l0 H0 Hnd1]; subst.
    inversion Hnd1 as [|u1 l1 H1 Hnd2]; subst.
    inversion Hnd2 as [|u2 l2 H2 Hnd3]; subst.
    exists p, q, r, s. repeat split.
    - intro h; subst; apply H0; left; reflexivity.
    - intro h; subst; apply H0; right; left; reflexivity.
    - intro h; subst; apply H0; right; right; left; reflexivity.
    - intro h; subst; apply H1; left; reflexivity.
    - intro h; subst; apply H1; right; left; reflexivity.
    - intro h; subst; apply H2; left; reflexivity.
  Qed.

End SchulzeWitnessN.
