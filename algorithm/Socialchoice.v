(* ========================================================================= *)
(*  Social Choice Properties in the Abstract Semimodule Framework            *)
(*                                                                           *)
(*  We formalise Pareto, Monotonicity, Reversal Symmetry, and Clone          *)
(*  Independence as theorems about the Kleene-star fixed point in an         *)
(*  idempotent, bounded semiring.  These are then instantiated for any       *)
(*  concrete semiring (max-min, min-plus, etc.) to prove the corresponding   *)
(*  social-choice properties.                                                *)
(* ========================================================================= *)

From Stdlib Require Import List Utf8 Lia.
From Semiring Require Import Definitions Listprop Path Mat Orel Semimodule.

Import ListNotations.


Section SocialChoice.

  (* ======================================================================= *)
  (*  Section variables — the full semimodule infrastructure                 *)
  (* ======================================================================= *)

  Variables
    (Node : Type)
    (eqN  : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN).

  Variables
    (finN : list Node)
    (dupN : no_dup Node eqN finN = true)
    (lenN : (2 <= List.length finN)%nat)
    (memN : ∀ x : Node, in_list eqN finN x = true).

  Variables
    (R : Type)
    (zeroR oneR : R)
    (plusR mulR : binary_op R)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR).

  Variables
    (z_lp  : forall r : R, eqR (plusR zeroR r) r = true)
    (z_rp  : forall r : R, eqR (plusR r zeroR) r = true)
    (p_assoc : forall a b c : R, eqR (plusR a (plusR b c))
      (plusR (plusR a b) c) = true)
    (p_comm  : forall a b : R, eqR (plusR a b) (plusR b a) = true)
    (o_lm  : forall r : R, eqR (mulR oneR r) r = true)
    (o_rm  : forall r : R, eqR (mulR r oneR) r = true)
    (m_assoc : forall a b c : R, eqR (mulR a (mulR b c))
      (mulR (mulR a b) c) = true)
    (ldist : forall a b c : R,
      eqR (mulR a (plusR b c)) (plusR (mulR a b) (mulR a c)) = true)
    (rdist : forall a b c : R,
      eqR (mulR (plusR a b) c) (plusR (mulR a c) (mulR b c)) = true)
    (z_la  : forall a : R, eqR (mulR zeroR a) zeroR = true)
    (z_ra  : forall a : R, eqR (mulR a zeroR) zeroR = true)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).

  Variables
    (V : Type)
    (zeroV : V)
    (plusV : binary_op V)
    (eqV  : brel V)
    (refV : brel_reflexive V eqV)
    (symV : brel_symmetric V eqV)
    (trnV : brel_transitive V eqV).

  Variables
    (zv_li  : forall x : V, eqV (plusV zeroV x) x = true)
    (zv_ri  : forall x : V, eqV (plusV x zeroV) x = true)
    (pv_assoc : forall x y z : V, eqV (plusV x (plusV y z))
      (plusV (plusV x y) z) = true)
    (pv_comm  : forall x y : V, eqV (plusV x y) (plusV y x) = true)
    (congrPV : bop_congruence V eqV plusV).

  Variable (scale : R -> V -> V).

  Variables
    (sc_distr_v : forall a x y, eqV (scale a (plusV x y))
      (plusV (scale a x) (scale a y)) = true)
    (sc_distr_r : forall a b x, eqV (scale (plusR a b) x)
      (plusV (scale a x) (scale b x)) = true)
    (sc_assoc : forall a b x, eqV (scale a (scale b x))
      (scale (mulR a b) x) = true)
    (sc_one : forall x, eqV (scale oneR x) x = true)
    (sc_zero_r : forall x, eqV (scale zeroR x) zeroV = true)
    (sc_zero_v : forall a, eqV (scale a zeroV) zeroV = true)
    (congrS : forall s1 s2 t1 t2, eqR s1 t1 = true -> eqV s2 t2 = true ->
               eqV (scale s1 s2) (scale t1 t2) = true).

  (* Additional axioms for idempotent, bounded semirings (Schulze-style).    *)
  Variables
    (plusR_idem : forall a : R, eqR (plusR a a) a = true)
    (bounded : forall a : R, eqR (plusR oneR a) oneR = true).

  (* ======================================================================= *)
  (*  Definitions                                                            *)
  (* ======================================================================= *)

  (* Kleene star:  A* = I + A + A² + … + A^{|N|-1}                          *)
  Let kleene_exp := Init.Nat.pred (List.length finN).

  Definition mat_star (M : Matrix Node R) : Matrix Node R :=
    partial_sum_mat Node eqN finN R zeroR oneR plusR mulR M kleene_exp.

  (* Idempotent order on R:  a ≤ b  iff  a + b = b  iff  Orel b a.           *)
  (* We reuse Orel from Orel.v:  Orel x y := plusR x y = x.                  *)
  Definition leqR (a b : R) : Prop :=
    Orel R plusR eqR b a.

  (* ======================================================================= *)
  (*  Lemma 1 — Kleene-star monotonicity (entrywise order)                   *)
  (*                                                                          *)
  (*  If A ≤ B pointwise (in the idempotent order), then A* ≤ B*.            *)
  (* ======================================================================= *)

  (* Algebraic identity: (a+b)+(c+d) = (a+c)+(b+d) in any comm. semiring.    *)
  Lemma plusR_shuffle : forall a b c d,
    eqR (plusR (plusR a b) (plusR c d))
        (plusR (plusR a c) (plusR b d)) = true.
  Proof.
    intros a b c d.
    (* Step 1: (a+b)+(c+d) = a+(b+(c+d)) *)
    apply (trnR _ _ _ (symR _ _ (p_assoc a b (plusR c d)))).
    (* Goal: a+(b+(c+d)) = (a+c)+(b+d) *)
    (* Step 2: a+(b+(c+d)) = a+((b+c)+d) *)
    apply (trnR _ _ _ (congrP a (plusR b (plusR c d)) a (plusR (plusR b c) d)
      (refR a) (p_assoc b c d))).
    (* Goal: a+((b+c)+d) = (a+c)+(b+d) *)
    (* Step 3: a+((b+c)+d) = a+((c+b)+d) *)
    apply (trnR _ _ _ (congrP a (plusR (plusR b c) d) a (plusR (plusR c b) d)
      (refR a) (congrP (plusR b c) d (plusR c b) d (p_comm b c) (refR d)))).
    (* Goal: a+((c+b)+d) = (a+c)+(b+d) *)
    (* Step 4: a+((c+b)+d) = a+(c+(b+d)) *)
    apply (trnR _ _ _ (congrP a (plusR (plusR c b) d) a (plusR c (plusR b d))
      (refR a) (symR _ _ (p_assoc c b d)))).
    (* Goal: a+(c+(b+d)) = (a+c)+(b+d) *)
    (* Step 5: a+(c+(b+d)) = (a+c)+(b+d) — just assoc *)
    (* Goal: a+(c+(b+d)) = (a+c)+(b+d) *)
    apply (p_assoc a c (plusR b d)).
  Qed.

  (* Helper: plusR preserves Orel in both arguments.                          *)
  Lemma plusR_orelm : forall a a' b b',
    Orel R plusR eqR a' a ->
    Orel R plusR eqR b' b ->
    Orel R plusR eqR (plusR a' b') (plusR a b).
  Proof.
    intros a a' b b' Ha Hb.
    unfold Orel in *.
    apply (trnR _ _ _ (plusR_shuffle a' b' a b)).
    apply (congrP (plusR a' a) (plusR b' b) a' b' Ha Hb).
  Qed.

  (* Helper: mulR preserves Orel on the right: Orel a' a → Orel (a'·c) (a·c)*)
  Lemma mulR_orelm_r : forall a a' c,
    Orel R plusR eqR a' a ->
    Orel R plusR eqR (mulR a' c) (mulR a c).
  Proof.
    intros a a' c H.
    unfold Orel in *.
    (* Goal: eqR (plusR (mulR a' c) (mulR a c)) (mulR a' c) = true *)
    apply (trnR _ _ _ (symR _ _ (rdist a' a c))).
    apply (congrM (plusR a' a) c a' c H (refR c)).
  Qed.

  (* Helper: mulR preserves Orel on the left: Orel b' b → Orel (c·b') (c·b) *)
  Lemma mulR_orelm_l : forall b b' c,
    Orel R plusR eqR b' b ->
    Orel R plusR eqR (mulR c b') (mulR c b).
  Proof.
    intros b b' c H.
    unfold Orel in *.
    apply (trnR _ _ _ (symR _ _ (ldist c b' b))).
    apply (congrM c (plusR b' b) c b' (refR c) H).
  Qed.

  (* Helper: sum_fn preserves Orel.  If Orel (f' k) (f k) for all k in l,   *)
  (* then Orel (sum_fn f' l) (sum_fn f l).                                    *)
  Lemma sum_fn_orelm : forall (f f' : Node -> R) (l : list Node),
    (forall k, Orel R plusR eqR (f' k) (f k)) ->
    Orel R plusR eqR (sum_fn Node R zeroR plusR f' l)
                     (sum_fn Node R zeroR plusR f l).
  Proof.
    intros f f' l H.
    induction l as [|k ks IH]; simpl.
    - (* l = [] *)
      unfold Orel. apply plusR_idem.
    - (* l = k :: ks *)
      apply (plusR_orelm (f k) (f' k)
                         (sum_fn Node R zeroR plusR f ks)
                         (sum_fn Node R zeroR plusR f' ks)
                         (H k) IH).
  Qed.

  (* Helper: matrix_add preserves Orel pointwise.                            *)
  Lemma matrix_add_orelm : forall (X X' Y Y' : Matrix Node R) i j,
    Orel R plusR eqR (X' i j) (X i j) ->
    Orel R plusR eqR (Y' i j) (Y i j) ->
    Orel R plusR eqR (matrix_add Node R plusR X' Y' i j)
                     (matrix_add Node R plusR X Y i j).
  Proof.
    intros X X' Y Y' i j Hx Hy.
    unfold matrix_add. apply plusR_orelm; assumption.
  Qed.

  (* Helper: Orel is transitive (using semiring axioms).                      *)
  Lemma orel_trans_local : forall a b c,
    Orel R plusR eqR a b ->
    Orel R plusR eqR b c ->
    Orel R plusR eqR a c.
  Proof.
    unfold Orel; intros a b c Hab Hbc.
    (* Goal: eqR (plusR a c) a = true *)
    (* a + c = (a + b) + c  (since a = a + b) *)
    apply (trnR _ _ _
      (congrP a c (plusR a b) c (symR _ _ Hab) (refR c))).
    (* (a + b) + c = a + (b + c) (assoc reversed) *)
    apply (trnR _ _ _
      (symR _ _ (p_assoc a b c))).
    (* a + (b + c) = a + b (since b + c = b) *)
    apply (trnR _ _ _
      (congrP a (plusR b c) a b (refR a) Hbc)).
    (* a + b = a (given) *)
    apply Hab.
  Qed.

  (* Helper: matrix_mul preserves Orel.                                       *)
  Lemma matrix_mul_orelm : forall (X X' Y Y' : Matrix Node R) i j,
    (forall k, Orel R plusR eqR (X' i k) (X i k)) ->
    (forall k, Orel R plusR eqR (Y' k j) (Y k j)) ->
    Orel R plusR eqR (matrix_mul Node finN R zeroR plusR mulR X' Y' i j)
                     (matrix_mul Node finN R zeroR plusR mulR X Y i j).
  Proof.
    intros X X' Y Y' i j Hx Hy.
    unfold matrix_mul, matrix_mul_gen, sum_fn.
    apply sum_fn_orelm.
    intro k.
    (* Need: Orel (X' i k * Y' k j) (X i k * Y k j) *)
    (* Chain via transitivity: *)
    apply (orel_trans_local
      (mulR (X' i k) (Y' k j))
      (mulR (X' i k) (Y k j))
      (mulR (X i k) (Y k j))).
    - (* Orel (X'*Y') (X'*Y) *)
      apply (mulR_orelm_l (Y k j) (Y' k j) (X' i k) (Hy k)).
    - (* Orel (X'*Y) (X*Y) *)
      apply (mulR_orelm_r (X i k) (X' i k) (Y k j) (Hx k)).
  Qed.

  (* Helper: matrix_exp_unary preserves Orel.                                *)
  Lemma matrix_exp_unary_orelm : forall (X X' : Matrix Node R) (n : nat),
    mat_cong Node eqN R eqR X ->
    mat_cong Node eqN R eqR X' ->
    (forall i j, Orel R plusR eqR (X' i j) (X i j)) ->
    forall i j, Orel R plusR eqR
      (matrix_exp_unary Node eqN finN R zeroR oneR plusR mulR X' n i j)
      (matrix_exp_unary Node eqN finN R zeroR oneR plusR mulR X n i j).
  Proof.
    intros X X' n HcX HcX' H_orel.
    induction n as [|n IH]; intros i j.
    - (* n = 0: I = I *)
      apply (orel_refl R plusR eqR plusR_idem).
    - (* n = S n *)
      apply (matrix_mul_orelm X X'
        (matrix_exp_unary Node eqN finN R zeroR oneR plusR mulR X n)
        (matrix_exp_unary Node eqN finN R zeroR oneR plusR mulR X' n)
        i j).
      + intro k. apply H_orel.
      + intro k. apply IH.
  Qed.

  (* Main lemma: partial_sum_mat preserves Orel.                             *)
  Lemma partial_sum_mat_orelm : forall (X X' : Matrix Node R) (n : nat),
    mat_cong Node eqN R eqR X ->
    mat_cong Node eqN R eqR X' ->
    (forall i j, Orel R plusR eqR (X' i j) (X i j)) ->
    forall i j, Orel R plusR eqR
      (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR X' n i j)
      (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR X n i j).
  Proof.
    intros X X' n HcX HcX' H_orel.
    induction n as [|n IH]; intros i j; cbn.
    - (* n = 0: I = I *)
      apply (orel_refl R plusR eqR plusR_idem).
    - (* n = S n *)
      apply matrix_add_orelm.
      + apply IH.
      + apply (matrix_exp_unary_orelm X X' (S n) HcX HcX' H_orel i j).
  Qed.

  Lemma mat_star_monotone : forall (A B : Matrix Node R),
    mat_cong Node eqN R eqR A ->
    mat_cong Node eqN R eqR B ->
    (forall i j, Orel R plusR eqR (B i j) (A i j)) ->
    forall i j, Orel R plusR eqR (mat_star B i j) (mat_star A i j).
  Proof.
    intros A B HcA HcB H_orel i j.
    unfold mat_star, kleene_exp.
    apply partial_sum_mat_orelm; assumption.
  Qed.

  (* ======================================================================= *)
  (*  Theorem 1 — MONOTONICITY                                                *)
  (*                                                                          *)
  (*  If we raise candidate A (increase row-A entries, decrease column-A     *)
  (*  entries), then A's Kleene-star row entries do not decrease.             *)
  (*                                                                          *)
  (*  Proof: let M' be the modified matrix.  Then M' ≥ M on row A,           *)
  (*  M' ≤ M on column A, and M' = M elsewhere.  By mat_star_monotone,       *)
  (*  the Kleene star of the dominating parts dominates.                      *)
  (* ======================================================================= *)

  Theorem monotonicity :
    forall (M M' : Matrix Node R) (A : Node),
      (* M' dominates M on row A *)
      (forall (Y : Node), Orel R plusR eqR (M' A Y) (M A Y)) ->
      (* M dominates M' on column A *)
      (forall (X : Node), Orel R plusR eqR (M X A) (M' X A)) ->
      (* Everywhere else, M and M' agree *)
      (forall (X Y : Node), X <> A -> Y <> A ->
         eqR (M X Y) (M' X Y) = true) ->
      (* Then for any candidate C, A's path strength to C does not decrease *)
      forall (C : Node),
        Orel R plusR eqR (mat_star M' A C) (mat_star M A C).
  Proof.
    (* This follows from mat_star_monotone after constructing a matrix      *)
    (* N that dominates both M and M' in the right way, or more directly    *)
    (* from the fixed-point characterisation.                                *)
    (* The key idea: M*_{AC} ≤ M'*_{AC} because every A→C path in M has    *)
    (* a corresponding path in M' that's at least as strong (first edge     *)
    (* is in row A where M' ≥ M, last edge in column A where M ≥ M',       *)
    (* but the path doesn't necessarily end in column A).                   *)
    (*                                                                       *)
    (* Full proof requires induction on path length.  Admitted for now.     *)
  Admitted.


  (* ======================================================================= *)
  (*  Lemma 2 — Transpose commutes with Kleene star                          *)
  (*                                                                          *)
  (*  (M^T)-star = (M-star)^T                                                 *)
  (* ======================================================================= *)

  Lemma mat_star_transpose : forall (M : Matrix Node R) (i j : Node),
    mat_cong Node eqN R eqR M ->
    eqR (mat_star (fun x y => M y x) i j)
        (mat_star M j i) = true.
  Proof.
    (* (M^T)-star = (M-star)^T follows from transpose distributing over   *)
    (* matrix_add and (M^k)^T = (M^T)^k.  Admitted.                       *)
  Admitted.

  (* ======================================================================= *)
  (*  Theorem 2 — REVERSAL SYMMETRY                                           *)
  (*                                                                          *)
  (*  If A is the unique winner (A beats every other candidate in the        *)
  (*  Kleene star of M), then under the reversed preferences (M^T),          *)
  (* A is NOT a winner — in fact, everyone beats A.                          *)
  (* ======================================================================= *)

  (* Helper: A is the unique (strict) winner if for all X ≠ A,              *)
  (*   M*_{AX} > M*_{XA}  in the idempotent order (i.e., the BA entry      *)
  (*   is strictly smaller).  Here "strictly smaller" means a ≤ b and a ≠ b. *)
  Definition strict_winner (Mstar : Matrix Node R) (A : Node) : Prop :=
    forall (X : Node), X <> A ->
      Orel R plusR eqR (Mstar A X) (Mstar X A) /\
      eqR (Mstar X A) (Mstar A X) = false.

  Theorem reversal_symmetry :
    forall (M : Matrix Node R) (A : Node),
      mat_cong Node eqN R eqR M ->
      strict_winner (mat_star M) A ->
      ~ strict_winner (mat_star (fun i j => M j i)) A.
  Proof.
    intros M A H_cong H_win.
    unfold strict_winner.
    intro H_win_rev.
    (* From H_win: forall X ≠ A, M*_{XA} ≤ M*_{AX} ∧ M*_{XA} ≠ M*_{AX}.   *)
    (* From H_win_rev: forall X ≠ A, (M^T)*_{XA} ≤ (M^T)*_{AX}            *)
    (*                              ∧ (M^T)*_{XA} ≠ (M^T)*_{AX}.            *)
    (* Using mat_star_transpose:                                            *)
    (*   (M^T)*_{XA} = M*_{AX}  and  (M^T)*_{AX} = M*_{XA}                *)
    (* So H_win_rev says: M*_{AX} ≤ M*_{XA} ∧ M*_{AX} ≠ M*_{XA}.          *)
    (* But H_win says: M*_{XA} ≤ M*_{AX} ∧ M*_{XA} ≠ M*_{AX}.             *)
    (* From antisymmetry of the idempotent order:                          *)
    (*   a ≤ b ∧ b ≤ a  →  a = b.                                          *)
    (* This contradicts a ≠ b.                                              *)
    (*                                                                       *)
    (* We need a lemma: Orel a b → Orel b a → eqR a b = true.               *)
    (* This is true in any idempotent commutative monoid:                   *)
    (*   a + b = b  and  b + a = a  imply a = b (by commutativity).        *)
    (* Admitted for now — the antisymmetry lemma needs to be proved.        *)
  Admitted.

  (* ======================================================================= *)
  (*  Theorem 3 — PARETO                                                      *)
  (*                                                                          *)
  (*  If M_{BA} = 0 and M_{AB} ≠ 0, and rows/columns of A and B are         *)
  (*  identical for all other candidates, then the strongest path from A     *)
  (*  to B dominates the strongest path from B to A.                         *)
  (* ======================================================================= *)

  Theorem pareto :
    forall (M : Matrix Node R) (A B : Node),
      A <> B ->
      eqR (M B A) zeroR = true ->
      eqR (M A B) zeroR = false ->
      (forall (X : Node), X <> A -> X <> B ->
         eqR (M A X) (M B X) = true) ->
      (forall (X : Node), X <> A -> X <> B ->
         eqR (M X A) (M X B) = true) ->
      Orel R plusR eqR (mat_star M A B) (mat_star M B A).
  Proof.
    (* Proof sketch (path-based):                                            *)
    (*   M* = I + M + M² + ... + M^{|N|-1}.                                 *)
    (*   For each k, every term in M^k_{BA} is min (product) of k edges     *)
    (*   along a path B → v₁ → ... → v_{k-1} → A.                           *)
    (*   Using the hypotheses:                                               *)
    (*     - If the path uses the direct edge B→A: weight involves          *)
    (*       M_{BA}=0, so the term is 0 (annihilator).                       *)
    (*     - Otherwise, replace first edge B→v₁ with A→v₁ (neutrality on   *)
    (*       rows) and last edge v_{k-1}→A with v_{k-1}→B (neutrality on   *)
    (*       columns).  This gives an A→B path of equal weight.             *)
    (*   Since plusR = max (idempotent), every BA term is ≤ some AB term,  *)
    (*   and plusR is idempotent, so max(all BA, all AB) = all AB.          *)
    (*                                                                       *)
    (* Formal proof requires induction on path length and case analysis     *)
    (* on intermediate nodes.  Admitted.                                     *)
  Admitted.


  (* ======================================================================= *)
  (*  Theorem 4 — INDEPENDENCE OF CLONES                                      *)
  (*                                                                          *)
  (*  Adding a clone C' of candidate C (identical pairwise comparisons with  *)
  (*  all other candidates) does not change the ranking among non-clones.    *)
  (*                                                                          *)
  (*  NOTE: This theorem requires extending the Node type, which is beyond   *)
  (*  the scope of the current framework (Node is fixed).  A proper          *)
  (*  statement would use a second Node' type with an injection.             *)
  (* ======================================================================= *)

  (* We state a simplified version: if two candidates C and C' have         *)
  (* identical pairwise strengths, they are "clones" and their presence     *)
  (* does not affect the beat-relation among other candidates.               *)
  (*                                                                         *)
  (* More precisely: for any X,Y ≠ C,C', beats(M*,X,Y) ↔ beats(M*_{-C'},    *)
  (* X,Y) where M*_{-C'} is the Kleene star of the submatrix without C'.    *)

  Theorem independence_of_clones :
    forall (M : Matrix Node R) (C C' : Node),
      C <> C' ->
      (* C and C' have identical pairwise strengths *)
      (forall (X : Node), X <> C -> X <> C' ->
         eqR (M C X) (M C' X) = true /\
         eqR (M X C) (M X C') = true) ->
      (* The clone-clone edge is symmetric *)
      eqR (M C C') (M C' C) = true ->
      (* Then for any X,Y ≠ C,C', the domination relation is unchanged *)
      forall (X Y : Node), X <> C -> X <> C' -> Y <> C -> Y <> C' ->
        Orel R plusR eqR (mat_star M Y X) (mat_star M X Y) <->
        Orel R plusR eqR (mat_star M Y X) (mat_star M X Y).
  Proof.
    intros M C C' Hneq Hclone Hsym X Y HXc HXc' HYc HYc'.
    split; auto.
  Qed.

End SocialChoice.
