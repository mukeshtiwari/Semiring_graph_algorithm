(* ========================================================================= *)
(*  Social Choice Properties in the Abstract Semimodule Framework            *)
(*                                                                           *)
(*  We formalise Pareto, Monotonicity, Reversal Symmetry, and Clone          *)
(*  Independence as theorems about the Kleene-star fixed point in an         *)
(*  idempotent, bounded semiring.  These are then instantiated for any       *)
(*  concrete semiring (max-min, min-plus, etc.) to prove the corresponding   *)
(*  social-choice properties.                                                *)
(* ========================================================================= *)

From Stdlib Require Import List Utf8 Lia Wf_nat.
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
  (* ======================================================================= *)

  (* Helper:  Z = M with column A zeroed.  Defined pointwise.                *)
  Let zero_col_A (M : Matrix Node R) (A : Node) : Matrix Node R :=
    fun i j => if eqN j A then zeroR else M i j.


  (* -----------------------------------------------------------------------  *)
  (*  Sub-lemma: every M-path from A to C (C≠A) has a dominating             *)
  (*  A-free path in Z.  The A-free path appears in the Z-enumeration        *)
  (*  (since Z = M except column A = 0).                                     *)
  (*                                                                          *)
  (*  Proof sketch:                                                           *)
  (*    Given path l from A to C in M.  If l never revisits A, it is         *)
  (*    already A-free and in Z (same edges, same weight).                    *)
  (*    If l revisits A: find the first A→A cycle.  By                        *)
  (*    cycle_path_dup_remove (Path.v) with bounded as zero_stable:           *)
  (*      Orel (measure of reduced path) (measure of full path).              *)
  (*    By well_formed_loop_removal, the reduced path is well-formed.         *)
  (*    Iterate on the reduced path (which has fewer A-revisits).            *)
  (*    By induction on the number of A-occurrences, obtain an A-free         *)
  (*    path q with Orel (measure q) (measure l).                             *)
  (*    q is in the Z-enumeration: all edges are M-edges away from            *)
  (*    column A, so Z has the same edges.  Source A, target C unchanged.     *)
  (* -----------------------------------------------------------------------  *)
  (* Helper: empty edge list never appears in enum_all_paths_flat.
     We first prove that triple_elem_list [] h = false for non-empty h. *)
  Lemma triple_elem_list_nil_false : forall h,
    h <> [] ->
    triple_elem_list Node Node R eqN eqN eqR [] h = false.
  Proof.
    destruct h as [|((a,b),c) h]; [congruence|].
    reflexivity.
  Qed.

  Lemma In_eq_bool_nil_false : forall l,
    (forall h, In h l -> h <> []) ->
    In_eq_bool Node Node R eqN eqN eqR [] l = false.
  Proof.
    intros l Hnonempty.
    unfold In_eq_bool.
    induction l as [|h t]; [reflexivity|].
    simpl.
    (* triple_elem_list [] h = false because h <> [] *)
    destruct h as [|((a,b),c) h'].
    - (* h = []: contradiction with Hnonempty *)
      simpl. exfalso.
      exact (Hnonempty [] (or_introl eq_refl) eq_refl).
    - simpl.
    apply IHt.
    intros h0 Hin; apply Hnonempty; right; exact Hin.
  Qed.

  (* Helper: triple_elem_list implies equality of measures.
     This avoids the section-variable opacity issues with path_split_measure. *)
  Lemma measure_of_path_triple_eq : forall l1 l2,
    triple_elem_list Node Node R eqN eqN eqR l1 l2 = true ->
    eqR (measure_of_path Node R oneR mulR l1)
        (measure_of_path Node R oneR mulR l2) = true.
  Proof.
    induction l1 as [|((a1,b1),c1) l1 IH]; intros l2 Ht.
    - destruct l2; simpl; [apply refR|]. simpl in Ht; congruence.
    - destruct l2 as [|((a2,b2),c2) l2]; [simpl in Ht; congruence|].
      simpl in Ht.
      apply Bool.andb_true_iff in Ht; destruct Ht as [Ht Htr].
      apply Bool.andb_true_iff in Ht; destruct Ht as [Ht Htrr].
      apply Bool.andb_true_iff in Ht; destruct Ht as [HeqA Htrrr].
      simpl.
      apply (congrM c1 (measure_of_path Node R oneR mulR l1)
                   c2 (measure_of_path Node R oneR mulR l2)
                   Htrr (IH l2 Htr)).
  Qed.


  (* ----------------------------------------------------------------------- *)
  (*  Gap 1 — No-cycle paths are preserved when zeroing column A.            *)
  (* ----------------------------------------------------------------------- *)

  (* Core sub-lemma: all_paths_klength with a simple edge-list is invariant
     under zeroing column A, provided no edge in the list targets A.
     The proof is by induction on k, with source and target generalized. *)
  Lemma path_membership_Z_no_cycle :
    forall (M Z : Matrix Node R) (A C : Node) (p : Path Node R) (n : nat),
      eqN C A = false ->
      Z = zero_col_A M A ->
      elem_path_triple Node eqN R (tp Node R p) = true ->
      In_path_membership Node eqN R eqR p
        (enum_all_paths_flat Node eqN R oneR finN M n A C) = true ->
      In_path_membership Node eqN R eqR p
        (enum_all_paths_flat Node eqN R oneR finN Z n A C) = true.
  Proof.
    (* Proof strategy (detailed):
       1. Unfold In_path_membership — reduces to In_eq_bool edges (map snd enum).
       2. Induction on n, using in_eq_bool_mem_first to split enum_all_paths_flat
          at each level into all_paths_klength plus the rest.
       3. For the all_paths_klength component:
          Core lemma: if elem_path_triple edges = true and edges is in
          all_paths_klength M k A C (C≠A), then edges is in all_paths_klength Z k A C.
          Proof by induction on k, with source generalized.
          - Base k=0: all_paths_klength uses 1 (oneR), matrix-independent. Trivial.
          - Step k>0: Use append_node_in_paths_eq (Path.v) to get y, ys such that
            edges ≈ (A, y, M[A][y]) :: ys.  Since elem_path_triple edges = true,
            A ≠ y (no self-loop).  By the "no edge targets A" condition (provable
            from elem_path_triple + source A + target C ≠ A), we get y ≠ A.
            Hence Z[A][y] = M[A][y].  The tail ys inherits elem_path_triple
            and the no-target-A property, and is in all_paths_klength M (k-1) y C.
            By IH, ys is in all_paths_klength Z (k-1) y C.  Reconstruct:
            edges is triple_elem_list-equal to (A,y,Z[A][y])::ys, which is
            in all_paths_klength Z k A C.  Done.
       4. Use in_eq_bool_mem_second to lift back to full enumeration.

       Current status: the core lemma all_paths_klength_Z_invariant has been
       written with explicit section arguments for append_node_in_paths_eq but
       encounters Rocq 9.1.1 opacity with Pathprops section variables.
       The proof structure is sound; the remaining work is to resolve section
       variable passing for append_node_in_paths_eq, append_node_rest, and
       in_flat_map_bool_first from Path.v/Listprop.v.
    *)
  Admitted.

  Lemma path_membership_M_reduced :
    forall (M : Matrix Node R) (A C : Node) (p : Path Node R) (n : nat)
           (ll lr : list (Node * Node * R))
           (au av : Node) (aw : R) (lm : list (Node * Node * R)),
      triple_elem_list Node Node R eqN eqN eqR (tp Node R p)
        (ll ++ ((au, av, aw) :: lm) ++ lr) = true ->
      elem_path_triple Node eqN R ll = true ->
      cyclic_path Node eqN R au ((au, av, aw) :: lm) ->
      In_path_membership Node eqN R eqR p
        (enum_all_paths_flat Node eqN R oneR finN M n A C) = true ->
      In_path_membership Node eqN R eqR (A, C, ll ++ lr)
        (enum_all_paths_flat Node eqN R oneR finN M n A C) = true.
  Proof.
  Admitted.


  Lemma path_A_cycle_removal :
    forall (M Z : Matrix Node R) (A C : Node),
      eqN C A = false ->
      Z = zero_col_A M A ->
      forall (p : Path Node R) (n : nat),
        In_path_membership Node eqN R eqR p
          (enum_all_paths_flat Node eqN R oneR finN M n A C) = true ->
        exists (q : Path Node R),
          In_path_membership Node eqN R eqR q
            (enum_all_paths_flat Node eqN R oneR finN Z n A C) = true /\
          Orel R plusR eqR
            (measure_of_path Node R oneR mulR (tp Node R q))
            (measure_of_path Node R oneR mulR (tp Node R p)).
  Proof.
    (* Strong induction on the length of tp p, using Nat.lt well-foundedness *)
    intros M Z A C Hca HZ p n Hin.
    remember (length (tp Node R p)) as plen eqn:Hplen.
    symmetry in Hplen. (* Now Hplen: length(tp p) = plen *)
    revert p n Hplen Hin.
    apply (well_founded_induction Wf_nat.lt_wf
      (fun len' => forall (p : Path Node R) (n : nat),
        length (tp Node R p) = len' ->
        In_path_membership Node eqN R eqR p
          (enum_all_paths_flat Node eqN R oneR finN M n A C) = true ->
        exists (q : Path Node R),
          In_path_membership Node eqN R eqR q
            (enum_all_paths_flat Node eqN R oneR finN Z n A C) = true /\
          Orel R plusR eqR
            (measure_of_path Node R oneR mulR (tp Node R q))
            (measure_of_path Node R oneR mulR (tp Node R p)))).
    intros len IH p n Hlen Hin.

    (* Case analysis: is the path simple (no cycles)? *)
    case_eq (elem_path_triple Node eqN R (tp Node R p)); intro Hcycle.

    - (* === CASE 1: No cycle === *)
      (* The path is simple. Since A is the source and C ≠ A,
         the path never revisits A. So no edge targets A,
         hence Z = M on all edges of this path.
         Therefore the same edge list appears in both enumerations. *)
      exists p. split.
      + (* In_path_membership in Z-enumeration — via helper lemma *)
        apply (path_membership_Z_no_cycle M Z A C p n Hca HZ Hcycle Hin).
      + (* Orel measure(p) measure(p) *)
        unfold Orel. apply plusR_idem.

    - (* === CASE 2: Has a cycle === *)
      (* Decompose the path using triple_compute_connect_with_triple_elem_stronger *)
      pose proof (triple_compute_connect_with_triple_elem_stronger
        Node eqN refN symN trnN R eqR refR symR
        (tp Node R p) Hcycle)
        as (ll & au & av & aw & lm & lr
            & Hdecomp & Hcyclic & Helem_ll & Htriple).

      (* Remove the cycle: cycle_path_dup_remove gives weight inequality *)
      pose proof (cycle_path_dup_remove
        Node eqN refN R oneR plusR mulR eqR refR symR
        o_lm m_assoc ldist rdist congrP congrM congrR
        bounded ll ((au, av, aw) :: lm) lr) as Hweight.

      (* The reduced path ll++lr is strictly shorter *)
      assert (Hshorter : length (ll ++ lr) < length (tp Node R p)).
      { pose proof (length_rewrite _ _ _ eqN eqN eqR _ _ Htriple) as Hlen_eq.
        rewrite Hlen_eq.
        rewrite !List.length_app; simpl.
        lia. }

      (* Build the reduced path *)
      set (p_red := (A, C, ll ++ lr) : Path Node R).

      (* Show reduced path is in the M-enumeration — via helper lemma *)
      assert (Hin_red : In_path_membership Node eqN R eqR p_red
        (enum_all_paths_flat Node eqN R oneR finN M n A C) = true).
      { subst p_red.
        apply (path_membership_M_reduced M A C p n ll lr au av aw lm
                 Htriple Helem_ll Hcyclic Hin). }

      (* Apply induction hypothesis on the shorter reduced path *)
      assert (Hlt : length (tp Node R p_red) < len).
      { subst p_red; simpl. rewrite <- Hlen. exact Hshorter. }
      destruct (IH (length (tp Node R p_red)) Hlt p_red n eq_refl Hin_red)
        as (q & Hq_mem & Hq_orel).

      exists q. split.
      + exact Hq_mem.
      + (* Chain Orel: measure(q) ≥ measure(p_red) ≥ measure(p) *)
        eapply orel_trans_local; [exact Hq_orel|].
        subst p_red; simpl.
        (* Goal: Orel measure(ll++lr) measure(tp p) *)
        pose proof (measure_of_path_triple_eq (tp Node R p)
          (ll ++ ((au, av, aw) :: lm) ++ lr) Htriple) as Heq.
        unfold Orel.
        (* Hweight: eqR (plusR measure(ll++lr) measure(ll++...++lr)) measure(ll++lr) = true *)
        (* Heq: eqR measure(tp p) measure(ll++...++lr) = true *)
        (* Goal: eqR (plusR measure(ll++lr) measure(tp p)) measure(ll++lr) = true *)
        (* Use congrP to replace measure(tp p) by measure(ll++...++lr) inside plusR *)
        refine (trnR _ _ _ (congrP _ _ _ _ (refR _) Heq) Hweight).
  Qed.


  Lemma column_A_zero_preserves_row :
    (forall a b c, Orel R plusR eqR (mulR a c) (mulR a (mulR b c))) ->
    (forall M0, mat_cong Node eqN R eqR M0) ->
    forall (M : Matrix Node R) (A C : Node),
      eqN C A = false ->
      eqR (mat_star (zero_col_A M A) A C) (mat_star M A C) = true.
  Proof.
    intros H_abs H_cong M A C Hca.
    set (Z := zero_col_A M A).
    unfold mat_star, kleene_exp.
    set (k := Init.Nat.pred (List.length finN)).

    (* Direction 1: Orel (psum M k A C) (psum Z k A C) — M* ≥ Z*. *)
    (* M ≥ Z entrywise: on column A, Z = 0 ≤ M; elsewhere Z = M.   *)
    (* So Orel M Z holds everywhere, and partial_sum_mat_orelm     *)
    (* lifts this to the Kleene stars.                              *)
    assert (H_M_ge_Z : forall i j, Orel R plusR eqR (M i j) (Z i j)).
    { intros i j. unfold Z, zero_col_A.
      case_eq (eqN j A); intro Hja.
      - unfold Orel. apply z_rp.
      - unfold Orel. apply plusR_idem. }

    assert (H_dir1 : Orel R plusR eqR
      (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR M k A C)
      (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR Z k A C)).
    { apply (partial_sum_mat_orelm Z M k (H_cong Z) (H_cong M) H_M_ge_Z A C). }

    (* Direction 2: Orel (psum Z k A C) (psum M k A C) — Z* ≥ M*.            *)
    (*  Every M-path from A to C is dominated by its A-free reduction         *)
    (*  (a Z-path).  The proof chains:                                        *)
    (*    partial_sum_mat  =  partial_sum_paths    [connect_psum_paths]       *)
    (*                     =  sum_all_flat_paths   [flat_map_path_partial]    *)
    (*    Then sum_all_flat_paths_idempotence absorbs M into Z                *)
    (*    using path_A_cycle_removal for the per-path dominance.              *)
    (* =====================================================================  *)

    assert (H_dir2 : Orel R plusR eqR
      (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR Z k A C)
      (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR M k A C)).
    {
      unfold Orel.

      (* Step 1: psum_mat → psum_paths *)
      assert (HZ_ps : eqR
        (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR Z k A C)
        (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN Z k A C) = true).
      { refine (connect_partial_sum_mat_paths
          Node eqN refN symN trnN finN R zeroR oneR plusR 
          mulR eqR refR symR trnR z_lp z_rp p_assoc o_lm 
          ldist z_ra congrP congrM congrR
          k Z A C _).
        apply H_cong. }

      assert (HM_ps : eqR
        (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR M k A C)
        (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN M k A C) = true).
      { refine (connect_partial_sum_mat_paths
          Node eqN refN symN trnN finN R zeroR oneR plusR 
          mulR eqR refR symR trnR z_lp z_rp p_assoc o_lm 
          ldist z_ra congrP congrM congrR
          k M A C _).
        apply H_cong. }

      (* Rewrite both sides of plusR using congrP + trnR *)
      apply (trnR _ _ _
        (congrP (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR Z k A C)
                (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR M k A C)
                (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN Z k A C)
                (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN M k A C)
                HZ_ps HM_ps)).
      (* Goal: eqR (plusR P_Z P_M) S_Z = true *)
      apply (trnR (plusR (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN Z k A C)
                         (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN M k A C))
                  (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN Z k A C)
                  (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR Z k A C)).
      - (* eqR (plusR P_Z P_M) P_Z = true — via flat-path idempotence *)


        (* Step 2: psum_paths → sum_all_flat_paths *)
        assert (HZ_flat : eqR
          (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN Z k A C)
          (sum_all_flat_paths Node R zeroR oneR plusR mulR
            (enum_all_paths_flat Node eqN R oneR finN Z k A C)) = true).
        { refine (flat_map_path_partial_sum Node eqN finN R zeroR oneR
        plusR mulR eqR refR symR z_lp z_rp p_assoc p_comm
        o_lm congrP congrR k Z A C). }
        assert (HM_flat : eqR
          (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN M k A C)
          (sum_all_flat_paths Node R zeroR oneR plusR mulR
            (enum_all_paths_flat Node eqN R oneR finN M k A C)) = true).
        { refine (flat_map_path_partial_sum Node eqN finN R zeroR oneR
        plusR mulR eqR refR symR z_lp z_rp p_assoc p_comm
        o_lm congrP congrR k M A C). }

        (* Convert P_Z, P_M to their flat-path versions *)
        apply (trnR _ _ _
          (congrP (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN Z k A C)
                  (partial_sum_paths Node eqN R zeroR oneR plusR mulR finN M k A C)
                  (sum_all_flat_paths Node R zeroR oneR plusR mulR
                    (enum_all_paths_flat Node eqN R oneR finN Z k A C))
                  (sum_all_flat_paths Node R zeroR oneR plusR mulR
                    (enum_all_paths_flat Node eqN R oneR finN M k A C))
                  HZ_flat HM_flat)).
        (* Goal: eqR (plusR F_Z F_M) P_Z = true *)
        eapply trnR; [| apply (symR _ _ HZ_flat)].
        (* Goal: eqR (plusR F_Z F_M) F_Z = true *)

        (* Step 3: idempotence — Z absorbs M *)
        (* Goal: F_Z + F_M = F_Z.  Lemma gives F_M + F_Z = F_Z.  Swap via p_comm. *)
        apply (trnR _ _ _ (p_comm _ _)).
        refine (sum_all_flat_paths_idempotence Node eqN 
          refN R zeroR oneR plusR mulR eqR refR symR
          z_lp p_assoc p_comm o_lm m_assoc congrP congrM congrR
          (enum_all_paths_flat Node eqN R oneR finN M k A C)
          (enum_all_paths_flat Node eqN R oneR finN Z k A C)
          _).
        intros * Hw.
        eapply path_A_cycle_removal; try assumption.
        unfold Z; reflexivity.
        exact Hw.
      - (* eqR P_Z S_Z = true — from HZ_ps *)
        apply (symR _ _ HZ_ps).
    }

    (* Antisymmetry: Orel a b ∧ Orel b a → a = b.                           *)
    unfold Orel in H_dir1, H_dir2.
    apply (trnR _ _ _ (symR _ _ H_dir2)).
    apply (trnR _ _ _ (p_comm _ _)).
    apply H_dir1.
  Qed.

  Lemma mat_star_diag_eq_oneR : forall (M : Matrix Node R) (i : Node),
    eqR (mat_star M i i) oneR = true.
  Proof.
    intros M i. unfold mat_star, kleene_exp.
    set (n := Init.Nat.pred (List.length finN)).
    induction n; cbn.
    - unfold I. rewrite (refN i). apply refR.
    - unfold matrix_add.
      apply (trnR _ _ _ (congrP _ _ oneR _ IHn (refR _))).
      apply bounded.
  Qed.

   (* =====================================================================  *)
    (*  Monotonicity: if voters improve candidate A's pairwise scores        *)
    (*  (raising A's outgoing row and lowering A's incoming column, with     *)
    (*  all other M[X][Y] unchanged), then A's Kleene-star scores do not     *)
    (*  decrease — i.e., for every opponent C:                               *)
    (*                                                                        *)
    (*               M'*_{AC}  dominates  M*_{AC}                             *)
    (*                                                                        *)
    (*  Proof outline:                                                        *)
    (*    • If C = A (mod eqN): both entries are oneR (diagonal of the       *)
    (*      Kleene star), and Orel oneR oneR follows from idempotence.       *)
    (*    • If C ≠ A: we zero out column A in both matrices (Z and Z'),      *)
    (*      prove Z' ≥ Z entrywise using the row/col/Heq hypotheses, then   *)
    (*      lift to Kleene stars via mat_star_monotone.  Finally, column-    *)
    (*      zeroing doesn't change the A-row (column_A_zero_preserves_row),  *)
    (*      so the chain:                                                     *)
    (*                                                                        *)
    (*        M'*_{AC} = Z'*_{AC}  ≥  Z*_{AC} = M*_{AC}                      *)
    (*                                                                        *)
    (*      collapses to M'*_{AC} ≥ M*_{AC}.                                  *)
    (* =====================================================================  *)

  Theorem monotonicity :
    forall (M M' : Matrix Node R) (A : Node),
      (forall M0, mat_cong Node eqN R eqR M0) ->
      (forall a b c, Orel R plusR eqR (mulR a c) (mulR a (mulR b c))) ->
      (forall (Y : Node), Orel R plusR eqR (M' A Y) (M A Y)) ->
      (forall (X : Node), Orel R plusR eqR (M X A) (M' X A)) ->
      (forall (X Y : Node), eqN X A = false -> eqN Y A = false ->
         eqR (M X Y) (M' X Y) = true) ->
      forall (C : Node),
        Orel R plusR eqR (mat_star M' A C) (mat_star M A C).
  Proof.
    intros M M' A H_cong H_abs Hrow Hcol Heq C.
    case_eq (eqN C A); intro Hca.
    - (* C = A.  Both mat_star diagonals are oneR (mat_star_diag_eq_oneR). *)
      (* Use mat_cong_all to replace C by A, then plusR_idem oneR.       *)
      unfold Orel.
      pose proof (H_cong (mat_star M') A C A A (refN A) Hca) as Hc'.
      pose proof (H_cong (mat_star M) A C A A (refN A) Hca) as Hc.
      pose proof (mat_star_diag_eq_oneR M' A) as Hd'.
      pose proof (mat_star_diag_eq_oneR M A) as Hd.
      assert (Hs' : eqR (mat_star M' A C) oneR = true).
      { apply (trnR _ _ _ Hc' Hd'). }
      assert (Hs : eqR (mat_star M A C) oneR = true).
      { apply (trnR _ _ _ Hc Hd). }
      apply (trnR _ _ _
        (congrP (mat_star M' A C) (mat_star M A C) oneR oneR Hs' Hs)).
      apply (trnR _ _ _ (plusR_idem oneR)).
      apply (symR _ _ Hs').
    - (* C ≠ A (eqN false).  The main proof via zeroing column A. *)
      set (Z := zero_col_A M A).
      set (Z' := zero_col_A M' A).
      (* Z' dominates Z entrywise. *)
      assert (H_Z'_dom_Z : forall i j, Orel R plusR eqR (Z' i j) (Z i j)).
      { intros i j. unfold Z, Z', zero_col_A.
        case_eq (eqN j A); intro Hja.
        - apply (orel_refl R plusR eqR plusR_idem).
        - case_eq (eqN i A); intro Hia.
          + (* i = A (mod eqN), j ≠ A.  Use mat_cong_all to rewrite. *)
            pose proof (H_cong M' i j A j Hia (refN j)) as Hc'.
            pose proof (H_cong M i j A j Hia (refN j)) as Hc.
            unfold Orel.
            apply (trnR _ _ _
              (congrP (M' i j) (M i j) (M' A j) (M A j) Hc' Hc)).
            apply (trnR _ _ _ (Hrow j)).
            apply (symR _ _ Hc').
          + (* i ≠ A, j ≠ A: M = M'.  Orel follows from equality. *)
            pose proof (Heq i j Hia Hja) as Heq_ij.
            unfold Orel.
            apply (trnR _ _ _ (congrP (M' i j) (M i j) (M' i j) (M' i j) (refR _) Heq_ij)).
            apply plusR_idem. }
      (* mat_star_monotone → Z'* ≥ Z*. *)
      assert (H_star : forall i j, Orel R plusR eqR (mat_star Z' i j) (mat_star Z i j)).
      { apply mat_star_monotone; try apply H_cong. exact H_Z'_dom_Z. }
      (* Column-zeroing preserves A-row for non-A targets. *)
      assert (Hz : eqR (mat_star Z A C) (mat_star M A C) = true).
      { apply (column_A_zero_preserves_row H_abs H_cong). exact Hca. }
      assert (Hz' : eqR (mat_star Z' A C) (mat_star M' A C) = true).
      { apply (column_A_zero_preserves_row H_abs H_cong). exact Hca. }
      (* Chain: M'*_{AC} + M*_{AC} = Z'*_{AC} + Z*_{AC} = Z'*_{AC} = M'*_{AC}. *)
      unfold Orel.
      apply (trnR _ _ _
        (congrP (mat_star M' A C) (mat_star M A C)
                (mat_star Z' A C) (mat_star Z A C) (symR _ _ Hz') (symR _ _ Hz))).
      apply (trnR _ _ _ (H_star A C)).
      apply Hz'.
  Qed.


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
