From Stdlib Require Import List Utf8
  Lia.
From Semiring Require Import PathN MatN 
  OrelN Structures.
Import ListNotations SemiringNotations.

Section Semimodule.
  Context 
    {Node : FinType.type}.


  (** A [Vector] is a [Node]-indexed family of elements of the semimodule
      carrier.  We use the packed [U] (which extends [CommutativeMonoid])
      so that the [Orel] order from [OrelN] is directly available. *)
  Definition Vector {R : Semiring.type} 
    {U : Semimodule.type R} : Type := 
    Node -> U. 

  Definition vec_zero {R : Semiring.type} 
    {U : Semimodule.type R} : @Vector R U:= 
    fun _ => zero.
  Definition vec_add {R : Semiring.type} 
    {U : Semimodule.type R} (x y : Vector) : @Vector R U := 
    fun (i : Node) => x i + y i.
  Definition vec_scale {R : Semiring.type} 
    {U : Semimodule.type R} (a : R) (v : Vector) : @Vector R U := 
    fun i => scale a (v i).

  (* (m · v)_i  :=  Σ_{j ∈ finN}  (v_j) ⊙ m_{i,j}                            *)
  (* v is a column vector *)

  Definition matrix_vector_action {R : Semiring.type} 
    {U : Semimodule.type R} (m : @Matrix Node R) (v : Vector) : @Vector R U := 
    fun (i : Node) =>
      List.fold_right
        (fun j acc => add (scale (m i j) (v j)) acc)
        zero elements.

  (* Efficient list-based version: map each row → fold (scale v_j m_{i,j})    *)
  Definition matrix_vector_action_eff {R : Semiring.type} 
    {U : Semimodule.type R} (m : list (list R)) (v : list U) : list U :=
    List.map (fun row =>
      List.fold_right add zero
        (List.map (fun '(r_elem, v_elem) => scale r_elem v_elem)
          (List.combine row v))) m.

  (* Look up a node in parallel with a value list ordered by finN             *)
  Fixpoint list_lookup {R : Semiring.type} 
    {U : Semimodule.type R} (keys : list Node) (vals : list U) (key : Node) : U :=
    match keys, vals with
    | k :: ks, v :: vs => if fin_eq_dec key k then v else list_lookup ks vs key
    | _, _ => zero
    end.

  (* Functional wrapper: convert Matrix/Vector to lists, compute, convert back. 
    Vector v is a column vector  *)
  Definition matrix_vector_action_eff_fun {R : Semiring.type} 
    {U : Semimodule.type R} (m : @Matrix Node R) (v : @Vector R U) : Vector :=
    let la := List.map (fun r => List.map (fun c => m r c) elements) elements in 
    let va := List.map (fun r => v r) elements in
    let result := matrix_vector_action_eff la va in
    fun i => list_lookup elements result i.


  (* Generic list_lookup_map: works for any list l                           *)
  Lemma list_lookup_map_gen {R : Semiring.type} 
    {U : Semimodule.type R} : forall (f : Node -> U) (l : list Node),
    forall (i : Node), NoDup l -> List.In i l -> 
    list_lookup l (List.map f l) i = f i.
  Proof.
    intros * H_dup H_in.
    revert i H_in.
    induction l as [|j js IH]; simpl; intros i H_in.
    - inversion H_in.
    - simpl in H_dup. inversion H_dup; subst.
      case(fin_eq_dec i j); intros Heq.
      + subst; reflexivity.
      + 
        destruct H_in as [H_eq | H_in_js].
        * rewrite H_eq in Heq. unfold not in Heq. 
          specialize (Heq eq_refl). inversion Heq.
        * apply (IH H2 i H_in_js).
  Qed.


   (* Generic: the efficient computation looked up equals the functional one   *)

  (* combine + map + fold_right = direct fold_right over the same list         *)
  Lemma combine_fold_eq {R : Semiring.type} {U : Semimodule.type R} : 
    forall (l : list Node) (A : Node -> Node -> R) (x : Node -> U) (r : Node),
    (List.fold_right add zero
      (List.map (fun '(re, ve) => scale re ve)
        (List.combine (List.map (fun c : Node => A r c) l)
                          (List.map (fun n : Node => x n) l))))
    = 
    (List.fold_right (fun j acc => add (scale (A r j) (x j)) acc) zero l).
  Proof.
    induction l as [|j js IH]; intros *.
    - cbn. reflexivity.
    - cbn. rewrite IH. reflexivity. 
  Qed.



  (** The efficient list-based action, when looked up at a valid index [i],
      returns the same value as the functional fold over the same list. *)
  Lemma list_lookup_eff_gen {R : Semiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (x : Node -> U) (l : list Node),
    forall (i : Node),
    NoDup l -> In i l ->
    list_lookup l
      (matrix_vector_action_eff
        (List.map (fun r => List.map (fun c => A r c) l) l)
        (List.map (fun r => x r) l))
      i
    = List.fold_right (fun j acc => add (scale (A i j) (x j)) acc) zero l.
  Proof.
    intros A x l i Hdup Hin.
    transitivity
      (List.fold_right add zero
         (List.map (fun '(re, ve) => scale re ve)
            (List.combine (List.map (fun c : Node => A i c) l)
                          (List.map (fun n : Node => x n) l)))).
    - unfold matrix_vector_action_eff.
      rewrite List.map_map.
      apply (list_lookup_map_gen
        (fun r => List.fold_right add zero
                   (List.map (fun '(re, ve) => scale re ve)
                      (List.combine (List.map (fun c : Node => A r c) l)
                                    (List.map (fun n : Node => x n) l))))
        l i Hdup Hin).
    - apply combine_fold_eq.
  Qed.


  (** Additive shuffle in the semimodule's commutative monoid:
      [(a+b)+(c+d) = (a+c)+(b+d)]. *)
  Lemma add_swap_mid_vec {R : Semiring.type} {U : Semimodule.type R} :
    forall (a b c d : U),
    add (add a b) (add c d) = add (add a c) (add b d).
  Proof.
    intros a b c d.
    rewrite (addA a b (c + d)).
    rewrite <- (addA b c d) at 1.
    rewrite (addC b c).
    rewrite (addA c b d).
    rewrite <- (addA a c (b + d)).
    reflexivity.
  Qed.


  (** Scalar multiplication distributes over a fold-right sum:
      [a ⊙ (Σ f j) = Σ (a ⊙ f j)]. *)
  Lemma fold_right_scale_distr {R : Semiring.type} {U : Semimodule.type R} :
    forall (f : Node -> U) (l : list Node) (a : R),
    scale a (List.fold_right (fun j acc => add (f j) acc) zero l) =
    List.fold_right (fun j acc => add (scale a (f j)) acc) zero l.
  Proof.
    intros f l a. induction l as [|j js IH]; simpl.
    - apply scale_zero_v.
    - rewrite (scale_distr_v (s := U) a (f j)).
      f_equal. exact IH.
  Qed.




  (** Combine of two maps over [elements] equals a map of pairs. *)
  Lemma combine_map_map {X Y : Type} (f : Node -> X) (g : Node -> Y) :
    List.combine (List.map f elements) (List.map g elements) =
    List.map (fun c => (f c, g c)) elements.
  Proof.
    induction elements as [|j js IH]; simpl; auto.
    rewrite IH. reflexivity.
  Qed.

  (** Lookup in a tabulated vector returns the function value. *)
  Lemma list_lookup_map {R : Semiring.type} {U : Semimodule.type R} :
    forall (f : Node -> U) (i : Node),
    list_lookup elements (List.map f elements) i = f i.
  Proof.
    intros f i.
    apply list_lookup_map_gen;
      [apply elements_nodup | apply elements_complete].
  Qed.

  (** The efficient list-based action, when looked up at any index, equals
      the functional matrix-vector action. *)
  Lemma list_lookup_eff {R : Semiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (x : Node -> U) (i : Node),
    list_lookup elements
      (matrix_vector_action_eff
        (List.map (fun r => List.map (fun c => A r c) elements) elements)
        (List.map (fun r => x r) elements))
      i
    = matrix_vector_action A x i.
  Proof.
    intros A x i.
    unfold matrix_vector_action.
    apply (list_lookup_eff_gen A x elements i
      (elements_nodup (s := Node))
      (elements_complete (s := Node) i)).
  Qed.

  (** The functional wrapper around the efficient action equals the
      functional action pointwise. *)
  Theorem matrix_vector_action_eff_fun_eq {R : Semiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (x : Node -> U) (i : Node),
    matrix_vector_action_eff_fun A x i = matrix_vector_action A x i.
  Proof.
    intros A x i.
    unfold matrix_vector_action_eff_fun.
    apply list_lookup_eff.
  Qed.


  (** Fold-right respects pointwise equality of the step function. *)
  Lemma fold_right_congr {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (f g : Node -> U),
    (forall j, f j = g j) ->
    List.fold_right (fun j acc => add (f j) acc) zero l =
    List.fold_right (fun j acc => add (g j) acc) zero l.
  Proof.
    induction l as [|j js IH]; simpl; intros f g Hfg.
    - reflexivity.
    - rewrite Hfg. f_equal. apply (IH f g Hfg).
  Qed.

  (** Sum of pointwise sum equals sum of sums:
      [Σ (f j + g j) = (Σ f j) + (Σ g j)]. *)
  Lemma fold_right_split {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (f g : Node -> U),
    List.fold_right (fun j acc => add (add (f j) (g j)) acc) zero l =
    add (List.fold_right (fun j acc => add (f j) acc) zero l)
        (List.fold_right (fun j acc => add (g j) acc) zero l).
  Proof.
    induction l as [|j js IH]; simpl; intros f g.
    - rewrite add0r. reflexivity.
    - rewrite IH. apply add_swap_mid_vec.
  Qed.

  (** Scale distributes over the sum of two scalar functions applied to
      a common vector: [Σ (a_j + b_j) ⊙ v_j = Σ a_j ⊙ v_j + Σ b_j ⊙ v_j]. *)
  Lemma fold_right_scale_add {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (f g : Node -> R) (v : Node -> U),
    List.fold_right (fun j acc => add (scale (f j + g j) (v j)) acc) zero l =
    add (List.fold_right (fun j acc => add (scale (f j) (v j)) acc) zero l)
        (List.fold_right (fun j acc => add (scale (g j) (v j)) acc) zero l).
  Proof.
    intros l f g v.
    transitivity (List.fold_right
      (fun j acc => add (add (scale (f j) (v j)) (scale (g j) (v j))) acc) zero l).
    - apply fold_right_congr. intro j.
      rewrite (scale_distr_r (s := U) (f j) (g j) (v j)). reflexivity.
    - apply fold_right_split.
  Qed.


  (** Scaling by a sum of scalars equals a sum of scaled values:
      [(Σ f k) ⊙ x = Σ (f k ⊙ x)]. *)
  Lemma fold_right_scale_r_sum {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (f : Node -> R) (x : U),
    scale (List.fold_right (fun k acc => f k + acc) 0 l) x =
    List.fold_right (fun k acc => add (scale (f k) x) acc) zero l.
  Proof.
    induction l as [|h t IH]; simpl; intros f x.
    - apply scale_zero_r.
    - rewrite scale_distr_r.
      f_equal. apply IH.
  Qed.



  (** In a bounded semiring, the module addition is idempotent:
      [v + v = v]. *)
  Lemma add_idem_module {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (v : U), add v v = v.
  Proof.
    intro v.
    assert (Hbound : add (one (s := R)) (one (s := R)) = one (s := R))
      by apply (add_bound (s := R) one).
    pose proof (scale_distr_r (s := U) one one v) as Hdist.
    (* Hdist: scale (1+1) v = scale 1 v + scale 1 v *)
    rewrite Hbound in Hdist.
    rewrite !(scale_one (s := U) v) in Hdist.
    symmetry. exact Hdist.
  Qed.

  (** Double sum interchange over the same list:
      [Σ_j Σ_k f j k = Σ_k Σ_j f j k]. *)
  Lemma fold_right_double_commute {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (f : Node -> Node -> U),
    List.fold_right
      (fun j acc =>
        add (List.fold_right (fun k acc' => add (f j k) acc') zero l) acc)
      zero l =
    List.fold_right
      (fun k acc =>
        add (List.fold_right (fun j acc' => add (f j k) acc') zero l) acc)
      zero l.
  Proof.
      induction l as [|h t IH]; simpl; intros f.
    - apply eq_refl.
    - (* Name the sub-expressions for clarity *)
      set (A := f h h).
      set (B := List.fold_right (fun k acc' => add (f h k) acc') zero t).
      set (C := List.fold_right (fun j acc' => add (f j h) acc') zero t).
      set (D := List.fold_right
                 (fun j acc =>
                    add (List.fold_right (fun k acc' => add (f j k) acc') zero t) acc) zero t).
      (* LHS = plusV (A + B) (plusV C D) via fold_right_split *)
      assert (HL : eq
        (List.fold_right (fun j acc =>
           add (List.fold_right (fun k acc' => add (f j k) acc') zero (h :: t)) acc)
           zero (h :: t))
        (add (add A B) (add C D))).
      { simpl.
        f_equal. unfold C, D.
        rewrite <-fold_right_split.
        reflexivity.
      }
      (* RHS = plusV (A + C) (plusV B D) via fold_right_split *)
      assert (HR : eq
        (List.fold_right (fun k acc =>
           add (List.fold_right (fun j acc' => add (f j k) acc') zero (h :: t)) acc)
           zero (h :: t))
        (add (add A C) (add B D))).
      { simpl.
        f_equal. unfold B, D.
        refine (eq_trans (fold_right_split t
        (fun k => f h k)
        (fun k => List.fold_right (fun j acc' => add (f j k) acc') zero t))_).
        f_equal. rewrite IH. reflexivity.
      }
      cbn in HL, HR.
      unfold A.
      rewrite HL, HR.
      apply add_swap_mid_vec.
  Qed.

  
    

  (** Matrix-multiplication associativity for the matrix-vector action:
      [(M₁·M₂)·v = M₁·(M₂·v)]. *)
  Lemma fold_right_mul_assoc {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (M1 M2 : Node -> Node -> R) (v : Node -> U) (i : Node),
    List.fold_right (fun j acc => add (scale
      (List.fold_right (fun k acc2 => M1 i k * M2 k j + acc2) 0 l) (v j)) acc)
      zero l =
    List.fold_right (fun j acc => add (scale (M1 i j)
      (List.fold_right (fun k acc2 => add (scale (M2 j k) (v k)) acc2) zero l)) acc)
      zero l.
  Proof.
    intros l M1 M2 v i.
    set (f := fun (j k : Node) => scale (M1 i k) (scale (M2 k j) (v j))).
    (* The proof mirrors Semimodule.v: use fold_right_scale_r_sum,
       fold_right_scale_distr, scale_assoc, fold_right_congr, and
       fold_right_double_commute. *)
  Admitted.

  (** Identity-matrix action yields zero on nodes not in the list. *)
  Lemma fold_right_identity_zero {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (v : Node -> U) (i : Node),
    ~ In i l ->
    List.fold_right (fun j acc => add (scale (I i j) (v j)) acc) zero l = zero.
  Proof.
  Admitted.

  (** Identity-matrix action returns the vector component at the
      matching index. *)
  Lemma fold_right_identity {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (v : Node -> U) (i : Node),
    NoDup l -> In i l ->
    List.fold_right (fun j acc => add (scale (I i j) (v j)) acc) zero l = v i.
  Proof.
  Admitted.

  (** The geometric sum at the node-count bound satisfies the Kleene
      fixpoint equation: [A* = I + A · A*]. *)
  Lemma geom_sum_fixpoint {R : BoundedSemiring.type} :
    forall (m : @Matrix Node R),
    (forall u v : Node, u = v -> m u v = 1) ->
    forall (c d : Node),
    geom_sum m (length (@elements Node) - 1)%nat c d =
    matrix_add I (matrix_mul m (geom_sum m (length (@elements Node) - 1)%nat)) c d.
  Proof.
    (* Provable using geom_sum_stable_after_node_bound and
       the recurrence of geom_sum (geom_sum_S from MatN.v). *)
  Admitted.

  (** Kleene fixed point: [x = A* · b ⇔ x = A · x + b]. *)
  Theorem kleene_fixed_point {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (b x : @Vector R U),
    (forall u v : Node, u = v -> A u v = 1) ->
    (forall i : Node, x i = matrix_vector_action
      (geom_sum A (length (@elements Node) - 1)%nat) b i) ->
    forall (i : Node), x i = vec_add (matrix_vector_action A x) b i.
  Proof.
    (* Proof uses geom_sum_fixpoint, fold_right_identity, fold_right_mul_assoc. *)
  Admitted.

  (** Vector addition is pointwise: [(x + y) i = x i + y i]. *)
  Lemma vec_add_pointwise {R : Semiring.type} {U : Semimodule.type R} :
    forall (u v : @Vector R U) (i : Node),
    vec_add u v i = u i + v i.
  Proof. reflexivity. Qed.

  (** From [x = A·x + b] and bounded idempotence, derive [b ≤ x]. *)
  Lemma absorb_b_fixpoint {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (b x : @Vector R U),
    (forall i : Node, x i = vec_add (matrix_vector_action A x) b i) ->
    forall i : Node, Orel (b i) (x i).
  Proof.
    (* Proof: x+b = (A·x+b)+b = A·x+(b+b) = A·x+b = x,
       using add_idem_module and addA/addC. *)
  Admitted.

  (** From [x = A·x + b] and bounded idempotence, derive [A·x ≤ x]. *)
  Lemma absorb_Ax_fixpoint {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (b x : @Vector R U),
    (forall i : Node, x i = vec_add (matrix_vector_action A x) b i) ->
    forall i : Node, Orel (matrix_vector_action A x i) (x i).
  Proof.
    (* Proof using add_idem_module, addA, addC, and the fixpoint hypothesis. *)
  Admitted.

  (** Matrix-vector action is monotone with respect to the Orel order.
      If [v ≤ u] pointwise, then [A·v ≤ A·u] pointwise. *)
  Lemma mva_monotone_Orel {R : IdempotentSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (u v : @Vector R U),
    (forall j, Orel (v j) (u j)) ->
    forall i, Orel (matrix_vector_action A v i) (matrix_vector_action A u i).
  Proof.
    (* Proof: use fold_right_split, fold_right_congr, scale_distr_v. *)
  Admitted.

  (** Absorption lifts through matrix powers:
      if [b ≤ x] and [A·x ≤ x], then [A^k·b ≤ x] for all [k]. *)
  Lemma matrix_pow_absorb {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (x b : @Vector R U) (k : nat),
    (forall i, Orel (b i) (x i)) ->
    (forall i, Orel (matrix_vector_action A x i) (x i)) ->
    forall i, Orel (matrix_vector_action (pow A k) b i) (x i).
  Proof.
    (* Proof by induction on k, using fold_right_mul_assoc,
       mva_monotone_Orel, and the absorption hypotheses. *)
  Admitted.

  (** Right matrix fixpoint: [A* = I + A* · A]. *)
  Lemma geom_sum_fixpoint_right {R : BoundedSemiring.type} :
    forall (m : @Matrix Node R),
    (forall u v : Node, u = v -> m u v = 1) ->
    forall (c d : Node),
    geom_sum m (length (@elements Node) - 1)%nat c d =
    matrix_add I (matrix_mul (geom_sum m (length (@elements Node) - 1)%nat) m) c d.
  Proof.
    (* Proof mirrors geom_sum_fixpoint using right-sided stabilization. *)
  Admitted.

  (** Right Kleene fixed point: [x = A*·b ⇒ x = A*·(A·b) + b]. *)
  Theorem kleene_fixed_point_right {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (b x : @Vector R U),
    (forall u v : Node, u = v -> A u v = 1) ->
    (forall i : Node, x i = matrix_vector_action
      (geom_sum A (length (@elements Node) - 1)%nat) b i) ->
    forall (i : Node), x i = vec_add
      (matrix_vector_action (geom_sum A (length (@elements Node) - 1)%nat)
        (matrix_vector_action A b)) b i.
  Proof.
    (* Proof uses geom_sum_fixpoint_right, fold_right_identity, fold_right_mul_assoc. *)
  Admitted.

  (** Leastness of the Kleene fixed point: [x = A·x + b] implies
      [A*·b ≤ x] in the Orel order, i.e., [A*·b] is below every solution. *)
  Theorem kleene_fixed_point_least {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (b x : @Vector R U),
    (forall u v : Node, u = v -> A u v = 1) ->
    (forall i : Node, x i = vec_add (matrix_vector_action A x) b i) ->
    forall (i : Node),
    Orel (matrix_vector_action (geom_sum A (length (@elements Node) - 1)%nat) b i) (x i).
  Proof.
    (* Proof follows Semimodule.v: use absorb_b_fixpoint, absorb_Ax_fixpoint,
       matrix_pow_absorb, and an induction over the partial-sum construction
       of geom_sum. *)
  Admitted.


End Semimodule.




