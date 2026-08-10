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

  (** Nested fold-right is invariant under swapping bound variable names:
      [Σ_k Σ_j F j k = Σ_j Σ_k F k j] (alpha-rename). *)
  Lemma fold_right_nest_alpha {R : Semiring.type} {U : Semimodule.type R} :
    forall (l1 l2 : list Node) (F : Node -> Node -> U),
    List.fold_right (fun k acc =>
      add (List.fold_right (fun j acc' => add (F j k) acc') zero l2) acc)
      zero l1 =
    List.fold_right (fun j acc =>
      add (List.fold_right (fun k acc' => add (F k j) acc') zero l2) acc)
      zero l1.
  Proof.
    intros l1 l2 F.
    apply (@fold_right_congr R U l1
      (fun k => List.fold_right (fun j acc' => add (F j k) acc') zero l2)
      (fun j => List.fold_right (fun k acc' => add (F k j) acc') zero l2)).
    intro x.
    apply (@fold_right_congr R U l2
      (fun j => F j x) (fun k => F k x)).
    intro y. reflexivity.
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
    (* f(j,k) := scale (M1 i k) (scale (M2 k j) (v j)) *)
    set (f := fun (j k : Node) => scale (M1 i k) (scale (M2 k j) (v j))).
    (* g(j,k) := scale (M1 i j) (scale (M2 j k) (v k)) *)
    set (g := fun (j k : Node) => scale (M1 i j) (scale (M2 j k) (v k))).

    (* Step 1: LHS = sum_j sum_k f(j,k) *)
    assert (HL :
      List.fold_right (fun j acc => add (scale
        (List.fold_right (fun k acc2 => M1 i k * M2 k j + acc2) 0 l) (v j)) acc)
        zero l =
      List.fold_right (fun j acc =>
        add (List.fold_right (fun k acc' => add (f j k) acc') zero l) acc)
        zero l).
    { apply (fold_right_congr l
        (fun j => scale (List.fold_right (fun k acc2 => M1 i k * M2 k j + acc2) 0 l) (v j))
        (fun j => List.fold_right (fun k acc' => add (f j k) acc') zero l)).
      intro j.
      rewrite (fold_right_scale_r_sum l (fun k => M1 i k * M2 k j) (v j)).
      apply (fold_right_congr l
        (fun k => scale (M1 i k * M2 k j) (v j))
        (fun k => f j k)).
      intro k. unfold f. rewrite scale_assoc. reflexivity.
    }

    (* Step 2: RHS = sum_j sum_k g(j,k) *)
    assert (HR :
      List.fold_right (fun j acc => add (scale (M1 i j)
        (List.fold_right (fun k acc2 => add (scale (M2 j k) (v k)) acc2) zero l)) acc)
        zero l =
      List.fold_right (fun j acc =>
        add (List.fold_right (fun k acc' => add (g j k) acc') zero l) acc)
        zero l).
    { apply (fold_right_congr l
        (fun j => scale (M1 i j)
          (List.fold_right (fun k acc2 => add (scale (M2 j k) (v k)) acc2) zero l))
        (fun j => List.fold_right (fun k acc' => add (g j k) acc') zero l)).
      intro j.
      rewrite (fold_right_scale_distr (fun k => scale (M2 j k) (v k)) l (M1 i j)).
      apply (fold_right_congr l
        (fun k => scale (M1 i j) (scale (M2 j k) (v k)))
        (fun k => g j k)).
      intro k. unfold g. reflexivity.
    }

    (* Step 3: sum_j sum_k g(j,k) = sum_k sum_j g(j,k) via double commute *)
    assert (Hcomm :
      List.fold_right (fun j acc =>
        add (List.fold_right (fun k acc' => add (g j k) acc') zero l) acc)
        zero l =
      List.fold_right (fun k acc =>
        add (List.fold_right (fun j acc' => add (g j k) acc') zero l) acc)
        zero l).
    { apply (fold_right_double_commute l g). }

    (* Step 4: sum_k sum_j g(j,k) = sum_j sum_k g(k,j) (alpha-rename) *)
    assert (H_alpha :
      List.fold_right (fun k acc =>
        add (List.fold_right (fun j acc' => add (g j k) acc') zero l) acc)
        zero l =
      List.fold_right (fun j acc =>
        add (List.fold_right (fun k acc' => add (g k j) acc') zero l) acc)
        zero l).
    { apply (fold_right_nest_alpha l l g). }

    (* Step 5: g(k,j) = f(j,k), so sum_j sum_k g(k,j) = sum_j sum_k f(j,k) *)
    assert (Hgf :
      List.fold_right (fun j acc =>
        add (List.fold_right (fun k acc' => add (g k j) acc') zero l) acc)
        zero l =
      List.fold_right (fun j acc =>
        add (List.fold_right (fun k acc' => add (f j k) acc') zero l) acc)
        zero l).
    { apply (@fold_right_congr R U l
        (fun j => List.fold_right (fun k acc' => add (g k j) acc') zero l)
        (fun j => List.fold_right (fun k acc' => add (f j k) acc') zero l)).
      intro j. apply (@fold_right_congr R U l
        (fun k => g k j) (fun k => f j k)).
      intro k.
      cbv delta [g f].
      reflexivity.
    }

    (* Chain: LHS = sum_j sum_k f = sum_j sum_k g(k,j) = sum_k sum_j g(j,k) = sum_j sum_k g(j,k) = RHS *)
    rewrite HL.  rewrite <-Hgf, <- Hcomm, <- HR.
    reflexivity.
  Qed.


  (** Identity-matrix action yields zero on nodes not in the list. *)
  Lemma fold_right_identity_zero {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (v : Node -> U) (i : Node),
    ~ In i l ->
    List.fold_right (fun j acc => add (scale (I i j) (v j)) acc) zero l = zero.
  Proof.
    induction l as [|j js IH]; simpl; intros v i Hnotin.
    - reflexivity.
    - unfold I.
      destruct (fin_eq_dec i j) as [Heq | Hneq].
      + (* i = j case: contradiction with ~ In i (j::js) *)
        subst. exfalso. apply Hnotin. simpl. auto.
      + (* i ≠ j case: I i j = 0 *)
        rewrite scale_zero_r, add0r.
        apply IH.
        intro Hin. apply Hnotin. simpl. auto.
  Qed.

  (** Identity-matrix action returns the vector component at the
      matching index. *)
  Lemma fold_right_identity {R : Semiring.type} {U : Semimodule.type R} :
    forall (l : list Node) (v : Node -> U) (i : Node),
    NoDup l -> In i l ->
    List.fold_right (fun j acc => add (scale (I i j) (v j)) acc) zero l = v i.
  Proof.
    induction l as [|j js IH]; simpl; intros v i Hdup Hin.
    - inversion Hin.
    - inversion_clear Hdup as [|? ? Hnotin Hdup'].
      unfold I.
      destruct (fin_eq_dec i j) as [Heq | Hneq].
      + (* i = j case: I i j = 1 *)
        subst.
        rewrite scale_one.
        transitivity (add (v j) zero).
        * apply (f_equal (add (v j))).
          apply (fold_right_identity_zero js v j Hnotin).
        * apply addr0.
      + (* i ≠ j case: I i j = 0 *)
        rewrite scale_zero_r, add0r.
        destruct Hin as [Heq | Hin_js].
        * exfalso. apply Hneq. symmetry. exact Heq.
        * apply (IH v i Hdup' Hin_js).
  Qed.


  (** The geometric sum at the node-count bound satisfies the Kleene
      fixpoint equation: [A* = I + A · A*]. *)
  Lemma geom_sum_fixpoint {R : BoundedSemiring.type} :
    forall (m : @Matrix Node R),
    (forall u v : Node, u = v -> m u v = 1) ->
    forall (c d : Node),
    geom_sum m (length (@elements Node) - 1)%nat c d =
    matrix_add I (matrix_mul m (geom_sum m (length (@elements Node) - 1)%nat)) c d.
  Proof.
    intros m Hdiag c d.
    pose proof (geom_sum_stable_after_node_bound 1 m Hdiag c d) as Hstable.
    rewrite Hstable.
    pose proof (elements_two_or_more (s := Node)) as Hlen_pos.
    assert (Harith : 1 + length (@elements Node) - 1 = S (length (@elements Node) - 1)) by lia.
    rewrite Harith.
    rewrite (geom_sum_S (length (@elements Node) - 1) m c d).
    reflexivity.
  Qed.

  (** Nested fold-right alpha-rename for semiring-valued sums. *)
  Lemma fold_right_alpha_R {R : Semiring.type} (l : list Node) (F : Node -> Node -> R) (j : Node) :
    List.fold_right (fun x y => F x j + y) 0 l =
    List.fold_right (fun k acc2 => F k j + acc2) 0 l.
  Proof.
    induction l as [|a l' IH]; simpl; [reflexivity|].
    apply (f_equal (fun t => F a j + t)). apply IH.
  Qed.

  (** Kleene fixed point: [x = A* · b ⇔ x = A · x + b]. *)
  Theorem kleene_fixed_point {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (b x : @Vector R U),
    (forall u v : Node, u = v -> A u v = 1) ->
    (forall i : Node, x i = matrix_vector_action
      (geom_sum A (length (@elements Node) - 1)%nat) b i) ->
    forall (i : Node), x i = vec_add (matrix_vector_action A x) b i.
  Proof.
    intros A b x Hdiag Hx i.
    set (Astar := geom_sum A (length (@elements Node) - 1)%nat).
    pose proof (geom_sum_fixpoint A Hdiag) as Hstar.

    (* Replace x i with (Astar·b) i, then unfold definitions *)
    rewrite (Hx i).
    unfold vec_add, matrix_vector_action.

    (* Goal: (Astar·b) i = (A·x) i + b i *)

    (* Step 1: (Astar·b) i = ((I + A·Astar)·b) i via fixpoint *)
    assert (H1 :
      List.fold_right (fun j acc => add (scale (Astar i j) (b j)) acc) zero elements =
      List.fold_right (fun j acc =>
        add (scale ((matrix_add I (matrix_mul A Astar)) i j) (b j)) acc) zero elements).
    { apply (fold_right_congr elements
        (fun j => scale (Astar i j) (b j))
        (fun j => scale ((matrix_add I (matrix_mul A Astar)) i j) (b j))).
      intro j. apply (f_equal (fun m => scale m (b j))). apply Hstar. }
    apply (eq_trans H1). clear H1.

    (* LHS = ((I + A·Astar)·b) i *)

    (* Step 2: distribute scale over matrix addition *)
    unfold matrix_add at 1.
    rewrite (fold_right_scale_add elements
      (fun j => I i j) (fun j => (matrix_mul A Astar) i j) b).

    (* LHS = (I·b) i + ((A·Astar)·b) i *)

    (* Step 3: I·b = b via identity *)
    assert (H_id :
      List.fold_right (fun j acc => add (scale (I i j) (b j)) acc) zero elements = b i).
    { apply (fold_right_identity elements b i
        (elements_nodup (s := Node))
        (elements_complete (s := Node) i)). }
    apply (eq_trans (f_equal2 add H_id eq_refl)).

    (* LHS = b i + ((A·Astar)·b) i *)

    (* Step 4: prove ((A·Astar)·b) i = (A·x) i, then add b i *)
    cut (
      List.fold_right (fun j acc => add (scale ((matrix_mul A Astar) i j) (b j)) acc) zero elements =
      List.fold_right (fun j acc => add (scale (A i j) (x j)) acc) zero elements).
    - intro Hcore.
      apply (eq_trans (f_equal (fun s => add (b i) s) Hcore)).
      apply (addC (b i) _).
    - (* Core equality: ((A·Astar)·b) i = (A·x) i *)
      unfold matrix_mul, sum.
      refine (eq_trans _ (eq_trans (fold_right_mul_assoc elements A Astar b i) _)).
      + (* alpha-x-y = alpha-k-acc2 *)
        apply (fold_right_congr elements
          (fun j => scale
            (List.fold_right (fun x y => A i x * Astar x j + y) 0 elements) (b j))
          (fun j => scale
            (List.fold_right (fun k acc2 => A i k * Astar k j + acc2) 0 elements) (b j))).
        intro j. apply (f_equal (fun s => scale s (b j))).
        apply (fold_right_alpha_R elements (fun x y => A i x * Astar x y) j).
      + (* Astar-fold = A·x *)
        apply (fold_right_congr elements
          (fun j => scale (A i j)
            (List.fold_right (fun k acc0 => add (scale (Astar j k) (b k)) acc0) zero elements))
          (fun j => scale (A i j) (x j))).
        intro j. apply (f_equal (scale (A i j))). symmetry. apply Hx.
  Qed.

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
    intros A b x Hfix i.
    unfold Orel, vec_add in *.
    rewrite (Hfix i).
    (* Goal: b i + (A·x i + b i) = A·x i + b i *)
    rewrite <- (addA (b i) (matrix_vector_action A x i) (b i)).
    rewrite (addC (b i) (matrix_vector_action A x i)).
    rewrite (addA (matrix_vector_action A x i) (b i) (b i)).
    rewrite (add_idem_module (b i)).
    reflexivity.
  Qed.


  (** From [x = A·x + b] and bounded idempotence, derive [A·x ≤ x]. *)
  Lemma absorb_Ax_fixpoint {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (b x : @Vector R U),
    (forall i : Node, x i = vec_add (matrix_vector_action A x) b i) ->
    forall i : Node, Orel (matrix_vector_action A x i) (x i).
  Proof.
    intros A b x Hfix i.
    unfold Orel, vec_add in *.
    rewrite (Hfix i).
    (* Goal: (A·x) i + ((A·x) i + b i) = (A·x) i + b i *)
    rewrite <- (addA (matrix_vector_action A x i)
                    (matrix_vector_action A x i) (b i)).
    rewrite (add_idem_module (matrix_vector_action A x i)).
    reflexivity.
  Qed.

  (** Orel transitivity for any commutative monoid (generalizes
      [orel_trans] in [OrelN.v] from [Semiring] to [CommutativeMonoid]). *)
  Lemma orel_trans_cm {V : CommutativeMonoid.type} (a b c : V) :
    Orel a b -> Orel b c -> Orel a c.
  Proof.
    unfold Orel. intros Hab Hbc.
    rewrite <- Hbc at 1.
    rewrite <- addA, Hab, Hbc.
    reflexivity.
  Qed.

  (** Matrix-vector action distributes over vector addition:
      [A·(u + v) = A·u + A·v]. *)
  Lemma mva_add_distr {R : Semiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (u v : @Vector R U) (i : Node),
    matrix_vector_action A (vec_add u v) i =
    vec_add (matrix_vector_action A u) (matrix_vector_action A v) i.
  Proof.
    intros A u v i.
    unfold matrix_vector_action, vec_add.
    apply (eq_trans (fold_right_congr elements
      (fun j => scale (A i j) (u j + v j))
      (fun j => add (scale (A i j) (u j)) (scale (A i j) (v j)))
      (fun j => scale_distr_v (s := U) (A i j) (u j) (v j)))).
    apply fold_right_split.
  Qed.

  (** Matrix-vector action is monotone with respect to the Orel order.
      If [v ≤ u] pointwise, then [A·v ≤ A·u] pointwise. *)
  Lemma mva_monotone_Orel {R : Semiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (u v : @Vector R U),
    (forall j, Orel (v j) (u j)) ->
    forall i, Orel (matrix_vector_action A v i) (matrix_vector_action A u i).
  Proof.
    intros A u v Hle i.
    unfold Orel, matrix_vector_action in *.
    (* Goal: (Σ scale (A i j) (v j)) + (Σ scale (A i j) (u j)) = Σ scale (A i j) (u j) *)
    refine (eq_trans (eq_sym (fold_right_split elements
      (fun j => scale (A i j) (v j))
      (fun j => scale (A i j) (u j)))) _).
    (* Goal: Σ (scale (A i j) (v j) + scale (A i j) (u j)) = Σ scale (A i j) (u j) *)
    apply (@fold_right_congr R U elements
      (fun j => add (scale (A i j) (v j)) (scale (A i j) (u j)))
      (fun j => scale (A i j) (u j))).
    intro j.
    setoid_rewrite <- (scale_distr_v (s := U) (A i j) (v j) (u j)).
    setoid_rewrite (Hle j).
    reflexivity.
  Qed.



  (** Absorption lifts through matrix powers:
      if [b ≤ x] and [A·x ≤ x], then [A^k·b ≤ x] for all [k]. *)
  Lemma matrix_pow_absorb {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (x b : @Vector R U) (k : nat),
    (forall i, Orel (b i) (x i)) ->
    (forall i, Orel (matrix_vector_action A x i) (x i)) ->
    forall i, Orel (matrix_vector_action (pow A k) b i) (x i).
  Proof.
    intros A x b k Hb HAx.
    induction k as [|k IH]; simpl.
    - (* k = 0: pow A 0 = I, so I·b = b *)
      intro i.
      unfold matrix_vector_action.
      setoid_rewrite (fold_right_identity elements b i
        (elements_nodup (s := Node))
        (elements_complete (s := Node) i)).
      apply Hb.
    - (* k = S k: pow A (S k) = matrix_mul A (pow A k) *)
      intro i.
      unfold Orel, matrix_vector_action in *.

      (* Prove ((A·A^k)·b) i = (A·(A^k·b)) i *)
      assert (H_mul_assoc :
        List.fold_right (fun j acc =>
          add (scale ((matrix_mul A (pow A k)) i j) (b j)) acc) zero elements =
        List.fold_right (fun j acc =>
          add (scale (A i j)
            (List.fold_right (fun k0 acc0 =>
              add (scale ((pow A k) j k0) (b k0)) acc0) zero elements)) acc)
          zero elements).
      { unfold matrix_mul, sum.
        apply (eq_trans
          (fold_right_congr elements
            (fun j => scale
              (List.fold_right (fun x y => A i x * (pow A k) x j + y) 0 elements) (b j))
            (fun j => scale
              (List.fold_right (fun k0 acc2 => A i k0 * (pow A k) k0 j + acc2) 0 elements) (b j))
            (fun j => f_equal (fun s => scale s (b j))
              (fold_right_alpha_R elements (fun x y => A i x * (pow A k) x y) j)))).
        apply (fold_right_mul_assoc elements A (pow A k) b i). }

      (* Apply the associativity to the LHS of the goal *)
      apply (eq_trans (f_equal (fun s => add s (x i)) H_mul_assoc)).

      (* Goal: (A·(A^k·b) i) + x i = x i *)
      pose proof (mva_monotone_Orel A x
        (matrix_vector_action (pow A k) b) IH i) as H_mid.
      unfold Orel, matrix_vector_action in H_mid.
      (* Transitivity: (A·(A^k·b) i) + x i = x i *)
      rewrite <- (HAx i) at 1.
      rewrite <- (addA _ (matrix_vector_action A x i) (x i)).
      setoid_rewrite H_mid. 
      setoid_rewrite (HAx i).
      reflexivity.
  Qed.



  (** Right matrix fixpoint: [A* = I + A* · A]. *)
  Lemma geom_sum_fixpoint_right {R : BoundedSemiring.type} :
    forall (m : @Matrix Node R),
    (forall u v : Node, u = v -> m u v = 1) ->
    forall (c d : Node),
    geom_sum m (length (@elements Node) - 1)%nat c d =
    matrix_add I (matrix_mul (geom_sum m (length (@elements Node) - 1)%nat) m) c d.
  Proof.
    intros m Hdiag c d.
    pose proof (geom_sum_stable_after_node_bound 1 m Hdiag c d) as Hstable.
    rewrite Hstable.
    pose proof (elements_two_or_more (s := Node)) as Hlen_pos.
    assert (Harith : 1 + length (@elements Node) - 1 = S (length (@elements Node) - 1)) by lia.
    rewrite Harith.
    rewrite (geom_sum_S_right (length (@elements Node) - 1) m c d).
    reflexivity.
  Qed.

  
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
    intros A b x Hdiag Hx i.
    set (Astar := geom_sum A (length (@elements Node) - 1)%nat).
    pose proof (geom_sum_fixpoint_right A Hdiag) as Hstar.

    (* Replace x i with (Astar·b) i, then unfold definitions *)
    rewrite (Hx i).
    unfold vec_add, matrix_vector_action.

    (* Goal: (Astar·b) i = (Astar·(A·b)) i + b i *)

    (* Step 1: (Astar·b) i = ((I + Astar·A)·b) i via fixpoint *)
    assert (H1 :
      List.fold_right (fun j acc => add (scale (Astar i j) (b j)) acc) zero elements =
      List.fold_right (fun j acc =>
        add (scale ((matrix_add I (matrix_mul Astar A)) i j) (b j)) acc) zero elements).
    { apply (fold_right_congr elements
        (fun j => scale (Astar i j) (b j))
        (fun j => scale ((matrix_add I (matrix_mul Astar A)) i j) (b j))).
      intro j. apply (f_equal (fun m => scale m (b j))). apply Hstar. }
    apply (eq_trans H1). clear H1.

    (* LHS = ((I + Astar·A)·b) i *)

    (* Step 2: distribute scale over matrix addition *)
    unfold matrix_add at 1.
    rewrite (fold_right_scale_add elements
      (fun j => I i j) (fun j => (matrix_mul Astar A) i j) b).

    (* LHS = (I·b) i + ((Astar·A)·b) i *)

    (* Step 3: I·b = b via identity *)
    assert (H_id :
      List.fold_right (fun j acc => add (scale (I i j) (b j)) acc) zero elements = b i).
    { apply (fold_right_identity elements b i
        (elements_nodup (s := Node))
        (elements_complete (s := Node) i)). }
    apply (eq_trans (f_equal2 add H_id eq_refl)).

    (* LHS = b i + ((Astar·A)·b) i *)

    (* Step 4: ((Astar·A)·b) i = (Astar·(A·b)) i via associativity *)
    cut (
      List.fold_right (fun j acc => add (scale ((matrix_mul Astar A) i j) (b j)) acc) zero elements =
      List.fold_right (fun j acc => add (scale (Astar i j)
        (List.fold_right (fun k acc0 => add (scale (A j k) (b k)) acc0) zero elements)) acc)
        zero elements).
    - intro Hcore.
      apply (eq_trans (f_equal (fun s => add (b i) s) Hcore)).
      apply (addC (b i) _).
    - (* Core equality: ((Astar·A)·b) i = (Astar·(A·b)) i *)
      unfold matrix_mul, sum.
      refine (eq_trans _ (eq_trans (fold_right_mul_assoc elements Astar A b i) _)).
      + (* alpha-x-y = alpha-k-acc2 *)
        apply (fold_right_congr elements
          (fun j => scale
            (List.fold_right (fun x y => Astar i x * A x j + y) 0 elements) (b j))
          (fun j => scale
            (List.fold_right (fun k acc2 => Astar i k * A k j + acc2) 0 elements) (b j))).
        intro j. apply (f_equal (fun s => scale s (b j))).
        apply (fold_right_alpha_R elements (fun x y => Astar i x * A x y) j).
      + reflexivity.
  Qed.

  (** Leastness of the Kleene fixed point: [x = A·x + b] implies
      [A*·b ≤ x] in the Orel order, i.e., [A*·b] is below every solution. *)
  Theorem kleene_fixed_point_least {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (b x : @Vector R U),
    (forall u v : Node, u = v -> A u v = 1) ->
    (forall i : Node, x i = vec_add (matrix_vector_action A x) b i) ->
    forall (i : Node),
    Orel (matrix_vector_action (geom_sum A (length (@elements Node) - 1)%nat) b i) (x i).
  Proof.
    intros A b x Hdiag Hfix i.
    unfold Orel, vec_add in *.
    set (Astar := fun n => geom_sum A n).

    (* From the fixpoint, derive b ≤ x and A·x ≤ x *)
    pose proof (absorb_b_fixpoint A b x Hfix) as Hb_all.
    pose proof (absorb_Ax_fixpoint A b x Hfix) as HAx_all.
    pose proof (Hb_all i) as Hb.
    pose proof (HAx_all i) as HAx.

    (* Prove by induction: for all n, x i + ((Astar n)·b) i = x i *)
    assert (H_all : forall n : nat,
      add (x i)
        (List.fold_right (fun j acc => add (scale ((Astar n) i j) (b j)) acc) zero elements)
      = x i).
    { induction n as [|n IH]; simpl.
      - (* n = 0: Astar 0 = I, I·b = b *)
        unfold Astar, matrix_vector_action.
        setoid_rewrite (fold_right_identity elements b i
          (elements_nodup (s := Node))
          (elements_complete (s := Node) i)).
        (* Goal: x i + b i = x i, but Hb: b i + x i = x i *)
        apply (eq_trans (addC (x i) (b i))). apply Hb.
      - (* n → S n: Astar (S n) = Astar n + pow A (S n) *)
        unfold Astar at 1.
        (* Distribute: (Astar n + pow A (S n))·b = (Astar n)·b + pow A (S n)·b *)
        unfold matrix_add.
        apply (eq_trans (f_equal (fun s => add (x i) s)
          (fold_right_scale_add elements
            (fun j => (geom_sum A n) i j)
            (fun j => (pow A (S n)) i j) b))).
        (* Goal: x i + ((Astar n)·b i + (pow A (S n))·b i) = x i *)
        rewrite <- (addA (x i) _ _).
        unfold Astar in IH.
        rewrite IH.
        (* Goal: x i + (pow A (S n))·b i = x i *)
        apply (eq_trans (addC (x i) _)).
        apply (matrix_pow_absorb A x b (S n) Hb_all HAx_all i). }

    unfold matrix_vector_action.
    transitivity (add (x i)
      (List.fold_right (fun j acc => add (scale ((Astar (length (@elements Node) - 1)) i j) (b j)) acc) zero elements)).
    - apply (addC _ (x i)).
    - apply (H_all (length (@elements Node) - 1)%nat).
  Qed.

  (** Orel antisymmetry holds in any commutative monoid:
      [a ≤ b] and [b ≤ a] imply [a = b].  The proof uses only commutativity. *)
  Lemma orel_antisym_cm {V : CommutativeMonoid.type} (a b : V) :
    Orel a b -> Orel b a -> a = b.
  Proof.
    unfold Orel. intros Hab Hba.
    rewrite <- Hba, addC.
    exact Hab.
  Qed.

  (** Post-fixpoint induction axiom for the Kleene star.  If [x] is a
      post-fixpoint of [z ↦ A·z + b] (i.e., [x ≤ A·x + b]), then [x] is
      bounded above by [A*·b].  This is the dual of [kleene_fixed_point_least]
      and not derivable from [BoundedSemiring] alone. 
      Kleene fixed point uniqueness: any two solutions of [x = A·x + b]
      are pointwise equal.  Proved using [star_post_fixpoint]. *)

  Theorem kleene_fixed_point_unique {R : BoundedSemiring.type} 
    {U : Semimodule.type R} : 
    forall (A : Node -> Node -> R) (b x y : @Vector R U),
    (forall (A : Node -> Node -> R) (x b : Node -> U),
    (forall i, Orel (x i) (vec_add (matrix_vector_action A x) b i)) ->
    forall i, Orel (x i)
      (matrix_vector_action (geom_sum A (length (@elements Node) - 1)) b i)) -> 
    (forall u v : Node, u = v -> A u v = 1) ->
    (forall i, x i = vec_add (matrix_vector_action A x) b i) ->
    (forall i, y i = vec_add (matrix_vector_action A y) b i) ->
    forall i, x i = y i.
  Proof.
    intros A b x y star_post_fixpoint Hdiag Hx Hy i.
    (* From the fixpoint: A*·b ≤ x (by kleene_fixed_point_least) *)
    pose proof (kleene_fixed_point_least A b x Hdiag Hx i) as Hx_least.
    pose proof (kleene_fixed_point_least A b y Hdiag Hy i) as Hy_least.
    (* Also: x ≤ A·x + b = x, so x ≤ A·x + b holds (by idempotence) *)
    assert (Hx_post : forall i, Orel (x i) (vec_add (matrix_vector_action A x) b i)).
    { intro j. unfold Orel, vec_add in *.
      rewrite (Hx j).
      apply add_idem_module. }
    assert (Hy_post : forall i, Orel (y i) (vec_add (matrix_vector_action A y) b i)).
    { intro j. unfold Orel, vec_add in *.
      rewrite (Hy j).
      apply add_idem_module. }
    (* By star_post_fixpoint: x ≤ A*·b and y ≤ A*·b *)
    pose proof (star_post_fixpoint A x b Hx_post i) as Hx_star.
    pose proof (star_post_fixpoint A y b Hy_post i) as Hy_star.
    (* Antisymmetry: Astar·b = x and Astar·b = y, so x = y *)
    pose proof (orel_antisym _ _ Hx_least Hx_star) as Hx_eq.
    pose proof (orel_antisym _ _ Hy_least Hy_star) as Hy_eq.
    apply (eq_trans (eq_sym Hx_eq) Hy_eq).
  Qed.

  (** Kleene star idempotence (vector-action level):
      [A*·(A*·b) = A*·b].  Requires the full strength of Kozen's
      [star_induction] with an inequality hypothesis; [star_post_fixpoint]
      alone is insufficient. *)
  Lemma geom_sum_idempotent_action {R : BoundedSemiring.type} {U : Semimodule.type R} :
    forall (A : Node -> Node -> R) (b : @Vector R U),
    (forall (A : Node -> Node -> R) (x b : Node -> U),
    (forall i, Orel (x i) (vec_add (matrix_vector_action A x) b i)) ->
    forall i, Orel (x i)
      (matrix_vector_action (geom_sum A (length (@elements Node) - 1)) b i)) ->
    (forall u v : Node, u = v -> A u v = 1) ->
    forall i,
    matrix_vector_action (geom_sum A (length (@elements Node) - 1))
      (matrix_vector_action (geom_sum A (length (@elements Node) - 1)) b) i =
    matrix_vector_action (geom_sum A (length (@elements Node) - 1)) b i.
  Proof.
    intros A b star_post Hdiag i.
    set (Astar := geom_sum A (length (@elements Node) - 1)).
    set (x := fun i : Node => matrix_vector_action Astar b i).

    (* 1. From kleene_fixed_point: x = A·x + b *)
    pose proof (kleene_fixed_point A b x Hdiag (fun _ => eq_refl)) as Hx_fix.
    (* Hx_fix : forall i, x i = vec_add (matrix_vector_action A x) b i *)

    (* 2. From idempotence: x = A·x + x *)
    assert (Hx_fix_self : forall i, x i = vec_add (matrix_vector_action A x) x i).
    { intro j.
      rewrite vec_add_pointwise.
      (* Goal: x j = (matrix_vector_action A x) j + x j *)
      apply eq_sym.
      (* Goal: (matrix_vector_action A x) j + x j = x j *)
      rewrite (Hx_fix j).
      (* Goal: (matrix_vector_action A x) j + vec_add (matrix_vector_action A x) b j = x j *)
      rewrite (vec_add_pointwise (matrix_vector_action A x) b j).
      (* Goal: (matrix_vector_action A x) j + ((matrix_vector_action A x) j + b j) = x j *)
      rewrite <- (addA ((matrix_vector_action A x) j) ((matrix_vector_action A x) j) (b j)).
      (* Goal: ((matrix_vector_action A x) j + (matrix_vector_action A x) j) + b j = x j *)
      rewrite (add_idem_module ((matrix_vector_action A x) j)).
      (* Goal: (matrix_vector_action A x) j + b j = x j *)
      rewrite <- (vec_add_pointwise (matrix_vector_action A x) b j).
      (* Goal: vec_add (matrix_vector_action A x) b j = x j *)
      rewrite <- (Hx_fix j).
      (* Goal: vec_add (matrix_vector_action A x) b j = vec_add (matrix_vector_action A x) b j *)
      reflexivity. }

    (* 3. kleene_fixed_point_least with (b:=x, x:=x) gives A*·x ≤ x *)
    pose proof (kleene_fixed_point_least A x x Hdiag Hx_fix_self i) as H_least.
    unfold x, Astar in H_least.

    (* 4. b ≤ x via absorb_b_fixpoint *)
    pose proof (absorb_b_fixpoint A b x Hx_fix) as Hb_le_x.

    (* 5. Prove x ≤ A·x + x to apply star_post_fixpoint *)
    assert (Hx_post : forall i, Orel (x i) (vec_add (matrix_vector_action A x) x i)).
    { intro j. unfold Orel, vec_add.
      (* Goal: x j + (A·x j + x j) = A·x j + x j *)
      rewrite <- (addA (x j) (matrix_vector_action A x j) (x j)).
      (* Goal: (x j + A·x j) + x j = A·x j + x j *)
      rewrite (addC (x j) (matrix_vector_action A x j)).
      (* Goal: (A·x j + x j) + x j = A·x j + x j *)
      rewrite (addA (matrix_vector_action A x j) (x j) (x j)).
      (* Goal: A·x j + (x j + x j) = A·x j + x j *)
      rewrite (add_idem_module (x j)).
      reflexivity. }

    (* 6. star_post_fixpoint gives x ≤ A*·x *)
    pose proof (star_post A x x Hx_post i) as H_star.
    unfold Astar in H_star.

    (* 7. Antisymmetry: A*·x = x *)
    apply (orel_antisym_cm _ _ H_least H_star).
  Qed.


End Semimodule.




