From Stdlib Require Import List Utf8
  Lia.
From Semiring Require Import Definitions
  Listprop Path Mat Orel.
Import ListNotations.


(* ========================================================================= *)
(*  SECTION 1 — Abstract semimodule: two-sorted axiomatisation               *)
(* ========================================================================= *)

Section Semimodule_def.

  (* Two-sorted structure *)
  Variables (R V : Type).

  (* ----------------------------------------------------------------------- *)
  (* 1a. Semiring (R, ⊕, ⊗, 0, 1)                                            *)
  (* ----------------------------------------------------------------------- *)

  Variables
    (zeroR oneR : R)
    (plusR mulR : binary_op R)
    (eqR  : brel R).

  (* ----------------------------------------------------------------------- *)
  (* 1b. Commutative monoid (V, ⊕_V, 0_V)                                     *)
  (* ----------------------------------------------------------------------- *)

  Variables
    (zeroV : V)
    (plusV : binary_op V)
    (eqV  : brel V).

  (* ----------------------------------------------------------------------- *)
  (* 1c. Scalar multiplication  ⊙ : V → R → V                                 *)
  (* ----------------------------------------------------------------------- *)

  (* We use RIGHT scalar: (v ⊙ a).  This avoids requiring commutativity of   *)
  (* mulR in the function-space instantiation where (v ⊙ a)_n := v_n ⊗ a.    *)

  Variable scale : R -> V -> V.

  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (finN : list Node).


  (* Now we scale this to matrix-vector semimodule. *)
  Definition Vector : Type := Node -> V. 

  Definition vec_zero : Vector := fun _ => zeroV.
  Definition vec_add  (x y : Vector) : Vector := fun i => plusV (x i) (y i).
  Definition vec_scale (a : R) (v : Vector) : Vector := fun i => scale a (v i).

  (* (m · v)_i  :=  Σ_{j ∈ finN}  (v_j) ⊙ m_{i,j}                            *)
  Definition matrix_vector_action (m : Matrix Node R) (v : Vector) : Vector := 
    fun (i : Node) =>
      List.fold_right
        (fun j acc => plusV (scale (m i j) (v j)) acc)
        zeroV
        finN.

  (* Efficient list-based version: map each row → fold (scale v_j m_{i,j})    *)
  Definition matrix_vector_action_eff (m : list (list R)) (v : list V) : list V :=
    List.map (fun row =>
      List.fold_right plusV zeroV
        (List.map (fun '(r_elem, v_elem) => scale r_elem v_elem)
          (List.combine row v))) m.

  (* Look up a node in parallel with a value list ordered by finN             *)
  Fixpoint list_lookup (keys : list Node) (vals : list V) (key : Node) : V :=
    match keys, vals with
    | k :: ks, v :: vs => if eqN key k then v else list_lookup ks vs key
    | _, _ => zeroV
    end.

  (* Functional wrapper: convert Matrix/Vector to lists, compute, convert back *)
  Definition matrix_vector_action_eff_fun (m : Matrix Node R) (v : Vector) : Vector :=
    let la := List.map (fun r => List.map (fun c => m r c) finN) finN in 
    let va := List.map (fun r => v r) finN in
    let result := matrix_vector_action_eff la va in
    fun i => list_lookup finN result i.

End Semimodule_def.

(* ========================================================================= *)
(*  SECTION 2 — Generic list lemmas (parameterized by any node list l)       *)
(* ========================================================================= *)

Section GenProofs.

  Variables
    (Node V R : Type)
    (eqN : brel Node) (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (eqR : brel R) (refR : brel_reflexive R eqR)
    (zeroV : V) (plusV : binary_op V) (eqV : brel V)
    (refV : brel_reflexive V eqV) (trnV : brel_transitive V eqV)
    (congrPV : bop_congruence V eqV plusV)
    (scale : R -> V -> V)
    (congrS : forall s1 s2 t1 t2, eqR s1 t1 = true -> eqV s2 t2 = true ->
               eqV (scale s1 s2) (scale t1 t2) = true).

  (* Generic list_lookup_map: works for any list l                           *)
  Lemma list_lookup_map_gen : forall (f : Node -> V) (l : list Node),
    (forall x y, eqN x y = true -> eqV (f x) (f y) = true) ->
    forall (i : Node),
    no_dup Node eqN l = true ->
    in_list eqN l i = true ->
    eqV (list_lookup V zeroV Node eqN l (List.map f l) i) (f i) = true.
  Proof.
    intros f l H_cong i H_dup H_in.
    revert i H_in.
    induction l as [|j js IH]; simpl; intros i H_in.
    - discriminate H_in.
    - simpl in H_dup.
      apply Bool.andb_true_iff in H_dup.
      destruct H_dup as [H_notin H_dup_t].
      case_eq (eqN i j); intros Heq.
      + apply (H_cong j i). apply symN. apply Heq.
      + simpl in H_in. apply Bool.orb_true_iff in H_in.
        destruct H_in as [H_eq | H_in_js].
        * rewrite Heq in H_eq. inversion H_eq.
        * apply (IH H_dup_t i H_in_js).
  Qed.

  (* Generic: the efficient computation looked up equals the functional one   *)

  (* combine + map + fold_right = direct fold_right over the same list         *)
  Lemma combine_fold_eq : forall (l : list Node) (A : Node -> Node -> R) (x : Node -> V) (r : Node),
    eqV
      (List.fold_right plusV zeroV
         (List.map (fun '(re, ve) => scale re ve)
            (List.combine (List.map (fun c : Node => A r c) l)
                          (List.map (fun n : Node => x n) l))))
      (List.fold_right (fun j acc => plusV (scale (A r j) (x j)) acc) zeroV l)
    = true.
  Proof.
    intros l A x r.
    induction l as [|j js IH]; simpl.
    - apply refV.
    - apply (congrPV _ _ _ _
        (congrS (A r j) (x j) (A r j) (x j) (refR _) (refV _)) IH).
  Qed.

  (* Row congruence: if A j = A i pointwise, fold_right results are equal     *)
  Lemma fold_right_row_congr : forall (l : list Node) (A : Node -> Node -> R)
      (x : Node -> V) (j i : Node),
    (forall k, eqR (A j k) (A i k) = true) ->
    eqV (List.fold_right (fun k acc => plusV (scale (A j k) (x k)) acc) zeroV l)
        (List.fold_right (fun k acc => plusV (scale (A i k) (x k)) acc) zeroV l)
    = true.
  Proof.
    intros l A x j i H_col.
    induction l as [|k ks IH]; simpl.
    - apply refV.
    - apply (congrPV _ _ _ _
        (congrS (A j k) (x k) (A i k) (x k) (H_col k) (refV (x k))) IH).
  Qed.

  (* eff_row is congruent: eqN u v = true → eff_row u = eff_row v            *)
  Lemma eff_row_congr : forall (l : list Node) (A : Node -> Node -> R) (x : Node -> V) (u v : Node),
    eqN u v = true ->
    (forall i j k, eqN i j = true -> eqR (A i k) (A j k) = true) ->
    eqV
      (List.fold_right plusV zeroV
         (List.map (fun '(re, ve) => scale re ve)
            (List.combine (List.map (fun c : Node => A u c) l)
                          (List.map (fun n : Node => x n) l))))
      (List.fold_right plusV zeroV
         (List.map (fun '(re, ve) => scale re ve)
            (List.combine (List.map (fun c : Node => A v c) l)
                          (List.map (fun n : Node => x n) l))))
    = true.
  Proof.
    intros l A x u v H_eq H_row.
    induction l as [|j js IH]; simpl.
    - apply refV.
    - apply (congrPV _ _ _ _
        (congrS (A u j) (x j) (A v j) (x j) (H_row u v j H_eq) (refV (x j))) IH).
  Qed.

  Lemma list_lookup_eff_gen :
    forall (A : Node -> Node -> R) (x : Node -> V) (l : list Node),
    (forall i j k, eqN i j = true -> eqR (A i k) (A j k) = true) ->
    forall (i : Node),
    no_dup Node eqN l = true ->
    in_list eqN l i = true ->
    eqV (list_lookup V zeroV Node eqN l
           (matrix_vector_action_eff R V zeroV plusV scale
             (List.map (fun r => List.map (fun c => A r c) l) l)
             (List.map (fun r => x r) l))
           i)
        (List.fold_right (fun j acc => plusV (scale (A i j) (x j)) acc) zeroV l)
        = true.
  Proof.
    intros A x l H_row i H_dup H_in.
    apply (trnV _
      (List.fold_right plusV zeroV
         (List.map (fun '(re, ve) => scale re ve)
            (List.combine (List.map (fun c : Node => A i c) l)
                          (List.map (fun n : Node => x n) l))))
      (List.fold_right (fun j acc => plusV (scale (A i j) (x j)) acc) zeroV l)).
    - (* eff lookup = eff_row i, via list_lookup_map_gen *)
      unfold matrix_vector_action_eff.
      rewrite List.map_map.
      exact (list_lookup_map_gen
        (fun r => List.fold_right plusV zeroV
                   (List.map (fun '(re, ve) => scale re ve)
                      (List.combine (List.map (fun c : Node => A r c) l)
                                    (List.map (fun n : Node => x n) l))))
        l
        (fun u v H_eq => eff_row_congr l A x u v H_eq H_row)
        i H_dup H_in).
    - (* eff_row i = functional i, via combine_fold_eq *)
      apply (combine_fold_eq l A x i).
  Qed.

End GenProofs.


Section Semimodule_proofs.

  (* *)
  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN).

  (* Assumption of number of nodes *)
  Variables 
    (finN : list Node)
    (dupN : no_dup Node eqN finN = true) (* finN is duplicate free *)
    (lenN : (2 <= List.length finN)%nat)
    (memN : ∀ x : Node, in_list eqN finN x = true).

  (* carrier set and the operators for semirng *)
  Variables
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR).

  Declare Scope Mat_scope.
  Delimit Scope Mat_scope with R.
  Bind Scope Mat_scope with R.
  Local Open Scope Mat_scope.


  Local Notation "0" := zeroR : Mat_scope.
  Local Notation "1" := oneR : Mat_scope.
  Local Infix "+" := plusR : Mat_scope.
  Local Infix "*" := mulR : Mat_scope.
  Local Infix "=r=" := eqR (at level 70) : Mat_scope.
  Local Infix "=n=" := eqN (at level 70) : Mat_scope.

  Variables 
    (* Semiring Axiom on R *)
    (zero_left_identity_plus  : forall r : R, 0 + r =r= r = true)
    (zero_right_identity_plus : forall r : R, r + 0 =r= r = true)
    (plus_associative : forall a b c : R, a + (b + c) =r= 
      (a + b) + c = true)
    (plus_commutative  : forall a b : R, a + b =r= b + a = true)
    (one_left_identity_mul  : forall r : R, 1 * r =r= r = true)
    (one_right_identity_mul : forall r : R, r * 1 =r= r = true)
    (mul_associative : forall a b c : R, a * (b * c) =r= 
      (a * b) * c = true)
    (left_distributive_mul_over_plus : forall a b c : R, 
      a * (b + c) =r= a * b + a * c = true)
    (right_distributive_mul_over_plus : forall a b c : R, 
      (a + b) * c =r= a * c + b * c = true)
    (zero_left_anhilator_mul  : forall a : R, 0 * a =r= 0 = true)
    (zero_right_anhilator_mul : forall a : R, a * 0 =r= 0 = true)
    (* end of axioms *)

    (* start of congruence relation *)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).
    (* end of congruence *)

  (* Assume Monoid axioms *)
  Variables
    (V : Type)
    (zeroV : V)
    (plusV : binary_op V)
    (eqV  : brel V)
    (refV : brel_reflexive V eqV)
    (symV : brel_symmetric V eqV)
    (trnV : brel_transitive V eqV).

  Local Infix "=v=" := eqV (at level 70) : Mat_scope.

  Variables
    (* Monoid Axiom on V *)
    (zeroV_left_identity  : forall x : V, plusV zeroV x =v= x = true)
    (zeroV_right_identity : forall x : V, plusV x zeroV =v= x = true)
    (plusV_associative : forall x y z : V, plusV x (plusV y z) =v=
      plusV (plusV x y) z = true)
    (plusV_commutative  : forall x y : V, plusV x y =v= plusV y x = true)
    (* end of monoid axioms *)

    (* congruence for plusV *)
    (congrPV : bop_congruence V eqV plusV).

  Variable (scale : R -> V -> V).

  (* instantiate with types *)
  Let Vector : Type := Vector V Node.
  Let vec_zero : Vector := vec_zero V zeroV Node.
  Let vec_add : Vector -> Vector -> Vector :=
    vec_add V plusV Node.
  Let vec_scale : R -> Vector -> Vector :=
    vec_scale R V scale Node.
  Let matrix_vector_action : Matrix Node R -> Vector -> Vector :=
    matrix_vector_action R V zeroV plusV scale Node finN.
  Let matrix_vector_action_eff : list (list R) -> list V -> list V :=
    matrix_vector_action_eff R V zeroV plusV scale.
  Let list_lookup : list Node -> list V -> Node -> V :=
    list_lookup V zeroV Node eqN.
  Let matrix_vector_action_eff_fun : Matrix Node R -> Vector -> Vector :=
    matrix_vector_action_eff_fun R V zeroV plusV scale Node eqN finN.
  
  (* Semimodule axioms *)
  Variables
    (scale_distr_v : forall a x y, eqV (scale a (plusV x y))
      (plusV (scale a x) (scale a y)) = true)
    (scale_distr_r : forall a b x, eqV (scale (plusR a b) x)
      (plusV (scale a x) (scale b x)) = true)
    (scale_assoc : forall a b x, eqV (scale a (scale b x))
      (scale (mulR a b) x) = true)
    (scale_one : forall x, eqV (scale oneR x) x = true)
    (scale_zero_r : forall x, eqV (scale zeroR x) zeroV = true)
    (scale_zero_v : forall a, eqV (scale a zeroV) zeroV = true)
    (congrS : forall s1 s2 t1 t2, eqR s1 t1 = true -> eqV s2 t2 = true ->
               eqV (scale s1 s2) (scale t1 t2) = true).


  (* ----------------------------------------------------------------------- *)
  (*  Group A — Lifted vector monoid (pointwise on Vector := Node → V)        *)
  (* ----------------------------------------------------------------------- *)

  Theorem vec_add_assoc : forall (x y z : Vector),
    (forall i : Node, eqV (vec_add x (vec_add y z) i)
                          (vec_add (vec_add x y) z i) = true).
  Proof.
    intros x y z i.
    unfold vec_add; simpl.
    apply plusV_associative.
  Qed.

  Theorem vec_add_comm : forall (x y : Vector),
    (forall i : Node, eqV (vec_add x y i) (vec_add y x i) = true).
  Proof.
    intros x y i.
    unfold vec_add; simpl.
    apply plusV_commutative.
  Qed.

  Theorem vec_add_zero_left : forall (x : Vector),
    (forall i : Node, eqV (vec_add vec_zero x i) (x i) = true).
  Proof.
    intros x i.
    unfold vec_add, vec_zero; simpl.
    apply zeroV_left_identity.
  Qed.

  Theorem vec_add_zero_right : forall (x : Vector),
    (forall i : Node, eqV (vec_add x vec_zero i) (x i) = true).
  Proof.
    intros x i.
    unfold vec_add, vec_zero; simpl.
    apply zeroV_right_identity.
  Qed.


  (* ----------------------------------------------------------------------- *)
  (*  Group B — Lifted vector scalar (pointwise)                              *)
  (* ----------------------------------------------------------------------- *)

  Theorem vec_scale_distr_v : forall (x y : Vector) (a : R),
    (forall i : Node, eqV (vec_scale a (vec_add x y) i)
                          (vec_add (vec_scale a x) (vec_scale a y) i) = true).
  Proof.
    intros x y a i.
    unfold vec_scale, vec_add; simpl.
    apply scale_distr_v.
  Qed.

  Theorem vec_scale_distr_r : forall (x : Vector) (a b : R),
    (forall i : Node, eqV (vec_scale (a + b) x i)
                          (vec_add (vec_scale a x) (vec_scale b x) i) = true).
  Proof.
    intros x a b i.
    unfold vec_scale, vec_add; simpl.
    apply scale_distr_r.
  Qed.

  Theorem vec_scale_assoc : forall (x : Vector) (a b : R),
    (forall i : Node, eqV (vec_scale a (vec_scale b x) i)
                          (vec_scale (a * b) x i) = true).
  Proof.
    intros x a b i.
    unfold vec_scale; simpl.
    apply scale_assoc.
  Qed.

  Theorem vec_scale_one : forall (x : Vector),
    (forall i : Node, eqV (vec_scale 1 x i) (x i) = true).
  Proof.
    intros x i.
    unfold vec_scale; simpl.
    apply scale_one.
  Qed.

  Theorem vec_scale_zero_r : forall (x : Vector),
    (forall i : Node, eqV (vec_scale 0 x i) (vec_zero i) = true).
  Proof.
    intros x i.
    unfold vec_scale, vec_zero; simpl.
    apply scale_zero_r.
  Qed.

  Theorem vec_scale_zero_v : forall (a : R),
    (forall i : Node, eqV (vec_scale a vec_zero i) (vec_zero i) = true).
  Proof.
    intros a i.
    unfold vec_scale, vec_zero; simpl.
    apply scale_zero_v.
  Qed.


  (* ----------------------------------------------------------------------- *)
  (*  Group C — Matrix-vector linearity                                       *)
  (* ----------------------------------------------------------------------- *)

  (* Helper: in a commutative monoid, (a+b)+(c+d) =v= (a+c)+(b+d)             *)
  Lemma plusV_shuffle : forall (a b c d : V),
    (plusV (plusV a b) (plusV c d) =v= plusV (plusV a c) (plusV b d)) = true.
  Proof.
    intros a b c d.
    refine (trnV
      (plusV (plusV a b) (plusV c d))
      (plusV a (plusV b (plusV c d)))
      (plusV (plusV a c) (plusV b d))
      (symV _ _ (plusV_associative a b (plusV c d)))
      (trnV
        (plusV a (plusV b (plusV c d)))
        (plusV a (plusV c (plusV b d)))
        (plusV (plusV a c) (plusV b d))
        (congrPV a (plusV b (plusV c d)) a (plusV c (plusV b d))
          (refV a)
          (trnV
            (plusV b (plusV c d))
            (plusV (plusV b c) d)
            (plusV c (plusV b d))
            (plusV_associative b c d)
            (trnV
              (plusV (plusV b c) d)
              (plusV (plusV c b) d)
              (plusV c (plusV b d))
              (congrPV (plusV b c) d (plusV c b) d
                (plusV_commutative b c) (refV d))
              (symV _ _ (plusV_associative c b d)))))
        (plusV_associative a c (plusV b d)))).
  Qed.

  Theorem matrix_vector_action_add : forall (A : Matrix Node R) (x y : Vector),
    (forall i : Node, (matrix_vector_action A (vec_add x y) i =v=
      vec_add (matrix_vector_action A x) (matrix_vector_action A y) i) = true).
  Proof.
    intros A x y i.
    unfold matrix_vector_action, vec_add.
    clear dupN lenN memN.
    induction finN as [|j js IH]; simpl.
    - refine (symV _ _ (zeroV_right_identity _)).
    - refine (trnV _ _ _
        (congrPV
          (scale (A i j) (plusV (x j) (y j)))
          (List.fold_right (fun k acc => plusV (scale (A i k) (plusV (x k) (y k))) acc) zeroV js)
          (plusV (scale (A i j) (x j)) (scale (A i j) (y j)))
          (List.fold_right (fun k acc => plusV (scale (A i k) (plusV (x k) (y k))) acc) zeroV js)
          (scale_distr_v (A i j) (x j) (y j))
          (refV _))
        (trnV _ _ _
          (congrPV
            (plusV (scale (A i j) (x j)) (scale (A i j) (y j)))
            (List.fold_right (fun k acc => plusV (scale (A i k) (plusV (x k) (y k))) acc) zeroV js)
            (plusV (scale (A i j) (x j)) (scale (A i j) (y j)))
            (plusV (List.fold_right (fun k acc => plusV (scale (A i k) (x k)) acc) zeroV js)
                   (List.fold_right (fun k acc => plusV (scale (A i k) (y k)) acc) zeroV js))
            (refV _)
            IH)
          (plusV_shuffle (scale (A i j) (x j)) (scale (A i j) (y j))
            (List.fold_right (fun k acc => plusV (scale (A i k) (x k)) acc) zeroV js)
            (List.fold_right (fun k acc => plusV (scale (A i k) (y k)) acc) zeroV js)))).
  Qed.

  (* Helper: scale distributes over fold_right of plusV                        *)
  Lemma fold_right_scale_distr : forall (f : Node -> V) (l : list Node) (a : R),
    (scale a (List.fold_right (fun j acc => plusV (f j) acc) zeroV l) =v=
     List.fold_right (fun j acc => plusV (scale a (f j)) acc) zeroV l) = true.
  Proof.
    intros f l a. induction l as [|j js IH]; simpl.
    - apply scale_zero_v.
    - refine (trnV _ _ _
        (scale_distr_v a (f j)
          (List.fold_right (fun k acc => plusV (f k) acc) zeroV js))
        (congrPV (scale a (f j))
          (scale a (List.fold_right (fun k acc => plusV (f k) acc) zeroV js))
          (scale a (f j))
          (List.fold_right (fun k acc => plusV (scale a (f k)) acc) zeroV js)
          (refV _) IH)).
  Qed.

  (* Hypothesis: scalars in the first argument of scale commute.              *)
  (*   a ⊙ (b ⊙ x)  =v=  b ⊙ (a ⊙ x)                                         *)
  (*                                                                           *)
  (* With left scalar scale : R → V → V, this says two scalars a,b applied    *)
  (* in sequence can be swapped.  It is equivalent to requiring that the      *)
  (* action of R on V factors through the center of R.                         *)
  Theorem matrix_vector_action_scale : forall (A : Matrix Node R) (x : Vector) (a : R),
    (forall a b x, eqV (scale a (scale b x)) (scale b (scale a x)) = true) ->
    (forall i : Node, (vec_scale a (matrix_vector_action A x) i =v=
      matrix_vector_action A (vec_scale a x) i) = true).
  Proof.
    intros A x a H_comm i.
    unfold matrix_vector_action, vec_scale.
    refine (trnV _ _ _ (fold_right_scale_distr
      (fun j => scale (A i j) (x j)) finN a) _).
    clear dupN lenN memN.
    induction finN as [|j js IH]; simpl.
    - apply refV.
    - apply (congrPV _ _ _ _ (H_comm a (A i j) (x j)) IH).
  Qed.


  (* ----------------------------------------------------------------------- *)
  (*  Group D — Functional ↔ efficient equivalence                            *)
  (* ----------------------------------------------------------------------- *)

  (* Proof sketch:                                                            *)
  (*   matrix_vector_action_eff maps each row r to Σ_c scale (A r c) (x c)    *)
  (*   which equals matrix_vector_action A x r by definition.                 *)
  (*   Then list_lookup finN result i returns result at position i.           *)
  (*   With dupN (no duplicates) and memN (i ∈ finN), the lookup returns      *)
  (*   exactly matrix_vector_action A x i.                                     *)

  (* Helper: combine of two maps equals map of pairs                           *)
  Lemma combine_map_map : forall (X Y : Type) (f : Node -> X) (g : Node -> Y),
    List.combine (List.map f finN) (List.map g finN) =
    List.map (fun c => (f c, g c)) finN.
  Proof.
    intros X Y f g.
    clear dupN lenN memN.
    induction finN as [|j js IH]; simpl; auto.
    rewrite IH. reflexivity.
  Qed.

  (* For each row r, the efficient row sum equals the functional action        *)
  Lemma matrix_vector_action_eff_row :
    forall (A : Matrix Node R) (x : Vector) (r : Node),
    eqV (List.fold_right plusV zeroV
          (List.map (fun '(r_elem, v_elem) => scale r_elem v_elem)
            (List.combine (List.map (fun c => A r c) finN)
                          (List.map (fun c => x c) finN))))
        (Semimodule.matrix_vector_action R V zeroV plusV scale Node finN A x r) = true.
  Proof.
    intros A x r.
    unfold matrix_vector_action.
    clear dupN lenN memN.
    induction finN as [|j js IH]; simpl.
    - apply refV.
    - apply (congrPV _ _ _ _ (refV _) IH).
  Qed.

  (* lookup in a mapped list returns f i (requires congruence of f w.r.t eqN) *)
  Lemma list_lookup_map : forall (f : Node -> V),
    (forall x y, eqN x y = true -> eqV (f x) (f y) = true) ->
    forall (i : Node),
    no_dup Node eqN finN = true ->
    in_list eqN finN i = true ->
    eqV (list_lookup finN (List.map f finN) i) (f i) = true.
  Proof.
    intros f H_cong i H_dup H_in.
    clear dupN lenN memN.
    revert i H_in.
    induction finN as [|j js IH]; simpl; intros i H_in.
    - (* finN = []: in_list [] i = false, contradiction *)
      discriminate H_in.
    - (* finN = j :: js *)
      simpl in H_dup.
      apply Bool.andb_true_iff in H_dup.
      destruct H_dup as [H_notin H_dup_t].
      case_eq (eqN i j); intros Heq.
      + (* eqN i j = true: lookup returns f j *)
        apply (H_cong j i). apply symN. apply Heq.
      + (* eqN i j = false: lookup recurses on js *)
        simpl in H_in. apply Bool.orb_true_iff in H_in.
        destruct H_in as [H_eq | H_in_js].
        * rewrite Heq in H_eq. inversion H_eq.
        * apply (IH H_dup_t i H_in_js).
  Qed.

  (* matrix_vector_action respects eqN in the row index when A does           *)
  Lemma matrix_vector_action_congr : forall (A : Matrix Node R) (x : Vector),
    (forall i j k, eqN i j = true -> eqR (A i k) (A j k) = true) ->
    forall i j, eqN i j = true ->
    eqV (Semimodule.matrix_vector_action R V zeroV plusV scale Node finN A x i)
        (Semimodule.matrix_vector_action R V zeroV plusV scale Node finN A x j) = true.
  Proof.
    intros A x H_congr i j Heq.
    unfold matrix_vector_action.
    clear dupN lenN memN.
    induction finN as [|k ks IH]; simpl.
    - apply refV.
    - apply (congrPV _ _ _ _
        (congrS _ _ _ _ (H_congr i j k Heq) (refV _))
        IH).
  Qed.

  (* The efficient computation, when looked up, equals the functional action   *)
  Lemma list_lookup_eff :
    forall (A : Matrix Node R) (x : Vector),
    (forall i j k, eqN i j = true -> eqR (A i k) (A j k) = true) ->
    forall (i : Node),
    eqV (list_lookup finN
           (matrix_vector_action_eff
             (List.map (fun r => List.map (fun c => A r c) finN) finN)
             (List.map (fun r => x r) finN))
           i)
        (matrix_vector_action A x i) = true.
  Proof.
    intros A x H_row i.
    unfold matrix_vector_action.
    apply (list_lookup_eff_gen Node V R eqN symN eqR refR zeroV plusV eqV refV trnV
      congrPV scale congrS A x finN H_row i dupN (memN i)).
  Qed.

  Theorem matrix_vector_action_eff_fun_eq :
    forall (A : Matrix Node R),
    (forall i j k, eqN i j = true -> eqR (A i k) (A j k) = true) ->
    forall (x : Vector),
    (forall i : Node, eqV (matrix_vector_action_eff_fun A x i)
    (matrix_vector_action A x i) = true).
  Proof.
    intros A H_row x i.
    unfold matrix_vector_action_eff_fun.
    apply list_lookup_eff; auto.
  Qed.

  Theorem list_lookup_correct : forall (k : Node) (v : V) (keys : list Node) (vals : list V),
    no_dup Node eqN (k :: keys) = true ->
    eqV (list_lookup (k :: keys) (v :: vals) k) v = true.
  Proof.
    intros k v keys vals Hdup.
    simpl. rewrite (refN k). apply refV.
  Qed.


  (* ----------------------------------------------------------------------- *)
  (*  Group E — Kleene star fixed point (connects to Mat.v)                   *)
  (* ----------------------------------------------------------------------- *)

  Let kleene_exp := Init.Nat.pred (List.length finN).

  (* ---- generic fold_right helper lemmas ---------------------------------- *)

  Lemma fold_right_congr : forall (l : list Node) (f g : Node -> V),
    (forall j, eqV (f j) (g j) = true) ->
    eqV (List.fold_right (fun j acc => plusV (f j) acc) zeroV l)
        (List.fold_right (fun j acc => plusV (g j) acc) zeroV l) = true.
  Proof.
    induction l as [|j js IH]; simpl; intros f g Hfg.
    - apply refV.
    - apply (congrPV _ _ _ _ (Hfg j) (IH f g Hfg)).
  Qed.

  Lemma fold_right_split : forall (l : list Node) (f g : Node -> V),
    eqV (List.fold_right (fun j acc => plusV (plusV (f j) (g j)) acc) zeroV l)
        (plusV (List.fold_right (fun j acc => plusV (f j) acc) zeroV l)
               (List.fold_right (fun j acc => plusV (g j) acc) zeroV l)) = true.
  Proof.
    induction l as [|j js IH]; simpl; intros f g.
    - apply (symV (plusV zeroV zeroV) zeroV (zeroV_right_identity zeroV)).
    - apply (trnV _
        (plusV (plusV (f j) (g j))
          (plusV (List.fold_right (fun j0 acc => plusV (f j0) acc) zeroV js)
                 (List.fold_right (fun j0 acc => plusV (g j0) acc) zeroV js)))
        _).
      + apply (congrPV _ _ _ _ (refV (plusV (f j) (g j))) (IH f g)).
      + clear IH.
        set (a := f j). set (b := g j).
        set (Sf := List.fold_right (fun j0 acc => plusV (f j0) acc) zeroV js).
        set (Sg := List.fold_right (fun j0 acc => plusV (g j0) acc) zeroV js).
        apply (trnV _ (plusV a (plusV b (plusV Sf Sg))) _
          (symV (plusV a (plusV b (plusV Sf Sg)))
                (plusV (plusV a b) (plusV Sf Sg))
                (plusV_associative a b (plusV Sf Sg)))).
        apply (trnV _ (plusV a (plusV (plusV Sf Sg) b)) _
          (congrPV _ _ _ _ (refV a) (plusV_commutative b (plusV Sf Sg)))).
        apply (trnV _ (plusV (plusV a (plusV Sf Sg)) b) _
          (plusV_associative a (plusV Sf Sg) b)).
        apply (trnV _ (plusV (plusV (plusV a Sf) Sg) b) _
          (congrPV (plusV a (plusV Sf Sg)) b
                   (plusV (plusV a Sf) Sg) b
                   (plusV_associative a Sf Sg)
                   (refV b))).
        apply (trnV _ (plusV (plusV a Sf) (plusV Sg b)) _
          (symV (plusV (plusV a Sf) (plusV Sg b))
                (plusV (plusV (plusV a Sf) Sg) b)
                (plusV_associative (plusV a Sf) Sg b))).
        apply (congrPV _ _ _ _ (refV (plusV a Sf)) (plusV_commutative Sg b)).
  Qed.

  Lemma fold_right_scale_add : forall (l : list Node) (f g : Node -> R) (v : Node -> V),
    eqV (List.fold_right (fun j acc => plusV (scale (f j + g j) (v j)) acc) zeroV l)
        (plusV (List.fold_right (fun j acc => plusV (scale (f j) (v j)) acc) zeroV l)
               (List.fold_right (fun j acc => plusV (scale (g j) (v j)) acc) zeroV l))
    = true.
  Proof.
    intros l f g v.
    apply (trnV _ _ _
      (fold_right_congr l
        (fun j => scale (f j + g j) (v j))
        (fun j => plusV (scale (f j) (v j)) (scale (g j) (v j)))
        (fun j => scale_distr_r (f j) (g j) (v j)))
      (fold_right_split l
        (fun j => scale (f j) (v j))
        (fun j => scale (g j) (v j)))).
  Qed.

  (* Helper: if eqN i k = false for all k in l, fold_right gives zeroV    *)
  Lemma fold_right_identity_zero : forall (l : list Node) (v : Vector) (i : Node),
    in_list eqN l i = false ->
    eqV (List.fold_right (fun j acc => plusV (scale ((I Node eqN R 0 1) i j) (v j)) acc) zeroV l)
        zeroV = true.
  Proof.
    induction l as [|j js IH]; simpl; intros v i H_not.
    - apply refV.
    - apply Bool.orb_false_iff in H_not.
      destruct H_not as [H_ij H_js].
      unfold I at 1.
      rewrite H_ij.  (* eqN i j = false, so I i j = 0 *)
      simpl.
      apply (trnV _ _ _
        (congrPV _ _ _ _ (scale_zero_r (v j)) (IH v i H_js))
        (zeroV_left_identity zeroV)).
  Qed.

  Lemma fold_right_identity : forall (l : list Node) (v : Vector) (i : Node),
    (forall x y, eqN x y = true -> eqV (v x) (v y) = true) ->
    no_dup Node eqN l = true ->
    in_list eqN l i = true ->
    eqV (List.fold_right (fun j acc => plusV (scale ((I Node eqN R 0 1) i j) (v j)) acc) zeroV l)
        (v i) = true.
  Proof.
    induction l as [|j js IH]; simpl; intros v i H_cong H_dup H_in.
    - discriminate H_in.
    - simpl in H_dup.
      apply Bool.andb_true_iff in H_dup.
      destruct H_dup as [H_notin H_dup'].
      case_eq (eqN i j); intros Heq_ij.
      + (* eqN i j = true: I i j = 1 *)
        unfold I at 1. rewrite Heq_ij. simpl.
        apply (trnV _ (plusV (v j) zeroV) _).
        * (* Head becomes v j, tail is zeroV since in_list js i = false *)
          apply (congrPV _ _ _ _ (scale_one (v j))
            (fold_right_identity_zero js v i
              (list_mem_not Node eqN symN trnN js i j Heq_ij
                (proj1 (Bool.negb_true_iff _) H_notin)))).
        * (* v j =v= v i, then v i + 0 =v= v i *)
          refine (trnV (plusV (v j) zeroV) (plusV (v i) zeroV) (v i)
            (congrPV (v j) zeroV (v i) zeroV
              (H_cong j i (symN _ _ Heq_ij)) (refV zeroV)) _).
          apply (trnV (plusV (v i) zeroV) (plusV zeroV (v i)) (v i)
            (plusV_commutative (v i) zeroV)
            (zeroV_left_identity (v i))).
      + (* eqN i j = false: I i j = 0 *)
        unfold I at 1. rewrite Heq_ij. simpl.
        apply Bool.orb_true_iff in H_in.
        destruct H_in as [Heq | H_in_js].
        * rewrite Heq in Heq_ij. discriminate Heq_ij.
        * apply (trnV _ _ _
            (congrPV _ _ _ _ (scale_zero_r (v j)) (IH v i H_cong H_dup' H_in_js))
            (zeroV_left_identity (v i))).
  Qed.

  Lemma fold_right_scale_r_sum : forall (l : list Node) (f : Node -> R) (x : V),
    eqV (scale (List.fold_right (fun k acc => f k + acc) zeroR l) x)
        (List.fold_right (fun k acc => plusV (scale (f k) x) acc) zeroV l) = true.
  Proof.
    induction l as [|h t IH]; simpl; intros f x.
    - apply scale_zero_r.
    - apply (trnV _ _ _
        (scale_distr_r (f h) (List.fold_right (fun k acc => f k + acc) zeroR t) x)).
      apply (congrPV _ _ _ _ (refV (scale (f h) x)) (IH f x)).
  Qed.

  Lemma fold_right_double_commute : forall (l : list Node) (f : Node -> Node -> V),
    eqV (List.fold_right
           (fun j acc =>
             plusV (List.fold_right (fun k acc' => plusV (f j k) acc') zeroV l) acc)
           zeroV l)
        (List.fold_right
           (fun k acc =>
             plusV (List.fold_right (fun j acc' => plusV (f j k) acc') zeroV l) acc)
           zeroV l) = true.
  Proof.
    induction l as [|h t IH]; simpl; intros f.
    - apply refV.
    - (* Name the sub-expressions for clarity *)
      set (A := f h h).
      set (B := List.fold_right (fun k acc' => plusV (f h k) acc') zeroV t).
      set (C := List.fold_right (fun j acc' => plusV (f j h) acc') zeroV t).
      set (D := List.fold_right
                 (fun j acc =>
                    plusV (List.fold_right (fun k acc' => plusV (f j k) acc') zeroV t) acc)
                 zeroV t).
      (* LHS = plusV (A + B) (plusV C D) via fold_right_split *)
      assert (HL : eqV
        (List.fold_right (fun j acc =>
           plusV (List.fold_right (fun k acc' => plusV (f j k) acc') zeroV (h :: t)) acc)
           zeroV (h :: t))
        (plusV (plusV A B) (plusV C D)) = true).
      { simpl.
        apply (congrPV _ _ _ _
          (trnV _ _ _
            (congrPV _ _ _ _ (refV A) (refV B))
            (refV _))).
        simpl.
        apply (trnV _ _ _
          (fold_right_split t
            (fun j => f j h)
            (fun j => List.fold_right (fun k acc' => plusV (f j k) acc') zeroV t))
          (refV _)).
      }
      (* RHS = plusV (A + C) (plusV B D) via fold_right_split *)
      assert (HR : eqV
        (List.fold_right (fun k acc =>
           plusV (List.fold_right (fun j acc' => plusV (f j k) acc') zeroV (h :: t)) acc)
           zeroV (h :: t))
        (plusV (plusV A C) (plusV B D)) = true).
      { simpl.
        apply (congrPV _ _ _ _
          (trnV _ _ _
            (congrPV _ _ _ _ (refV A) (refV C))
            (refV _))).
        simpl.
        apply (trnV _ _ _
          (fold_right_split t
            (fun k => f h k)
            (fun k => List.fold_right (fun j acc' => plusV (f j k) acc') zeroV t))).
        (* Now: plusV B D_swapped =v= plusV B D *)
        apply (congrPV _ _ _ _ (refV B)
          (symV _ _ (IH (fun j k : Node => f j k)))).
      }
      (* Now: plusV (A+B) (C+D) =v= plusV (A+C) (B+D) by comm/assoc *)
      assert (H_mid : eqV (plusV (plusV A B) (plusV C D))
                          (plusV (plusV A C) (plusV B D)) = true).
      { assert (H1 : eqV (plusV (plusV A B) (plusV C D))
                         (plusV A (plusV B (plusV C D))) = true).
        { apply (symV _ _ (plusV_associative A B (plusV C D))). }
        assert (H2 : eqV (plusV A (plusV B (plusV C D)))
                         (plusV A (plusV (plusV B C) D)) = true).
        { refine (congrPV A (plusV B (plusV C D)) A (plusV (plusV B C) D)
            (refV A) _).
          apply (plusV_associative B C D). }
        assert (H3 : eqV (plusV A (plusV (plusV B C) D))
                         (plusV A (plusV (plusV C B) D)) = true).
        { refine (congrPV A (plusV (plusV B C) D) A (plusV (plusV C B) D)
            (refV A) _).
          refine (congrPV (plusV B C) D (plusV C B) D
            (plusV_commutative B C) (refV D)). }
        assert (H4 : eqV (plusV A (plusV (plusV C B) D))
                         (plusV A (plusV C (plusV B D))) = true).
        { refine (congrPV A (plusV (plusV C B) D) A (plusV C (plusV B D))
            (refV A) _).
          apply (symV _ _ (plusV_associative C B D)). }
        assert (H5 : eqV (plusV A (plusV C (plusV B D)))
                         (plusV (plusV A C) (plusV B D)) = true).
        { apply (plusV_associative A C (plusV B D)). }
        apply (trnV _ _ _ H1
          (trnV _ _ _ H2
            (trnV _ _ _ H3
              (trnV _ _ _ H4 H5)))).
      }
      apply (trnV _ _ _ HL).
      apply (trnV _ _ _ H_mid).
      apply (symV _ _ HR).
  Qed.

  Lemma fold_right_mul_assoc : forall (l : list Node) (M1 M2 : Matrix Node R) (v : Vector) (i : Node),
    eqV (List.fold_right (fun j acc => plusV (scale
           (List.fold_right (fun k acc2 => M1 i k * M2 k j + acc2) 0 l) (v j)) acc)
           zeroV l)
        (List.fold_right (fun j acc => plusV (scale (M1 i j)
           (List.fold_right (fun k acc2 => plusV (scale (M2 j k) (v k)) acc2) zeroV l)) acc)
           zeroV l) = true.
  Proof.
    intros l M1 M2 v i.
    (* f(j,k) := scale (M1 i k) (scale (M2 k j) (v j)) *)
    set (f := fun (j k : Node) => scale (M1 i k) (scale (M2 k j) (v j))).
    (* g(j,k) := scale (M1 i j) (scale (M2 j k) (v k)) *)
    set (g := fun (j k : Node) => scale (M1 i j) (scale (M2 j k) (v k))).

    (* Step 1: LHS = sum_j sum_k f(j,k) *)
    assert (HL : eqV
      (List.fold_right (fun j acc => plusV (scale
         (List.fold_right (fun k acc2 => M1 i k * M2 k j + acc2) 0 l) (v j)) acc)
         zeroV l)
      (List.fold_right (fun j acc =>
         plusV (List.fold_right (fun k acc' => plusV (f j k) acc') zeroV l) acc)
         zeroV l) = true).
    { apply (fold_right_congr l
        (fun j => scale (List.fold_right (fun k acc2 => M1 i k * M2 k j + acc2) 0 l) (v j))
        (fun j => List.fold_right (fun k acc' => plusV (f j k) acc') zeroV l)).
      intro j.
      apply (trnV _ _ _
        (fold_right_scale_r_sum l (fun k => M1 i k * M2 k j) (v j))).
      apply (fold_right_congr l
        (fun k => scale (M1 i k * M2 k j) (v j))
        (fun k => f j k)).
      intro k. unfold f. apply (symV _ _ (scale_assoc (M1 i k) (M2 k j) (v j))).
    }

    (* Step 2: RHS = sum_j sum_k g(j,k) *)
    assert (HR : eqV
      (List.fold_right (fun j acc => plusV (scale (M1 i j)
         (List.fold_right (fun k acc2 => plusV (scale (M2 j k) (v k)) acc2) zeroV l)) acc)
         zeroV l)
      (List.fold_right (fun j acc =>
         plusV (List.fold_right (fun k acc' => plusV (g j k) acc') zeroV l) acc)
         zeroV l) = true).
    { apply (fold_right_congr l
        (fun j => scale (M1 i j)
          (List.fold_right (fun k acc2 => plusV (scale (M2 j k) (v k)) acc2) zeroV l))
        (fun j => List.fold_right (fun k acc' => plusV (g j k) acc') zeroV l)).
      intro j.
      refine (trnV _ _ _
        (fold_right_scale_distr (fun k => scale (M2 j k) (v k)) l (M1 i j)) _).
      apply (fold_right_congr l
        (fun k => scale (M1 i j) (scale (M2 j k) (v k)))
        (fun k => g j k)).
      intro k. unfold g. apply refV.
    }

    (* Step 3: sum_j sum_k g(j,k) = sum_k sum_j g(j,k) via double commute *)
    assert (Hcomm : eqV
      (List.fold_right (fun j acc =>
         plusV (List.fold_right (fun k acc' => plusV (g j k) acc') zeroV l) acc)
         zeroV l)
      (List.fold_right (fun k acc =>
         plusV (List.fold_right (fun j acc' => plusV (g j k) acc') zeroV l) acc)
         zeroV l) = true).
    { apply (fold_right_double_commute l g). }

    (* Step 4: sum_k sum_j g(j,k) = sum_j sum_k g(k,j) via alpha-equivalence *)
    (* These are identical up to bound variable renaming *)
    assert (H_alpha : eqV
      (List.fold_right (fun k acc =>
         plusV (List.fold_right (fun j acc' => plusV (g j k) acc') zeroV l) acc)
         zeroV l)
      (List.fold_right (fun j acc =>
         plusV (List.fold_right (fun k acc' => plusV (g k j) acc') zeroV l) acc)
         zeroV l) = true).
    { apply refV. }

    (* Step 5: g(k,j) = f(j,k), so sum_j sum_k g(k,j) = sum_j sum_k f(j,k) *)
    assert (Hgf : eqV
      (List.fold_right (fun j acc =>
         plusV (List.fold_right (fun k acc' => plusV (g k j) acc') zeroV l) acc)
         zeroV l)
      (List.fold_right (fun j acc =>
         plusV (List.fold_right (fun k acc' => plusV (f j k) acc') zeroV l) acc)
         zeroV l) = true).
    { apply (fold_right_congr l
        (fun j => List.fold_right (fun k acc' => plusV (g k j) acc') zeroV l)
        (fun j => List.fold_right (fun k acc' => plusV (f j k) acc') zeroV l)).
      intro j. apply (fold_right_congr l
        (fun k => g k j) (fun k => f j k)).
      intro k. unfold g, f. apply refV.
    }

    (* Chain: LHS = sum_j sum_k f(j,k) = sum_j sum_k g(k,j) = sum_k sum_j g(j,k) = sum_j sum_k g(j,k) = RHS *)
    refine (trnV
      (List.fold_right (fun j acc => plusV (scale
         (List.fold_right (fun k acc2 => M1 i k * M2 k j + acc2) 0 l) (v j)) acc) zeroV l)
      (List.fold_right (fun j acc =>
         plusV (List.fold_right (fun k acc' => plusV (f j k) acc') zeroV l) acc) zeroV l)
      (List.fold_right (fun j acc => plusV (scale (M1 i j)
         (List.fold_right (fun k acc2 => plusV (scale (M2 j k) (v k)) acc2) zeroV l)) acc) zeroV l)
      HL _).
    refine (trnV _ _ _ (symV _ _ Hgf) _).
    refine (trnV _ _ _ (symV _ _ H_alpha) _).
    refine (trnV _ _ _ (symV _ _ Hcomm) _).
    apply (symV _ _ HR).
  Qed.

  (* Matrix-level Kleene fixpoint: A* = I + A *M A*                         *)
  Lemma partial_sum_mat_fixpoint :
    forall (A : Matrix Node R),
    mat_cong Node eqN R eqR A ->
    (forall u v : Node, eqN u v = true -> eqR (A u v) 1 = true) ->
    (forall a : R, 1 + a =r= 1 = true) ->
    forall (c d : Node),
    partial_sum_mat Node eqN finN R 0 1 plusR mulR A kleene_exp c d =r=
    (matrix_add Node R plusR (I Node eqN R 0 1)
      (matrix_mul Node finN R 0 plusR mulR A
         (partial_sum_mat Node eqN finN R 0 1 plusR mulR A kleene_exp))) c d = true.
  Proof.
    (* The proof below is correct once the segment variations argument to   *)
    (* zero_stable_partial is sorted out. It uses Mat.v lemmas:             *)
    (*   zero_stable_partial : A*n = A*(Sn)                                 *)
    (*   astar_aide_gen_q_stable_matrix : A*(Sn) = I + A *M A*n            *)
    (*   Combining: A*n = I + A *M A*n                                      *)
    intros A H_cong H_diag H_bounded c d.
    pose proof (zero_stable_partial Node eqN refN symN trnN finN dupN lenN memN
      R 0 1 plusR mulR eqR refR symR trnR
      zero_left_identity_plus zero_right_identity_plus
      plus_associative plus_commutative
      one_left_identity_mul one_right_identity_mul
      mul_associative
      left_distributive_mul_over_plus right_distributive_mul_over_plus
      zero_right_anhilator_mul
      congrP congrM congrR
      H_bounded) as Hzs.
    specialize (Hzs 1%nat A H_cong H_diag c d).
    unfold kleene_exp in Hzs |- *.
    replace (Nat.pred (length finN)) with 
    (length finN - 1) by lia.
    eapply trnR; [exact Hzs | ]. 
    replace (1 + length finN - 1) with 
    (S (length finN - 1)) by lia.
    eapply  astar_aide_gen_q_stable_matrix; 
    eauto. 
  Qed.

  (* ---- main theorems --------------------------------------------------- *)

  Theorem kleene_fixed_point_idem :
    forall (A : Matrix Node R) (b x : Vector),
      mat_cong Node eqN R eqR A ->
      (forall u v : Node, eqN u v = true -> eqR (A u v) 1 = true) ->
      (forall a : R, 1 + a =r= 1 = true) ->
      (forall i : Node, eqV (x i)
        (matrix_vector_action
          (partial_sum_mat Node eqN finN R 0 1 plusR mulR A
             kleene_exp) b i) = true) ->
      (forall i : Node, eqV (vec_add (matrix_vector_action A x) b i)
                          (vec_add b (matrix_vector_action A x) i) = true).
  Proof.
    intros A b x ? ? H_bounded Hx i.
    unfold vec_add.
    apply plusV_commutative.
  Qed.

  Theorem kleene_fixed_point :
    forall (A : Matrix Node R) (b x : Vector),
      mat_cong Node eqN R eqR A ->
      (forall u v : Node, eqN u v = true -> eqR (A u v) 1 = true) ->
      (forall a : R, 1 + a =r= 1 = true) ->
      (forall x y : Node, eqN x y = true -> eqV (b x) (b y) = true) ->
      (forall i : Node, eqV (x i)
        (matrix_vector_action (partial_sum_mat Node eqN finN R 0 1 plusR mulR A
          kleene_exp) b i) = true) ->
      (forall i : Node, eqV (x i) (vec_add (matrix_vector_action A x) b i) = true).
  Proof.
    intros A b x H_cong H_diag H_bounded H_cong_b Hx_all i.
    (* Hx_all : forall i : Node, x i =v= (A*·b) i *)
    unfold matrix_vector_action, vec_add.

    (* Step 0: name the Kleene star for brevity *)
    set (Astar := partial_sum_mat Node eqN finN R 0 1 plusR mulR A kleene_exp).

    (* Hx_at_i: x i =v= (A*·b) i *)
    pose proof (Hx_all i) as Hx_at_i.
    apply (trnV _ _ _ Hx_at_i).

    (* Goal: (A*·b) i =v= plusV ((A·x) i) (b i) *)

    (* Step 1: matrix fixpoint A* = I + A_mat A*  --->  A*·b = (I+A_mat A* )·b *)
    pose proof (partial_sum_mat_fixpoint A H_cong H_diag H_bounded) as Hstar.
    assert (H1 : eqV
      (List.fold_right (fun j acc => plusV (scale (Astar i j) (b j)) acc) zeroV finN)
      (List.fold_right (fun j acc => plusV (scale
         ((matrix_add Node R plusR (I Node eqN R 0 1)
            (matrix_mul Node finN R 0 plusR mulR A Astar)) i j) (b j)) acc) zeroV finN)
      = true).
    { apply (fold_right_congr finN
        (fun j => scale (Astar i j) (b j))
        (fun j => scale ((matrix_add Node R plusR (I Node eqN R 0 1)
          (matrix_mul Node finN R 0 plusR mulR A Astar)) i j) (b j))
        (fun j => congrS _ _ _ _ (Hstar i j) (refV (b j)))). }
    apply (trnV _ _ _ H1); clear H1.

    (* Goal: ((I+A_mat A* )·b) i =v= plusV ((A·x) i) (b i) *)

    (* Step 2: distribute scale over matrix addition via fold_right_scale_add *)
    assert (Hdist := fold_right_scale_add finN
      (fun j => (I Node eqN R 0 1) i j)
      (fun j => matrix_mul Node finN R 0 plusR mulR A Astar i j)
      (fun j => b j)).
    simpl in Hdist.  (* beta-reduce the lambda applications *)

    apply (trnV
      (List.fold_right (fun j acc => plusV (scale ((matrix_add Node R plusR (I Node eqN R 0 1)
        (matrix_mul Node finN R 0 plusR mulR A Astar)) i j) (b j)) acc) zeroV finN)
      (plusV
        (List.fold_right (fun j acc => plusV (scale ((I Node eqN R 0 1) i j) (b j)) acc) zeroV finN)
        (List.fold_right (fun j acc => plusV (scale (matrix_mul Node finN R 0 plusR mulR A Astar i j) (b j)) acc) zeroV finN))
      (plusV
        (List.fold_right (fun j acc => plusV (scale (A i j) (x j)) acc) zeroV finN)
        (b i))
      Hdist).

    (* Goal: plusV (I·b i) ((A_mat A* )·b i) =v= plusV ((A·x) i) (b i) *)

    (* Step 3: I·b i =v= b i *)
    apply (trnV
      (plusV
        (List.fold_right (fun j acc => plusV (scale ((I Node eqN R 0 1) i j) (b j)) acc) zeroV finN)
        (List.fold_right (fun j acc => plusV (scale (matrix_mul Node finN R 0 plusR mulR A Astar i j) (b j)) acc) zeroV finN))
      (plusV (b i)
        (List.fold_right (fun j acc => plusV (scale (matrix_mul Node finN R 0 plusR mulR A Astar i j) (b j)) acc) zeroV finN))
      (plusV
        (List.fold_right (fun j acc => plusV (scale (A i j) (x j)) acc) zeroV finN)
        (b i))
      (congrPV _ _ _ _
        (fold_right_identity finN b i H_cong_b dupN (memN i))
        (refV (List.fold_right (fun j acc => plusV (scale (matrix_mul Node finN R 0 plusR mulR A Astar i j) (b j)) acc) zeroV finN)))
      ).

    (* Goal: plusV (b i) ((A_mat A* )·b i) =v= plusV ((A·x) i) (b i) *)

    (* Step 4: commute b i and ((A_mat A* )·b) i *)
    apply (trnV _ _ _
      (plusV_commutative (b i) (List.fold_right
        (fun j acc => plusV (scale (matrix_mul Node finN R 0 plusR mulR A Astar i j) (b j)) acc) zeroV finN))).

    (* Goal: plusV ((A_mat A* )·b i) (b i) =v= plusV ((A·x) i) (b i) *)

    (* Step 5: cancel b i on both sides *)
    refine (congrPV
      (List.fold_right (fun j acc => plusV (scale (matrix_mul Node finN R 0 plusR mulR A Astar i j) (b j)) acc) zeroV finN)
      (b i)
      (List.fold_right (fun j acc => plusV (scale (A i j) (x j)) acc) zeroV finN)
      (b i)
      _ 
      (refV (b i))).
    (* Goal: ((A_mat A* )·b) i =v= (A·x) i *)

    (* Step 6: (A_mat A* )·b = A·(A*·b) via associativity *)
    apply (trnV _ _ _
      (fold_right_mul_assoc finN A Astar b i)).

    (* Step 7: replace A*·b with x using Hx_all *)
    apply (fold_right_congr finN
      (fun j => scale (A i j) (List.fold_right (fun k acc => plusV (scale (Astar j k) (b k)) acc) zeroV finN))
      (fun j => scale (A i j) (x j))
      (fun j => congrS (A i j) _ (A i j) _ (refR _) (symV _ _ (Hx_all j)))).
  Qed.

End Semimodule_proofs.

