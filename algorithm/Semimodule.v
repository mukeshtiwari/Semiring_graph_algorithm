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

  Variable scale : V -> R -> V.

  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (finN : list Node).


  (* Now we scale this to matrix-vector semimodule. *)
  Definition Vector : Type := Node -> V. 

  Definition vec_zero : Vector := fun _ => zeroV.
  Definition vec_add  (x y : Vector) : Vector := fun i => plusV (x i) (y i).
  Definition vec_scale (v : Vector) (a : R) : Vector := fun i => scale (v i) a.

  (* (m · v)_i  :=  Σ_{j ∈ finN}  (v_j) ⊙ m_{i,j}                            *)
  Definition matrix_vector_action (m : Matrix Node R) (v : Vector) : Vector := 
    fun (i : Node) =>
      List.fold_right
        (fun j acc => plusV (scale (v j) (m i j)) acc)
        zeroV
        finN.

  (* Efficient list-based version: map each row → fold (scale v_j m_{i,j})    *)
  Definition matrix_vector_action_eff (m : list (list R)) (v : list V) : list V :=
    List.map (fun row =>
      List.fold_right plusV zeroV
        (List.map (fun '(r_elem, v_elem) => scale v_elem r_elem)
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

(* Here goes the generic proof *)
Section Generic_proof. 

End Generic_proof.


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

  Variable (scale : V -> R -> V).

  (* instantiate with types *)
  Let Vector : Type := Vector V Node.
  Let vec_zero : Vector := vec_zero V zeroV Node.
  Let vec_add : Vector -> Vector -> Vector :=
    vec_add V plusV Node.
  Let vec_scale : Vector -> R -> Vector :=
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
    (scale_distr_v : forall x y a, eqV (scale (plusV x y) a)
      (plusV (scale x a) (scale y a)) = true)
    (scale_distr_r : forall x a b, eqV (scale x (plusR a b))
      (plusV (scale x a) (scale x b)) = true)
    (scale_assoc : forall x a b, eqV (scale (scale x a) b)
      (scale x (mulR a b)) = true)
    (scale_one : forall x, eqV (scale x oneR) x = true)
    (scale_zero_r : forall x, eqV (scale x zeroR) zeroV = true)
    (scale_zero_v : forall a, eqV (scale zeroV a) zeroV = true)
    (congrS : forall s1 s2 t1 t2, eqV s1 t1 = true -> eqR s2 t2 = true ->
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
    (forall i : Node, eqV (vec_scale (vec_add x y) a i)
                          (vec_add (vec_scale x a) (vec_scale y a) i) = true).
  Proof.
    intros x y a i.
    unfold vec_scale, vec_add; simpl.
    apply scale_distr_v.
  Qed.

  Theorem vec_scale_distr_r : forall (x : Vector) (a b : R),
    (forall i : Node, eqV (vec_scale x (a + b) i)
                          (vec_add (vec_scale x a) (vec_scale x b) i) = true).
  Proof.
    intros x a b i.
    unfold vec_scale, vec_add; simpl.
    apply scale_distr_r.
  Qed.

  Theorem vec_scale_assoc : forall (x : Vector) (a b : R),
    (forall i : Node, eqV (vec_scale (vec_scale x a) b i)
                          (vec_scale x (a * b) i) = true).
  Proof.
    intros x a b i.
    unfold vec_scale; simpl.
    apply scale_assoc.
  Qed.

  Theorem vec_scale_one : forall (x : Vector),
    (forall i : Node, eqV (vec_scale x 1 i) (x i) = true).
  Proof.
    intros x i.
    unfold vec_scale; simpl.
    apply scale_one.
  Qed.

  Theorem vec_scale_zero_r : forall (x : Vector),
    (forall i : Node, eqV (vec_scale x 0 i) (vec_zero i) = true).
  Proof.
    intros x i.
    unfold vec_scale, vec_zero; simpl.
    apply scale_zero_r.
  Qed.

  Theorem vec_scale_zero_v : forall (a : R),
    (forall i : Node, eqV (vec_scale vec_zero a i) (vec_zero i) = true).
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
          (scale (plusV (x j) (y j)) (A i j))
          (List.fold_right (fun k acc => plusV (scale (plusV (x k) (y k)) (A i k)) acc) zeroV js)
          (plusV (scale (x j) (A i j)) (scale (y j) (A i j)))
          (List.fold_right (fun k acc => plusV (scale (plusV (x k) (y k)) (A i k)) acc) zeroV js)
          (scale_distr_v (x j) (y j) (A i j))
          (refV _))
        (trnV _ _ _
          (congrPV
            (plusV (scale (x j) (A i j)) (scale (y j) (A i j)))
            (List.fold_right (fun k acc => plusV (scale (plusV (x k) (y k)) (A i k)) acc) zeroV js)
            (plusV (scale (x j) (A i j)) (scale (y j) (A i j)))
            (plusV (List.fold_right (fun k acc => plusV (scale (x k) (A i k)) acc) zeroV js)
                   (List.fold_right (fun k acc => plusV (scale (y k) (A i k)) acc) zeroV js))
            (refV _)
            IH)
          (plusV_shuffle (scale (x j) (A i j)) (scale (y j) (A i j))
            (List.fold_right (fun k acc => plusV (scale (x k) (A i k)) acc) zeroV js)
            (List.fold_right (fun k acc => plusV (scale (y k) (A i k)) acc) zeroV js)))).
  Qed.

  Theorem matrix_vector_action_scale : forall (A : Matrix Node R) (x : Vector) (a : R),
    (forall i : Node, eqV (vec_scale (matrix_vector_action A x) a i)
      (matrix_vector_action A (vec_scale x a) i) = true).
  Proof. Admitted.


  (* ----------------------------------------------------------------------- *)
  (*  Group D — Functional ↔ efficient equivalence                            *)
  (* ----------------------------------------------------------------------- *)

  Theorem matrix_vector_action_eff_fun_eq :
    forall (A : Matrix Node R) (x : Vector),
    (forall i : Node, eqV (matrix_vector_action_eff_fun A x i)
    (matrix_vector_action A x i) = true).
  Proof. Admitted.

  Theorem list_lookup_correct : forall (keys : list Node) (vals : list V) (k : Node) (v : V),
    no_dup Node eqN keys = true -> in_list eqN keys k = true ->
    eqV (list_lookup keys vals k) v = true.
  Proof. Admitted.


  (* ----------------------------------------------------------------------- *)
  (*  Group E — Kleene star fixed point (connects to Mat.v)                   *)
  (* ----------------------------------------------------------------------- *)

  (* Let A* := partial_sum_mat A (length finN - 1) be the Kleene star.       *)
  (* In a bounded semiring (where 1 + a = 1), Mat.v proves A* = I + A·_M A*. *)
  (* We lift this to the semimodule fixed-point theorem.                       *)

  Theorem kleene_fixed_point :
    forall (A : Matrix Node R) (b x : Vector),
      (* bounded semiring: 1 + a = 1 for all a *)
      (forall a : R, 1 + a =r= 1 = true) ->
      (* x = A* · b *)
      (forall i : Node, eqV (x i) 
        (matrix_vector_action (partial_sum_mat Node eqN finN R 0 1 plusR mulR A
          (Init.Nat.pred (List.length finN))) b i) = true) ->
      (* Then x satisfies: x = A·x + b *)
      (forall i : Node, eqV (x i) (vec_add (matrix_vector_action A x) b i) = true).
  Proof. Admitted.

  Theorem kleene_fixed_point_idem :
    forall (A : Matrix Node R) (b x : Vector),
      (forall a : R, 1 + a =r= 1 = true) ->
      (forall i : Node, eqV (x i)
        (matrix_vector_action
          (partial_sum_mat Node eqN finN R 0 1 plusR mulR A
             (Init.Nat.pred (List.length finN))) b i) = true) ->
      (forall i : Node, eqV (vec_add (matrix_vector_action A x) b i)
                          (vec_add b (matrix_vector_action A x) i) = true).
  Proof. Admitted.


End Semimodule_proofs.

