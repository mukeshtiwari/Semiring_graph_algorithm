From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
Require Import
  Algorithm.Definitions
  Algorithm.Listprop
  Algorithm.Orel
  Algorithm.Path.
Import ListNotations.




Section Matrix_def.

  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (finN : list Node).

  (* carrier set and the operators *)
  Variables
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)
    (eqR  : brel R).
    

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

  (* returns the cth row of m *)
  Definition get_row (m : Matrix Node R) (c : Node) : Node -> R := 
    fun d => m c d.

  (* returns the cth column of m *)
  Definition get_col (m : Matrix Node R) (c : Node) : Node -> R :=
    fun d => m d c.

  (* zero matrix, additive identity of plus *)
  Definition zero_matrix : Matrix Node R := 
    fun _ _ => 0.
  


  (* identity matrix, mulitplicative identity of mul *)
  (* Idenitity Matrix *)
  Definition I : Matrix Node R := 
    fun (c d : Node) =>
    match c =n= d with 
    | true => 1
    | false => 0 
    end.
  
  
  (* transpose the matrix m *)
  Definition transpose (m : Matrix Node R) : Matrix Node R := 
    fun (c d : Node) => m d c.

  

  (* pointwise addition to two matrices *)
  Definition matrix_add (m₁ m₂ : Matrix Node R) : Matrix Node R :=
    fun c d => (m₁ c d + m₂ c d).

  
  Fixpoint sum_fn (f : Node -> R) (l : list Node) : R :=
    match l with 
    | [] => 0
    | h :: t => f h + sum_fn f t
    end.


  (* generalised matrix multiplication *)
  Definition matrix_mul_gen (m₁ m₂ : Matrix Node R) 
    (l : list Node) : Matrix Node R :=
    fun (c d : Node) => 
      sum_fn (fun y => (m₁ c y * m₂ y d)) l.



  
  (* Specialised form of general multiplicaiton *)
  Definition matrix_mul (m₁ m₂ : Matrix Node R) := 
    matrix_mul_gen m₁ m₂ finN.

  
  Fixpoint matrix_exp_unary (m : Matrix Node R) (n : nat) : Matrix Node R :=
    match n with 
    | 0%nat => I 
    | S n' => matrix_mul m (matrix_exp_unary m n')
    end.
  
  
    
  Fixpoint repeat_op_ntimes_rec (e : Matrix Node R) (n : positive) : Matrix Node R :=
    match n with
    | xH => e
    | xO p => let ret := repeat_op_ntimes_rec e p in matrix_mul ret ret
    | xI p => let ret := repeat_op_ntimes_rec e p in 
      matrix_mul e (matrix_mul ret ret)
    end.

  Definition matrix_exp_binary (e : Matrix Node R) (n : N) :=
    match n with
    | N0 => I
    | Npos p => repeat_op_ntimes_rec e p 
    end.



  Fixpoint exp_r (a : R) (n : nat) : R :=
    match n with 
    | O => 1
    | S n' => a * exp_r a n'
    end.


  Fixpoint partial_sum_r (a : R) (n : nat) : R :=
    match n with
    | O => 1
    | S n' => (partial_sum_r a n') + exp_r a n
    end.


  (* Print Grammar constr. *)
  Local Infix "+M" := matrix_add (at level 50) : Mat_scope.
  Local Infix "*M" := matrix_mul (at level 40) : Mat_scope.

  Fixpoint partial_sum_mat (m : Matrix Node R) (n : nat) : Matrix Node R :=
    match n with
    | O => I 
    | S n' => (partial_sum_mat m n') +M (matrix_exp_unary m n)
    end.

  

  (* f is congruent wrt =n= *)
  Definition fncong (f : Node -> R) : Prop :=
    forall a b : Node, a =n= b = true -> 
    f a =r= f b = true.

  (* congruence relation on matrix *)
  Definition mat_cong (m : Matrix Node R) : Prop :=
    forall a b c d, a =n= c = true -> 
    b =n= d = true -> m a b =r= m c d = true.


  (* two matrices are equal only if they are equal every point *)
  Definition two_mat_congr (m₁ m₂ : Matrix Node R) : Prop :=
    forall c d, m₁ c d =r= m₂ c d = true.

  (* more general version *)
  Definition two_mat_congr_gen (m₁ m₂ : Matrix Node R) : Prop :=
    forall a b c d, a =n= c = true -> b =n= d = true -> 
    m₁ a b =r= m₂ c d = true. 

  
End Matrix_def.



Section Matrix_proofs.


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

  (* carrier set and the operators *)
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
    (plus_idempotence : forall a : R, a + a =r= a = true)
    (zero_stable : forall a : R, 1 + a =r= 1 = true)
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

    
    Lemma zero_add_left : forall c d m,
      matrix_add Node R plusR (zero_matrix Node R zeroR) m c d =r= 
      m c d = true.
    Proof using Node R eqR plusR zeroR 
    zero_left_identity_plus.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_left_identity_plus.
      exact eq_refl.
    Qed.
    
    Lemma zero_add_right : forall c d m, 
      matrix_add Node R plusR m 
      (zero_matrix Node R zeroR) c d =r= 
      m c d = true.
    Proof using Node R eqR plusR zeroR 
    zero_right_identity_plus.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_right_identity_plus.
      exact eq_refl.
    Qed. 

    Lemma matrix_add_assoc : forall m₁ m₂ m₃ c d, 
      matrix_add _ _ plusR m₁ (matrix_add _ _ plusR m₂ m₃) c d =r= 
      matrix_add _ _ plusR (matrix_add Node R plusR m₁ m₂) m₃ c d = true.
    Proof using Node R eqR plusR plus_associative.
      unfold matrix_add; intros.
      rewrite plus_associative;
      exact eq_refl.
    Qed.

    
    Lemma matrix_add_comm : forall m₁ m₂ c d, 
      matrix_add Node R plusR m₁ m₂ c d =r= 
      matrix_add Node R plusR m₂ m₁ c d = true.
    Proof using Node R eqR plusR plus_commutative.
      intros; unfold matrix_add.
      rewrite plus_commutative.
      reflexivity.
    Qed.


    Lemma sum_with_two_var : forall fn ga u v, 
      fn =r= u + v= true -> ga + fn =r= u + (ga + v) = true.
    Proof using R congrP congrR eqR plusR plus_associative 
    plus_commutative refR symR.
      intros.
      unfold bop_congruence in congrP.
      assert (Ht: ga + fn =r= ga + (u + v) = true).
      apply congrP; [apply refR | exact H].
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : u + (ga + v) =r= u + (v + ga) = true).
      apply congrP. apply refR.
      apply plus_commutative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : (u + v) + ga =r= u + (v + ga) = true).
      apply symR, plus_associative.
      rewrite <-Ht. apply congrR.
      apply plus_commutative. 
      apply refR.
    Qed.


    Lemma sum_first_congr : forall fa ga u v fn, 
      fn =r= u + v = true -> 
      fa + ga + fn =r= fa + u + (ga + v) = true.
    Proof using R congrP congrR eqR plusR refR symR
    plus_associative plus_commutative.
      intros.
      pose proof (congrP fa (ga + fn) fa (u + (ga + v)) (refR fa)
        (sum_with_two_var _ _ _ _ H)) as Href.
      rewrite <-Href.
      apply congrR, symR, plus_associative.
      apply symR, plus_associative.
    Qed.
    
    
    Lemma sum_fn_congr : 
      forall (f g : Node -> R) (a : Node) (l : list Node),
      sum_fn Node R zeroR plusR (λ x : Node, f x + g x) l =r= 
      sum_fn Node R zeroR plusR f l + 
      sum_fn Node R zeroR plusR g l = true ->
      f a + g a + sum_fn Node R zeroR plusR (λ x : Node, f x + g x) l =r= 
      f a + sum_fn Node R zeroR plusR f l + 
      (g a + sum_fn Node R zeroR plusR g l) = true.
    Proof using Node R congrP congrR eqR plusR 
    plus_associative plus_commutative refR symR zeroR.
      intros. 
      apply sum_first_congr.
      exact H.
    Qed.
  

    Lemma sum_fn_add : 
      forall (f g : Node -> R) (l : list Node), 
      sum_fn Node R zeroR plusR (fun x => f x + g x) l =r= 
      sum_fn Node R zeroR plusR f l + 
      sum_fn Node R zeroR plusR g l = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    plus_commutative refR symR zeroR zero_left_identity_plus.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_identity_plus.
      + apply sum_fn_congr. 
        exact IHl.
    Qed.


    Lemma mul_gen_left_distr : 
      forall c fa fn gn, 
      fn =r= c * gn = true -> c * fa + fn =r= c * (fa + gn) = true.
    Proof using R congrP congrR eqR left_distributive_mul_over_plus 
    mulR plusR refR.
      intros ? ? ? ? H.
      assert (Ht : c * fa + fn =r= c * fa + c * gn = true).
      apply congrP. 
      apply refR. 
      exact H.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : c * (fa + gn) =r= c * fa + c * gn = true).
      apply left_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply congrP; 
      apply refR.
    Qed.
    


    Lemma mul_constant_left : 
      forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn Node R zeroR plusR (fun x => c * f x) l =r= 
      (c * sum_fn Node R zeroR plusR f l) = true.
    Proof using Node R congrP congrR eqR left_distributive_mul_over_plus 
    mulR plusR refR symR zeroR zero_right_anhilator_mul.
      intros ? ?. 
      induction l; simpl.
      + apply symR,
        zero_right_anhilator_mul.
      + apply mul_gen_left_distr; 
        exact IHl.
    Qed.


    Lemma mul_gen_right_distr : 
      forall c fa fn gn, 
      fn =r= gn * c = true -> fa * c + fn =r= (fa + gn) * c = true.
    Proof using R congrP congrR eqR mulR plusR refR
    right_distributive_mul_over_plus.
      intros.
      assert (Ht : fa * c + fn =r= fa * c + gn * c = true).
      apply congrP. 
      apply refR. 
      exact H.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : (fa + gn) * c =r= fa * c + gn * c = true).
      apply right_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply congrP; 
      apply refR.
    Qed.


    Lemma mul_constant_right : 
      forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn Node R zeroR plusR (fun x => (f x * c)) l =r= 
      sum_fn Node R zeroR plusR f l * c = true.
    Proof using Node R congrP congrR eqR mulR plusR refR
    right_distributive_mul_over_plus symR zeroR zero_left_anhilator_mul.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_anhilator_mul.
      + apply mul_gen_right_distr; exact IHl.
    Qed.


    Lemma push_mul_right_gen : forall a b c d fn gn, 
      fn =r= gn = true -> 
      (a * b + c) * d + fn =r= a * b * d + c * d + gn = true.
    Proof using R congrP eqR mulR plusR 
    right_distributive_mul_over_plus.
      intros. apply congrP.
      apply right_distributive_mul_over_plus.
      exact H.
    Qed.

    (* This need right distributive (a + b) * c = a * c + b * c*)  
    Lemma push_mul_right_sum_fn : 
      forall (l₂ l₁ : list Node) 
      (m₁ m₂ m₃ : Matrix Node R) a x x0,
      sum_fn Node R zeroR plusR (λ y : Node,
        ((m₁ x a * m₂ a y + sum_fn Node R zeroR plusR 
          (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁) * m₃ y x0)) l₂ =r= 
      sum_fn Node R zeroR plusR (λ y : Node, 
        (m₁ x a * m₂ a y * m₃ y x0 + sum_fn Node R zeroR plusR 
          (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁ * m₃ y x0)) l₂ = true.
    Proof using Node R congrP eqR mulR plusR refR
    right_distributive_mul_over_plus zeroR.
      intros.
      revert l₁ m₁ m₂ m₃ a x x0.
      induction l₂; simpl; intros ? ? ? ? ? ? ?.
      + apply refR.
      + apply push_mul_right_gen, IHl₂.
    Qed.



    Local Lemma rewrite_gen_ind : 
      forall a b c d e f g, 
      a * d + f =r= g = true -> 
      a * (b * c + d) + (e * c + f) =r= 
      (a * b + e) * c + g = true.
    Proof using R congrP congrR eqR left_distributive_mul_over_plus mulR
    mul_associative plusR plus_associative plus_commutative refR
    right_distributive_mul_over_plus symR.
      intros.
      assert (Ht : a * (b * c + d) + (e * c + f) =r= 
        a * b * c + a * d + (e * c + f) = true).
      apply congrP.
      assert (Hw : a * b * c + a * d =r= a * (b * c) + a * d = true).
      apply congrP. apply symR. apply mul_associative.
      apply refR. apply symR.
      rewrite <-Hw; clear Hw. 
      apply congrR. apply refR.
      apply left_distributive_mul_over_plus.
      apply refR.
      rewrite <-Ht; clear Ht. 
      apply congrR. 
      apply refR. apply symR.
      assert (Ht : a * b * c + a * d + (e * c + f) =r= 
        a * b * c + (a * d + (e * c + f)) = true).
      apply symR. apply plus_associative.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : a * b * c + (a * d + (e * c + f)) =r= 
        a * b * c + (e * c + a * d + f) = true).
      apply congrP. apply refR.
      assert (Hw : a * d + (e * c + f) =r= 
        a * d + e * c + f = true).
      apply plus_associative.
      rewrite <- Hw; clear Hw.
      apply congrR. apply refR.
      apply congrP. 
      apply plus_commutative.
      apply refR. 
      rewrite <- Ht; clear Ht.
      apply congrR.
      apply refR. apply symR.
      assert (Ht : (a * b + e) * c + g =r= 
        a * b * c + e * c + g = true).
      apply congrP.
      apply right_distributive_mul_over_plus.
      apply refR. apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      assert (Ht : a * b * c + e * c + g =r= 
        a * b * c + (e * c + g) = true).
      apply symR.
      apply plus_associative. 
      apply symR in Ht.
      rewrite <- Ht; clear Ht.
      apply congrR. apply congrP.
      apply refR.
      assert (Ht : e * c + g =r= e * c + (a * d + f) = true).
      apply congrP. apply refR.
      apply symR. exact H.
      apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. apply symR.
      apply plus_associative.
      all: apply refR.
    Qed.

    
    Lemma matrix_mul_gen_assoc : 
      forall l₁ l₂ m₁ m₂ m₃ (c d : Node),
      (matrix_mul_gen Node R zeroR plusR mulR m₁ 
        (matrix_mul_gen Node R zeroR plusR mulR m₂ m₃ l₂) l₁ c d) =r= 
      (matrix_mul_gen Node R zeroR plusR mulR 
        (matrix_mul_gen Node R zeroR plusR mulR  m₁ m₂ l₁) m₃ l₂ c d) = true.
    Proof using Node R congrP congrR eqR left_distributive_mul_over_plus mulR
    mul_associative plusR plus_associative plus_commutative refR
    right_distributive_mul_over_plus symR zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_anhilator_mul.
      intros.
        revert l₁ l₂ m₁ m₂ m₃ c d.
      unfold matrix_mul_gen; induction l₁; simpl;
      intros ? ? ? ? ? ?. 
      +
        induction l₂; simpl.
        ++ apply refR.
        ++ 
          apply symR.
          assert (Ht: 0 * m₃ a d + 
            sum_fn Node R 0 plusR (λ y : Node, 0 * m₃ y d) l₂ =r= 
            0 + sum_fn Node R 0 plusR  (λ y : Node, 0 * m₃ y d) l₂ = true).
          apply congrP. 
          apply zero_left_anhilator_mul.
          apply refR. 
          rewrite <-Ht; clear Ht.
          apply congrR. 
          apply refR.
          assert (Ht : 0 + sum_fn Node R 0 plusR  (λ y : Node, 0 * m₃ y d) l₂ =r=
            sum_fn Node R 0 plusR (λ y : Node, 0 * m₃ y d) l₂ = true).
          apply zero_left_identity_plus. 
          apply symR in Ht.
          rewrite <-Ht. 
          apply congrR.
          exact IHl₂. 
          apply refR.
      (* inductive case *)
      + specialize (IHl₁ l₂ m₁ m₂ m₃ c d).
        (* This one is going to be tricky *)
        assert (Ht: m₁ c a * sum_fn Node R 0 plusR  (λ y : Node, m₂ a y * m₃ y d) l₂ +
          sum_fn Node R 0 plusR 
            (λ y : Node, m₁ c y * 
              sum_fn Node R 0 plusR  (λ y0 : Node, m₂ y y0 * m₃ y0 d) l₂) l₁ =r=
          m₁ c a * sum_fn Node R 0 plusR (λ y : Node, m₂ a y * m₃ y d) l₂ + 
          sum_fn Node R 0 plusR 
            (λ y : Node,
              sum_fn Node R 0 plusR  (λ y0 : Node, m₁ c y0 * m₂ y0 y) l₁ * m₃ y d) l₂ = true).
        apply congrP.
        apply refR. 
        exact IHl₁.
        rewrite <-Ht.
        apply congrR. 
        apply refR.
        clear Ht; clear IHl₁.
        apply symR.
        induction l₂; simpl.
        ++ 
          assert (Ht : m₁ c a * 0 + 0 =r= 0 + 0 = true).
          apply congrP. 
          apply zero_right_anhilator_mul.
          apply refR.
          rewrite <-Ht. apply congrR.
          apply refR. apply symR.
          apply zero_left_identity_plus.
        ++ apply rewrite_gen_ind. exact IHl₂.
    Qed.

    Lemma sum_fn_list_app : 
      forall (l₁ l₂ : list Node) (f : Node -> R), 
      sum_fn Node R zeroR plusR f (l₁ ++ l₂) =r= 
      (sum_fn Node R zeroR plusR f l₁ + sum_fn Node R zeroR plusR f l₂) = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    refR symR zeroR zero_left_identity_plus.
      induction l₁; simpl.
      intros ? ?.
      + apply symR, zero_left_identity_plus.
      + intros ? ?.
        specialize (IHl₁ l₂ f).
        assert (Ht : f a + sum_fn Node R zeroR plusR f l₁ + 
          sum_fn Node R zeroR plusR f l₂ =r= 
          f a + (sum_fn Node R zeroR plusR f l₁ + 
          sum_fn Node R zeroR plusR f l₂) = true).
        apply symR, plus_associative.
        apply symR in Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply congrP.
        apply refR. 
        exact IHl₁.
        apply refR.
    Qed.


    
    Lemma sum_fn_three_list_app : 
      forall (l₁ l₂ l₃ : list Node) 
      (f : Node -> R), 
      sum_fn Node R zeroR plusR f (l₁ ++ l₂ ++ l₃) =r= 
      sum_fn Node R zeroR plusR f l₁ + 
      sum_fn Node R zeroR plusR f l₂ + 
      sum_fn Node R zeroR plusR f l₃ = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    refR symR zeroR zero_left_identity_plus.
      intros. 
      assert (Ht : sum_fn Node R zeroR plusR f (l₁ ++ l₂ ++ l₃) =r= 
        sum_fn Node R zeroR plusR f l₁ + sum_fn Node R zeroR plusR f (l₂ ++ l₃) = true).
      apply sum_fn_list_app. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      assert (Ht: sum_fn Node R zeroR plusR f l₁ + 
        sum_fn Node R zeroR plusR f l₂ + 
        sum_fn Node R zeroR plusR f l₃ =r= 
        sum_fn Node R zeroR plusR f l₁ + 
        (sum_fn Node R zeroR plusR f l₂ + 
        sum_fn Node R zeroR plusR f l₃) = true).
      apply symR. 
      apply plus_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply congrP. 
      apply refR.
      apply sum_fn_list_app.
    Qed.






    Lemma sum_fn_zero : 
      forall (l₁ l₂ : list Node) (f : Node -> R),
      sum_fn Node R zeroR plusR f l₁ =r= 0 = true ->  
      sum_fn Node R zeroR plusR f (l₁ ++ l₂) =r= 
      sum_fn Node R zeroR plusR f l₂ = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    refR symR zeroR zero_left_identity_plus.
      intros ? ? ? Hf.
      assert (sum_fn Node R zeroR plusR f (l₁ ++ l₂) =r= 
      sum_fn Node R zeroR plusR f l₁ + sum_fn Node R zeroR plusR f l₂ = true).
      apply sum_fn_list_app.
      rewrite <-H; clear H.
      apply congrR. 
      apply refR.
      assert (Ht : sum_fn Node R zeroR plusR f l₁ + 
        sum_fn Node R zeroR plusR f l₂ =r= 
        0 + sum_fn Node R zeroR plusR f l₂ = true).
      apply congrP. 
      exact Hf.
      apply refR. 
      apply symR.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR. 
      apply zero_left_identity_plus.
    Qed.

    

   
    Lemma sum_fn_list_eqv_gen : forall (l la lb : list Node) 
      (f : Node -> R), 
      fncong Node eqN R eqR f -> list_eqv Node eqN l (la ++ lb) = true ->
      sum_fn Node R zeroR plusR f l =r= 
      sum_fn Node R zeroR plusR f (la ++ lb) = true.
    Proof using Node R congrP eqN eqR plusR refR zeroR.
      induction l.
      + simpl; intros ? ? ? Hc Hl.
        destruct (la ++ lb).
        simpl. 
        apply refR.
        inversion Hl.
      + intros ? ? ? Hc Hl. 
        destruct la; destruct lb.
        - inversion Hl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          specialize (IHl [] lb f Hc Hlb).
          simpl in IHl. 
          apply congrP.
          apply Hc. 
          exact Hla.
          exact IHl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          apply congrP.
          apply Hc. 
          exact Hla.
          specialize (IHl la [] f Hc Hlb).
          exact IHl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          specialize(IHl la (n0 :: lb) f Hc Hlb).
          apply congrP.
          apply Hc. 
          exact Hla.
          exact IHl.
    Qed.

    Lemma sum_fn_list_eqv : 
      forall (l la lb : list Node) 
      (c : Node) (f : Node -> R), 
      fncong Node eqN R eqR f ->
      list_eqv Node eqN l (la ++ [c] ++ lb) = true ->
      sum_fn Node R zeroR plusR f l =r= 
      sum_fn Node R zeroR plusR f (la ++ [c] ++ lb) = true.
    Proof using Node R congrP eqN eqR plusR refR zeroR.
      intros ? ? ? ? ? Hc Hl.
      exact (sum_fn_list_eqv_gen l la ([c] ++ lb) f Hc Hl).
    Qed. 


    Lemma sum_fn_not_mem : 
      forall (l : list Node) (c d : Node) 
      (m : Node -> Node -> R), 
      in_list eqN l c = false ->
      sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
      0 = true.
    Proof using Node R congrP congrR eqN eqR mulR oneR plusR refR symR zeroR
    zero_left_anhilator_mul zero_left_identity_plus.
      induction l; simpl; intros c d m H.
      + apply refR.
      + apply Bool.orb_false_iff in H.
        destruct H as [Ha Hb]. 
        rewrite Ha.
        specialize (IHl c d m Hb).
        assert (Ht : 0 * m a d + 
          sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
          0 + sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) l 
          = true).
        apply congrP. 
        apply zero_left_anhilator_mul.
        apply refR. 
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply refR.
        apply symR. 
        rewrite <-IHl. 
        apply congrR.
        apply zero_left_identity_plus.
        apply refR.
    Qed.

   
    Lemma matrix_mul_left_identity_gen : 
      forall (l : list Node),
      l <> [] -> 
      (∀ x : Node, in_list eqN l x = true) -> 
      no_dup Node eqN l = true -> 
      forall (m : Matrix Node R) (c d : Node),
      mat_cong Node eqN R eqR m ->
      matrix_mul_gen Node R zeroR plusR mulR 
        (I Node eqN R 0 1) m l c d =r= m c d = true.
    Proof using Node R congrM congrP congrR eqN eqR mulR oneR
    one_left_identity_mul plusR plus_associative refN refR 
    symN symR trnN zeroR zero_left_anhilator_mul 
    zero_left_identity_plus zero_right_identity_plus.
      unfold matrix_mul_gen, I.
      intros ? Hl Hx Hn ? ? ? Hm.
      destruct (list_split _ eqN refN symN trnN l c Hl (Hx c) 
        Hn) as [la [lb [Hleq [Hina Hinb]]]].
      assert (Ht : 
        sum_fn Node R zeroR plusR 
          (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
        sum_fn Node R zeroR plusR 
          (λ y : Node, (if c =n= y then 1 else 0) * m y d) (la ++ [c] ++ lb)
        = true).
      apply sum_fn_list_eqv.
      unfold fncong.
      intros.
      destruct (c =n= a) eqn:Ht.
      pose proof (trnN _ _ _ Ht H) as Hcb.
      rewrite Hcb. 
      assert (Htt : 1 * m a d =r= m a d = true).
      apply one_left_identity_mul.
      rewrite <-Htt; clear Htt. 
      apply congrR.
      apply refR.
      assert (Htt : 1 * m b d =r= m b d = true).
      apply one_left_identity_mul.
      rewrite <-Htt; clear Htt.
      apply congrR. 
      apply refR.
      apply Hm. 
      exact H.
      apply refN.
      case_eq (c =n= b); intros Hf; auto.
      apply symN in H.
      assert (Htt := trnN _ _ _ Hf H).
      rewrite Ht in Htt.
      inversion Htt.

      exact Hleq. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR. 
      assert (Ht : 
        sum_fn Node R zeroR plusR
        (λ y : Node, (if c =n= y then 1 else 0) * m y d) (la ++ [c] ++ lb)
        =r= 
        sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) la + 
        sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) [c] + 
        sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) lb = true).
      apply sum_fn_three_list_app.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      simpl. 
      assert (Hc : c =n= c = true).
      apply refN. 
      rewrite Hc; clear Hc.
      apply symR.
      assert (Ht : 
        sum_fn Node R zeroR plusR
        (λ y : Node, (if c =n= y then 1 else 0) * m y d) la + 
        (1 * m c d + 0) +
        sum_fn Node R zeroR plusR
        (λ y : Node, (if c =n= y then 1 else 0) * m y d) lb =r= 
        0 + (1 * m c d + 0) + 0 = true).
      apply congrP. 
      apply congrP.
      apply sum_fn_not_mem. 
      exact Hina.
      apply refR.
      apply sum_fn_not_mem. 
      exact Hinb.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht : 0 + (1 * m c d + 0) + 0 =r= 
        0 + (1 * m c d + 0) = true).
      apply zero_right_identity_plus. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR. 
      assert (Ht: 0 + (1 * m c d + 0) =r= (1 * m c d + 0) = true).
      apply zero_left_identity_plus.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : 1 * m c d + 0 =r= 1 * m c d = true).
      apply zero_right_identity_plus. 
      rewrite <-Ht; 
      clear Ht. 
      apply congrR.
      apply refR.
      apply symR. 
      apply one_left_identity_mul.
    Qed.

    

    Lemma sum_fn_not_mem_dnode : 
      forall (l : list Node) (c d : Node) 
      (m : Node -> Node -> R), 
      in_list eqN l d = false ->
      sum_fn Node R zeroR plusR 
      (λ y : Node, m c y * (if y =n= d then 1 else 0)) l =r= 0 = true.
    Proof using Node R congrP congrR eqN eqR mulR oneR plusR refR 
    symN symR zeroR zero_right_anhilator_mul zero_right_identity_plus.
      induction l; simpl; intros c d m H.
      + apply refR.
      + apply Bool.orb_false_iff in H.
        destruct H as [Ha Hb].
        assert (a =n= d = false).
        case_eq (a =n= d); intro Hf; auto.
        apply symN in Hf.
        rewrite Hf in Ha.
        inversion Ha.
        rewrite H.
        assert (Ht : 
          m c a * 0 +
          sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) l =r= 
          m c a * 0 + 0 = true).
        apply congrP. 
        apply refR.
        specialize (IHl c d m Hb).
        exact IHl.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply congrP. 
        apply refR.
        apply refR.
        apply symR.
        assert (Ht : m c a * 0 + 0 =r= m c a * 0 = true).
        apply zero_right_identity_plus.
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply refR.
        apply symR.
        apply zero_right_anhilator_mul.
    Qed.

      

    Lemma matrix_mul_right_identity_gen : 
      forall (l : list Node),
      l <> [] -> 
      (∀ x : Node, in_list eqN l x = true) -> 
      no_dup Node eqN l = true -> 
      forall (m : Matrix Node R ) (c d : Node),
      mat_cong Node eqN R eqR m ->
      matrix_mul_gen Node R zeroR plusR mulR 
        m (I Node eqN R 0 1) l c d =r= m c d = true.
    Proof using Node R congrM congrP congrR eqN eqR mulR oneR
    one_right_identity_mul plusR plus_associative refN refR symN symR trnN zeroR
    zero_left_identity_plus zero_right_anhilator_mul zero_right_identity_plus.
      unfold matrix_mul_gen, I.
      intros ? Hl Hx Hn ? ? ? Hm.
      destruct (list_split _ eqN refN symN trnN l d Hl (Hx d) 
        Hn) as [la [lb [Hleq [Hina Hinb]]]].
      assert (Ht : 
        sum_fn Node R zeroR plusR 
          (λ y : Node, m c y * (if y =n= d then 1 else 0)) l =r= 
        sum_fn Node R zeroR plusR
          (λ y : Node, m c y * (if y =n= d then 1 else 0)) (la ++ [d] ++ lb)
        = true).
      apply sum_fn_list_eqv.
      unfold fncong.
      intros.
      destruct (a =n= d) eqn:Ht.
      apply symN in H.
      pose proof (trnN _ _ _ H Ht) as Hbd.
      rewrite Hbd.
      assert (Htt : m c a * 1 =r= m c a = true).
      apply one_right_identity_mul.
      rewrite <-Htt; clear Htt. 
      apply congrR.
      apply refR.
      assert (Htt : m c b * 1 =r= m c b = true).
      apply one_right_identity_mul.
      rewrite <-Htt; clear Htt.
      apply congrR. 
      apply refR.
      apply Hm. 
      apply refN. 
      apply symN in H. 
      exact H.
      case_eq (b =n= d); intros Hf; auto.
      assert (Htt := trnN _ _ _ H Hf).
      rewrite Ht in Htt.
      inversion Htt.
      exact Hleq. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht : 
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) (la ++ [d] ++ lb)
        =r= 
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) la + 
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) [d] + 
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) lb = true).
      apply sum_fn_three_list_app.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      simpl. 
      assert (Hd : d =n= d = true).
      apply refN. 
      rewrite Hd; clear Hd.
      assert (Ht :
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) la +
        (m c d * 1 + 0) +
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) lb =r= 
        0 + (m c d * 1 + 0) + 0 = true).
      apply congrP. 
      apply congrP.
      apply sum_fn_not_mem_dnode. 
      exact Hina.
      apply refR.
      apply sum_fn_not_mem_dnode. 
      exact Hinb.
      apply symR.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht : 0 + (m c d * 1 + 0) + 0 =r= 
        0 + (m c d * 1 + 0)  = true).
      apply zero_right_identity_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht: 0 + (m c d * 1 + 0) =r= (m c d * 1 + 0) = true).
      apply zero_left_identity_plus.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : m c d * 1 + 0 =r= m c d * 1 = true).
      apply zero_right_identity_plus. 
      rewrite <-Ht; 
      clear Ht. 
      apply congrR. 
      apply refR.
      apply symR. 
      apply one_right_identity_mul.
    Qed.

   
    Lemma matrix_mul_assoc : 
      forall m₁ m₂ m₃ (c d : Node),
      matrix_mul Node finN R 0 plusR mulR m₁ 
        (matrix_mul Node finN R 0 plusR mulR m₂ m₃) c d =r= 
      matrix_mul Node finN R 0 plusR mulR 
        (matrix_mul Node finN R 0 plusR mulR m₁ m₂) m₃ c d = true.
    Proof using Node R congrP congrR eqR finN left_distributive_mul_over_plus
    mulR mul_associative plusR plus_associative plus_commutative refR
    right_distributive_mul_over_plus symR zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_anhilator_mul.
      unfold matrix_mul.
      apply matrix_mul_gen_assoc.
    Qed.

    
    Theorem empN : finN <> [].
    Proof.
      intro Hfin.
      destruct finN.
      simpl in lenN;
      nia.
      congruence.
    Qed.


    Lemma matrix_mul_left_identity : 
      forall m (c d : Node), 
      mat_cong Node eqN R eqR m -> 
      matrix_mul Node finN R 0 plusR mulR 
        (I Node eqN R 0 1) m c d =r= m c d = true.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN lenN memN mulR oneR
    one_left_identity_mul plusR plus_associative refN refR symN symR trnN zeroR
    zero_left_anhilator_mul zero_left_identity_plus zero_right_identity_plus.
      unfold matrix_mul.
      apply matrix_mul_left_identity_gen.
      intro Hfin.
      destruct finN.
      simpl in lenN;
      nia.
      congruence.
      apply memN.
      apply dupN.
    Qed.

    Lemma matrix_mul_right_identity : 
      forall m (c d : Node),
      mat_cong Node eqN R eqR m -> 
      matrix_mul Node finN R 0 plusR mulR 
        m (I Node eqN R 0 1) c d =r= m c d = true.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN memN lenN mulR oneR
    one_right_identity_mul plusR plus_associative refN refR symN symR trnN zeroR
    zero_left_identity_plus zero_right_anhilator_mul zero_right_identity_plus.
      unfold matrix_mul.
      apply matrix_mul_right_identity_gen.
      apply empN. 
      apply memN.
      apply dupN.
    Qed.


    (* now prove that slow and fast computes the same value. *)
    Lemma binnat_zero : 
      forall (n : nat), 
      0%N = N.of_nat n -> 
      n = 0%nat.
    Proof.
      induction n; 
      try lia.
    Qed.

  
    Lemma binnat_odd : forall (p : positive) (n : nat), 
      N.pos (xI p) = N.of_nat n -> 
      exists k,  n = (2 * k + 1)%nat /\  (N.pos p) = (N.of_nat k).
    Proof.
      intros p n Hp.
      destruct (Even.even_or_odd n) as [H | H].
      apply Even.even_equiv in H. 
      destruct H as [k Hk].
      (* Even (impossible) Case *)
      rewrite Hk in Hp; lia.
      (* Odd (possible) case *)
      apply Even.odd_equiv in H. 
      destruct H as [k Hk].
      rewrite Hk in Hp. 
      exists k.
      split. 
      exact Hk. 
      lia.
    Qed.

    


    Lemma binnat_even : forall (p : positive) (n : nat), 
      N.pos (xO p) = N.of_nat n :> N -> 
      exists k, n = (Nat.mul 2 k) /\  (N.pos p) = (N.of_nat k).
    Proof.
      intros p n Hp.
      destruct (Even.even_or_odd n) as [H | H].
      apply Even.even_equiv in H. 
      destruct H as [k Hk].
      (* Even (possible) case*)
      rewrite Hk in Hp. 
      exists k.
      split. 
      exact Hk. lia.
      (* Odd (impossible) case *)
      apply Even.odd_equiv in H. 
      destruct H as [k Hk].
      rewrite Hk in Hp. lia.
    Qed.

    (* end of generic nat lemma *)


    Lemma add_r_cong : 
      forall a b c d, a =r= c = true ->
      b =r= d = true -> a + b =r= c + d = true.
    Proof using R congrP eqR plusR.
      intros ? ? ? ? Hac Hbd.
      apply congrP.
      exact Hac.
      exact Hbd.
    Qed.

    Lemma mat_pointwise_cong : 
      forall a b c d e f g h 
      (m₁ m₂ : Matrix Node R), 
      a =n= c = true -> 
      b =n= d = true ->
      e =n= g = true -> 
      f =n= h = true ->
      mat_cong Node eqN R eqR m₁ -> 
      mat_cong Node eqN R eqR m₂ -> 
      m₁ a b * m₂ e f =r=  m₁ c d * m₂ g h = true.
    Proof using Node R congrM eqN eqR mulR.
      intros ? ? ? ? ? ? ? ? ? ? Hac Hbd Heg Hfh
        Hm₁ Hm₂.
      apply congrM.
      apply Hm₁; assumption.
      apply Hm₂; assumption.
    Qed.

    Lemma sum_fn_mul_congr : forall l m₁ m₂ a b c d, 
      (a =n= c) = true  -> (b =n= d) = true ->
      mat_cong Node eqN R eqR m₁ -> 
      mat_cong Node eqN R eqR m₂ ->
      sum_fn Node R zeroR plusR (λ y : Node, m₁ a y * m₂ y b) l =r= 
      sum_fn Node R zeroR plusR (λ y : Node, m₁ c y * m₂ y d) l = true.
    Proof using Node R congrM congrP eqN eqR mulR 
    plusR refN refR zeroR.
      induction l; simpl; 
      intros ? ? ? ? ? ? Hac Hbd Hm₁ Hm₂.
      + apply refR.
      + apply add_r_cong.
        apply mat_pointwise_cong;
        try assumption; try (apply refN).
        apply IHl; assumption.
    Qed.

  
    Lemma mat_mul_cong : 
      forall m₁ m₂ a b c d, 
      a =n= c= true -> 
      b =n= d = true -> 
      mat_cong Node eqN R eqR m₁ -> 
      mat_cong Node eqN R eqR m₂ -> 
      matrix_mul Node finN R 0 plusR mulR m₁ m₂ a b =r= 
      matrix_mul Node finN R 0 plusR mulR m₁ m₂ c d = true.
    Proof using Node R congrM congrP eqN eqR finN mulR 
    plusR refN refR zeroR.
      intros.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_mul_congr; assumption.
    Qed.

    Lemma identity_cong : 
      forall a b c d, 
      (a =n= c) = true -> 
      (b =n= d) = true ->
      I Node eqN R 0 1 a b =r= I Node eqN R 0 1 c d = true.
    Proof using Node R eqN eqR oneR refR symN trnN zeroR.
      intros ? ? ? ? Hac Hbd.
      unfold I.
      case_eq (a =n= b); intros Hf; auto.
      assert (Ht1 := trnN _ _ _ Hf Hbd).
      apply symN in Hac.
      assert (Ht2 := trnN _ _ _ Hac Ht1).
      rewrite Ht2. 
      apply refR.
      case_eq (c =n= d); intros Hcd; auto.
      assert (Had := trnN _ _ _ Hac Hcd).
      apply symN in Hbd.
      assert (Habt := trnN _ _ _ Had Hbd).
      rewrite Habt in Hf.
      inversion Hf.
    Qed.

    
    Lemma mat_exp_cong : 
      ∀ k e (a b c d : Node),
      (a =n= c) = true → 
      (b =n= d) = true →
      mat_cong Node eqN R eqR e →
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k a b =r= 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k c d = true.
    Proof using Node R congrM congrP eqN eqR finN 
    mulR oneR plusR refN refR symN trnN zeroR.
      induction k; simpl; 
      intros ? ? ? ? ? Hac Hbd Hme.
      + apply identity_cong; assumption.
      + apply mat_mul_cong. 
        exact Hac.
        exact Hbd. 
        exact Hme.
        unfold mat_cong; intros.
        apply IHk; assumption.
    Qed.

    
    Lemma sum_fn_mul_congr_diff : 
      forall l (e m₁ m₂ : Matrix Node R) c d,
      two_mat_congr Node R eqR m₁ m₂ ->  
      sum_fn Node R 0 plusR (λ y : Node, e c y * m₁ y d) l =r= 
      sum_fn Node R 0 plusR (λ y : Node, e c y * m₂ y d) l = true.
    Proof using Node R congrM congrP eqR mulR plusR refR zeroR.
      induction l; simpl; 
      intros  ? ? ? ? ? Hm.
      + apply refR.
      + apply add_r_cong.
        apply congrM.
        apply refR.
        apply Hm.
        apply IHl; assumption.
    Qed.

    (* naming is very difficult. I can't come up meaningful names *)
    Lemma mat_mul_cong_diff : 
      forall e m₁ m₂ c d,
      two_mat_congr  Node R eqR m₁ m₂ ->
      matrix_mul Node finN R 0 plusR mulR e m₁ c d =r= 
      matrix_mul Node finN R 0 plusR mulR e m₂ c d = true.
    Proof using Node R congrM congrP eqR finN mulR plusR refR zeroR.
      intros ? ? ? ? ? Hm.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_mul_congr_diff.
      exact Hm.
    Qed.

    
    Lemma push_out_e_unary_nat_gen : forall k1 k2 e c d,
      mat_cong Node eqN R eqR e -> 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR e (k1 + k2)  c d =r= 
      matrix_mul Node finN R 0 plusR mulR 
        (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k1) 
        (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k2) c d = true.
    Proof using Node R congrM congrP congrR dupN lenN eqN eqR finN
    left_distributive_mul_over_plus memN mulR mul_associative oneR
    one_left_identity_mul plusR plus_associative plus_commutative refN refR
    right_distributive_mul_over_plus symN symR trnN zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_anhilator_mul zero_right_identity_plus.
      induction k1; simpl.
      + intros ? ? ? ? ?.
        apply symR, matrix_mul_left_identity.
        unfold mat_cong. intros.
        apply mat_exp_cong; assumption.
      + intros ? ? ? ? He.
        pose proof  (IHk1 k2 e c d He).
        assert (Ht : matrix_mul Node finN R 0 plusR mulR e 
            (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e (k1 + k2)) c d =r=
          matrix_mul  Node finN R 0 plusR mulR e 
            (matrix_mul Node finN R 0 plusR mulR
            (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k1) 
            (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k2)) c d = true).
        apply mat_mul_cong_diff. 
        unfold two_mat_congr; intros.
        apply IHk1. 
        exact He.
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply refR.
        apply symR.
        apply matrix_mul_assoc.
    Qed.


    
    Lemma sum_fn_congr_gen : 
      forall l m₁ m₂ m₃ m₄ a b c d,
      a =n= c = true -> 
      b =n= d = true ->
      two_mat_congr_gen Node eqN R eqR m₁ m₃ -> 
      two_mat_congr_gen Node eqN R eqR m₂ m₄ -> 
      sum_fn Node R 0 plusR (λ y : Node, m₁ a y * m₂ y b) l =r=
      sum_fn Node R 0 plusR (λ y : Node, m₃ c y * m₄ y d) l = true.
    Proof using Node R congrM congrP eqN eqR mulR plusR refN refR zeroR.
      induction l; simpl; 
      intros ? ? ? ? ? ? ? ? Hac Hbd Hm₁ Hm₂.
      + apply refR.
      + apply congrP.
        apply congrM.
        apply Hm₁.
        exact Hac. 
        apply refN.
        apply Hm₂.
        apply refN. 
        exact Hbd.
        apply IHl; 
        (try assumption; try (apply refN)).
    Qed.

    Lemma mat_mul_cong_gen : 
      forall m₁ m₂ m₃ m₄ a b c d,
      a =n= c = true -> 
      b =n= d = true -> 
      two_mat_congr_gen Node eqN R eqR m₁ m₃ -> 
      two_mat_congr_gen Node eqN R eqR m₂ m₄ -> 
      matrix_mul Node finN R 0 plusR mulR m₁ m₂ a b =r= 
      matrix_mul Node finN R 0 plusR mulR m₃ m₄ c d = true.
    Proof using Node R congrM congrP eqN eqR finN mulR 
    plusR refN refR zeroR.
      intros ? ? ? ? ? ? ? ? Hac Hbd H₁ H₂.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_congr_gen; assumption.
    Qed.

    Lemma sum_fn_mat_ind : 
      forall l m₁ m₂ u v, 
      (forall c d, m₁ c d =r= m₂ c d = true) ->
      sum_fn Node R 0 plusR (λ y : Node, m₁ u y * m₁ y v) l =r=
      sum_fn Node R 0 plusR (λ y : Node, m₂ u y * m₂ y v) l = true.
    Proof using Node R congrM congrP eqR mulR plusR refR zeroR.
      induction l; simpl; 
      intros  ? ? ? ? Hm.
      + apply refR.
      +
        apply add_r_cong.
        apply congrM. 
        apply Hm.
        apply Hm.
        apply IHl; assumption.
    Qed.


    Lemma mat_equal_ind : 
      forall m₁ m₂ u v,
      (forall c d, m₁ c d =r= m₂ c d = true) ->
      matrix_mul Node finN R 0 plusR mulR m₁ m₁ u v =r= 
      matrix_mul Node finN R 0 plusR mulR m₂ m₂ u v = true.
    Proof using Node R congrM congrP eqR finN mulR 
    plusR refR zeroR.
      intros ? ? ? ? Hcd.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_mat_ind.
      apply Hcd.
    Qed.


    Lemma matrix_exp_unary_binary_eqv : 
      forall (n : N) (m : Matrix Node R) c d,
      mat_cong Node eqN R eqR m -> 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR m (N.to_nat n) c d =r= 
      matrix_exp_binary Node eqN finN R 0 1 plusR mulR m n c d = true.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN
    left_distributive_mul_over_plus lenN memN mulR mul_associative oneR
    one_left_identity_mul one_right_identity_mul plusR plus_associative
    plus_commutative refN refR right_distributive_mul_over_plus symN symR trnN zeroR
    zero_left_anhilator_mul zero_left_identity_plus zero_right_anhilator_mul
    zero_right_identity_plus.
      destruct n;
      intros ? ? ? Hm.
      + apply refR.
      + 
        assert (Hw : forall w, matrix_exp_binary Node eqN finN R 0 1 plusR mulR m (N.pos w) = 
          repeat_op_ntimes_rec Node finN R 0 plusR mulR m w).
        reflexivity.
        revert c d. 
        induction p.
        rewrite Hw in IHp. 
        rewrite Hw.
        - intros ? ?.
          assert (Ht : N.pos (xI p) = N.of_nat (N.to_nat (N.pos (xI p)))).
          rewrite Nnat.N2Nat.id; reflexivity.
          destruct (binnat_odd p (N.to_nat (N.pos (xI p))) Ht) as 
            [k [Ha Hb]].
          rewrite Ha. 
          rewrite Hb in IHp.
          rewrite Nnat.Nat2N.id in IHp.
          assert (Hv : (2 * k + 1 = 1 + k + k)%nat).
          lia. 
          rewrite Hv; clear Hv.
          simpl. 
          apply mat_mul_cong_diff.
          unfold two_mat_congr; intros u v.
          pose proof push_out_e_unary_nat_gen k k m 
            u v Hm as Htt.
          rewrite <- Htt.
          apply congrR. 
          apply refR.
          apply mat_equal_ind.
          intros. 
          apply symR. 
          apply IHp.
        - intros ? ?. 
          rewrite Hw in IHp. 
          rewrite Hw.
          assert (Ht : N.pos (xO p) = N.of_nat (N.to_nat (N.pos (xO p)))).
          rewrite Nnat.N2Nat.id; reflexivity.
          destruct (binnat_even p (N.to_nat (N.pos (xO p))) Ht) as 
            [k [Ha Hb]].
          rewrite Ha. 
          rewrite Hb in IHp.
          rewrite Nnat.Nat2N.id in IHp.
          assert (Hv : (2 * k = k + k)%nat).
          lia. 
          rewrite Hv; clear Hv.
          simpl.
          pose proof push_out_e_unary_nat_gen k k m 
            c d Hm as Htt.
          rewrite <- Htt; clear Htt.
          apply congrR. 
          apply refR.
          apply mat_equal_ind.
          intros. 
          apply symR. 
          simpl in IHp.
          apply IHp.
        - intros ? ?. 
          simpl.
          apply matrix_mul_right_identity.
          exact Hm.
    Qed.

    Lemma sum_fn_sum_fn_fold : 
      forall l f, 
      sum_fn Node R 0 plusR f l =r= 
      sum_fn_fold Node R 0 plusR f l = true.
    Proof using Node R congrP eqR plusR refR zeroR.
      induction l.
      + simpl; intros ?.
        apply refR.
      + simpl; intros ?.
        apply congrP.
        apply refR.
        apply IHl.
    Qed.



    Lemma matrix_path_equation : forall n m c d,
      mat_cong Node eqN R eqR m -> 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n c d =r= 
      sum_all_rvalues R 0 plusR 
        (get_all_rvalues Node R 1 mulR 
          (construct_all_paths Node eqN R 1 finN m n c d)) = true.
    Proof using Node R congrM congrP congrR eqN eqR finN
    left_distributive_mul_over_plus mulR oneR one_left_identity_mul plusR
    plus_associative refN refR symN symR trnN trnR zeroR zero_left_identity_plus
    zero_right_anhilator_mul zero_right_identity_plus.
      intros ? ? ? ? Hm.
      unfold sum_all_rvalues, get_all_rvalues, construct_all_paths;
      rewrite map_map.
      revert n c d.
      induction n.
      + simpl; intros ? ?; unfold I.
        destruct (c =n= d) eqn:Ht.
        - simpl. apply symR.
          assert (Htw: 1 * 1 + 0 =r= 1 + 0 = true).
          apply congrP.
          apply one_left_identity_mul.
          apply refR.
          rewrite <- Htw; clear Htw.
          apply congrR.
          apply refR.
          apply symR.
          apply zero_right_identity_plus.
        - simpl. apply refR.
      + simpl; intros ? ?.
        unfold matrix_mul, matrix_mul_gen.
        assert (Ht : 
        (sum_fn Node R 0 plusR 
          (λ y : Node, m c y * matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n y d) finN =r=
        fold_right (λ b a : R, b + a) 0
          (map (λ x : list (Node * Node * R), measure_of_path Node R 1 mulR x)
             (append_node_in_paths Node R m c
                (flat_map (λ x : Node, all_paths_klength Node eqN R 1 finN m n x d) finN))))
        =
        (sum_fn_fold Node R 0 plusR  
          (λ y : Node, m c y * matrix_exp_unary Node eqN finN R 0 1 plusR mulR  m n y d) finN =r=
        fold_right (λ b a : R, b + a) 0
          (map (λ x : list (Node * Node * R), measure_of_path Node R 1 mulR x)
             (append_node_in_paths Node R m c
                (flat_map (λ x : Node, all_paths_klength Node eqN R 1 finN m n x d) finN))))).
        apply congrR.
        apply sum_fn_sum_fn_fold.
        apply refR.
        rewrite Ht; clear Ht.
        unfold sum_fn_fold.
        apply symR.
        rewrite <-(fold_map_rel Node eqN refN symN trnN finN R 0 1 plusR mulR eqR refR 
          symR trnR zero_left_identity_plus plus_associative left_distributive_mul_over_plus
          zero_right_anhilator_mul congrP 
          congrM congrR finN m n c d).
        apply congrR.
        apply refR.
        apply fold_right_cong;
        try assumption.
        intros.
        apply congrP.
        apply congrM.
        apply refR.
        apply IHn.
        exact H.
        exact Hm.
    Qed.

    
    Lemma matrix_add_idempotence : forall m c d, 
      matrix_add Node R plusR m m c d =r= m c d = true.
    Proof using Node R eqR plusR plus_idempotence.
      unfold matrix_add; intros *.
      apply plus_idempotence.
    Qed.


  
    Lemma exp_r_pow_add : 
      forall (n m : nat) (a : R), 
      exp_r _ 1 mulR a (n + m) =r= 
      exp_r  _ 1 mulR a n * exp_r  _ 1 mulR a m = true.
    Proof using R congrM congrR eqR mulR mul_associative oneR
    one_left_identity_mul refR symR.
      induction n.
      - simpl; intros ? ?.
        apply symR. 
        apply one_left_identity_mul.
      - simpl; intros ? ?.
        apply symR.
        assert (Ht : (a * exp_r  _ 1 mulR a n * exp_r  _ 1 mulR a m =r= 
          a * exp_r  _ 1 mulR a (n + m)) =
          (a * (exp_r  _ 1 mulR a n * exp_r  _ 1 mulR a m) =r= a * exp_r  _ 1 mulR a (n + m))).
        apply congrR. 
        apply symR.
        apply mul_associative.
        apply refR.
        rewrite Ht; clear Ht.
        apply congrM.
        apply refR.
        apply symR.
        apply IHn.
    Qed.


  

     
    Lemma astar_aide_zero_stable : 
      forall (t : nat) (a : R),
      partial_sum_r R 1 plusR mulR a t + a * exp_r  _ 1 mulR a t =r=
      partial_sum_r R 1 plusR mulR a t = true.
    Proof using R congrM congrP congrR eqR mulR oneR one_left_identity_mul
    one_right_identity_mul plusR plus_associative refR
    right_distributive_mul_over_plus symR zero_stable.
      induction t.
      - simpl; intros ?. 
        rewrite <-(zero_stable a).
        apply congrR.
        apply congrP.
        apply refR.
        apply one_right_identity_mul.
        apply refR.
      - simpl; intros ?. 
      assert (Ht:
      (partial_sum_r R 1 plusR mulR a t + a * exp_r R 1 mulR a t + a * (a * exp_r R 1 mulR a t) =r=
      partial_sum_r R 1 plusR mulR a t + a * exp_r R 1 mulR a t) =
      (partial_sum_r R 1 plusR mulR a t + (a * exp_r R 1 mulR a t + a * (a * exp_r R 1 mulR a t)) =r=
      partial_sum_r R 1 plusR mulR a t + a * exp_r R 1 mulR a t)).
      apply congrR.
      apply symR.
      apply plus_associative.
      apply refR.
      rewrite Ht; clear Ht.
      apply congrP.
      apply refR.
      remember (a * exp_r R 1 mulR a t) as aw.
      assert (Ht : (aw + a * aw =r= aw) =
        (1 * aw + a * aw =r= aw)).
      apply congrR.
      apply congrP.
      apply symR.
      apply one_left_identity_mul.
      apply refR.
      apply refR.
      rewrite Ht; clear Ht.
      assert (Ht : (1 * aw + a * aw =r= aw) =
        ((1 + a) * aw =r= aw)).
      apply congrR.
      apply symR.
      apply right_distributive_mul_over_plus.
      apply refR.
      rewrite Ht; clear Ht.
      assert (Ht : ((1 + a) * aw =r= aw) = 
        (((1 + a) * aw =r= 1 * aw))).
      apply congrR.
      apply refR.
      apply symR.
      apply one_left_identity_mul.
      rewrite Ht; clear Ht.
      apply congrM.
      apply zero_stable.
      apply refR.
    Qed.



    (* special case q := 0 *)
    Lemma astar_exists_zero_stable : 
      forall (t : nat) (a : R), 
      partial_sum_r R 1 plusR mulR a t =r= partial_sum_r R 1 plusR mulR a 0 = true.
    Proof using R congrM congrP congrR eqR mulR oneR one_left_identity_mul
    one_right_identity_mul plusR plus_associative refR
    right_distributive_mul_over_plus symR zero_stable.
      induction t.
      - simpl; intros ?.
        apply refR.
      - simpl; intros ?.
        rewrite <-(astar_aide_zero_stable t a).
        apply congrR.
        apply refR.
        simpl in IHt.
        apply symR.
        exact (IHt a).
    Qed.




    Lemma astar_aide_gen_q_stable :
      forall (t : nat) (a : R),
      (partial_sum_r R 1 plusR mulR a (S t)) =r= 
      (1 + a * partial_sum_r R 1 plusR mulR a t) = true.
    Proof using R congrP congrR eqR
    left_distributive_mul_over_plus mulR oneR plusR
    plus_associative refR symR.
      induction t.
      - simpl; intros ?.
        apply refR.
      - simpl; intros ?.
        simpl in IHt.
        assert (Ht : 1 + a * (partial_sum_r R 1 plusR mulR a t + a * exp_r R 1 mulR  a t) =r=
          (1 + (a * partial_sum_r R 1 plusR mulR a t + a * (a * exp_r R 1 mulR  a t))) = true).
        apply congrP. apply refR.
        apply left_distributive_mul_over_plus.
        apply symR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        assert (Ht : partial_sum_r R 1 plusR mulR a t + 
          a * exp_r R 1 mulR  a t + a * (a * exp_r R 1 mulR  a t) =r=
          1 + a * partial_sum_r R 1 plusR mulR a t + a * (a * exp_r R 1 mulR  a t) = true).
        apply congrP.
        apply IHt. apply refR.
        rewrite <-Ht; clear Ht.
        apply congrR. apply refR.
        assert (Ht : 1 + a * partial_sum_r R 1 plusR mulR a t + a * (a * exp_r R 1 mulR a t) =r= 
          1 +  (a * partial_sum_r R 1 plusR mulR a t + a * (a * exp_r R 1 mulR a t)) = true).
        apply symR. apply plus_associative.
        apply symR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        apply refR.
    Qed.
        

    
    Lemma astar_exists_gen_q_stable : 
      forall (q : nat),
      (forall w : R, partial_sum_r R 1 plusR mulR w q =r= 
        partial_sum_r R 1 plusR mulR w (S q) = true) -> 
      forall (t : nat) (a : R), 
      partial_sum_r R 1 plusR mulR a (t + q) =r= 
      partial_sum_r R 1 plusR mulR a q = true.
    Proof using R congrM congrP congrR eqR
    left_distributive_mul_over_plus mulR oneR plusR
    plus_associative refR symR.
      intros ? q_stable.
      induction t.
      - simpl; intros ?.
        apply refR.
      - simpl; intros ?.
        pose proof (astar_aide_gen_q_stable (t + q) a) as Ht.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        assert (Ht : 1 + a * partial_sum_r R 1 plusR mulR a (t + q) =r= 
          1 + a * partial_sum_r R 1 plusR mulR a q = true).
        apply congrP. apply refR. 
        apply congrM. apply refR.
        apply IHt.
        apply symR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        pose proof (astar_aide_gen_q_stable q a) as Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply q_stable.
        apply refR.
    Qed.

    
    Lemma mat_add_cong_gen : 
      forall m₁ m₂ m₃ m₄ c d, 
      two_mat_congr Node R eqR m₁ m₃ -> 
      two_mat_congr Node R eqR m₂ m₄ -> 
      matrix_add Node R plusR m₁ m₂ c d =r= 
      matrix_add Node R plusR m₃ m₄ c d = true.
    Proof using Node R congrP eqR plusR.
      intros * H₁ H₂.
      unfold matrix_add.
      apply congrP.
      apply H₁; intros *;
      apply refN.
      apply H₂; intros *;
      apply refN.
    Qed.

    
    Lemma sum_fn_mul_distribute_over_plus_left : 
      forall (l : list Node) 
      (m₁ m₂ m₃ : Matrix Node R) (c d : Node),
      (sum_fn Node R 0 plusR (λ y : Node, m₁ c y * (m₂ y d + m₃ y d)) l =r=
      sum_fn Node R 0 plusR (λ y : Node, m₁ c y * m₂ y d) l +
      sum_fn Node R 0 plusR (λ y : Node, m₁ c y * m₃ y d) l) = true.
    Proof using Node R congrP congrR eqR left_distributive_mul_over_plus mulR
    plusR plus_associative plus_commutative refR symR zeroR
    zero_left_identity_plus.
      induction l.
      - simpl. intros ? ? ? ? ?.
        apply symR, zero_left_identity_plus.
      - simpl; intros ? ? ? ? ?.
        pose proof (IHl m₁ m₂ m₃ c d) as IHt.
        remember (sum_fn Node R 0 plusR (λ y : Node, m₁ c y * (m₂ y d + m₃ y d)) l) as sfn₁.
        remember (sum_fn Node R 0 plusR (λ y : Node, m₁ c y * m₂ y d) l) as sfn₂.
        remember (sum_fn Node R 0 plusR (λ y : Node, m₁ c y * m₃ y d) l) as sfn₃.
        assert (Ht : (m₁ c a * (m₂ a d + m₃ a d) + sfn₁ =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃)) = 
        ((m₁ c a * m₂ a d + m₁ c a * m₃ a d) + (sfn₂ + sfn₃) =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃))).
        apply congrR.
        apply congrP.
        apply left_distributive_mul_over_plus.
        apply IHt.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht : 
        (m₁ c a * m₂ a d + m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃)) = 
        (m₁ c a * m₂ a d + (m₁ c a * m₃ a d + (sfn₂ + sfn₃)) =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃))).
        apply congrR.
        apply symR. apply plus_associative.
        apply refR. 
        rewrite Ht; clear Ht.
        assert (Ht : 
        (m₁ c a * m₂ a d + (m₁ c a * m₃ a d + (sfn₂ + sfn₃)) =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃)) =
        (m₁ c a * m₂ a d + (m₁ c a * m₃ a d + (sfn₂ + sfn₃)) =r=
        m₁ c a * m₂ a d + (sfn₂ + (m₁ c a * m₃ a d + sfn₃)))).
        apply congrR.
        apply refR.
        apply symR.
        apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        assert (Ht : 
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r= sfn₂ + (m₁ c a * m₃ a d + sfn₃)) = 
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r= (m₁ c a * m₃ a d + sfn₃) + sfn₂)).
        apply congrR.
        apply refR.
        apply plus_commutative.
        rewrite Ht; clear Ht.
        assert (Ht: 
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r= m₁ c a * m₃ a d + sfn₃ + sfn₂) =
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r= m₁ c a * m₃ a d + (sfn₃ + sfn₂))).
        apply congrR. apply refR.
        apply symR. apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        apply plus_commutative.
    Qed.


    (* Print Grammar constr. *)
    Local Infix "+M" := (matrix_add Node R plusR) (at level 50) : Mat_scope.
    Local Infix "*M" := (matrix_mul Node finN R 0 plusR mulR) (at level 40) : Mat_scope.
        

    Lemma left_distributive_mat_mul_over_plus : 
      forall (m₁ m₂ m₃ : Matrix Node R) (c d : Node), 
      (m₁ *M (m₂ +M m₃)) c d =r= 
      (m₁ *M m₂ +M m₁ *M m₃) c d = true.
    Proof using Node R congrP congrR eqR finN left_distributive_mul_over_plus
    mulR plusR plus_associative plus_commutative refR symR zeroR
    zero_left_identity_plus.
      intros *.
      unfold matrix_mul, matrix_mul_gen,
      matrix_add.
      apply sum_fn_mul_distribute_over_plus_left.
    Qed.
      



    Lemma astar_aide_gen_q_stable_matrix :
      forall (t : nat) (m : Matrix Node R) (c d : Node),
      (partial_sum_mat Node eqN finN R 0 1 plusR mulR m (S t) c d) =r= 
      (I Node eqN R 0 1 +M 
      m *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m t) c d = true.
    Proof using Node R congrM congrP congrR dupN eqN eqR
    finN left_distributive_mul_over_plus memN
    mulR mul_associative oneR one_left_identity_mul
    one_right_identity_mul plusR plus_associative
    plus_commutative plus_idempotence refN refR
    right_distributive_mul_over_plus symN
    symR trnN trnR zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_anhilator_mul
    zero_right_identity_plus.
      induction t.
      - simpl; intros ? ? ?.
        apply refR.
      - simpl; intros ? ? ?.
        remember (partial_sum_mat Node eqN finN R 0 1 plusR mulR m t) as pmt.
        remember (matrix_exp_unary Node eqN finN R 0 1 plusR mulR m t) as umt.
        assert (Ht : ((pmt +M m *M umt) +M m *M (m *M umt)) c d =r=
          ((I Node eqN R 0 1 +M m *M pmt) +M m *M (m *M umt)) c d = true).
        apply mat_add_cong_gen.
        unfold two_mat_congr;
        intros u v. 
        simpl in IHt.
        pose proof (IHt m u v) as IHs.
        rewrite <-Heqpmt in IHs.
        rewrite <-Hequmt in IHs.
        exact IHs.
        unfold two_mat_congr; intros a b.
        apply refR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        apply symR.
        assert (Ht : ((I Node eqN R 0 1 +M m *M pmt) +M m *M (m *M umt)) c d =r= 
          (I Node eqN R 0 1 +M (m *M pmt +M m *M (m *M umt))) c d = true).
        apply symR.
        apply matrix_add_assoc.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        apply symR.
        apply mat_add_cong_gen.
        unfold two_mat_congr; intros a b.
        apply refR.
        unfold two_mat_congr; intros a b.
        apply symR.
        apply left_distributive_mat_mul_over_plus.
    Qed.



    Lemma astar_exists_gen_q_stable_matrix : 
      forall (q : nat) (m : Matrix Node R),
      (forall (c d : Node), 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m q c d =r= 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m (S q) c d = true) -> 
      forall (t : nat)  (u v : Node), 
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m (t + q) u v =r= 
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m q u v = true.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN
    left_distributive_mul_over_plus memN mulR mul_associative oneR
    one_left_identity_mul one_right_identity_mul plusR plus_associative
    plus_commutative plus_idempotence refN refR right_distributive_mul_over_plus
    symN symR trnN trnR zeroR zero_left_anhilator_mul zero_left_identity_plus
    zero_right_anhilator_mul zero_right_identity_plus.
      intros * q_stable.
      induction t.
      - simpl; intros *.
        apply refR.
      - simpl; intros *.
        pose proof (astar_aide_gen_q_stable_matrix (t + q) m u v) as IHs.
        simpl in IHs.
        rewrite <-IHs; clear IHs.
        apply congrR.
        apply refR.
        pose proof (astar_aide_gen_q_stable_matrix q m u v) as Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. apply q_stable.
        apply mat_add_cong_gen.
        unfold two_mat_congr; intros a b.
        apply refR.
        unfold two_mat_congr; intros a b.
        apply mat_mul_cong_diff.
        unfold two_mat_congr; intros ut vt.
        specialize (IHt ut vt).
        exact IHt.
    Qed.



    
    Lemma sum_fn_mul_distribute_over_plus_right : 
      forall (l : list Node) (m₁ m₂ m₃ : Matrix Node R) (c d : Node),
      (sum_fn Node R 0 plusR (λ y : Node, (m₂ c y + m₃ c y) * m₁ y d) l =r=
      sum_fn Node R 0 plusR (λ y : Node, m₂ c y * m₁ y d) l +
      sum_fn Node R 0 plusR (λ y : Node, m₃ c y * m₁ y d) l) = true.
    Proof using Node R congrP congrR eqR mulR plusR plus_associative
    plus_commutative refR right_distributive_mul_over_plus symR zeroR
    zero_left_identity_plus.
      induction l.
      - simpl. intros ? ? ? ? ?.
        apply symR, zero_left_identity_plus.
      - simpl; intros ? ? ? ? ?.
        pose proof (IHl m₁ m₂ m₃ c d) as IHt.
        remember (sum_fn Node R 0 plusR (λ y : Node, (m₂ c y + m₃ c y) * m₁ y d) l) as sfn₁.
        remember (sum_fn Node R 0 plusR (λ y : Node, m₂ c y * m₁ y d) l) as sfn₂.
        remember (sum_fn Node R 0 plusR (λ y : Node, m₃ c y * m₁ y d) l) as sfn₃.
        assert (Ht: 
        ((m₂ c a + m₃ c a) * m₁ a d + sfn₁ =r=
        m₂ c a * m₁ a d + sfn₂ + (m₃ c a * m₁ a d + sfn₃)) =
        ((m₂ c a * m₁ a d + m₃ c a * m₁ a d) + (sfn₂ + sfn₃) =r=
        m₂ c a * m₁ a d + sfn₂ + (m₃ c a * m₁ a d + sfn₃))).
        apply congrR.
        apply congrP.
        apply right_distributive_mul_over_plus.
        exact IHt.
        apply refR.
        rewrite Ht; clear Ht.
        assert(Ht: 
        (m₂ c a * m₁ a d + m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r=
        m₂ c a * m₁ a d + sfn₂ + (m₃ c a * m₁ a d + sfn₃)) =
        (m₂ c a * m₁ a d + (m₃ c a * m₁ a d + (sfn₂ + sfn₃)) =r=
        m₂ c a * m₁ a d + (sfn₂ + (m₃ c a * m₁ a d + sfn₃)))).
        apply congrR.
        apply symR. apply plus_associative.
        apply symR. apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        assert (Ht : 
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r= sfn₂ + (m₃ c a * m₁ a d + sfn₃)) = 
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r= (m₃ c a * m₁ a d + sfn₃) + sfn₂)).
        apply congrR.
        apply refR.
        apply plus_commutative.
        rewrite Ht; clear Ht.
        assert (Ht: 
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r= m₃ c a * m₁ a d + sfn₃ + sfn₂) =
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r= m₃ c a * m₁ a d + (sfn₃ + sfn₂))).
        apply congrR. apply refR.
        apply symR. apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        apply plus_commutative.
    Qed.
    

    Lemma right_distributive_mat_mul_over_plus : 
      forall (m₁ m₂ m₃ : Matrix Node R) (c d : Node), 
      ((m₂ +M m₃) *M m₁) c d =r= 
      (m₂ *M m₁ +M m₃ *M m₁) c d = true.
    Proof using Node R congrP congrR eqR finN mulR plusR plus_associative
    plus_commutative refR right_distributive_mul_over_plus symR zeroR
    zero_left_identity_plus.
      intros *.
      unfold matrix_mul, matrix_mul_gen,
      matrix_add.
      apply sum_fn_mul_distribute_over_plus_right.
    Qed.


  
    Lemma partial_sum_mat_cong : forall n m,
      mat_cong Node eqN R eqR m ->  
      mat_cong Node eqN R eqR (partial_sum_mat Node eqN finN 
      R zeroR oneR plusR mulR m n).
    Proof using Node R congrM congrP eqN eqR finN 
    mulR oneR plusR refN refR symN trnN zeroR.
      unfold mat_cong.
      induction n.
      - simpl; intros ? ? ? ? ? Hm Hac Hbd.
        apply identity_cong; assumption.
      - simpl; intros ? ? ? ? ? HM Hac Hbd.
        remember (partial_sum_mat Node eqN finN 
        R zeroR oneR plusR mulR m n) as pmn.
        remember (matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) as men.
        unfold matrix_add, matrix_mul, 
        matrix_mul_gen.
        apply congrP.
        rewrite Heqpmn.
        apply IHn; assumption.
        apply sum_fn_mul_congr.
        assumption.
        assumption.
        assumption.
        unfold mat_cong.
        intros au av bu bv Hab Hcd.
        rewrite Heqmen.
        apply mat_exp_cong; assumption.
    Qed.

    
    Lemma mat_mul_idem_ind : 
      forall n m c d,  
      (m *M partial_sum_mat Node eqN finN R zeroR oneR plusR mulR m n +M 
        partial_sum_mat Node eqN finN 
        R zeroR oneR plusR mulR m n) c d =r=
      (partial_sum_mat Node eqN finN 
      R zeroR oneR plusR mulR m (S n) c d) = true.
    Proof using Node R congrP congrR eqN eqR finN left_distributive_mul_over_plus
    mulR oneR plusR plus_associative plus_commutative plus_idempotence refR symR
    zeroR zero_left_identity_plus.
      induction n.
      - simpl; intros ? ? ?.
        apply matrix_add_comm.
      - simpl; intros ? ? ?.
        pose proof (IHn m c d) as IHs.
        simpl in IHs.
        remember (partial_sum_mat Node eqN finN 
        R zeroR oneR plusR mulR m n) as m₁.
        remember (matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) as m₂.
        assert (Ht :
        ((m *M (m₁ +M m *M m₂) +M (m₁ +M m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) =
        (((m *M m₁ +M m *M (m *M m₂)) +M (m₁ +M m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply congrP.
        apply left_distributive_mat_mul_over_plus.
        apply refR.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht:
        (((m *M m₁ +M m *M (m *M m₂)) +M (m₁ +M m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) = 
        (((m *M m₁ +M m *M (m *M m₂)) +M (m *M m₁ +M m₁)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply congrP.
        apply congrP.
        apply refR.
        apply refR.
        apply symR.
        apply IHs.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht :
        (((m *M m₁ +M m *M (m *M m₂)) +M (m *M m₁ +M m₁)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) =
        (((m *M m₁ +M m₁) +M (m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply matrix_add_comm.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht:
        (((m *M m₁ +M m₁) +M (m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) = 
        (((m₁ +M m *M m₁) +M (m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply congrP.
        apply matrix_add_comm.
        apply refR.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht: 
        (((m₁ +M m *M m₁) +M (m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) = 
        (((m₁ +M m *M m₁ +M m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply matrix_add_assoc.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht:
        ((((m₁ +M m *M m₁) +M m *M m₁) +M m *M (m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) =
        (((m₁ +M m *M m₁) +M m *M (m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply congrP.
        assert (Htv: 
        (((m₁ +M m *M m₁) +M m *M m₁) c d =r= (m₁ +M m *M m₁) c d) =
        ((m₁ +M (m *M m₁ +M m *M m₁)) c d =r= (m₁ +M m *M m₁) c d)).
        apply congrR.
        apply symR. 
        apply matrix_add_assoc.
        apply symR.
        apply refR.
        rewrite Htv; clear Htv.
        apply congrP.
        apply refR.
        apply plus_idempotence.
        apply refR.
        apply refR.
        rewrite Ht; clear Ht.
        apply congrP.
        rewrite <-IHs.
        apply congrR.
        apply matrix_add_comm.
        apply refR.
        apply refR.
    Qed.

      
    
    Lemma matrix_pow_idempotence :
      forall (n : nat) (m : Matrix Node R) 
      (c d : Node),
      mat_cong Node eqN R eqR m ->
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR (m +M I Node eqN R 0 1) n c d =r= 
      partial_sum_mat Node eqN finN 
      R zeroR oneR plusR mulR m n c d = true.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN
    left_distributive_mul_over_plus lenN memN mulR oneR one_left_identity_mul plusR
    plus_associative plus_commutative plus_idempotence refN refR
    right_distributive_mul_over_plus symN symR trnN zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_identity_plus.
      induction n.
      - simpl; intros ? ? ? Hm.
        apply refR.
      - simpl; intros ? ? ? Hm.
        pose proof (IHn m c d) as IHs.
        assert (Ht : 
        (((m +M I Node eqN R 0 1) *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR (m +M I Node eqN R 0 1) n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M 
          m *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d) =
        (((m +M I Node eqN R 0 1) *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M 
          m *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d)).
        apply congrR.
        apply mat_mul_cong_diff.
        unfold two_mat_congr; intros u v.
        exact (IHn m u v Hm).
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht : 
        (((m +M I Node eqN R 0 1) *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M m 
          *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d) =
        (((m *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M 
          I Node eqN R 0 1 *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M m 
        *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d))).
        apply congrR.
        apply right_distributive_mat_mul_over_plus.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht : 
        ((m *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M I Node eqN R 0 1 
          *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M m 
          *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d) = 
        ((m *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M 
          partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M m 
        *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d)).
        apply congrR.
        apply mat_add_cong_gen.
        unfold two_mat_congr; intros u v.
        apply refR.
        unfold two_mat_congr; intros u v.
        apply matrix_mul_left_identity.
        apply partial_sum_mat_cong; exact Hm.
        apply refR.
        rewrite Ht; clear Ht.
        apply mat_mul_idem_ind.
    Qed.

    
    Lemma connect_partial_sum_mat_paths : forall n m c d,
      mat_cong Node eqN R eqR m -> 
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m n c d =r= 
      partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d = true.
    Proof.
      induction n.
      + intros * Hm; simpl;
        apply refR.
      + intros * Hm; simpl.
        unfold matrix_mul, matrix_add.
        apply congrP.
        exact (IHn m c d Hm).
        pose proof matrix_path_equation (S n) m c d Hm as Hp.
        rewrite <-Hp.
        apply congrR.
        simpl. unfold matrix_mul, 
        matrix_add.
        apply refR.
        apply refR.
    Qed.


    Lemma connect_unary_matrix_exp_partial_sum_paths : forall n m c d,
      mat_cong Node eqN R eqR m -> 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR (m +M I Node eqN R 0 1) n c d =r= 
      partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d = true.
    Proof.
      intros * Hm.
      pose proof matrix_pow_idempotence n m c d Hm as Hp.
      pose proof connect_partial_sum_mat_paths n m c d Hm as Hpp.
      eapply trnR with (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n c d); assumption.
    Qed.


   


    Lemma zero_stable_partial : forall m,
      mat_cong Node eqN R eqR m -> 
      (∀ u v : Node, (u =n= v) = true → (m u v =r= 1) = true) ->
      (forall (c d : Node), 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR  m (length finN - 1) c d =r= 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR  m (length finN) c d = true).
    Proof.
      intros * Hm Huv ? ?.
      rewrite <-(connect_partial_sum_mat_paths
        (length finN - 1) m c d Hm).
      apply congrR.
      apply refR.
      rewrite <-(connect_partial_sum_mat_paths
        (length finN) m c d Hm).
      apply congrR.
      apply refR.
      assert (Hwt: (1 + length finN - 1 = length finN)%nat).
      nia.
      rewrite <-Hwt at 2;
      clear Hwt.
      eapply zero_stable_partial_sum_path with (k := S O) (eqR := eqR)
        (Node := Node) (eqN := eqN) (R := R) (zeroR := 0)
        (oneR := 1) (plusR := plusR) (mulR := mulR)
        (finN := finN) (m := m) (c := c) (d := d);
      try assumption.
    Qed.



    Lemma matrix_fixpoint : forall (n : nat) (m : Matrix Node R) c d,
      mat_cong Node eqN R eqR m ->
      (forall (c d : Node), 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m (length finN) c d =r= 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m (S (length finN)) c d = true) ->  
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
      (m +M I Node eqN R 0 1) (List.length finN) c d =r= 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
      (m +M I Node eqN R 0 1) (n + List.length finN) c d = true.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN
    left_distributive_mul_over_plus lenN memN mulR mul_associative oneR
    one_left_identity_mul one_right_identity_mul plusR plus_associative
    plus_commutative plus_idempotence refN refR right_distributive_mul_over_plus symN
    symR trnN trnR zeroR zero_left_anhilator_mul zero_left_identity_plus
    zero_right_anhilator_mul zero_right_identity_plus.
      intros ? ? ? ? Hm q_stable.
      apply symR.
      assert (Ht:
      (matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
        (m +M I Node eqN R 0 1) (n + length finN) c d =r=
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
        (m +M I Node eqN R 0 1) (length finN) c d) =
      (partial_sum_mat Node eqN finN R 0 1 plusR mulR m (n + length finN) c d =r=
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m (length finN) c d)).
      apply congrR.
      apply matrix_pow_idempotence; exact Hm.
      apply matrix_pow_idempotence; exact Hm.
      rewrite Ht; clear Ht.
      apply astar_exists_gen_q_stable_matrix.
      intros ut vt.
      apply q_stable.
    Qed.


End Matrix_proofs.




      

      
      
  
    
    




  



    
    


  
