From Stdlib Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia PeanoNat Ring_theory.
From Semiring Require Import Definitions
  Listprop Orel Path.
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

 
  Definition sum_fn (f : Node -> R) (l : list Node) : R :=
    List.fold_right (fun x y => f x + y) 0 l.


  (* sum of the elements of a matrix *)


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
    | xI p => 
      let reta := repeat_op_ntimes_rec e p in 
      let retb := matrix_mul reta reta in
      matrix_mul e retb
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

  
  
  (* Dot product of two lists *)
  Definition dot_product (v1 v2 : list R) : R :=
    fold_left plusR (map (fun '(x, y) => mulR x y) 
    (combine v1 v2)) zeroR.
    
  Fixpoint zip_with {A B C : Type} 
    (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
    match xs, ys with
    | x :: xs, y :: ys => f x y :: zip_with f xs ys
    | _, _ => []
    end.

  Fixpoint transpose_eff {A : Type} (xss : list (list A)) : list (list A) :=
    match xss with
    | [] => []
    | xssh :: xsst => 
      match xsst with 
      | [] =>  map (fun y => [y]) xssh 
      | _ :: _ => zip_with List.cons xssh (transpose_eff xsst)
      end 
    end.


  (* Matrix multiplication *)
  Definition matrix_mul_eff (la lb : list (list R)) : list (list R) :=
    let lbT := transpose_eff lb in
    map (fun row =>
      map (fun col => dot_product row col) lbT) la.


  Fixpoint matrix_exp_unary_eff (m : list (list R)) 
    (n : nat) : list (list R) :=
    match n with 
    | 0%nat =>  List.map (fun r => List.map (fun c => I r c) finN) finN 
    | S n' => matrix_mul_eff m (matrix_exp_unary_eff m n')
    end.


  Fixpoint repeat_op_ntimes_rec_eff (e : list (list R)) 
    (n : positive) : list (list R) :=
    match n with
    | xH => e
    | xO p => let ret := repeat_op_ntimes_rec_eff e p in 
      matrix_mul_eff ret ret
    | xI p => let reta := repeat_op_ntimes_rec_eff e p in
      let retb := matrix_mul_eff reta reta in
      matrix_mul_eff e retb
    end.

  Definition matrix_exp_binary_eff (e : list (list R)) (n : N) : list (list R) :=
    match n with
    | N0 => List.map (fun r => List.map (fun c => I r c) finN) finN 
    | Npos p => repeat_op_ntimes_rec_eff e p
    end.
  
  
  Fixpoint mapi_aux {A B : Type} (f : nat -> A -> B) (l : list A) (i : nat) : list B :=
    match l with
    | [] => []
    | x :: xs => f i x :: mapi_aux f xs (S i)
    end.

  Definition mapi {A B : Type} (f : nat -> A -> B) (l : list A) : list B :=
    mapi_aux f l 0.

  (* Build a lookup table from Node to its index in finN *)
  Definition index_map : Node -> nat :=
    let tbl := mapi (fun i n => (n, i)) finN in
    fun x => match List.find (fun '(n, _) => eqN n x) tbl with
      | Some (_, i) => i
      | None => 0%nat (* default case, shouldn't happen if x ∈ finN *)
      end.

  Definition mat_mul_eff_fun (m₁ m₂ : Node -> Node -> R) : Node -> Node -> R :=
    let la := List.map (fun r => List.map (fun c => m₁ r c) finN) finN in 
    let lb := List.map (fun r => List.map (fun c => m₂ r c) finN) finN in 
    let me := matrix_mul_eff la lb in 
    let idx := index_map in 
    fun c d => 
      let row := idx c in
      let col := idx d in
      List.nth col (List.nth row me []) zeroR.

  Definition matrix_exp_unary_eff_fun (m : Node -> Node -> R) (n : nat) 
    : Node -> Node -> R := 
    let la := List.map (fun r => List.map (fun c => m r c) finN) finN in 
    let me := matrix_exp_unary_eff la n in 
    let idx := index_map in 
    fun c d => 
      let row := idx c in
      let col := idx d in
      List.nth col (List.nth row me []) zeroR.

  Definition matrix_exp_binary_eff_fun (m : Node -> Node -> R) (n : N) : 
    Node -> Node -> R := 
    let la := List.map (fun r => List.map (fun c => m r c) finN) finN in 
    let me := matrix_exp_binary_eff la n in 
    let idx := index_map in
    fun c d => 
      let row := idx c in
      let col := idx d in
      List.nth col (List.nth row me []) zeroR.

End Matrix_def.



Section GenProofs.


  Theorem zip_with_length {A B C : Type} 
    (f : A -> B -> C) : ∀ (xs : list A) (ys : list B), 
    List.length (zip_with f xs ys) = 
    Nat.min (List.length xs) (List.length ys).
  Proof.
    induction xs as [|xsh xst ih].
    +
      intros ys; reflexivity. 
    +
      intros *.
      destruct ys as [|ysh yst].
      ++
        cbn; reflexivity.
      ++
        cbn. f_equal.
        eapply ih.
  Qed.

  
  Theorem transpose_map {A : Type} : ∀ (xs : list A ), 
    xs <> [] -> transpose_eff (map (λ y : A, [y]) xs) = [xs].
  Proof.
    induction xs as [|xsh xst ih].
    + 
      intro ha.
      congruence.
    +
      intro ha.
      destruct xst as [|xsth xstt].
      ++
        cbn; reflexivity.
      ++
        remember (xsth :: xstt) as xst.
        cbn.
        assert(hb : map (λ y : A, [y]) xst = [xsth] :: map (λ y : A, [y]) xstt).
        rewrite Heqxst. cbn. reflexivity.
        rewrite hb; clear hb.
        assert (hb : xst <> []). rewrite Heqxst. 
        intro hb. congruence.
        specialize(ih hb).
        rewrite Heqxst in ih.
        assert (hc : map (λ y : A, [y]) (xsth :: xstt) = [xsth] :: 
          map (λ y : A, [y]) xstt).
        cbn. reflexivity. rewrite hc in ih; clear hc.
        rewrite ih. subst. reflexivity.
  Qed.

  
  
  Theorem transpose_zip {A : Type} : ∀ (xss : list (list A)) (xs : list A),
    xss <> [] -> length xs = length xss -> 
    transpose_eff (zip_with cons xs xss) = xs :: transpose_eff xss.
  Proof. 
    induction xss as [|xssh xsst ih].
    +
      intros * ha hb.
      congruence.
    +
      intros * ha hb.
      destruct xsst as [|xssth xsttt].
      ++
        cbn in hb |- *.
        assert (hc : ∃ y : A, xs = [y]).
        {
          destruct xs as [|xsh xst]; 
          cbn in hb; try nia.
          exists xsh.
          destruct xst. cbn in hb.
          reflexivity.
          cbn in hb. nia.
        }
        destruct hc as (y & hc).
        subst. cbn.
        reflexivity.
      ++
        remember (xssth :: xsttt) as xst.
        cbn in hb |- *.
        rewrite Heqxst.
        rewrite <- Heqxst.
        destruct xs as [|xsa xsb]; 
        [cbn in hb; nia | ].
        assert (hc : zip_with cons (xsa :: xsb) (xssh :: xst) = 
          cons xsa xssh :: zip_with cons xsb xst). reflexivity.
        rewrite hc; clear hc.
        inversion hb as [hbb]; clear hb.
        rewrite Heqxst in hbb |- * .
        assert (hb : transpose_eff ((xsa :: xssh) :: 
          zip_with cons xsb (xssth :: xsttt)) = 
          zip_with cons (xsa :: xssh) 
          (transpose_eff (zip_with cons xsb (xssth :: xsttt)))). 
        {
           destruct xsb as [|xsbh xsbt];
          [cbn in hbb; try nia | reflexivity].
        }
        rewrite hb; clear hb.
        assert (hb : xst <> []). subst. 
        intro hb; congruence.
        rewrite <-Heqxst in hbb |- *.
        pose proof (ih xsb hb hbb) as hc.
        rewrite hc. cbn; reflexivity.
  Qed.


  Theorem zip_non_empty {A : Type} :
    ∀ (xss : list (list A)) (xs : list A), 
    xss <> [] -> xs <> [] ->
    zip_with cons xs xss ≠ [].
  Proof.
    destruct xss as [|xssh xsst].
    +
      intros * ha hb.
      congruence.
    +
      intros [|xsh xst] ha hb.
      ++
        congruence.
      ++
        intro hc. cbn in hc.
        congruence.
  Qed.


  Theorem transpose_eff_non_empty {A : Type} : 
    ∀ (xss : list (list A)), xss <> [] -> 
    (∀ (xs : list A), In xs xss -> ∀ (ys : list A), 
      In ys xss -> List.length xs = List.length ys ∧ 0 < List.length xs) -> 
     transpose_eff xss ≠ [].
  Proof.
    induction xss as [|xssh xsst ih].
    +
      intros ha hb; try congruence.
    +
      destruct xsst as [|xssth xsstt].
      ++
        intros ha hb.
        cbn. intro hc.
        specialize (hb xssh (or_introl eq_refl)
          xssh (or_introl eq_refl)).
        destruct hb as (_ & hbr).
        assert(hb : xssh <> []).
        { 
          destruct xssh as [|xsshh xssht];
          cbn in hbr; try nia.
          intro hb. congruence.
        }
        eapply hb.
        eapply map_eq_nil; exact hc.
      ++
        (* inductive case *)
        remember (xssth :: xsstt) as xst.
        intros * ha hb.
        assert(hc : xst <> []).
        {
          subst; intro hc; congruence.
        }
        assert(hd : ∀ xs : list A, In xs xst → ∀ ys : list A, In ys xst →
          length xs = length ys ∧ 0 < length xs).
        {
          intros * he * hf.
          eapply hb; cbn; right; 
          assumption.
        }
        (* i know that  transpose_eff xst ≠ [] 
        and xssh <> [] *)
        specialize(ih hc hd).
        pose proof (hb xssh (or_introl eq_refl) xssh 
        (or_introl eq_refl)) as he.
        destruct he as (_ & her).
        assert (he : xssh <> []).
        {
          destruct xssh as [|xsshh xssht];
          cbn in her; try nia.
          intro he; congruence.
        }
        assert (hf : transpose_eff (xssh :: xst) = 
        zip_with List.cons xssh (transpose_eff xst)).
        { 
          rewrite Heqxst; reflexivity.
        }
        rewrite hf; clear hf.
        eapply zip_non_empty; assumption.
  Qed.


  Theorem zip_map_length {A : Type} : 
    ∀ (ys zs : list A), 
    List.length ys = List.length zs -> 
    length (zip_with cons ys (map (λ y : A, [y]) zs)) = length ys.
  Proof.
    induction ys as [|ysh yst ih].
    +
      intros * ha. cbn; reflexivity.
    +
      intros [|zsh zst] ha.
      ++
        cbn in ha; nia.
      ++
        cbn. rewrite ih.
        reflexivity.
        cbn in ha. inversion ha; subst;
        reflexivity.
  Qed.

  Theorem zip_transpose_length {A : Type} : 
    ∀ (xs ys : list A) zs,
    List.length xs = List.length ys -> 
    List.length ys = List.length zs -> 
    length xs = length (zip_with cons ys zs).
  Proof.
    induction xs as [|xsh xst ih].
    +
      intros [|ysh yst] [|zsh zst] ha hb;
      cbn in ha, hb; try congruence; 
      try reflexivity.
    +
      intros [|ysh yst] [|zsh zst] ha hb;
      cbn in ha, hb; try congruence.
      cbn. erewrite <-ih.
      reflexivity.
      inversion ha; 
      reflexivity.
      inversion hb; reflexivity.
  Qed.


  Theorem transpose_length {A : Type} : 
    ∀ (xst : list (list A)) (xsh : list A),
    0 < List.length xst -> 0 < List.length xsh -> 
    (∀ xs : list A, In xs (xsh :: xst) → ∀ ys : list A, 
    In ys (xsh :: xst) → length xs = length ys ∧ 0 < length xs) ->
    (* transpose_eff (transpose_eff xst) = xst -> *)
    length xsh = length (transpose_eff xst).
  Proof.
    induction xst as [|xsth xstt ih].
    +
      intros * ha hb hc.
      cbn in ha; nia.
    +
      destruct xstt as [|xsstth xssttt].
      ++
        intros [|xshh xsht] ha hb hc.
        *
          cbn in hb; nia.
        *
          pose proof (hc (xshh :: xsht)  (or_introl eq_refl)
            xsth (or_intror (or_introl eq_refl))) as he.
          destruct he as (hel & her).
          cbn. rewrite length_map, <-hel;
          reflexivity.
      ++
        (* induction case *)
        assert (hd : transpose_eff (xsth :: xsstth :: xssttt) = 
          zip_with List.cons xsth (transpose_eff (xsstth :: xssttt))).
        cbn. reflexivity.
        remember (xsstth :: xssttt) as xst.
        intros * ha hb hc.
        rewrite hd.
        destruct (hc xsh (or_introl eq_refl) xsth 
          (or_intror (or_introl eq_refl))) as (hel & her).
        rewrite Heqxst in hc.
        destruct (hc xsth (or_intror (or_introl eq_refl)) 
          xsstth (or_intror (or_intror (or_introl eq_refl)))) as 
          (hfl & hfr).
        assert (hg : 0 < length xst). subst; cbn; nia.
        assert(hf : (∀ xs : list A, In xs (xsh :: xst) → ∀ ys : list A, 
          In ys (xsh :: xst) → length xs = length ys ∧ 0 < length xs)).
        {
          intros * hf * hi.
          apply hc.
          rewrite <- Heqxst.
          firstorder.
          rewrite <-Heqxst.
          firstorder. 
        }
        specialize (ih xsh hg hb hf).
        rewrite Heqxst.
        eapply zip_transpose_length.
        assumption.
        rewrite <-Heqxst.
        nia.
  Qed.
   


  Theorem transpose_eff_involutive {A : Type} :
    ∀ (xss : list (list A)), 
    (forall (xs : list A), In xs xss -> ∀ (ys : list A), 
      In ys xss -> List.length xs = List.length ys ∧ 0 < List.length xs) -> 
    transpose_eff (transpose_eff xss) = xss.
  Proof.
    induction xss as [| xsh xsst ih].
    +
      intro ha. reflexivity.
    +
      destruct xsst as [|xssth xsstt].
      ++
        intro ha. cbn.
        eapply transpose_map.
        specialize (ha xsh (or_introl eq_refl)).
        intro hb. subst. simpl in ha.
        specialize (ha [] (or_introl eq_refl)). 
        nia.
      ++
        intro ha.
        assert (hb : transpose_eff (xsh :: xssth :: xsstt) = 
          zip_with List.cons xsh (transpose_eff (xssth :: xsstt))).
        cbn. reflexivity.
        rewrite hb; clear hb.
        (* induction part *)
        remember (xssth :: xsstt) as xst.
        rewrite transpose_zip.
        *
          rewrite ih;
          [reflexivity | intros * hb * hc].
          eapply ha; cbn; right; assumption.
        *
          eapply transpose_eff_non_empty;
          [intro hb; congruence | intros * hb * hc].
          eapply ha; cbn; right; assumption.
        *
          assert(hb : (∀ xs : list A, In xs xst → ∀ ys : list A, 
          In ys xst → length xs = length ys ∧ 0 < length xs)).
          {
            intros * hb * hc.
            eapply ha; cbn; right;
            assumption.
          }
          specialize(ih hb).
          assert(hc : 0 < List.length xsh).
          {
            destruct (ha xsh (or_introl eq_refl) 
            xsh (or_introl eq_refl)) as (hal & har);
            assumption.
          }
          assert(hd : 0 < List.length xst).
          {
            subst; cbn; nia.
          }
          eapply transpose_length; 
          assumption.
  Qed.


  (* Generalized lemma: dot_product of two lists equals the sum over a   *)
  (* node list of pointwise products, for any semiring-like structure.   *)
  Lemma dot_product_sum_fn_equiv_gen :
    forall (Node R : Type)
      (eqR : brel R) (refR : brel_reflexive R eqR) (symR : brel_symmetric R eqR) (trnR : brel_transitive R eqR)
      (zeroR : R) (plusR mulR : binary_op R)
      (congrP : bop_congruence R eqR plusR) (congrM : bop_congruence R eqR mulR)
      (zero_left_id : forall r : R, eqR (plusR zeroR r) r = true)
      (zero_right_id : forall r : R, eqR (plusR r zeroR) r = true)
      (flpa : forall (l : list R) (a b : R),
        eqR (fold_left plusR l (plusR a b)) (plusR a (fold_left plusR l b)) = true)
      (flca : forall (l : list R) (a b : R),
        eqR a b = true -> eqR (fold_left plusR l a) (fold_left plusR l b) = true)
      (f g : Node -> R) (l1 l2 : list R) (ln : list Node) (def : Node),
    List.length l1 = List.length ln ->
    List.length l2 = List.length ln ->
    (forall (i : nat), (i < List.length ln)%nat ->
      eqR (List.nth i l1 zeroR) (f (List.nth i ln def)) = true) ->
    (forall (i : nat), (i < List.length ln)%nat ->
      eqR (List.nth i l2 zeroR) (g (List.nth i ln def)) = true) ->
    eqR (fold_left plusR (map (fun '(x, y) => mulR x y) (combine l1 l2)) zeroR)
      (List.fold_right (fun y acc => plusR (mulR (f y) (g y)) acc) zeroR ln) = true.
  Proof.
    intros Node R eqR refR symR trnR zeroR plusR mulR congrP congrM
      zero_left_id zero_right_id flpa flca f g l1 l2 ln def
      Hlen1 Hlen2 Hl1 Hl2.
    revert l2 ln Hlen1 Hlen2 Hl1 Hl2.
    induction l1 as [|a1 l1' IH]; intros l2 ln Hlen1 Hlen2 Hl1 Hl2.
    - (* l1 = [] *)
      simpl in Hlen1. symmetry in Hlen1. apply length_zero_iff_nil in Hlen1. subst ln.
      destruct l2; [| simpl in Hlen2; lia].
      simpl. apply refR.
    - (* l1 = a1 :: l1' *)
      simpl in Hlen1, Hlen2.
      destruct l2 as [|a2 l2']; [simpl in Hlen2; lia|].
      destruct ln as [|n ln']; [simpl in Hlen1; lia|].
      simpl in Hlen1, Hlen2.
      inversion Hlen1 as [Hlen1']; inversion Hlen2 as [Hlen2'].
      (* Head element-wise hypotheses *)
      assert (Ha1 : eqR a1 (f n) = true).
      { specialize (Hl1 0%nat). simpl in Hl1. apply Hl1. lia. }
      assert (Ha2 : eqR a2 (g n) = true).
      { specialize (Hl2 0%nat). simpl in Hl2. apply Hl2. lia. }
      (* Tail element-wise hypotheses *)
      assert (Hl1' : forall i, (i < List.length ln')%nat ->
        eqR (List.nth i l1' zeroR) (f (List.nth i ln' def)) = true).
      { intros i Hi. specialize (Hl1 (S i)). simpl in Hl1. apply Hl1. lia. }
      assert (Hl2' : forall i, (i < List.length ln')%nat ->
        eqR (List.nth i l2' zeroR) (g (List.nth i ln' def)) = true).
      { intros i Hi. specialize (Hl2 (S i)). simpl in Hl2. apply Hl2. lia. }
      (* Simplify the goal *)
      simpl (combine (a1 :: l1') (a2 :: l2')).
      simpl (map (fun '(x, y) => mulR x y) _).
      simpl (fold_left plusR _ zeroR).
      (* Goal: eqR (fold_left plusR (map ... (combine l1' l2')) (plusR zeroR (mulR a1 a2)))
                 (plusR (mulR (f n) (g n)) (fold_right ... ln')) *)
      eapply trnR with (y := fold_left plusR (map (fun '(x, y) => mulR x y) (combine l1' l2')) (mulR a1 a2)).
      { apply flca. apply zero_left_id. }
      { eapply trnR with (y := plusR (mulR a1 a2) (fold_left plusR (map (fun '(x, y) => mulR x y) (combine l1' l2')) zeroR)).
        { eapply trnR with (y := fold_left plusR (map (fun '(x, y) => mulR x y) (combine l1' l2')) (plusR (mulR a1 a2) zeroR)).
          { apply flca. apply symR. apply zero_right_id. }
          { apply flpa. } }
        { apply (congrP (mulR a1 a2) (fold_left plusR (map (fun '(x, y) => mulR x y) (combine l1' l2')) zeroR)
            (mulR (f n) (g n)) (fold_right (fun y acc => plusR (mulR (f y) (g y)) acc) zeroR ln')).
          { apply (congrM a1 a2 (f n) (g n) Ha1 Ha2). }
          { apply (IH l2' ln' Hlen1' Hlen2' Hl1' Hl2'). } } }
  Qed.

  
  (* Helper: nth does not depend on default when index is in bounds.    *)
  Lemma nth_default_indep :
    forall (A : Type) (idx : nat) (l : list A) (d1 d2 : A),
    (idx < List.length l)%nat -> List.nth idx l d1 = List.nth idx l d2.
  Proof.
    intros A idx l d1 d2 Hlt.
    generalize dependent idx.
    induction l as [|a l' IH]; intros idx Hlt.
    - inversion Hlt.
    - destruct idx as [|idx'].
      + reflexivity.
      + simpl in Hlt. cbn. 
        eapply IH. nia.
  Qed.

  (* Lemma: transpose swaps indices under nth, as a plain equality.      *)
  Lemma nth_nil (A : Type) (n : nat) (d : A) : List.nth n [] d = d.
  Proof.
    induction n; simpl; reflexivity.
  Qed.

  Lemma nth_singleton_nil (A : Type) (n : nat) : List.nth n [ [] ] ([] : list A) = [].
  Proof.
    induction n; simpl; [reflexivity | destruct n; reflexivity].
  Qed.

  (* Helper lemma: nth 0 of nth i on map singletons = nth i on original *)
  Lemma nth_0_map_singleton :
    forall (A : Type) (l : list A) (i : nat) (d : A),
    List.nth 0 (List.nth i (List.map (fun y => [y]) l) ([] : list A)) d =
    List.nth i l d.
  Proof.
    intros A l i d. revert i.
    induction l as [|x l' IHl]; intros i; simpl.
    - destruct i; reflexivity.
    - destruct i as [|i']; simpl; [reflexivity | apply IHl].
  Qed.

End GenProofs.
         


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
    Proof using zero_left_identity_plus.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_left_identity_plus.
      exact eq_refl.
    Qed.
    
    Lemma zero_add_right : forall c d m, 
      matrix_add Node R plusR m 
      (zero_matrix Node R zeroR) c d =r= 
      m c d = true.
    Proof using zero_right_identity_plus.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_right_identity_plus.
      exact eq_refl.
    Qed. 

    Lemma matrix_add_assoc : forall m₁ m₂ m₃ c d, 
      matrix_add _ _ plusR m₁ (matrix_add _ _ plusR m₂ m₃) c d =r= 
      matrix_add _ _ plusR (matrix_add Node R plusR m₁ m₂) m₃ c d = true.
    Proof using plus_associative.
      unfold matrix_add; intros.
      rewrite plus_associative;
      exact eq_refl.
    Qed.

    
    Lemma matrix_add_comm : forall m₁ m₂ c d, 
      matrix_add Node R plusR m₁ m₂ c d =r= 
      matrix_add Node R plusR m₂ m₁ c d = true.
    Proof using plus_commutative.
      intros; unfold matrix_add.
      rewrite plus_commutative.
      reflexivity.
    Qed.


    Lemma sum_with_two_var : forall fn ga u v, 
      fn =r= u + v= true -> ga + fn =r= u + (ga + v) = true.
    Proof using congrP congrR plus_associative plus_commutative refR symR.
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
    Proof using congrP congrR plus_associative plus_commutative refR symR.
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
    Proof using congrP congrR plus_associative plus_commutative refR symR.
      intros. 
      apply sum_first_congr.
      exact H.
    Qed.
  

    Lemma sum_fn_add : 
      forall (f g : Node -> R) (l : list Node), 
      sum_fn Node R zeroR plusR (fun x => f x + g x) l =r= 
      sum_fn Node R zeroR plusR f l + 
      sum_fn Node R zeroR plusR g l = true.
    Proof using congrP congrR plus_associative plus_commutative refR symR
      zero_left_identity_plus.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_identity_plus.
      + apply sum_fn_congr. 
        exact IHl.
    Qed.


    Lemma mul_gen_left_distr : 
      forall c fa fn gn, 
      fn =r= c * gn = true -> c * fa + fn =r= c * (fa + gn) = true.
    Proof using congrP congrR left_distributive_mul_over_plus refR.
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
    Proof using congrP congrR left_distributive_mul_over_plus refR symR
      zero_right_anhilator_mul.
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
    Proof using congrP congrR refR right_distributive_mul_over_plus.
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
    Proof using congrP congrR refR right_distributive_mul_over_plus
      symR zero_left_anhilator_mul.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_anhilator_mul.
      + apply mul_gen_right_distr; exact IHl.
    Qed.


    Lemma push_mul_right_gen : forall a b c d fn gn, 
      fn =r= gn = true -> 
      (a * b + c) * d + fn =r= a * b * d + c * d + gn = true.
    Proof using congrP right_distributive_mul_over_plus.
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
    Proof using congrP refR right_distributive_mul_over_plus.
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
    Proof using congrP congrR left_distributive_mul_over_plus
      mul_associative plus_associative plus_commutative refR
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
    Proof using congrP congrR left_distributive_mul_over_plus
      mul_associative plus_associative plus_commutative refR
      right_distributive_mul_over_plus symR
      zero_left_anhilator_mul zero_left_identity_plus zero_right_anhilator_mul.
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
    Proof using congrP congrR plus_associative refR symR
      zero_left_identity_plus.
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
    Proof using congrP congrR plus_associative refR symR
      zero_left_identity_plus.
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
    Proof using congrP congrR plus_associative refR
      symR zero_left_identity_plus.
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
    Proof using congrP refR.
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
    Proof using congrP refR.
      intros ? ? ? ? ? Hc Hl.
      exact (sum_fn_list_eqv_gen l la ([c] ++ lb) f Hc Hl).
    Qed. 


    Lemma sum_fn_not_mem : 
      forall (l : list Node) (c d : Node) 
      (m : Node -> Node -> R), 
      in_list eqN l c = false ->
      sum_fn Node R zeroR plusR (λ y : Node, 
      (if c =n= y then 1 else 0) * m y d) l =r= 0 = true.
    Proof using congrP congrR refR symR zero_left_anhilator_mul
      zero_left_identity_plus.
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
    Proof using congrM congrP congrR one_left_identity_mul plus_associative
      refN refR symN symR trnN zero_left_anhilator_mul zero_left_identity_plus
      zero_right_identity_plus.
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
    Proof using congrP congrR refR symN symR zero_right_anhilator_mul
      zero_right_identity_plus.
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
    Proof using congrM congrP congrR one_right_identity_mul plus_associative
      refN refR symN symR trnN zero_left_identity_plus zero_right_anhilator_mul
      zero_right_identity_plus.
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
    Proof using congrP congrR left_distributive_mul_over_plus mul_associative
      plus_associative plus_commutative refR right_distributive_mul_over_plus
      symR zero_left_anhilator_mul zero_left_identity_plus zero_right_anhilator_mul.
      unfold matrix_mul.
      apply matrix_mul_gen_assoc.
    Qed.

    
    Theorem empN : finN <> [].
    Proof using dupN lenN memN.
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
    Proof using congrM congrP congrR dupN lenN memN one_left_identity_mul
      plus_associative refN refR symN symR trnN zero_left_anhilator_mul
      zero_left_identity_plus zero_right_identity_plus.
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
    Proof using congrM congrP congrR dupN lenN memN one_right_identity_mul
      plus_associative refN refR symN symR trnN zero_left_identity_plus
      zero_right_anhilator_mul zero_right_identity_plus.
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
    Proof using lenN.
      induction n; 
      try lia.
    Qed.

  
    Lemma binnat_odd : 
    forall (p : positive) (n : nat), 
    N.pos (xI p) = N.of_nat n -> 
    exists k,  n = (2 * k + 1)%nat /\  (N.pos p) = (N.of_nat k).
  Proof.
    intros p n Hp.
    destruct (Nat.Even_or_Odd  n) as [H | H].
    destruct H as [k Hk]. 
    (* Even (impossible) Case *)
    rewrite Hk in Hp; lia.
    (* Odd (possible) case *)
    destruct H as [k Hk].
    rewrite Hk in Hp. exists k.
    split. exact Hk. lia.
  Qed.

    


  Lemma binnat_even : forall (p : positive) (n : nat), 
    N.pos (xO p) = N.of_nat n :> N -> 
    exists k, n = (Nat.mul 2 k) /\  (N.pos p) = (N.of_nat k).
  Proof.
    intros p n Hp.
    destruct (Nat.Even_or_Odd n) as [H | H].
    destruct H as [k Hk].
    (* Even (possible) case*)
    rewrite Hk in Hp. exists k.
    split. exact Hk. lia.
    (* Odd (impossible) case *)
    destruct H as [k Hk].
    rewrite Hk in Hp. lia.
  Qed.

    (* end of generic nat lemma *)


    Lemma add_r_cong : 
      forall a b c d, a =r= c = true ->
      b =r= d = true -> a + b =r= c + d = true.
    Proof using congrP.
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
    Proof using congrM.
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
    Proof using congrM congrP refN refR.
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
    Proof using congrM congrP refN refR.
      intros.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_mul_congr; assumption.
    Qed.

    Lemma identity_cong : 
      forall a b c d, 
      (a =n= c) = true -> 
      (b =n= d) = true ->
      I Node eqN R 0 1 a b =r= I Node eqN R 0 1 c d = true.
    Proof using refR symN trnN.
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
    Proof using congrM congrP refN refR symN trnN.
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
    Proof using congrM congrP refR.
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
    Proof using congrM congrP refR.
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
    Proof using congrM congrP congrR dupN left_distributive_mul_over_plus
      lenN memN mul_associative one_left_identity_mul plus_associative
      plus_commutative refN refR right_distributive_mul_over_plus symN
      symR trnN zero_left_anhilator_mul zero_left_identity_plus
      zero_right_anhilator_mul zero_right_identity_plus.
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
    Proof using congrM congrP refN refR.
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
    Proof using congrM congrP refN refR.
      intros ? ? ? ? ? ? ? ? Hac Hbd H₁ H₂.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_congr_gen; assumption.
    Qed.

    Lemma sum_fn_mat_ind : 
      forall l m₁ m₂ u v, 
      (forall c d, m₁ c d =r= m₂ c d = true) ->
      sum_fn Node R 0 plusR (λ y : Node, m₁ u y * m₁ y v) l =r=
      sum_fn Node R 0 plusR (λ y : Node, m₂ u y * m₂ y v) l = true.
    Proof using congrM congrP refR.
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
    Proof using congrM congrP refR.
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
    Proof using congrM congrP congrR dupN left_distributive_mul_over_plus
      lenN memN mul_associative one_left_identity_mul one_right_identity_mul
      plus_associative plus_commutative refN refR right_distributive_mul_over_plus
      symN symR trnN zero_left_anhilator_mul zero_left_identity_plus
      zero_right_anhilator_mul zero_right_identity_plus.
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
    Proof using congrP refR.
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
    Proof using congrM congrP congrR left_distributive_mul_over_plus one_left_identity_mul
      plus_associative refN refR symN symR trnN trnR zero_left_identity_plus
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

    
    Lemma matrix_add_idempotence  
      (plus_idempotence : forall a : R, a + a =r= a = true) :
    forall m c d, 
      matrix_add Node R plusR m m c d =r= m c d = true.
    Proof.
      unfold matrix_add; intros *.
      apply plus_idempotence.
    Qed.
    

    
  
    Lemma exp_r_pow_add : 
      forall (n m : nat) (a : R), 
      exp_r _ 1 mulR a (n + m) =r= 
      exp_r  _ 1 mulR a n * exp_r  _ 1 mulR a m = true.
    Proof using congrM congrR mul_associative one_left_identity_mul refR symR.
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

  
  

    (* 0-stable implies *)
    Lemma astar_aide_zero_stable 
      (zero_stable : forall a : R, 1 + a =r= 1 = true) :
      forall (t : nat) (a : R),
      partial_sum_r R 1 plusR mulR a t + a * exp_r  _ 1 mulR a t =r=
      partial_sum_r R 1 plusR mulR a t = true.
    Proof using congrM congrP congrR one_left_identity_mul one_right_identity_mul
      plus_associative refR right_distributive_mul_over_plus symR.
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
    


    
    Lemma astar_aide_gen_q_stable :
      forall (t : nat) (a : R),
      (partial_sum_r R 1 plusR mulR a (S t)) =r= 
      (1 + a * partial_sum_r R 1 plusR mulR a t) = true.
    Proof using congrP congrR left_distributive_mul_over_plus 
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
    

    (* 
      Lemma 4 https://cs.nyu.edu/~mohri/pub/jalc.pdf
    *)
     Lemma astar_exists_gen_q_stable (q : nat) :
      (forall w : R, partial_sum_r R 1 plusR mulR w q =r= 
        partial_sum_r R 1 plusR mulR w (S q) = true) -> 
      forall (t : nat) (a : R), 
      partial_sum_r R 1 plusR mulR a (t + q) =r= 
      partial_sum_r R 1 plusR mulR a q = true.
     Proof using congrM congrP congrR left_distributive_mul_over_plus
       plus_associative refR symR.
       intros * k_closed.
       induction t as [|t Iht];
         intro a.
       +
         simpl; eapply refR.
       +
          pose proof (astar_aide_gen_q_stable (t + q) a) as IHs.
          simpl in IHs.
          rewrite <-IHs; clear IHs.
          apply congrR; [eapply refR |].
          pose proof (astar_aide_gen_q_stable q a) as Ht.
          rewrite <-Ht; clear Ht.
          apply congrR; [eapply k_closed |].
          eapply congrP; [eapply refR | ].
          eapply congrM; [eapply refR | eapply Iht].
     Qed.

     

    (* 0-stable implies q-stable *)
    
     Lemma astar_aide_zero_stable_q_stable :
      forall (t : nat) (a : R) (zero_stable : forall a : R, 1 + a =r= 1 = true),
      partial_sum_r R 1 plusR mulR a t =r= partial_sum_r R 1 plusR mulR a (S t) = true. 
     Proof using congrM congrP congrR one_left_identity_mul one_right_identity_mul
       plus_associative refR right_distributive_mul_over_plus symR.
       intros * zero_stable; simpl.
       eapply symR, astar_aide_zero_stable;
         try assumption.
     Qed.
    
        
    Lemma astar_exists_gen_zero_stable : 
      forall (q : nat),
      (forall w : R, 1 + w =r= 1 = true) -> 
      forall (t : nat) (a : R), 
      partial_sum_r R 1 plusR mulR a (t + q) =r= 
      partial_sum_r R 1 plusR mulR a q = true.
    Proof using congrM congrP congrR left_distributive_mul_over_plus
      one_left_identity_mul one_right_identity_mul plus_associative refR
      right_distributive_mul_over_plus symR.
      intros * zero_stable *.
      eapply astar_exists_gen_q_stable.
      intros; eapply astar_aide_zero_stable_q_stable.
      assumption.      
    Qed.
    
    

    
    Lemma mat_add_cong_gen : 
      forall m₁ m₂ m₃ m₄ c d, 
      two_mat_congr Node R eqR m₁ m₃ -> 
      two_mat_congr Node R eqR m₂ m₄ -> 
      matrix_add Node R plusR m₁ m₂ c d =r= 
      matrix_add Node R plusR m₃ m₄ c d = true.
    Proof using congrP.
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
    Proof using congrP congrR left_distributive_mul_over_plus
      plus_associative plus_commutative refR symR zero_left_identity_plus.
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
    Proof using congrP congrR left_distributive_mul_over_plus plus_associative
      plus_commutative refR symR zero_left_identity_plus.
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
    Proof.
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
    

  
    Lemma astar_exists_gen_q_stable_matrix (q : nat) : 
      forall (m : Matrix Node R),
      (forall (c d : Node), 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m q c d =r= 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m (S q) c d = true) -> 
      forall (t : nat)  (u v : Node), 
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m (t + q) u v =r= 
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m q u v = true.
    Proof using congrM congrP congrR left_distributive_mul_over_plus
      plus_associative plus_commutative refR symR zero_left_identity_plus.
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
        apply congrR. 
        apply q_stable.
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
    Proof using congrP congrR plus_associative plus_commutative refR
      right_distributive_mul_over_plus symR zero_left_identity_plus.
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
    Proof using congrP congrR plus_associative plus_commutative refR
      right_distributive_mul_over_plus symR zero_left_identity_plus.
      intros *.
      unfold matrix_mul, matrix_mul_gen,
      matrix_add.
      apply sum_fn_mul_distribute_over_plus_right.
    Qed.


  
    Lemma partial_sum_mat_cong : forall n m,
      mat_cong Node eqN R eqR m ->  
      mat_cong Node eqN R eqR (partial_sum_mat Node eqN finN 
      R zeroR oneR plusR mulR m n).
    Proof using congrM congrP refN refR symN trnN.
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

    
    (* m +M *)
    Lemma mat_mul_idem_ind 
      (plus_idempotence : forall a : R, a + a =r= a = true) : 
      forall n m c d,  
      (m *M partial_sum_mat Node eqN finN R zeroR oneR plusR mulR m n +M 
        partial_sum_mat Node eqN finN R zeroR oneR plusR mulR m n) c d =r=
      (partial_sum_mat Node eqN finN R zeroR oneR plusR mulR m (S n) c d) = true.
    Proof using congrP congrR left_distributive_mul_over_plus plus_associative
      plus_commutative refR symR zero_left_identity_plus.
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

      
    
    Lemma matrix_pow_idempotence 
      (plus_idempotence : forall a : R, a + a =r= a = true) :
      forall (n : nat) (m : Matrix Node R) (c d : Node),
      mat_cong Node eqN R eqR m ->
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR (m +M I Node eqN R 0 1) n c d =r= 
      partial_sum_mat Node eqN finN R zeroR oneR plusR mulR m n c d = true.
    Proof using congrM congrP congrR dupN left_distributive_mul_over_plus
      lenN memN one_left_identity_mul plus_associative plus_commutative
      refN refR right_distributive_mul_over_plus symN symR
      trnN zero_left_anhilator_mul zero_left_identity_plus zero_right_identity_plus.
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
        eapply plus_idempotence.
    Qed.

    
    Lemma connect_partial_sum_mat_paths : forall n m c d,
      mat_cong Node eqN R eqR m -> 
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m n c d =r= 
      partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d = true.
    Proof using congrM congrP congrR left_distributive_mul_over_plus
      one_left_identity_mul plus_associative refN refR symN symR trnN
      trnR zero_left_identity_plus zero_right_anhilator_mul zero_right_identity_plus.
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


    Lemma connect_unary_matrix_exp_partial_sum_paths 
      (plus_idempotence : forall a : R, a + a =r= a = true) : 
      forall n m c d,
      mat_cong Node eqN R eqR m -> 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR (m +M I Node eqN R 0 1) n c d =r= 
      partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d = true.
    Proof using congrM congrP congrR dupN left_distributive_mul_over_plus
      lenN memN one_left_identity_mul plus_associative plus_commutative
      refN refR right_distributive_mul_over_plus symN
      symR trnN trnR zero_left_anhilator_mul zero_left_identity_plus
      zero_right_anhilator_mul zero_right_identity_plus.
      intros * Hm.
      pose proof matrix_pow_idempotence plus_idempotence n m c d Hm as Hp.
      pose proof connect_partial_sum_mat_paths n m c d Hm as Hpp.
      eapply trnR with (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n c d); 
      assumption.
    Qed.
    

     Lemma zero_stable_partial 
      (zero_stable : forall a : R, 1 + a =r= 1 = true) : 
      forall k m,
      mat_cong Node eqN R eqR m -> 
      (∀ u v : Node, (u =n= v) = true → (m u v =r= 1) = true) ->
      (forall (c d : Node), 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR  m (length finN - 1) c d =r= 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR  m (k + length finN - 1) c d = true).
    Proof.
      intros * Hm Huv ? ?.
      rewrite <-(connect_partial_sum_mat_paths
        (length finN - 1) m c d Hm).
      apply congrR.
      apply refR.
      rewrite <-(connect_partial_sum_mat_paths
        (k + length finN -1) m c d Hm).
      apply congrR.
      apply refR.
      eapply zero_stable_partial_sum_path;
      try assumption.
    Qed.
   

    
    Lemma matrix_fixpoint 
      (plus_idempotence : forall a : R, a + a =r= a = true)
      (zero_stable : forall a : R, 1 + a =r= 1 = true) :
      forall (n : nat) (m : Matrix Node R) c d,
       (∀ u v : Node, (u =n= v) = true → (m u v =r= 1) = true) ->
      mat_cong Node eqN R eqR m ->  
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
      (m +M I Node eqN R 0 1) (List.length finN - 1) c d =r= 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
      (m +M I Node eqN R 0 1) (n + List.length finN - 1) c d = true.
    Proof.
      intros * Ha Hb.
      pose proof connect_unary_matrix_exp_partial_sum_paths.
      rewrite <-(connect_unary_matrix_exp_partial_sum_paths plus_idempotence 
        (length finN - 1) m c d Hb).
      eapply congrR.
      eapply refR.
      rewrite <-(connect_unary_matrix_exp_partial_sum_paths plus_idempotence 
        (n + length finN - 1) m c d Hb).
      eapply congrR.
      eapply refR.
      eapply zero_stable_partial_sum_path; try assumption.
    Qed.


    Theorem zero_stable_implies_idempotence : 
      (forall a : R, 1 + a =r= 1 = true) -> 
      (forall a : R, a + a =r= a = true).
    Proof.
      intros * Ht a.
      specialize (Ht 1).
      assert (Ha : (1 * a + 1 * a =r= a) = ((1 + 1) * a =r= a)).
      apply congrR.
      apply symR.
      apply right_distributive_mul_over_plus.
      apply refR.
      assert (Hb : (a + a =r= a) = (1 * a + 1 * a =r= a)).
      apply congrR.
      eapply congrP.
      apply symR.
      apply one_left_identity_mul.
      apply symR.
      apply one_left_identity_mul.
      apply refR.
      rewrite Ha in Hb.
      rewrite Hb.
      clear Ha Hb. 
      assert (Ha : ((1 + 1) * a =r= a) = (1 * a =r= a)).
      apply congrR.
      apply congrM.
      exact Ht.
      apply refR.
      apply refR.
      rewrite Ha.
      apply one_left_identity_mul.
    Qed.


    Lemma matrix_fixpoint_general 
      (zero_stable : forall a : R, 1 + a =r= 1 = true) :
      forall (n : nat) (m : Matrix Node R) c d,
       (∀ u v : Node, (u =n= v) = true → (m u v =r= 1) = true) ->
      mat_cong Node eqN R eqR m ->  
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
      (m +M I Node eqN R 0 1) (List.length finN - 1) c d =r= 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
      (m +M I Node eqN R 0 1) (n + List.length finN - 1) c d = true.
    Proof.
      intros * Ha Hb. 
      apply matrix_fixpoint; 
      try assumption.
      apply zero_stable_implies_idempotence; 
      try assumption.
    Qed. 


    Lemma matrix_ppath_equation_gen : forall n m c d,
      mat_cong Node eqN R eqR m -> 
      partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d =r=
       sum_all_rvalues R 0 plusR 
        (get_all_rvalues Node R 1 mulR 
          (enum_all_paths_flat Node eqN R oneR finN m n c d)) = true.
    Proof.
      intros * Ha.
      eapply trnR.
      eapply flat_map_path_partial_sum; try assumption.
      eapply symR.
      eapply fold_right_sum_all_flat_paths; try assumption.
    Qed.

    Lemma matrix_ppath_equation : forall n m c d,
      mat_cong Node eqN R eqR m ->
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m n c d =r= 
      sum_all_rvalues R 0 plusR 
        (get_all_rvalues Node R 1 mulR 
          (enum_all_paths_flat Node eqN R oneR finN m n c d)) = true.
    Proof.
      intros * Ha.
      eapply trnR.
      eapply connect_partial_sum_mat_paths;
      try assumption.
      eapply matrix_ppath_equation_gen;
      try assumption.
    Qed.

  

    (* ----------------------------------------------------------------- *)
    (* Helper lemmas for matrix_exp_unary_eff_fun_matrix_unary_eqv       *)
    (* ----------------------------------------------------------------- *)

    (* Custom accessors to avoid List.nth type inference issues           *)
    Definition nthR (l : list R) (n : nat) : R := List.nth n l zeroR.
    Definition nthRL (ll : list (list R)) (i : nat) : list R := List.nth i ll [].
    Definition nthRR (ll : list (list R)) (i j : nat) : R :=
      nthR (nthRL ll i) j.

    (* Helper: accessing the list-of-lists encoding via index_map gives   *)
    (* back the original matrix value, assuming mat_cong.                 *)

    (* Lemma: List.nth n (List.map f l) d1 = f (List.nth n l d2) when    *)
    (* n is within bounds.                                                *)
    Lemma nth_map_any_default :
      forall (A B : Type) (f : A -> B) (l : list A) (n : nat) (d1 : B) (d2 : A),
      (n < List.length l)%nat ->
      List.nth n (List.map f l) d1 = f (List.nth n l d2).
    Proof.
      induction l as [|x l IH]; intros n d1 d2 Hn.
      - simpl in Hn. inversion Hn.
      - simpl.
        destruct n as [|n'].
        + reflexivity.
        + simpl in Hn.
          apply IH.
          nia.
    Qed.

    (* Lemma: index_map returns a valid index into finN, and the node at  *)
    (* that index is eqN-equivalent to the input.                         *)

    (* General lemma: for any list l with no_dup and x in l,             *)
    (* List.find on mapi_aux returns the matching element and its index.  *)
    Lemma find_mapi_aux_correct :
      forall (l : list Node) (x : Node) (start : nat),
      in_list eqN l x = true ->
      no_dup Node eqN l = true ->
      exists (j : nat),
      (j < List.length l)%nat /\
      List.find (fun '(n, _) => eqN n x) (mapi_aux (fun i n => (n, i)) l start) =
      Some (List.nth j l x, (start + j)%nat) /\
      eqN (List.nth j l x) x = true.
    Proof.
      induction l as [|a rest IH]; intros x start Hin Hdup.
      - simpl in Hin. discriminate.
      - simpl in Hin.
        destruct (eqN x a) eqn:Heq_xa.
        + (* eqN x a = true, so eqN a x = true by symN *)
          assert (Heq_ax : eqN a x = true) by (apply symN; exact Heq_xa).
          simpl in Hdup.
          apply Bool.andb_true_iff in Hdup. destruct Hdup as [Hnotin Hdup_rest].
          exists 0%nat.
          split.
          { simpl; nia. }
          split.
          { simpl. rewrite Heq_ax. rewrite Nat.add_0_r. reflexivity. }
          { simpl. exact Heq_ax. }
        + (* eqN x a = false, search in rest *)
          simpl in Hin.
          simpl in Hdup.
          apply Bool.andb_true_iff in Hdup. destruct Hdup as [Hnotin Hdup_rest].
          simpl (mapi_aux _ (a :: rest) start).
          case_eq (eqN a x); intro Heq_ax.
          * (* eqN a x = true: but then eqN x a = true by symN, contradiction *)
            apply symN in Heq_ax.
            rewrite Heq_xa in Heq_ax. discriminate.
          * (* eqN a x = false: skip this element *)
            cbn.
            rewrite Heq_ax.
            destruct (IH x (S start) Hin Hdup_rest) as [j [Hj_len [Hfind Heq_nx]]].
            exists (S j).
            split.
            { simpl; nia. }
            split.
            { simpl. rewrite Hfind. f_equal.  f_equal.  nia. }
            { simpl. exact Heq_nx. }
    Qed.

    Lemma index_map_correct :
      forall (x : Node),
      in_list eqN finN x = true ->
      (index_map Node eqN finN x < List.length finN)%nat /\
      eqN (List.nth (index_map Node eqN finN x) finN x) x = true.
    Proof.
      intros x Hin.
      unfold index_map.
      destruct (find_mapi_aux_correct finN x 0 Hin dupN) as [j [Hj_len [Hfind Heq]]].
      (* Hfind: List.find ... (mapi_aux ... finN 0) = Some (List.nth j finN x, (0 + j)%nat) *)
      (* The goal contains: match List.find ... (mapi ... finN) ... with ... end *)
      (* Note: mapi f finN = mapi_aux f finN 0 *)
      unfold mapi.
      rewrite Hfind.
      simpl.
      split.
      - exact Hj_len.
      - exact Heq.
    Qed.

    Lemma list_encode_access : 
      forall (m : Matrix Node R) c d,
      mat_cong Node eqN R eqR m ->
      nthRR (List.map (fun r => List.map (fun c' => m r c') finN) finN)
        (index_map Node eqN finN c) (index_map Node eqN finN d) =r= m c d = true.
    Proof.
      intros m c d Hm.
      unfold nthRR, nthR, nthRL.
      assert (Hc_correct := index_map_correct c (memN c)).
      assert (Hd_correct := index_map_correct d (memN d)).
      destruct Hc_correct as [Hc_bound Hc_eqN].
      destruct Hd_correct as [Hd_bound Hd_eqN].
      rewrite (nth_map_any_default Node (list R)
        (fun r : Node => List.map (fun c' : Node => m r c') finN)
        finN (index_map Node eqN finN c) ([] : list R) c Hc_bound).
      rewrite (nth_map_any_default Node R
        (fun c' : Node => m (List.nth (index_map Node eqN finN c) finN c) c')
        finN (index_map Node eqN finN d) zeroR d Hd_bound).
      apply (Hm (List.nth (index_map Node eqN finN c) finN c)
                (List.nth (index_map Node eqN finN d) finN d) c d).
      - exact Hc_eqN.
      - exact Hd_eqN.
    Qed.

    (* Helper: fold_right and fold_left coincide for commutative plus.   *)

    (* Lemma: fold_left plusR l (a + b) =r= a + fold_left plusR l b.       *)
    Lemma fold_left_plus_add :
      forall (l : list R) (a b : R),
      fold_left plusR l (a + b) =r= a + fold_left plusR l b = true.
    Proof.
      induction l as [|h t IH]; intros a b.
      - simpl. apply refR.
      - simpl.
        pose proof (IH (a + b) h) as IH1.
        pose proof (IH b h) as IH2.
        eapply trnR with (y := (a + b) + fold_left plusR t h).
        + exact IH1.
        + eapply trnR with (y := a + (b + fold_left plusR t h)).
          * apply symR; apply plus_associative.
          * apply (congrP a (b + fold_left plusR t h) a (fold_left plusR t (b + h))).
            -- apply refR.
            -- apply symR; exact IH2.
    Qed.

    (* Lemma: fold_left respects =r= on the accumulator.                   *)
    Lemma fold_left_congr_acc :
      forall (l : list R) (a b : R),
      a =r= b = true ->
      fold_left plusR l a =r= fold_left plusR l b = true.
    Proof.
      induction l as [|h t IH]; intros a b Heq.
      - simpl. exact Heq.
      - simpl. apply IH. apply congrP; [exact Heq | apply refR].
    Qed.

    Lemma fold_right_plus_comm : 
      forall (l : list R),
      List.fold_right plusR zeroR l =r= 
      List.fold_left plusR l zeroR = true.
    Proof.
      induction l as [|h t IH].
      - (* l = [] *)
        simpl. apply refR.
      - (* l = h :: t *)
        simpl (List.fold_right plusR zeroR (h :: t)).
        simpl (List.fold_left plusR (h :: t) zeroR).
        (* Goal: h + fold_right plusR 0 t =r= fold_left plusR t (0 + h) *)
        eapply trnR with (y := h + List.fold_left plusR t zeroR).
        + (* h + fold_right ... t =r= h + fold_left ... t 0 *)
          apply (congrP h (List.fold_right plusR zeroR t)
            h (List.fold_left plusR t zeroR)).
          * apply refR.
          * exact IH.
        + (* Goal: h + fold_left plusR t 0 =r= fold_left plusR t (0 + h) *)
          eapply trnR with (y := List.fold_left plusR t h).
          * (* h + fold_left plusR t 0 =r= fold_left plusR t h *)
            apply symR.
            eapply trnR with (y := List.fold_left plusR t (h + 0)).
            -- apply (fold_left_congr_acc t h (h + 0)).
               apply symR; apply zero_right_identity_plus.
            -- apply fold_left_plus_add.
          * (* fold_left ... t h =r= fold_left ... t (0 + h) *)
            apply (fold_left_congr_acc t h (0 + h)).
            apply symR; apply zero_left_identity_plus.
    Qed.

    (* Helper: if b =r= c then a + b =r= a + c *)
    Lemma plus_congr_right : forall a b c, b =r= c = true -> a + b =r= a + c = true.
    Proof using congrP refR.
      intros a b c H.
      unfold bop_congruence in congrP.
      apply (congrP a b a c (refR a) H).
    Qed.

    (* Helper: sum_fn f finN equals fold_right plusR 0 (map f finN).     *)
    Lemma sum_fn_eq_map_fold : 
      forall (f : Node -> R),
      sum_fn Node R zeroR plusR f finN =r=
      List.fold_right plusR zeroR (List.map f finN) = true.
    Proof.
      intros f.
      unfold sum_fn.
      (* Generalize: prove over any list l *)
      assert (H : forall (l : list Node),
        List.fold_right (fun x y => f x + y) zeroR l =r=
        List.fold_right plusR zeroR (List.map f l) = true).
      {
        induction l as [|a l' IHl].
        - simpl. apply refR.
        - simpl.
          (* Goal: f a + fold_right (...) 0 l' =r= f a + fold_right plusR 0 (map f l') *)
          (* IHl: fold_right (...) 0 l' =r= fold_right plusR 0 (map f l') *)
          assert (Hr := refR (f a)).
          pose proof (congrP (f a) (List.fold_right (fun x y => f x + y) zeroR l')
            (f a) (List.fold_right plusR zeroR (List.map f l')) Hr IHl) as Hgoal.
          exact Hgoal.
      }
      apply H.
    Qed.

   
    (* Helper: dot_product of row i of la and col j of lb                *)
    (* equals sum_fn (fun y => m₁ (node_i) y * m₂ y (node_j)) finN.      *)

    (* Lemma: if two lists l1, l2 (of length = length finN) element-wise  *)
    (* encode functions f, g over finN, then dot_product l1 l2 equals     *)
    (* sum_fn (fun y => f y * g y) finN.                                   *)
    Lemma dot_product_sum_fn_equiv :
      forall (f g : Node -> R) (l1 l2 : list R) (def : Node),
      List.length l1 = List.length finN ->
      List.length l2 = List.length finN ->
      (forall (i : nat), (i < List.length finN)%nat ->
        List.nth i l1 zeroR =r= f (List.nth i finN def) = true) ->
      (forall (i : nat), (i < List.length finN)%nat ->
        List.nth i l2 zeroR =r= g (List.nth i finN def) = true) ->
      fold_left plusR (map (fun '(x, y) => mulR x y) (combine l1 l2)) zeroR =r=
      sum_fn Node R zeroR plusR (fun y : Node => f y * g y) finN = true.
    Proof.
      intros f g l1 l2 def Hlen1 Hlen2 Hl1 Hl2.
      unfold sum_fn.
      apply (dot_product_sum_fn_equiv_gen Node R eqR refR symR trnR
        zeroR plusR mulR congrP congrM
        zero_left_identity_plus zero_right_identity_plus
        fold_left_plus_add fold_left_congr_acc
        f g l1 l2 finN def Hlen1 Hlen2 Hl1 Hl2).
    Qed.

    (* Helper: if eqN a (nth n l d) and n < length l, then a ∈ in_list.  *)
    Lemma nth_in_list :
      forall (l : list Node) (n : nat) (d a : Node),
      (n < List.length l)%nat ->
      eqN a (List.nth n l d) = true ->
      in_list eqN l a = true.
    Proof.
      induction l as [|x l' IH]; intros n d a Hn Heq.
      - simpl in Hn; lia.
      - destruct n as [|n'].
        + simpl in Heq. simpl.
          rewrite Heq. reflexivity.
        + simpl in Hn.
          simpl. apply Bool.orb_true_iff. right.
          apply (IH n' d a).
          * lia.
          * exact Heq.
    Qed.

    (* Helper: in a no_dup list, if two positions have eqN-equivalent     *)
    (* elements, then the positions are equal.                            *)
    Lemma nth_no_dup_inj :
      forall (l : list Node) (i j : nat) (d : Node),
      no_dup Node eqN l = true ->
      (i < List.length l)%nat -> (j < List.length l)%nat ->
      eqN (List.nth i l d) (List.nth j l d) = true -> i = j.
    Proof.
      induction l as [|a l' IH]; intros i j d Hdup Hi Hj Heq.
      - simpl in Hi; lia.
      - simpl in Hdup.
        apply Bool.andb_true_iff in Hdup. destruct Hdup as [Hnotin Hdup_l'].
        assert (Hin_false : in_list eqN l' a = false).
        { destruct (in_list eqN l' a); [discriminate | reflexivity]. }
        destruct i as [|i']; destruct j as [|j'].
        + (* i=0, j=0 *) reflexivity.
        + (* i=0, j=S j' *)
          simpl in Heq.
          (* Heq: eqN a (nth j' l' d) = true,
             but in_list l' a = false, contradiction via nth_in_list *)
          apply nth_in_list with (n := j') (d := d) in Heq.
          * rewrite Heq in Hin_false. discriminate.
          * simpl in Hj; lia.
        + (* i=S i', j=0 *)
          simpl in Heq.
          apply symN in Heq.
          apply nth_in_list with (n := i') (d := d) in Heq.
          * rewrite Heq in Hin_false. discriminate.
          * simpl in Hi; lia.
        + (* i=S i', j=S j' *)
          simpl in Heq. simpl in Hi, Hj.
          f_equal.
          apply (IH i' j' d Hdup_l'); [lia | lia | exact Heq].
    Qed.

    Lemma index_map_nth :
      forall (i : nat) (default_n : Node),
      (i < List.length finN)%nat ->
      index_map Node eqN finN (List.nth i finN default_n) = i.
    Proof.
      intros i default_n Hi.
      set (x := List.nth i finN default_n).
      assert (Hin : in_list eqN finN x = true).
      { apply nth_in_list with (n := i) (d := default_n); [exact Hi | apply refN]. }
      destruct (find_mapi_aux_correct finN x 0 Hin dupN) as [j [Hj_bound [Hfind Heq]]].
      unfold index_map, mapi.
      rewrite Hfind. simpl.
      assert (Heq' : eqN (List.nth j finN default_n) (List.nth i finN default_n) = true).
      {
        subst x.
        assert (Htmp := nth_default_indep Node j finN (nth i finN default_n) default_n Hj_bound).
        rewrite Htmp in Heq. exact Heq.
      }
      apply (nth_no_dup_inj finN j i default_n dupN Hj_bound Hi Heq').
    Qed.

    (* Lemma: transpose_eff swaps nthRR indices.                          *)

    (* ----------------------------------------------------------------- *)
    (* Helper: inversion lemma for In (zip_with cons xs yss)             *)
    Lemma in_zip_with_cons_inv {A : Type} (xs : list A) (yss : list (list A)) (zs : list A) :
      In zs (zip_with cons xs yss) ->
      exists x ys, zs = x :: ys /\ In x xs /\ In ys yss.
    Proof.
      revert xs yss.
      induction xs as [|x xs IH]; intros yss Hin.
      - simpl in Hin. inversion Hin.
      - destruct yss as [|ys yss]; [simpl in Hin; inversion Hin|].
        simpl in Hin. destruct Hin as [Heq | Hin_tl].
        subst. exists x, ys.
        split; [reflexivity | split; [left; reflexivity | left; reflexivity]].
        apply IH in Hin_tl.
        destruct Hin_tl as [x' [ys' [Heq [Hx' Hys']]]].
        subst. exists x', ys'.
        split; [reflexivity | split; [right; exact Hx' | right; exact Hys']].
    Qed.

    (* ----------------------------------------------------------------- *)
    (* General fact: for an M×N matrix, transpose_eff gives an N×M matrix. *)

    (* Helper: all rows of a non-empty list have the same length          *)
    Definition all_rows_same_length {A : Type} (lb : list (list A)) (L : nat) : Prop :=
      forall (xs : list A), In xs lb -> List.length xs = L.

    (* If lb has M rows of length L (M>0, L>0), then transpose_eff lb   *)
    (* has L rows of length M.                                            *)
    Lemma transpose_eff_rows_cols {A : Type} (lb : list (list A)) (M L : nat) :
      List.length lb = M ->
      all_rows_same_length lb L ->
      0 < M -> 0 < L ->
      List.length (transpose_eff lb) = L /\
      all_rows_same_length (transpose_eff lb) M.
    Proof.
      revert M L.
      induction lb as [|r1 lb' IH]; intros M L HlenM Hrows HposM HposL.
      - (* lb = [], M = 0 contradicts HposM *)
        simpl in HlenM. lia.
      - (* lb = r1 :: lb' *)
        simpl in HlenM.
        assert (Hlen_r1 : List.length r1 = L).
        { apply Hrows. simpl; auto. }
        destruct lb' as [|r2 lb''].
        + (* lb = [r1], M = 1 *)
          simpl in HlenM. subst M.
          assert (Hpos_r1 : 0 < List.length r1) by lia.
          split.
          { (* length (transpose_eff [r1]) = L *)
            simpl (transpose_eff [r1]).
            rewrite length_map. exact Hlen_r1. }
          { (* all rows of transpose_eff [r1] have length 1 *)
            unfold all_rows_same_length.
            intros xs Hin.
            apply in_map_iff in Hin.
            destruct Hin as [y [Hy Hin_r1]].
            subst xs. simpl. reflexivity. }
        + (* lb = r1 :: r2 :: lb'', M >= 2 *)
          simpl (transpose_eff (r1 :: r2 :: lb'')).
          assert (Hpos_M' : 0 < List.length (r2 :: lb'')).
          { simpl. pose proof HlenM. simpl in H. lia. }
          assert (Hrows_tail : all_rows_same_length (r2 :: lb'') L).
          { intros xs Hin. apply Hrows. simpl; auto. }
          assert (Hlen_tail : List.length (r2 :: lb'') = M - 1).
          { simpl. rewrite <-HlenM. cbn. lia. }
          (* Note: M-1 could be 0 when M=1, but M>=2, so M-1 >= 1 > 0 *)
          assert (Hpos_M'_gt0 : 0 < M - 1) by lia.
          (* Apply IH to the tail *)
          assert (Htrans := IH (M-1) L Hlen_tail Hrows_tail Hpos_M'_gt0 HposL).
          destruct Htrans as [Hlen_trans Hrows_trans].
          (* Part 1: length of zip_with *)
          split.
          * (* length (zip_with cons r1 (transpose_eff (r2 :: lb''))) = L *)
            rewrite zip_with_length.
            rewrite Hlen_r1.
            rewrite <- Hlen_trans.
            rewrite PeanoNat.Nat.min_id.
            reflexivity.
          * (* all rows of zip_with have length M *)
            unfold all_rows_same_length.
            intros xs Hin.
            apply in_zip_with_cons_inv in Hin.
            destruct Hin as [x [ys [Heq [Hin_r1 Hin_trans]]]].
            subst xs.
            simpl.
            assert (Hlen_ys : List.length ys = M - 1).
            { apply Hrows_trans. exact Hin_trans. }
            lia.
    Qed.

    (* Helper: nth on zip_with cons when i is in bounds of both lists    *)
    Lemma nth_zip_with_cons_in_bounds {A : Type} (xs : list A) (yss : list (list A)) (i : nat) :
      forall (ndv : A),
      (i < List.length xs)%nat -> (i < List.length yss)%nat ->
      List.nth i (zip_with cons xs yss) [] =
      List.cons (List.nth i xs ndv) (List.nth i yss []).
    Proof.
      revert xs yss.
      induction i as [|i IH]; intros xs yss ndv Hxs Hyss.
      - (* i = 0 *)
        destruct xs as [|x xs]; [simpl in Hxs; lia |].
        destruct yss as [|ys yss]; [simpl in Hyss; lia |].
        simpl. reflexivity.
      - (* i = S i *)
        destruct xs as [|x xs]; [simpl in Hxs; lia |].
        destruct yss as [|ys yss]; [simpl in Hyss; lia |].
        simpl. apply IH; simpl in Hxs, Hyss; lia.
    Qed.

    (* Helper: nth on zip_with cons when i is out of bounds              *)
    Lemma nth_zip_with_cons_overflow {A : Type} (xs : list A) (yss : list (list A)) (i : nat) :
      (List.length xs <= i \/ List.length yss <= i)%nat ->
      List.nth i (zip_with cons xs yss) [] = [].
    Proof.
      intros Hle.
      apply nth_overflow.
      rewrite zip_with_length.
      destruct Hle as [Hle | Hle].
      - refine (Nat.le_trans _ _ _ (Nat.le_min_l _ _) Hle).
      - refine (Nat.le_trans _ _ _ (Nat.le_min_r _ _) Hle).
    Qed.

    (* Helper: plain equality for nth on transpose_eff                    *)
    Lemma nth_transpose_eff_eq :
      forall (lb : list (list R)) (i j : nat),
      (forall (xs : list R), In xs lb -> List.length xs = List.length finN) ->
      List.nth j (List.nth i (transpose_eff lb) []) zeroR =
      List.nth i (List.nth j lb []) zeroR.
    Proof.
      induction lb as [|r lb' IH]; intros i j Hrows.
      - simpl. destruct i, j; reflexivity.
      - assert (Hlen_r : List.length r = List.length finN).
        { apply Hrows. simpl; auto. }
        destruct lb' as [|r' lb''].
        + (* single row [r] *)
          simpl.
          destruct (i <? List.length r)%nat eqn:Hi.
          * apply Nat.ltb_lt in Hi.
            rewrite (nth_map_any_default R (list R) (fun y => [y]) r i [] zeroR Hi).
            destruct j; simpl; [reflexivity |].
            destruct j; simpl; [destruct i; reflexivity |].
            destruct i; reflexivity.
          * apply Nat.ltb_ge in Hi.
            rewrite (nth_overflow (List.map (fun y : R => [y]) r) ([] : list R)).
            { destruct j; simpl.
              - rewrite (nth_overflow r zeroR); [reflexivity | exact Hi].
              - destruct j; simpl; [destruct i; reflexivity | destruct i; reflexivity]. }
            { rewrite length_map. exact Hi. }
        + (* multiple rows r :: r' :: lb'' *)
          simpl.
          assert (Hrows_rest : forall xs, In xs (r' :: lb'') -> List.length xs = List.length finN).
          { intros xs Hin. apply Hrows. simpl; auto. }
          assert (Hlen_rest : List.length (transpose_eff (r' :: lb'')) = List.length finN).
          {
            set (M := List.length (r' :: lb'')). set (L := List.length finN).
            assert (HlenM : List.length (r' :: lb'') = M) by reflexivity.
            assert (HposM : 0 < M).
            { subst M; simpl. pose proof Hlen_r. assert (2 <= List.length finN)%nat by apply lenN. lia. }
            assert (HposL : 0 < L).
            { subst L. assert (2 <= List.length finN)%nat by apply lenN. lia. }
            pose proof (transpose_eff_rows_cols (r' :: lb'') M L HlenM Hrows_rest HposM HposL)
              as [Hlen_t' _].
            exact Hlen_t'.
          }
          destruct (i <? List.length finN)%nat eqn:Hi.
          * apply Nat.ltb_lt in Hi.
            assert (Hi_r : (i < List.length r)%nat) by lia.
            assert (Hi_t : (i < List.length (transpose_eff (r' :: lb'')))%nat) by lia.
            (* Directly use nth_zip_with_cons_in_bounds by matching the goal *)
            match goal with
            | [ |- context [ List.nth ?j (List.nth ?i (zip_with ?c ?x ?y) []) ?d ] ] =>
              pose proof (nth_zip_with_cons_in_bounds x y i zeroR Hi_r Hi_t) as Hzip;
              rewrite Hzip
            end.
            destruct j; simpl; [reflexivity |].
            apply (IH i j Hrows_rest).
          * apply Nat.ltb_ge in Hi.
            assert (Hr_le_i : List.length r <= i) by (rewrite Hlen_r; exact Hi).
            match goal with
            | [ |- context [ List.nth ?j (List.nth ?i (zip_with ?c ?x ?y) []) ?d ] ] =>
              rewrite (nth_zip_with_cons_overflow x y i (or_introl Hr_le_i))
            end.
            destruct j as [|j'].
            -- simpl. apply eq_sym. apply (nth_overflow r zeroR). rewrite Hlen_r. exact Hi.
            -- simpl.
               destruct j' as [|j''].
               ++ (* j' = 0 *)
                  destruct (0 <? List.length (r' :: lb''))%nat eqn:Hj.
                  { apply Nat.ltb_lt in Hj.
                    apply (nth_In (A:=list R) (n:=0) (r' :: lb'') ([] : list R)) in Hj.
                    apply Hrows_rest in Hj. simpl in Hj.
                    apply eq_sym. apply nth_overflow. rewrite Hj. exact Hi. }
                  { apply Nat.ltb_ge in Hj.
                    apply eq_sym.
                    assert (Hlen_r' : List.length r' = List.length finN).
                    { apply Hrows_rest. simpl; auto. }
                    apply (nth_overflow r' zeroR). rewrite Hlen_r'. exact Hi. }
               ++ (* j' = S j'' *)
                  destruct (S j'' <? List.length (r' :: lb''))%nat eqn:Hj.
                  { apply Nat.ltb_lt in Hj.
                    apply (nth_In (A:=list R) (n:=S j'') (r' :: lb'') ([] : list R)) in Hj.
                    apply Hrows_rest in Hj. simpl in Hj.
                    apply eq_sym. apply nth_overflow. rewrite Hj. exact Hi. }
                  { apply Nat.ltb_ge in Hj.
                    apply eq_sym.
                    simpl. rewrite (nth_overflow lb'' (n:=j'') ([] : list R)).
                    - simpl. apply (nth_overflow ([] : list R) (n:=i)). apply Nat.le_0_l.
                    - simpl in Hj. cbn in Hj. nia. }
    Qed.

    Lemma transpose_eff_nthRR :
      forall (lb : list (list R)) (i j : nat),
      (forall (xs : list R), In xs lb -> List.length xs = List.length finN) ->
      nthRR (transpose_eff lb) i j =r= nthRR lb j i = true.
    Proof.
      intros lb i j Hrows.
      unfold nthRR, nthR, nthRL.
      rewrite nth_transpose_eff_eq.
      eapply refR.
      exact Hrows.
    Qed.

    Lemma transpose_eff_square :
      forall (lb : list (list R)),
      List.length lb = List.length finN ->
      (forall (xs : list R), In xs lb -> List.length xs = List.length finN) ->
      List.length (transpose_eff lb) = List.length finN /\
      (forall (xs : list R), In xs (transpose_eff lb) -> List.length xs = List.length finN).
    Proof.
      intros lb Hlen Hrows.
      set (N := List.length finN).
      assert (HposN : 0 < N).
      { subst N. assert (2 <= List.length finN)%nat by apply lenN. lia. }
      apply (transpose_eff_rows_cols lb N N Hlen Hrows HposN HposN).
    Qed.

    Lemma dot_product_row_col_eqv :
      forall (la lb : list (list R)) (m₁ m₂ : Matrix Node R) (c d : Node),
      List.length la = List.length finN ->
      List.length lb = List.length finN ->
      (forall u v, nthRR la (index_map Node eqN finN u) (index_map Node eqN finN v) =r= m₁ u v = true) ->
      (forall u v, nthRR lb (index_map Node eqN finN u) (index_map Node eqN finN v) =r= m₂ u v = true) ->
      (forall (xs : list R), In xs la -> List.length xs = List.length finN) ->
      (forall (xs : list R), In xs lb -> List.length xs = List.length finN) ->
      (fold_left plusR 
        (map (fun '(x, y) => mulR x y) 
          (combine (nthRL la (index_map Node eqN finN c))
                   (nthRL (transpose_eff lb) (index_map Node eqN finN d)))) zeroR) =r=
      sum_fn Node R zeroR plusR (fun y : Node => m₁ c y * m₂ y d) finN = true.
    Proof.
      intros la lb m₁ m₂ c d Hla_rows Hlb_rows Hla Hlb Hla_len Hlb_len.
      set (idx := index_map Node eqN finN).
      set (row := nthRL la (idx c)).
      set (col := nthRL (transpose_eff lb) (idx d)).
      (* Establish that row has length = length finN *)
      assert (Hlen_row : List.length row = List.length finN).
      {
        unfold row, idx, nthRL.
        assert (Hbound : (index_map Node eqN finN c < List.length la)%nat).
        { rewrite Hla_rows. destruct (index_map_correct c (memN c)) as [Hidx_bound _]; exact Hidx_bound. }
        pose proof (@nth_In (list R) (index_map Node eqN finN c) la ([] : list R) Hbound) as Hin.
        apply Hla_len in Hin.
        exact Hin.
      }
      (* Establish that col has length = length finN *)
      assert (Hlen_col : List.length col = List.length finN).
      {
        unfold col, idx, nthRL.
        destruct (transpose_eff_square lb Hlb_rows Hlb_len) as [Ht_len Ht_rows].
        assert (Hbound : (index_map Node eqN finN d < List.length (transpose_eff lb))%nat).
        { rewrite Ht_len. destruct (index_map_correct d (memN d)) as [Hidx_bound _]; exact Hidx_bound. }
        pose proof (@nth_In (list R) (index_map Node eqN finN d) (transpose_eff lb) ([] : list R) Hbound) as Hin.
        apply Ht_rows in Hin.
        exact Hin.
      }
      (* Element-wise correspondence for row *)
      assert (Hrow_elem : forall (i : nat), (i < List.length finN)%nat ->
        List.nth i row zeroR =r= m₁ c (List.nth i finN c) = true).
      {
        intros i Hi.
        unfold row, idx, nthRL, nthRR, nthR.
        pose proof (index_map_nth i c Hi) as Hidx_nth.
        pose proof (Hla c (List.nth i finN c)) as Hrow_val.
        rewrite Hidx_nth in Hrow_val.
        unfold nthRR, nthR, nthRL in Hrow_val.
        exact Hrow_val.
      }
      (* Element-wise correspondence for col *)
      assert (Hcol_elem : forall (i : nat), (i < List.length finN)%nat ->
        List.nth i col zeroR =r= (fun y => m₂ y d) (List.nth i finN c) = true).
      {
        intros i Hi.
        unfold col, idx, nthRL, nthRR, nthR.
        pose proof (index_map_nth i c Hi) as Hidx_nth.
        pose proof (transpose_eff_nthRR lb (idx d) i Hlb_len) as Htrans.
        unfold nthRR, nthR, nthRL in Htrans.
        (* Htrans : nth i (nth (idx d) (transpose_eff lb) []) zeroR =r=
                    nth (idx d) (nth i lb []) zeroR *)
        pose proof (Hlb (List.nth i finN c) d) as Hcol_val.
        rewrite Hidx_nth in Hcol_val.
        unfold nthRR, nthR, nthRL in Hcol_val.
        (* Hcol_val : nth (idx d) (nth i lb []) zeroR =r= m₂ (nth i finN c) d *)
        (* Goal: nth i (nth (idx d) (transpose_eff lb) []) zeroR =r= m₂ (nth i finN c) d *)
        eapply trnR.
        - exact Htrans.
        - exact Hcol_val.
      }
      (* Now apply the main equivalence lemma *)
      apply (dot_product_sum_fn_equiv (fun y => m₁ c y) (fun y => m₂ y d) row col c
        Hlen_row Hlen_col Hrow_elem Hcol_elem).
    Qed.


    (* KEY LEMMA: matrix_mul_eff on list-of-lists (accessed via          *)
    (* index_map) coincides with the mathematical matrix_mul.             *)
    Lemma matrix_mul_eff_fun_eqv_matrix_mul :
      forall (m₁ m₂ : Matrix Node R) (c d : Node),
      mat_cong Node eqN R eqR m₁ ->
      mat_cong Node eqN R eqR m₂ ->
      mat_mul_eff_fun Node eqN finN R zeroR plusR mulR m₁ m₂ c d =r=
      matrix_mul Node finN R zeroR plusR mulR m₁ m₂ c d = true.
    Proof.
      intros m₁ m₂ c d Hm₁ Hm₂.
      unfold mat_mul_eff_fun, matrix_mul.
      set (idx := index_map Node eqN finN).
      set (la := List.map (fun r : Node => List.map (fun c' : Node => m₁ r c') finN) finN).
      set (lb := List.map (fun r : Node => List.map (fun c' : Node => m₂ r c') finN) finN).
      (* Length properties *)
      assert (Hlen_la : List.length la = List.length finN).
      { subst la. apply length_map. }
      assert (Hlen_lb : List.length lb = List.length finN).
      { subst lb. apply length_map. }
      assert (Hrows_la : forall (xs : list R), In xs la -> List.length xs = List.length finN).
      { subst la. intros xs Hin. apply in_map_iff in Hin. destruct Hin as [? [Hinmem Hxs]]. subst xs. apply length_map. }
      assert (Hrows_lb : forall (xs : list R), In xs lb -> List.length xs = List.length finN).
      { subst lb. intros xs Hin. apply in_map_iff in Hin. destruct Hin as [? [Hinmem Hxs]]. subst xs. apply length_map. }
      (* Element-wise correspondence *)
      assert (Hla_correspond : forall u v, nthRR la (idx u) (idx v) =r= m₁ u v = true).
      { intros u v. subst la idx. apply list_encode_access. exact Hm₁. }
      assert (Hlb_correspond : forall u v, nthRR lb (idx u) (idx v) =r= m₂ u v = true).
      { intros u v. subst lb idx. apply list_encode_access. exact Hm₂. }
      (* Bounds for index_map *)
      assert (Hbound_c : (idx c < List.length la)%nat).
      { subst la idx. rewrite length_map. destruct (index_map_correct c (memN c)) as [Hbound _]; exact Hbound. }
      assert (Hbound_d : (idx d < List.length (transpose_eff lb))%nat).
      {
        destruct (transpose_eff_square lb Hlen_lb Hrows_lb) as [Ht_len _].
        rewrite Ht_len.
        subst idx.
        destruct (index_map_correct d (memN d)) as [Hbound _]; exact Hbound.
      }
      (* Expand the efficient multiplication *)
      subst la lb idx.
      unfold matrix_mul_eff, nthRR, nthR, nthRL.
      cbv beta.
      rewrite (nth_map_any_default (list R) (list R)
        (fun (row : list R) => List.map (fun col : list R => dot_product R zeroR plusR mulR row col) (transpose_eff (List.map (fun r : Node => List.map (fun c' : Node => m₂ r c') finN) finN)))
        (List.map (fun r : Node => List.map (fun c' : Node => m₁ r c') finN) finN)
        (index_map Node eqN finN c)
        ([] : list R) ([] : list R) Hbound_c).
      cbv beta.
      rewrite (nth_map_any_default (list R) R
        (fun col : list R => dot_product R zeroR plusR mulR
          (List.nth (index_map Node eqN finN c) (List.map (fun r : Node => List.map (fun c' : Node => m₁ r c') finN) finN) ([] : list R)) col)
        (transpose_eff (List.map (fun r : Node => List.map (fun c' : Node => m₂ r c') finN) finN))
        (index_map Node eqN finN d)
        zeroR ([] : list R) Hbound_d).
      cbv beta.
      unfold dot_product.
      apply (dot_product_row_col_eqv
        (List.map (fun r : Node => List.map (fun c' : Node => m₁ r c') finN) finN)
        (List.map (fun r : Node => List.map (fun c' : Node => m₂ r c') finN) finN)
        m₁ m₂ c d).
      - (* length la = length finN *)
        apply length_map.
      - (* length lb = length finN *)
        apply length_map.
      - (* element-wise correspondence for la *)
        intros u v. apply list_encode_access. exact Hm₁.
      - (* element-wise correspondence for lb *)
        intros u v. apply list_encode_access. exact Hm₂.
      - (* rows of la have correct length *)
        intros xs Hin. apply in_map_iff in Hin. destruct Hin as [? [Hinmem Hxs]]. subst xs. apply length_map.
      - (* rows of lb have correct length *)
        intros xs Hin. apply in_map_iff in Hin. destruct Hin as [? [Hinmem Hxs]]. subst xs. apply length_map.
    Qed.

    (* Generalized version: works for ANY la, lb that encode congruent    *)
    (* matrices (not just enc(m₁), enc(m₂)).                              *)
    Lemma matrix_mul_eff_access_general :
      forall (la lb : list (list R)) (m₁ m₂ : Matrix Node R) (c d : Node),
      List.length la = List.length finN ->
      List.length lb = List.length finN ->
      (forall u v, nthRR la (index_map Node eqN finN u) (index_map Node eqN finN v) =r= m₁ u v = true) ->
      (forall u v, nthRR lb (index_map Node eqN finN u) (index_map Node eqN finN v) =r= m₂ u v = true) ->
      (forall xs, In xs la -> List.length xs = List.length finN) ->
      (forall xs, In xs lb -> List.length xs = List.length finN) ->
      nthRR (matrix_mul_eff R zeroR plusR mulR la lb) 
        (index_map Node eqN finN c) (index_map Node eqN finN d) =r=
      matrix_mul Node finN R zeroR plusR mulR m₁ m₂ c d = true.
    Proof.
      intros la lb m₁ m₂ c d Hlen_la Hlen_lb Hla Hlb Hrows_la Hrows_lb.
      set (idx := index_map Node eqN finN).
      assert (Hbound_c : (idx c < List.length la)%nat).
      { rewrite Hlen_la. destruct (index_map_correct c (memN c)) as [Hb _]; exact Hb. }
      assert (Hbound_d : (idx d < List.length (transpose_eff lb))%nat).
      { destruct (transpose_eff_square lb Hlen_lb Hrows_lb) as [Ht_len _].
        rewrite Ht_len. destruct (index_map_correct d (memN d)) as [Hb _]; exact Hb. }
      unfold matrix_mul_eff, nthRR, nthR, nthRL.
      cbv beta.
      rewrite (nth_map_any_default (list R) (list R)
        (fun (row : list R) => List.map (fun col : list R => dot_product R zeroR plusR mulR row col) (transpose_eff lb))
        la (idx c) ([] : list R) ([] : list R) Hbound_c).
      cbv beta.
      rewrite (nth_map_any_default (list R) R
        (fun col : list R => dot_product R zeroR plusR mulR
          (List.nth (idx c) la ([] : list R)) col)
        (transpose_eff lb) (idx d) zeroR ([] : list R) Hbound_d).
      cbv beta.
      unfold dot_product.
      apply (dot_product_row_col_eqv la lb m₁ m₂ c d Hlen_la Hlen_lb Hla Hlb Hrows_la Hrows_lb).
    Qed.

  
    (* Local wrapper for matrix_mul_eff                                     *)
    Let mul_eff (la lb : list (list R)) : list (list R) :=
      matrix_mul_eff R zeroR plusR mulR la lb.

    (* Local wrapper for matrix_exp_unary_eff                               *)
    Let exp_eff (la : list (list R)) (n : nat) : list (list R) :=
      matrix_exp_unary_eff Node eqN finN R zeroR oneR plusR mulR la n.

    (* Helper: matrix_mul_eff applied to la and a list encoding of m_exp *)

    (* Structural lemma: exp_eff preserves well-formedness                 *)
    Lemma exp_eff_preserves_wf :
      forall (la : list (list R)) (n : nat),
      List.length la = List.length finN ->
      (forall xs, In xs la -> List.length xs = List.length finN) ->
      List.length (exp_eff la n) = List.length finN /\
      (forall xs, In xs (exp_eff la n) -> List.length xs = List.length finN).
    Proof.
      intros ll n Hlen_ll Hrows_ll.
      induction n as [|n' IHn].
      - (* n = 0 *)
        unfold exp_eff. simpl.
        split.
        + apply length_map.
        + intros xs Hin. apply in_map_iff in Hin. destruct Hin as [? [Hinmem Hxs]]. subst xs. apply length_map.
      - (* n = S n' *)
        unfold exp_eff. simpl.
        destruct IHn as [Hlen_exp Hrows_exp].
        split.
        + (* length *) unfold matrix_mul_eff. rewrite length_map. exact Hlen_ll.
        + (* rows *) intros xs Hin. unfold matrix_mul_eff in Hin.
          apply in_map_iff in Hin. destruct Hin as [row [Hxs Hin_ll]].
          subst xs. rewrite length_map.
          destruct (transpose_eff_square (exp_eff ll n') Hlen_exp Hrows_exp) as [Ht_len _].
          exact Ht_len.
    Qed.

    Lemma matrix_mul_eff_list_vs_fun :
      forall (m : Matrix Node R) (n : nat) (c d : Node),
      mat_cong Node eqN R eqR m ->
      let la := List.map (fun r => List.map (fun c' => m r c') finN) finN in
      let idx := index_map Node eqN finN in
      nthRR (mul_eff la (exp_eff la n)) (idx c) (idx d) =r=
      matrix_mul Node finN R zeroR plusR mulR m 
        (matrix_exp_unary Node eqN finN R zeroR oneR plusR mulR m n) c d = true.
    Proof.
      intros m n c d Hm.
      cbv beta.
      set (la := List.map (fun r : Node => List.map (fun c' : Node => m r c') finN) finN).
      set (idx := index_map Node eqN finN).
      revert c d.
      induction n as [|n' IHn]; intros c d.
      - (* n = 0 *)
        unfold exp_eff, mul_eff.
        simpl (matrix_exp_unary_eff Node eqN finN R zeroR oneR plusR mulR la 0).
        (* exp_eff la 0 = enc(I) *)
        assert (Hid_cong : mat_cong Node eqN R eqR (I Node eqN R zeroR oneR)).
        { unfold mat_cong. intros a b u v Ha Hb. apply identity_cong; assumption. }
        apply (matrix_mul_eff_access_general la
          (List.map (fun r => List.map (fun c' => I Node eqN R zeroR oneR r c') finN) finN)
          m (I Node eqN R zeroR oneR) c d).
        + (* length la = length finN *) subst la; apply length_map.
        + (* length enc(I) = length finN *) apply length_map.
        + (* nthRR la ... =r= m ... *) intros u v. subst la. apply list_encode_access. exact Hm.
        + (* nthRR enc(I) ... =r= I ... *) intros u v. apply list_encode_access. exact Hid_cong.
        + (* rows of la *) subst la. intros xs Hin. apply in_map_iff in Hin. destruct Hin as [? [Hinmem Hxs]]. subst xs. apply length_map.
        + (* rows of enc(I) *) intros xs Hin. apply in_map_iff in Hin. destruct Hin as [? [Hinmem Hxs]]. subst xs. apply length_map.
      - (* n = S n' *)
        unfold exp_eff, mul_eff.
        simpl (matrix_exp_unary_eff Node eqN finN R zeroR oneR plusR mulR la (S n')).
        (* Goal: nthRR (matrix_mul_eff la (matrix_mul_eff la (exp_eff la n'))) (idx c) (idx d) =r=
                 matrix_mul m (matrix_exp_unary m (S n')) c d *)
        set (lb_inner := matrix_mul_eff R zeroR plusR mulR la (exp_eff la n')).
        (* Well-formedness of la *)
        assert (Hlen_la : List.length la = List.length finN).
        { subst la; apply length_map. }
        assert (Hrows_la : forall xs, In xs la -> List.length xs = List.length finN).
        { subst la. intros xs Hin. apply in_map_iff in Hin. destruct Hin as [? [Hinmem Hxs]]. subst xs. apply length_map. }
        (* Well-formedness of exp_eff la n' *)
        assert (Hwf_exp : List.length (exp_eff la n') = List.length finN /\
          (forall xs, In xs (exp_eff la n') -> List.length xs = List.length finN)).
        { apply (exp_eff_preserves_wf la n' Hlen_la Hrows_la). }
        destruct Hwf_exp as [Hlen_exp Hrows_exp].
        (* Well-formedness of lb_inner *)
        assert (Hlen_lb : List.length lb_inner = List.length finN).
        { unfold lb_inner, matrix_mul_eff. rewrite length_map. exact Hlen_la. }
        assert (Hrows_lb : forall xs, In xs lb_inner -> List.length xs = List.length finN).
        {
          intros xs Hin.
          unfold lb_inner, matrix_mul_eff in Hin.
          apply in_map_iff in Hin. destruct Hin as [row [Hxs Hin_la]].
          subst xs. rewrite length_map.
          destruct (transpose_eff_square (exp_eff la n') Hlen_exp Hrows_exp) as [Ht_len _].
          exact Ht_len.
        }
        (* Encoding: lb_inner encodes matrix_exp_unary m (S n') via IH *)
        assert (Hlb_encodes : forall u v, nthRR lb_inner (idx u) (idx v) =r=
          matrix_exp_unary Node eqN finN R zeroR oneR plusR mulR m (S n') u v = true).
        {
          intros u v.
          specialize (IHn u v).
          unfold lb_inner, mul_eff in *.
          exact IHn.
        }
        (* Apply the generalized lemma *)
        apply (matrix_mul_eff_access_general la lb_inner m
          (matrix_exp_unary Node eqN finN R zeroR oneR plusR mulR m (S n')) c d
          Hlen_la Hlen_lb).
        + (* nthRR la ... =r= m ... *) intros u v. subst la. apply list_encode_access. exact Hm.
        + (* nthRR lb_inner ... =r= matrix_exp_unary m (S n') ... *) exact Hlb_encodes.
        + (* rows of la *) exact Hrows_la.
        + (* rows of lb_inner *) exact Hrows_lb.
    Qed.

    Lemma matrix_exp_unary_eff_fun_matrix_unary_eqv : 
      forall (n : nat) (m : Matrix Node R) c d,
      mat_cong Node eqN R eqR m -> 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n c d  =r= 
      matrix_exp_unary_eff_fun Node eqN finN R 0 1 plusR mulR m n c d = true.
    Proof.
      induction n as [|n ihn]; intros m c d Hm.
      - (* n = 0 *)
        simpl (matrix_exp_unary Node eqN finN R 0 1 plusR mulR m 0 c d).
        unfold matrix_exp_unary_eff_fun.
        unfold exp_eff, nthRR, nthR, nthRL.
        simpl (matrix_exp_unary_eff Node eqN finN R zeroR oneR plusR mulR
          (List.map (fun r => List.map (fun c' => m r c') finN) finN) 0).
        apply symR.
        assert (Hid_cong : mat_cong Node eqN R eqR (I Node eqN R zeroR oneR)).
        { unfold mat_cong. intros a b u v Ha Hb. apply identity_cong; assumption. }
        apply (list_encode_access (I Node eqN R zeroR oneR) c d Hid_cong).
      - (* n = S n *)
        simpl (matrix_exp_unary Node eqN finN R 0 1 plusR mulR m (S n) c d).
        unfold matrix_exp_unary_eff_fun.
        cbn.
        apply symR.
        apply matrix_mul_eff_list_vs_fun with (m := m) (n := n); assumption.
    Qed.

    Lemma matrix_exp_unary_eff_fun_binary_eqv : 
      forall (n : N) (m : Matrix Node R) c d,
      mat_cong Node eqN R eqR m -> 
      matrix_exp_unary_eff_fun Node eqN finN R 0 1 plusR mulR m (N.to_nat n) c d =r= 
      matrix_exp_binary_eff_fun Node eqN finN R 0 1 plusR mulR m n c d = true.
    Proof.
    Admitted.


    (* This theorem allows us to swap matrix_exp_binary with 
      matrix_exp_binary_eff_fun *)
    Lemma matrix_exp_binary_eff_fun_binary_eqv : 
      forall (n : N) (m : Matrix Node R) c d,
      mat_cong Node eqN R eqR m -> 
      matrix_exp_binary Node eqN finN R 0 1 plusR mulR m n c d =r= 
      matrix_exp_binary_eff_fun Node eqN finN R 0 1 plusR mulR m n c d = true.
    Proof.
      intros * ha.
      eapply trnR.
      +
        eapply symR, matrix_exp_unary_binary_eqv.
        exact ha.
      +
        eapply trnR.
        eapply matrix_exp_unary_eff_fun_matrix_unary_eqv. 
        exact ha.
        eapply matrix_exp_unary_eff_fun_binary_eqv.
        exact ha.
    Qed.





End Matrix_proofs.
