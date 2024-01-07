From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
Require Import
  Algorithm.Definitions
  Algorithm.Listprop 
  Algorithm.Orel.
Import ListNotations.


Definition Matrix (Node R : Type) := Node -> Node -> R.

Section Pathdefs.
  Variables 
    (Node : Type)
    (eqN  : brel Node).

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


  (* a path is a triple *)
  Definition Path : Type := Node * Node * list (Node * Node * R). 


  Definition source (c : Node) (l : list (Node * Node * R)) : bool :=
    match l with 
    | [] => false
    | (x, _, _) :: _ => c =n= x 
    end.
  

  Definition target_alt (d : Node) (l : list (Node * Node * R)) := 
    match List.rev l with
    | [] => false
    | (x, y, r) :: t => d =n= y
    end. 


  Fixpoint target (d : Node) (l : list (Node * Node * R)) : bool :=
    match l with
    | [] => false
    | (x, y, r) :: t => match t with 
      | [] => d =n= y
      | hs :: ts => target d t
    end
    end.


  (* path strength between c and d *)
  Fixpoint measure_of_path (l : list (Node * Node * R)) : R :=
    match l with 
    | [] => 1
    | (_, _, v) :: t => v * measure_of_path t
    end.

  
  

  
  Fixpoint well_formed_path_aux (m : Matrix Node R) 
    (l : list (Node * Node * R)) : bool :=
    match l with 
    | [] => true
    | (c, x, v) :: tl => (m c x =r= v) && match tl with 
      | [] => true
      | (y, _, _) :: _ => (x =n= y) && well_formed_path_aux m tl
      end
    end.


  
  Definition fp (p : Path) : Node :=
    match p with
    |(a, _, _) => a
    end. 

  Definition sp (p : Path) : Node :=
    match p with
    |(_, b, _) => b
    end. 
  
  Definition tp (p : Path) : list (Node * Node * R):=
    match p with
    |(_, _, l) => l
    end.

    
  (* stick a node 'c' in all the paths, represented by l *)
  Fixpoint append_node_in_paths (m : Matrix Node R) 
    (c : Node) (l : list (list (Node * Node * R))) : 
    list (list (Node * Node * R)) := 
  match l with 
  | [] => []
  | h :: t => match h with 
    | [] => append_node_in_paths m c t
    | (x, _, _) :: ht => 
      ((c, x, m c x) :: h) :: append_node_in_paths m c t
    end 
  end.


  (* list of all paths of lenghth k from c to d. 
    xs is list of all candidates *)
  Fixpoint all_paths_klength (xs : list Node) 
    (m : Matrix Node R) (k : nat) 
    (c d : Node) : list (list (Node * Node * R)) :=
    match k with
    | O => if c =n= d then [[(c, d, 1)]] else []
    | S k' =>
        let lf := List.flat_map (fun x => all_paths_klength xs m k' x d) xs
        in append_node_in_paths m c lf
    end.

  
  Definition construct_all_paths (xs : list Node) 
    (m : Node -> Node -> R) (k : nat) 
    (c d : Node) : list Path :=
    let lp := all_paths_klength xs m k c d in 
    List.map (fun l => (c, d, l)) lp.

  (* get all the R values from path *)
  Definition get_all_rvalues (pl : list Path): list R :=
    List.map (fun '(_, _, l) => measure_of_path l) pl.


  Definition sum_all_rvalues (pl : list R) :=
    List.fold_right (fun b a => b + a) 0 pl.

  (* sum_fn using fold_right *)
  Definition sum_fn_fold (f : Node -> R) (l : list Node) : R :=
    List.fold_right (fun b a => f b + a) 0 l.


  (* congruence relation on matrix *)
  Definition mat_cong (m : Matrix Node R) : Prop :=
    forall a b c d, a =n= c = true -> 
    b =n= d = true -> m a b =r= m c d = true.
  

  Definition in_eq_bool_cong 
    (f : Node → list (list (Node * Node * R))) :=
    forall (x a : Node) (y : list (Node * Node * R)),  
    (x =n= a) = true -> 
    In_eq_bool _ _ _ eqN eqN eqR y (f a) = 
    In_eq_bool _ _ _ eqN eqN eqR y (f x).
    
    
  Definition cyclic_path (c : Node) 
    (l : list (Node * Node * R)) :=
    l <> [] /\ source c l = true /\ 
    target c l = true.

  
  
  (* assume that path is well_founded *)
  Fixpoint collect_nodes_from_a_path  
    (l : list (Node * Node * R)) : list Node :=
    match l with
    | [] => []
    | (a, b, _) :: t => match t with
      | [] => [a; b]
      | _ :: _ => a :: collect_nodes_from_a_path t
    end
    end.

  (* Constructs well founded path *)  
  Fixpoint construct_path_from_nodes (l : list Node) (m : Matrix Node R) : 
  list (Node * Node * R) :=
  match l with 
  | [] => []
  | u :: t => match t with
    | [] => []
    | v :: _ => (u, v, m u v) :: construct_path_from_nodes t m
  end
  end.

  (* Checks if au is second element of path or not  *)      
  Fixpoint elem_path_triple_tail (au : Node) (l : list (Node * Node * R)) : bool :=
    match l with
    | [] => false
    | (bu, bv, _) :: t => (au =n= bv) || elem_path_triple_tail au t
    end.


  
  Fixpoint keep_collecting (au : Node) (l : list (Node * Node * R)) :=
    match l with
    | [] => []
    | (bu, bv, bw) :: t => if (au =n= bv) then [(bu, bv, bw)] else 
        (bu, bv, bw) :: keep_collecting au t
    end.
    
  Fixpoint keep_dropping (au : Node) (l : list (Node * Node * R)) :=
    match l with
    | [] => []
    | (bu, bv, bw) :: t => if (au =n= bv) then t else 
      keep_dropping au t
    end.

  (* computes the loop in a path *)
  Fixpoint elem_path_triple_compute_loop (l : list (Node * Node * R)) := 
    match l with
    | [] => None
    | (au, av, aw) :: t => if au =n= av then Some [(au, av, aw)] (* loop at the head, 1 length *)
      else 
          if elem_path_triple_tail au t then Some ((au, av, aw) :: keep_collecting au t)
          else elem_path_triple_compute_loop t
    end.

  (* This function is very similar to the above one, except it returns the 
    left over from the front ++ loop ++ rest of the list *)  
  Fixpoint elem_path_triple_compute_loop_triple (l : list (Node * Node * R)) := 
    match l with
    | [] => ([], None, [])
    | (au, av, aw) :: t => if au =n= av then ([], Some [(au, av, aw)], t) 
      else 
          if elem_path_triple_tail au t then 
          ([], Some ((au, av, aw) :: keep_collecting au t), keep_dropping au t)
          else match elem_path_triple_compute_loop_triple t with 
            | (fp, sp, tp) => ((au, av, aw) :: fp, sp, tp)
          end
    end.

  (* elem_path_triple l = true means l does not have any cycle *)     
  Fixpoint elem_path_triple (l : list (Node * Node * R)) : bool := 
    match l with
    | [] => true 
    | (au, av, _) :: t => 
        negb (au =n= av) && 
        negb (elem_path_triple_tail au t) && 
        elem_path_triple t 
    end.


  
  Fixpoint partial_sum_paths (l : list Node) 
    (m : Matrix Node R) (n : nat) (c d : Node) : R :=
    match n with
    | O => 
      match c =n= d with 
      | true => 1
      | false => 0 
      end
    | S n' =>  partial_sum_paths l m n' c d + 
      sum_all_rvalues (get_all_rvalues (construct_all_paths l m n c d))
    end.

  
  
  (* Get all the paths in one big list *)
  Fixpoint enum_all_paths_flat (l : list Node) 
    (m : Matrix Node R) (n : nat) (c d : Node) : list Path :=
  match n with
  | O => construct_all_paths l m O c d
  | S n' => 
    construct_all_paths l m n c d ++ 
    enum_all_paths_flat l m n' c d
  end.
  
  
  Fixpoint sum_all_flat_paths (l : list Path) : R :=
    match l with
    | [] => 0
    | (_, _, h) :: t => measure_of_path h + 
      sum_all_flat_paths t
    end.

  (* Checks if a path p appears in lpp or not *)
  Definition In_path_membership (p : Path) (lpp : list Path) : bool :=
    match p with
    | (_, _, lp) => 
      (In_eq_bool _ _ _ eqN eqN eqR lp 
        (List.map (fun '(_, _, lt) => lt) lpp))
    end. 
  
  

  
End Pathdefs.

Section Pathprops.

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
    (* semiring axiom on R *)
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
    (* end of semiring axioms *)
  
    (* 1 is additive annhilator *)
    (zero_stable : forall a : R, 1 + a =r= 1 = true)
    (* end of axioms *)

    (* start of congruence relation *)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).
    (* end of congruence *)




  (* append node path function contains only 
    non-empty list *)  
  Lemma append_node_in_paths_non_empty_list : 
    forall (l : list (list (Node * Node * R))) 
      (m : Matrix Node R) (c : Node),  
    all_elems_non_empty_list _ 
    (append_node_in_paths Node R m c l) = true.
  Proof using Type.
    induction l as [|a l IHl].
    + simpl; intros ? ?; 
      reflexivity.
    + simpl; destruct a.
      ++ 
        apply IHl.
      ++
        intros; repeat destruct p;
        simpl; apply IHl.
  Qed.

  
  Lemma append_node_in_paths_eq : 
    ∀ (l : list (list (Node * Node * R))) 
    (m : Matrix Node R) (c : Node) 
    (xs : list (Node * Node * R)), 
    In_eq_bool _ _ _  eqN eqN eqR xs 
      (append_node_in_paths Node R m c l) = true -> 
    ∃ (y : Node) (ys : list (Node * Node * R)), 
      triple_elem_list _ _ _ eqN eqN eqR 
        xs ((c, y, m c y) :: ys) = true /\
      source Node eqN R c xs = true /\ 
      source Node eqN R y ys = true /\ 
      ys <> [].
  Proof using refN symN.
    induction l.
    - simpl; intros ? ? ? Hf.
      inversion Hf.
    - intros ? ? ? H.
      simpl in H.
      destruct a.
      apply IHl with (m := m) (c := c).
      exact H.
      repeat destruct p.
      simpl in H.
      apply Bool.orb_true_iff in H.
      destruct H.
      exists n, ((n, n0, r) :: a).
      split. exact H.
      destruct xs. simpl in H.
      congruence. 
      repeat destruct p.
      simpl in H. simpl.
      apply Bool.andb_true_iff in H.
      destruct H as [Hl Hr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hll Hlr].
      apply Bool.andb_true_iff in Hll.
      destruct Hll as [Hlll Hlllr].
      split. 
      apply symN. 
      exact Hlll. 
      split. 
      apply refN.
      intro Hf. 
      inversion Hf.
      apply IHl with (m := m) (c := c).
      exact H.
  Qed.

  
  Lemma non_empty_paths_in_kpath : 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ 
        oneR finN m n c d) = true -> xs <> [].
  Proof using refN symN.
    induction n.
    - simpl; intros ? ? ? ? Hin.
      case (eqN c d) eqn:Ht.
      simpl in Hin.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin | Hin].
      intro Hf. 
      rewrite Hf in Hin.
      simpl in Hin. 
      congruence.
      congruence.
      intro Hf. 
      rewrite Hf in Hin.
      simpl in Hin. 
      congruence.
    - simpl; intros ? ? ? ? Hin.
      destruct (append_node_in_paths_eq
        (flat_map (λ x : Node, 
          all_paths_klength _ eqN _ oneR finN m n x d) finN)
        m c xs Hin) as [y [ys [Hl Hr]]].
      intro Hf. 
      rewrite Hf in Hl.
      simpl in Hl. 
      congruence.
  Qed.


  Lemma source_in_kpath : 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)), 
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ 
        oneR finN m n c d) = true -> 
    source Node eqN R c xs = true.
  Proof using refN symN.
    induction n.
    - simpl; intros ? ? ? ? Hin.
      case (eqN c d) eqn:Ht.
      simpl in Hin.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin | Hin].
      destruct xs.
      simpl in Hin. 
      congruence.
      simpl in Hin.
      simpl.
      repeat destruct p.
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hr].
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hrr].
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hrrr].
      apply symN. 
      exact Hin.
      congruence.
      simpl in Hin.
      congruence.
    - simpl; intros ? ? ? ? Hin.
      destruct (append_node_in_paths_eq 
        (flat_map (λ x : Node, 
          all_paths_klength _ eqN _ oneR finN m n x d) finN)
        m c xs Hin) as [y [ys [Hl [Hr Hw]]]].
      assumption.
  Qed.

  

  Lemma append_node_rest : 
    forall l m c xs,
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (append_node_in_paths Node R m c l) = true ->
    In_eq_bool _ _ _ eqN eqN eqR 
      (List.tl xs) l = true.
  Proof using Type.
    induction l.
    - simpl; 
      intros ? ? ? Hin.
      inversion Hin.
    - simpl; 
      intros ? ? ? Hin. 
      destruct a.
      eapply Bool.orb_true_iff.
      right. 
      apply IHl with (m := m) (c := c).
      exact Hin.
      repeat destruct p.
      simpl in Hin.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [H | H].
      apply Bool.orb_true_iff.
      left. 
      apply triple_trim_tail 
        with (a := (c, n, m c n)).
      exact H.
      apply Bool.orb_true_iff.
      right. 
      apply IHl with (m := m) (c := c).
      exact H.
  Qed.


  
  Lemma target_tail_forward : 
    forall (xs : list (Node * Node * R)) (d : Node), 
    target Node eqN R d (List.tl xs) = true -> 
    target Node eqN R d xs = true.
  Proof using Type.
    destruct xs.
    - simpl; intros ? ?.
      exact H.
    - simpl; intros ? ?.
      repeat destruct p.
      destruct xs.
      simpl in H.
      congruence.
      exact H.
  Qed.

  Lemma target_tail_backward : 
    forall (xs : list (Node * Node * R)) (d : Node),
    List.tl xs <> [] -> 
    target Node eqN R d xs = true -> 
    target Node eqN R d (List.tl xs) = true.
  Proof using Type.
    destruct xs.
    - simpl; intros ? ?.
      congruence.
    - intros ? ? Ht.
      simpl in H.
      simpl.
      destruct xs.
      congruence.
      remember (p0 :: xs) as pxs.
      repeat destruct p.
      simpl in Ht.
      rewrite Heqpxs in Ht.
      rewrite <-Heqpxs in Ht.
      exact Ht.
  Qed.


  Lemma in_eq_append_cong : 
    forall l m a x y,
    mat_cong Node eqN R eqR m -> 
    a =n= x = true ->  
    In_eq_bool _ _ _ eqN eqN eqR y 
      (append_node_in_paths _ _  m a l) =
    In_eq_bool _ _ _ eqN eqN eqR y 
    (append_node_in_paths _ _ m x l).
  Proof using refN symN symR trnN trnR.
    induction l.
    - simpl; intros ? ? ? ? Hm Hax;
      reflexivity.
    - simpl; intros ? ? ? ? Hm Hax.
      destruct a.
      + apply IHl. exact Hm. exact Hax.
      + repeat destruct p.
        simpl. 
        pose proof (IHl m a0 x y Hm Hax) as IH.
        rewrite IH.
        apply orb_eq.
        apply triple_eq_cong;
        try assumption.
        apply refN.
        apply Hm.
        exact Hax.
        apply refN.
  Qed.
  


  Lemma all_paths_cong : 
    forall n m d,
    mat_cong Node eqN R eqR m -> 
    in_eq_bool_cong Node eqN R eqR (λ x : Node, 
        all_paths_klength  _ eqN _ oneR finN m n x d).
  Proof using refN symN symR trnN trnR.
    unfold in_eq_bool_cong.
    induction n.
    - simpl; intros ? ? Hm ? ? ? Hxa.
      case_eq (a =n= d); intros Ht.
      assert(Hv : x =n= d = true).
      eapply trnN with a; assumption.
      rewrite Hv; clear Hv.
      destruct y; simpl.
      reflexivity.
      repeat destruct p.
      repeat rewrite Bool.orb_false_r.
      assert (Hv : (n =n= a) = (n =n= x)).
      case_eq (n =n= a); intros Hna;
      case_eq (n =n= x); intros Hnx; auto.
      apply symN in Hxa.
      pose proof (trnN _ _ _ Hna Hxa) as Hf.
      rewrite Hf in Hnx; congruence.
      pose proof (trnN _ _ _ Hnx Hxa) as Hf.
      rewrite Hf in Hna; congruence.
      rewrite Hv. reflexivity.
      simpl; case_eq (x =n= d); 
      intro Hx; auto.
      apply symN in Hxa.
      pose proof (trnN _ _ _ Hxa Hx) as Hw.
      rewrite Ht in Hw.
      congruence.    
    - simpl; intros ? ? Hm ? ? ? Hxa.
      remember (flat_map (λ x0 : Node, all_paths_klength _ eqN _ oneR 
      finN m n x0 d) finN)
      as l.
      apply in_eq_append_cong.
      exact Hm.
      apply symN. 
      exact Hxa.
  Qed.


 
  Lemma target_in_kpath : 
    forall (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    mat_cong Node eqN R eqR m ->
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ 
      oneR finN m n c d) = true -> 
    target Node eqN R d xs = true.
  Proof using refN symN symR trnN trnR.
    induction n.
    - simpl; intros ? ? ? ? Hm Hin.
      case (c =n= d) eqn:Ht.
      simpl in Hin.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin | Hin].
      destruct xs.
      simpl in Hin. 
      congruence.
      simpl in Hin.
      simpl.
      repeat destruct p.
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hr].
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hrr].
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hrrr].
      destruct xs.
      apply symN. 
      exact Hrrr.
      simpl in Hr.
      repeat destruct p.
      congruence.
      congruence.
      simpl in Hin.
      congruence.
    - simpl; intros ? ? ? ? Hm Hin.
      pose proof append_node_rest
      (flat_map (λ x : Node, all_paths_klength _ eqN _ 
      oneR finN m n x d) finN)
      m c xs Hin as Hv.
      destruct (proj1 (in_flat_map_bool _ _ _ 
        eqN eqN eqR refN finN (List.tl xs)
        (λ x : Node, all_paths_klength _ eqN _ 
        oneR finN m n x d)
        (all_paths_cong _ _ _ Hm)) Hv) as [w [Ha Hb]].
      specialize (IHn m w d (List.tl xs) Hm Hb).
      apply target_tail_forward.
      exact IHn.
  Qed.    
      

  
  
  Lemma source_target_and_non_empty_kpath : 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    mat_cong Node eqN R eqR m ->  
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ oneR 
        finN m n c d) = true ->
    xs <> [] ∧
    source _ eqN _ c xs = true ∧
    target _ eqN _ d xs = true.
  Proof using refN symN symR trnN trnR.
    intros ? ? ? ? ? Hm Hin.
    split.
    apply non_empty_paths_in_kpath with 
      (n := n) (m := m) (c := c) (d := d).
    exact Hin.
    split.
    apply source_in_kpath with 
      (n := n) (m := m) (d := d).
    exact Hin.
    eapply target_in_kpath with 
    (n := n) (m := m) (d := d).
    exact Hm.
    exact Hin.
  Qed.
    

  Lemma well_formed_by_extending : 
    forall xs ys c y m, 
    mat_cong Node eqN R eqR m -> 
    ys <> [] ->  
    triple_elem_list _ _ _ eqN eqN eqR 
      xs ((c, y, m c y) :: ys) = true -> 
    source Node eqN _ c xs = true -> 
    source _ eqN _ y ys = true ->
    well_formed_path_aux Node eqN R eqR m (List.tl xs) = true ->
    well_formed_path_aux Node eqN R eqR m xs = true.
  Proof using congrR refR symN symR trnN.
    destruct xs.
    - simpl; intros ? ? ? ? Hm Hys Ht Hs Hsy Hw.
      congruence.
    - intros ? ? ? ? Hm Hys Ht Hs Hsy Hw.
      destruct xs.
      + simpl in * |- *.
        repeat destruct p.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Hrrr].
        apply Bool.andb_true_iff.
        split. apply symR in Htrr.
        rewrite <-Htrr.
        apply congrR. apply Hm.
        apply symN.
        apply symN. exact Ht.
        exact Hrrr.
        apply refR.
        reflexivity.
      +
        repeat destruct p. 
        repeat destruct p0.
        repeat destruct p.
        assert (Hwt : well_formed_path_aux Node eqN R eqR m (tl ((n, n0, r) :: (n1, n2, r0) :: xs)) =
        well_formed_path_aux Node eqN R eqR m (((n1, n2, r0) :: xs))).
        reflexivity. rewrite Hwt in Hw; clear Hwt.
        assert (Hg : well_formed_path_aux Node eqN R eqR m ((n, n0, r) :: (n1, n2, r0) :: xs) =
        ((m n n0 =r= r) &&
        ((n0 =n= n1) && well_formed_path_aux Node eqN R eqR m ((n1, n2, r0) :: xs)))%bool).
        reflexivity. rewrite Hg; clear Hg.
        assert (Hvt : triple_elem_list _ _ _ eqN eqN eqR ((n, n0, r) :: (n1, n2, r0) :: xs)
        ((c, y, m c y) :: ys) = 
        ((n =n= c) && (n0 =n= y) && (r =r= m c y) &&
        triple_elem_list _ _ _ eqN eqN eqR ((n1, n2, r0) :: xs) ys)%bool).
        reflexivity.
        rewrite Hvt in Ht; clear Hvt.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Hrrr].
        apply Bool.andb_true_iff.
        split.
        apply symR in Htrr.
        rewrite <-Htrr.
        apply congrR. apply Hm.
        apply symN.
        apply symN. exact Ht.
        exact Hrrr.
        apply refR.
        apply Bool.andb_true_iff.
        split.
        destruct ys.
        simpl in Htr. congruence.
        repeat destruct p.
        simpl in Htr.
        simpl in Hsy.
        apply Bool.andb_true_iff in Htr.
        destruct Htr as [Htr Htt].
        apply Bool.andb_true_iff in Htr.
        destruct Htr as [Htr Htrrt].
        apply Bool.andb_true_iff in Htr.
        destruct Htr as [Htr Hrrw].
        pose proof (trnN _ _ _ Hrrr Hsy) as Ha.
        apply symN in Htr.
        exact (trnN _ _ _ Ha Htr).
        exact Hw.
  Qed.





  (* paths generated by all_paths_klength function are well formed *)
  Lemma all_paths_well_formed_in_kpaths : 
    forall (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    (forall c d, (c =n= d) = true -> (m c d =r= 1) = true) -> 
    mat_cong Node eqN R eqR m ->  
    In_eq_bool _ _ _ eqN eqN eqR xs (all_paths_klength _ eqN _ 
    oneR finN m n c d) = true ->
    well_formed_path_aux Node eqN R eqR m xs = true.
  Proof using congrR refN refR symN symR trnN trnR. 
    induction n.
    - simpl; intros ? ? ? ? Hcd Hm Hin.
      case (c =n= d) eqn:Ht.
      simpl in Hin.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin | Hin].
      destruct xs.
      simpl in Hin. 
      congruence.
      simpl in Hin.
      simpl.
      repeat destruct p.
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hr].
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hrr].
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hrrr].
      destruct xs.
      apply Bool.andb_true_iff.
      split. apply symN in Ht.
      pose proof (trnN _ _ _ Hrrr Ht) as Hv.
      pose proof (trnN _ _ _ Hv (symN  _ _ Hin)) as Hw.
      apply symN in Hw.
      pose proof (Hcd _ _ Hw) as Hwt.
      rewrite <-Hwt.
      apply congrR. apply refR.
      exact Hrr.
      reflexivity.
      simpl in Hr. 
      repeat destruct p.
      congruence.
      congruence.
      simpl in Hin.
      congruence.
  -   simpl; intros ? ? ? ? Hcd Hm Hin.
      pose proof append_node_rest
      (flat_map (λ x : Node, all_paths_klength _ eqN _ 
      oneR finN m n x d) finN)
      m c xs Hin as Hv.
      destruct (proj1 (in_flat_map_bool  _ _ _ 
      eqN eqN eqR refN finN (List.tl xs)
      (λ x : Node, all_paths_klength _ eqN _ 
      oneR finN m n x d)
      (all_paths_cong _ _ _ Hm)) Hv) as [w [Ha Hb]].
      specialize (IHn m w d (List.tl xs) Hcd Hm Hb).
      destruct (append_node_in_paths_eq
      (flat_map (λ x : Node, all_paths_klength _ eqN _ 
      oneR finN m n x d) finN)
      m c xs Hin) as [y [ys [Hu [Hvt [Hwl Hwr]]]]].
      apply well_formed_by_extending with (ys := ys) (c := c) (y := y);
      assumption.
  Qed.


  Lemma path_end_unit_loop : 
    forall k l m c d, 
    In_eq_bool _ _ _ eqN eqN eqR l 
    (all_paths_klength _ eqN _ 
      oneR finN m k c d) = true ->
    exists l', 
      triple_elem_list _ _ _ eqN eqN eqR 
        l (l' ++ [(d, d, 1)]) = true.   
  Proof using refN symN trnN.
    induction k.
    + simpl. 
      intros ? ? ? ? Hin.
      case (c =n= d) eqn:Hcd.
      exists [].
      simpl.
      destruct l as [|((au, av), aw) l].
      simpl in Hin;
      congruence.
      destruct l as [|((bu, bv), bw) l].
      simpl in * |- *.
      rewrite Bool.orb_false_r in Hin.
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin _].
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin Hinr].
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hinl Hinrr].
      rewrite (trnN _ _ _ Hinl Hcd),
      Hinrr, Hinr; reflexivity.
      simpl in Hin.
      rewrite Bool.orb_false_r, 
        Bool.andb_false_r in Hin.
      congruence.
      simpl in Hin.
      congruence.
    + simpl. 
      intros ? ? ? ? Hin.
      destruct (append_node_in_paths_eq
        (flat_map (λ x : Node, all_paths_klength _ eqN _ 
        oneR finN m k x d) finN)
        m c l Hin) as [y [ys [Hl Hr]]].
      pose proof append_node_rest _ _ _ _ 
        Hin as Hap.
      destruct (in_flat_map_bool_first _ _ _ 
        eqN eqN eqR refN finN _ _ Hap) as (x & Hf & Heb).
      simpl in Heb.
      destruct (IHk _ _ _ _ Heb) as 
      (l' & Hte).
      exists ((c, y, m c y) :: l').
      simpl.
      destruct l as [|((au, av), aw) l].
      simpl in Hl;
      congruence.
      simpl in Hl, Hte.
      simpl.
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlrr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlrrr].
      rewrite Hl, Hlrrr, Hlrr.
      simpl.
      exact Hte.
  Qed.



  Lemma source_same_path : 
    forall l₁ l₂ x y,
    triple_elem_list _ _ _ eqN eqN eqR l₁ l₂ = true -> 
    source _ eqN _ x l₁ = true -> 
    source _ eqN _ y l₂ = true ->
    x =n= y = true.
  Proof using symN trnN.
    induction l₁.
    + intros * Ht Hx Hy. 
      simpl in * |-. 
      congruence. 
    + intros * Ht Hx Hy.
      destruct l₂ as [|b l₂].
      simpl in Hy; congruence.
      destruct a as ((au, av), aw).
      destruct b as ((bu, bv), bw).
      simpl in * |-.
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrrr].
      apply symN in Hy.
      eapply trnN with au.
      exact Hx.
      apply trnN with bu; 
      assumption.
  Qed.


  Lemma all_paths_in_klength : 
    ∀ (k : nat) (m : Matrix Node R) 
    (c d : Node) xs,
    mat_cong Node eqN R eqR m -> 
    In_eq_bool _ _ _ eqN eqN eqR 
      xs (all_paths_klength _ eqN _ 
      oneR finN m k c d) = true ->
    (List.length xs = S k).
  Proof using refN symN symR trnN trnR.
    induction k.
    + simpl; intros ? ? ? ? Hm Hin.
      case (c =n= d) eqn:Hcd.
      destruct xs. 
      simpl in Hin.
      congruence.
      simpl in Hin. destruct p as ((u, v), w).
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hin _].
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [Hl Hin].
      simpl. destruct xs.
      simpl. reflexivity.
      simpl in Hin. 
      destruct p as ((px, py), pw).
      congruence.
      simpl in Hin.
      congruence.
    + simpl; intros ? ? ? ? Hm Hin.
      pose proof append_node_in_paths_eq _ m c _ Hin as Hp.
      destruct Hp as [y [ys [Hy [Hsc [Hsd Hyn]]]]].
      apply append_node_rest in Hin.
      apply in_flat_map_bool_first in Hin.
      destruct Hin as [x [Hl Hr]].
      pose proof IHk m x d (List.tl xs) Hm Hr as Hind.
      pose proof source_target_and_non_empty_kpath k m x d 
        (List.tl xs) Hm Hr as (Ha & Hb & Hc).
      (* ys = List.tl xs that means y = x *)
      assert(Htt: triple_elem_list _ _ _ eqN eqN eqR (List.tl xs) ys = true).
      destruct xs. simpl in Hsc; congruence.
      simpl in Hy. simpl. destruct p as ((u, v), w).
      apply Bool.andb_true_iff in Hy.
      destruct Hy as [Hyl Hy]. exact Hy.
      pose proof source_same_path _ _ _ _ Htt Hb Hsd as Hp.
      apply list_tl_lia; assumption.
      apply refN.
  Qed.

  Lemma source_target_non_empty_kpath_and_well_formed : 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    (forall c d, (c =n= d) = true -> (m c d =r= 1) = true) -> 
    mat_cong Node eqN R eqR m ->  
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ oneR 
        finN m n c d) = true ->
    xs <> [] ∧
    source _ eqN _ c xs = true ∧
    target _ eqN _ d xs = true ∧
    well_formed_path_aux Node eqN R eqR m xs = true ∧
    (List.length xs = S n)%nat ∧
    exists xs', 
      triple_elem_list _ _ _ eqN eqN eqR 
        xs (xs' ++ [(d, d, 1)]) = true. 
  Proof using congrR refN refR symN symR trnN trnR. 
    intros ? ? ? ? ? Hcd Hm Hin.
    split.
    apply non_empty_paths_in_kpath with 
      (n := n) (m := m) (c := c) (d := d).
    exact Hin.
    split.
    apply source_in_kpath with 
      (n := n) (m := m) (d := d).
    exact Hin.
    split.
    eapply target_in_kpath with 
    (n := n) (m := m) (d := d).
    exact Hm.
    exact Hin.
    split.
    eapply all_paths_well_formed_in_kpaths;
    try assumption.
    exact Hin.
    split.
    eapply all_paths_in_klength.
    exact Hm.
    exact Hin.
    eapply path_end_unit_loop.
    exact Hin.
  Qed.


  (* generic lemma about list. It does not use any section assumption *)
  Lemma target_alt_end : 
    forall (l : list (Node * Node * R))
    (x : Node * Node * R) (d : Node),
    target_alt _ eqN _ d (l ++ [x]) = 
    target_alt _ eqN _ d [x].
  Proof.
    intros ? ? ?.
    unfold target_alt.
    rewrite rev_unit.
    assert (Ht : rev [x] = [x]).
    reflexivity.
    rewrite Ht; clear Ht.
    reflexivity.
  Qed.


  Lemma target_end : 
    forall (l : list (Node * Node * R))
    (x : Node * Node * R) (d : Node),
    target _ eqN _ d (l ++ [x]) = 
    target _ eqN _ d [x].
  Proof using Type.
    induction l.
    - simpl; intros ? ?. reflexivity.
    - intros ? ?.
      assert (Ht : target _ eqN _ d ((a :: l) ++ [x]) = 
        target _ eqN _ d (l ++ [x])).
      simpl. destruct a. destruct p.
      destruct (l ++ [x]) eqn:Hv.
      pose proof app_eq_nil l [x] Hv as Hw.
      destruct Hw as [Hwl Hwr].
      congruence. reflexivity.
      rewrite Ht. apply IHl.
  Qed.


  Lemma target_target_alt_same : 
    forall (l : list (Node * Node * R)) (d : Node), 
    target _ eqN _ d l = target_alt _ eqN _ d l.
  Proof using Type.
    induction l using rev_ind.
    - unfold target_alt; simpl; intros ?.
      reflexivity.
    - intros ?. rewrite target_alt_end, target_end.
      reflexivity.
  Qed.

  
  Lemma triple_elem_rewrite :
    forall xs ys m c au av aw,
    mat_cong Node eqN R eqR m ->
    tl xs ≠ [] ->  
    source Node eqN R c xs = true ->
    well_formed_path_aux Node eqN R eqR m xs = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      (List.tl xs) ((au, av, aw) :: ys) = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      xs ((c, au, m c au) :: (au, av, aw) :: ys) = true.
  Proof using congrR refR symN symR trnN.
    intros * Hm Ha Hs Hw Ht.
    destruct xs as [|((bbu, bbv), bbw) xs].
    simpl in Ha;
    congruence.
    destruct xs as [|((cbu, cbv), cbw) xs].
    simpl in Ha;
    congruence.
    simpl in Ha, Hs.
    remember ((cbu, cbv, cbw) :: xs) as cxs.
    simpl in Hw, Ht.
    simpl.
    rewrite Heqcxs in Hw.
    apply Bool.andb_true_iff in Hw.
    destruct Hw as [Hwl Hw].
    apply Bool.andb_true_iff in Hw.
    destruct Hw as [Hwll Hw].
    apply symN in Hs;
    rewrite Hs, Ht.
    simpl.
    rewrite Heqcxs in Ht.
    simpl in Ht.
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htr].
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htll].
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htlr].
    rewrite (trnN _ _ _ Hwll Ht).
    simpl.
    apply Bool.andb_true_iff.
    split.
    apply symR.
    rewrite <-Hwl.
    apply congrR.
    apply Hm.
    apply symN; 
    exact Hs.
    apply symN.
    apply trnN with cbu;
    try assumption.
    apply refR.
    reflexivity.
  Qed.


  
 
  Lemma append_node_rest_rev : 
    forall l m c xs,
    mat_cong Node eqN R eqR m -> 
    source _ eqN _ c xs = true -> 
    List.tl xs <> [] ->
    well_formed_path_aux Node eqN R eqR m xs = true ->
    In_eq_bool _ _ _ eqN eqN eqR (List.tl xs) l = true ->
    In_eq_bool _ _ _ eqN eqN eqR xs 
    (append_node_in_paths _ _ m c l) = true.
  Proof using congrR refN refR symN symR trnN trnR.
    induction l as [|al l IHl].
    + intros * Hm Hs Hl Hw Hin.
      simpl in *.
      congruence.
    + intros * Hm Hs Hl Hw Hin.
      simpl in Hin.
      simpl.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin | Hin].
      assert (Hat : exists au av aw ys, 
        al = ((au, av), aw) :: ys).
      destruct xs as [|((bu, bv), bw) xs].
      simpl in Hl;
      congruence.
      simpl in Hl, Hin.
      destruct xs as [|((cu, cv), cw) xs].
      simpl in Hl; 
      congruence.
      destruct al as [|((alu, alv), alw) al].
      simpl in Hin;
      congruence.
      exists alu, alv, alw, al. 
      reflexivity.
      destruct Hat as (au & av & aw & ys & Hat).
      rewrite Hat.
      assert (Hst : triple_elem_list Node Node R 
        eqN eqN eqR xs ((c, au, m c au) :: al) = true).
      rewrite Hat.
      eapply triple_elem_rewrite; 
      try assumption.
      rewrite Hat in Hin.
      exact Hin.
      eapply path_tl_rewrite;
      try assumption.
      apply triple_elem_eq_list_sym;
      try assumption.
      exact Hst.
      simpl.
      apply Bool.orb_true_iff.
      left.
      repeat (rewrite refN).
      repeat rewrite refR.
      simpl.
      rewrite Hat.
      apply triple_elem_eq_list_refl;
      try assumption.
      (* inductive hypothesis *)
      destruct al as [|((alu, alv), alw) al].
      apply IHl; try
      assumption.
      destruct xs as [|((cu, cv), cw) xs].
      simpl in Hl;
      congruence.
      simpl in Hl.
      destruct xs as [|((du, dv), dw) xs].
      simpl in Hl; 
      congruence.
      simpl.
      apply Bool.orb_true_iff.
      right. 
      remember ((cu, cv, cw) :: (du, dv, dw) :: xs) as cxs.
      apply IHl;
      try assumption.
      intro Hf;
      rewrite Heqcxs in Hf;
      simpl in Hf;
      congruence.
  Qed.



    


  (* *)
  Lemma source_target_non_empty_kpath_and_well_formed_rev : 
    ∀ (xs : list (Node * Node * R)) 
    (m : Matrix Node R) (c d : Node) ,
    mat_cong Node eqN R eqR m ->
    source _ eqN _ c (xs ++ [(d, d, 1)]) = true ->
    target _ eqN _ d (xs ++ [(d, d, 1)]) = true ->
    well_formed_path_aux Node eqN R eqR m (xs ++ [(d, d, 1)]) = true ->
    In_eq_bool _ _ _ eqN eqN eqR (xs ++ [(d, d, 1)])  
      (all_paths_klength _ eqN _ oneR 
        finN m (List.length xs) c d) = true.
  Proof using congrR memN refN refR symN symR trnN trnR.
    induction xs as [|((au, av), aw) xs].
    + intros * Hm Hs Ht Hw.
      simpl in *.
      rewrite Hs.
      simpl.
      apply symN in Hs.
      rewrite Hs, refN, refR.
      reflexivity.
    + intros * Hm Hs Ht Hw.
      simpl in Hs, Hw.
      assert (Hwt: exists bu bv bw ys, 
        xs ++ [(d, d, 1)] = (bu, bv, bw) :: ys).
      destruct xs as [|((cu, cv), cw) xs].
      exists d, d, 1, [].
      reflexivity.
      simpl.
      exists cu, cv, cw, (xs ++ [(d, d, 1)]).
      reflexivity.
      destruct Hwt as (bu & bv & bw & ys & Hwt).
      rewrite Hwt in Hw. 
      rewrite <-Hwt in Hw.
      simpl.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      assert (Hst: source Node eqN R bu (xs ++ [(d, d, 1)]) = true).
      rewrite Hwt; simpl; apply refN.
      assert (Htt: target Node eqN R d (xs ++ [(d, d, 1)]) = true).
      rewrite target_end;
      simpl; apply refN.
      specialize (IHxs m bu d Hm Hst Htt Hw).
      rewrite Hwt.
      rewrite Hwt in IHxs.
      (* Proof hinges on this lemma *)
      eapply append_node_rest_rev.
      simpl.
      exact Hm.
      exact Hs.
      simpl.
      intro Hf; congruence.
      remember ((bu, bv, bw) :: ys) as bys.
      simpl.
      rewrite Heqbys.
      rewrite <-Heqbys.
      rewrite Hwl, Hwll.
      rewrite Hwt in Hw.
      rewrite Hw.
      reflexivity.
      simpl.
      eapply in_flat_map_bool_second.
      intros ? ? ? Hxa.
      apply all_paths_cong.
      exact Hm.
      exact Hxa.
      apply memN.
      exact IHxs.
  Qed.      




  Lemma path_split_measure : forall l l₁ l₂, 
    triple_elem_list _ _ _ eqN eqN eqR l (l₁ ++ l₂) = true  -> 
    measure_of_path _ _ oneR mulR l =r= 
    measure_of_path _ _ oneR mulR l₁ * 
    measure_of_path _ _ oneR mulR l₂ = true.
  Proof using congrM congrR mul_associative one_left_identity_mul refR symR.
    induction l.
    - simpl; intros ? ? Hl.
      destruct l₁; 
      destruct l₂; 
      simpl in * |- *.
      apply symR. 
      apply one_left_identity_mul.
      all: congruence.
    - simpl; intros ? ? Hl.
      destruct a. 
      destruct p.
      destruct l₁; 
      destruct l₂; 
      simpl in * |- *.
      congruence.
      repeat destruct p.
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlrr].
      assert (Ht : 1 * (r0 * measure_of_path _ _ oneR mulR l₂) =r= 
        (r0 * measure_of_path _ _ oneR mulR l₂) = true).
      apply one_left_identity_mul.
      apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. apply congrM.
      exact Hlr.
      pose proof (IHl [] l₂) as IHs.
      simpl in IHs.
      specialize (IHs Hr).
      rewrite <-IHs.
      apply congrR. 
      apply refR.
      apply symR.
      apply one_left_identity_mul.
      apply refR.
      repeat destruct p.
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlrr].
      specialize (IHl l₁ [] Hr).
      simpl in IHl.
      assert (Ht : r0 * (measure_of_path _ _ oneR mulR l₁ * 1) =r= 
      r0 * measure_of_path _ _ oneR mulR l₁ * 1 = true).
      apply mul_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply congrM.
      exact Hlr. exact IHl.
      apply refR.
      repeat destruct p.
      destruct p0.
      destruct p.
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlrr].
      specialize (IHl l₁ ((n3, n4, r1) :: l₂) Hr).
      simpl in IHl.
      assert (Ht : r0 * (measure_of_path _ _ oneR mulR l₁ * 
        (r1 * measure_of_path _ _ oneR mulR l₂)) =r= 
        r0 * measure_of_path _ _ oneR mulR l₁ * 
        (r1 * measure_of_path _ _ oneR mulR l₂) = true).
      apply mul_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply congrM.
      exact Hlr.
      exact IHl.
      apply refR.
  Qed.



  
  Lemma fold_map_pullout : forall l w,
    fold_right (fun a b => a + b) 0 
      (map (fun y => w * measure_of_path _ _  oneR mulR y) l) =r=
    w * fold_right (fun a b => a + b) 0 
      (map (@measure_of_path Node R oneR mulR) l) = true.
  Proof using congrP congrR left_distributive_mul_over_plus refR symR zero_right_anhilator_mul.
    induction l.
    - simpl; intros ?.
      apply symR, 
      zero_right_anhilator_mul.
    - simpl; intros ?.
      assert (Ht: w *
        (measure_of_path Node R oneR mulR a +
        fold_right (λ a0 b : R, a0 + b) 0 
        (map (measure_of_path Node R oneR mulR) l)) =r= 
        w * measure_of_path Node R oneR mulR a + 
        w * fold_right (λ a0 b : R, a0 + b) 0 
        (map (measure_of_path Node R oneR mulR) l) = true).
      apply left_distributive_mul_over_plus.
      apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply congrP.
      apply refR.
      apply IHl.
      apply refR.
  Qed.


  

  Lemma map_measure_simp_gen :
    forall (l : list (list (Node * Node * R))) 
    (m : Matrix Node R) (c a : Node),
    mat_cong Node eqN R eqR m ->
    (forall xs, 
      In_eq_bool _ _ _ eqN eqN eqR xs l = true -> 
      xs <> [] /\ source Node eqN R a xs = true) ->
    list_eqv _ eqR 
      (map (measure_of_path _ _  oneR mulR) 
           (append_node_in_paths Node R m c l))
      (map (fun y => m c a * 
        measure_of_path _ _  oneR mulR y) l) = true.
  Proof using congrM refN refR symN.
    induction l as [|ys yss IH].
    - simpl; intros ? ? ? Hm Hin.
      reflexivity.
    - simpl; intros ? ? ? Hm Hin.
      assert (Ht : (triple_elem_list _ _ _ eqN eqN eqR ys ys || 
        In_eq_bool _ _ _ eqN eqN eqR ys yss)%bool = true).
      apply Bool.orb_true_iff.
      left. 
      apply triple_elem_eq_list_refl;
      try assumption.
      pose proof (Hin ys Ht) as Ha.
      destruct Ha as [Ha Hs].
      destruct ys. 
      congruence. 
      simpl.
      repeat destruct p.
      simpl. 
      simpl in Hs.
      apply Bool.andb_true_iff.
      split.
      apply congrM.
      apply Hm. 
      apply refN.
      apply symN. 
      exact Hs.
      apply refR. 
      apply IH. 
      exact Hm.
      intros ? Hxs.
      apply Hin.
      apply Bool.orb_true_iff.
      right. 
      exact Hxs.
  Qed.



  Lemma map_measure_simp : 
    forall m n c d a, 
    mat_cong Node eqN R eqR m -> 
    list_eqv _ eqR 
    (map (measure_of_path _ _  oneR mulR) 
      (append_node_in_paths Node R m c 
        (all_paths_klength _ eqN _ oneR finN m n a d)))
    (map (fun y => m c a * measure_of_path _ _ oneR mulR y) 
      (all_paths_klength _ eqN _ oneR finN m n a d)) = true.
  Proof using congrM refN refR symN symR trnN trnR.
    intros ? ? ? ? ? Hm.
    apply map_measure_simp_gen.
    exact Hm.
    intros ? Hin.
    pose proof source_target_and_non_empty_kpath n m a d xs 
      Hm Hin as (Ha & Hb & Hc).
    split; assumption.
  Qed.



  Lemma fold_right_congr : 
    forall l₁ l₂,
    list_eqv R eqR l₁ l₂ = true -> 
    fold_right (fun a b => a + b) 0 l₁ =r= 
    fold_right (fun a b => a + b) 0 l₂ = true.
  Proof using congrP refR.
    induction l₁; destruct l₂; simpl; intro H.
    - apply refR.
    - inversion H.
    - inversion H.
    - apply Bool.andb_true_iff in H.
      destruct H as [Hl Hr].
      apply congrP.
      exact Hl.
      apply IHl₁.
      exact Hr.
  Qed.

  Lemma append_node_app : 
    forall (l₁ l₂ : list (list (Node * Node * R))) 
    (m : Matrix Node R) (c : Node), 
    fold_right (λ u v : R, u + v) 0
      (map (measure_of_path Node R 1 mulR)
        (append_node_in_paths Node R m c
          (l₁ ++ l₂))) 
    =r=
    fold_right (λ u v : R, u + v) 0
      (map (measure_of_path Node R 1 mulR)
        (append_node_in_paths Node R m c l₁ ++ 
        append_node_in_paths Node R m c l₂)) = true.
  Proof using congrP refR.
    induction l₁ as [|a l₁ IHL₁].
    - simpl; intros ? ? ?.
      apply refR.
    - simpl; intros ? ? ?.
      destruct a.
      apply IHL₁.
      repeat destruct p.
      simpl. 
      apply congrP.
      apply refR.
      apply IHL₁.
  Qed.


  (* x * l1 + x * l2 + x * l3 = x * (l1 + l2 + l3) *)
  Lemma fold_right_measure : forall n m c a d,
    mat_cong Node eqN R eqR m -> 
    (fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
    (map (measure_of_path Node R 1 mulR)
      (append_node_in_paths Node R m c 
        (all_paths_klength _ eqN _ oneR finN m n a d))) =r=
    m c a *
    fold_right (λ b v : R, b + v) 0
      (map (measure_of_path Node R 1 mulR) 
        (all_paths_klength _ eqN _ oneR finN m n a d))) = true.
  Proof using congrM congrP congrR left_distributive_mul_over_plus refN refR
    symN symR trnN trnR zero_right_anhilator_mul.
    intros ? ? ? ? ? Hm.
    assert (Ht : 
    fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
    (map (measure_of_path Node R 1 mulR)
      (append_node_in_paths Node R m c 
        (all_paths_klength _ eqN _ oneR finN m n a d))) =r= 
    fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
    (map (fun y => m c a * measure_of_path Node R 1 mulR y) 
      (all_paths_klength _ eqN _ oneR finN m n a d)) = true).
    apply fold_right_congr.
    apply map_measure_simp.
    exact Hm.
    rewrite <-Ht; clear Ht.
    apply congrR.
    apply refR.
    apply symR.
    apply fold_map_pullout.
  Qed.


  
  








  Lemma path_reconstruction : 
    forall (l : list (Node * Node * R)) m,
    mat_cong Node eqN R eqR m ->
    well_formed_path_aux _ eqN _ eqR m l = true -> 
    triple_elem_list _ _ _ eqN eqN eqR 
      (construct_path_from_nodes _ _ 
        (collect_nodes_from_a_path Node R l) m)
      l = true.
  Proof using congrR refN refR symN.
    induction l.
    + intros * Hm Hw. 
      simpl; reflexivity.
    + intros * Hm Hw. 
      simpl.
      destruct a as ((au, av), aw).
      destruct l.
      simpl in * |- *.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hw _].
      repeat (apply Bool.andb_true_iff; split;
      try (apply refN); try assumption).
      reflexivity.
      (* induction case *)
      destruct p as ((pu, pv), pw). 
      assert (Hwt: (well_formed_path_aux _ eqN _ eqR m 
        ((au, av, aw) :: (pu, pv, pw) :: l) = 
        (m au av =r= aw) && ((av =n= pu) && 
        well_formed_path_aux _ eqN _ eqR m ((pu, pv, pw) :: l)))%bool).
      simpl. reflexivity.
      rewrite Hwt in Hw; clear Hwt.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      specialize (IHl m Hm Hw).
      assert (Hwt: construct_path_from_nodes _ _ 
        (au :: collect_nodes_from_a_path Node R ((pu, pv, pw) :: l)) m =
        (au, pu, m au pu) :: 
        construct_path_from_nodes _ _ 
          (collect_nodes_from_a_path _ _ ((pu, pv, pw) :: l)) m).
      simpl. destruct l.
      reflexivity. reflexivity.
      rewrite Hwt; clear Hwt.
      remember (construct_path_from_nodes _ _ 
      (collect_nodes_from_a_path _ _ ((pu, pv, pw) :: l)) m) as ml.
      remember ((pu, pv, pw) :: l) as pl.
      simpl.
      repeat (apply Bool.andb_true_iff; split).
      apply refN. apply symN. exact Hwll.
      rewrite <-Hwl. apply congrR.
      apply Hm. apply refN.
      apply symN. exact Hwll.
      apply refR.
      exact IHl.
  Qed.


  
  Lemma source_list_construction : forall l c m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux _ eqN _ eqR  m l = true -> 
    source _ eqN R c l = true ->
    exists d lc, 
    triple_elem_list _ _ _ eqN eqN eqR 
      l ((c, d, m c d) :: lc) = true.
  Proof using congrR refN refR symN symR.
    destruct l.
    + intros ? ? Hm Hw Hs.
      simpl in Hs. congruence.
    + intros ? ? Hm Hw Hs.
      destruct p as ((u, v), w).
      simpl in * |- *.
      exists v, l.
      repeat (apply Bool.andb_true_iff; split).
      apply symN; assumption.
      apply refN.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hw _].
      apply symR. rewrite <-Hw.
      apply congrR.
      apply Hm. exact Hs.
      apply refN.
      apply refR.
      apply triple_elem_eq_list_refl;
      try assumption.
  Qed.


  Lemma target_list_construction : 
    forall l c m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux _ eqN _ eqR m l = true -> 
    target _ eqN R c l = true ->
    exists d lc, 
    triple_elem_list  _ _ _ eqN eqN eqR 
      l (lc ++ [(d, c, m d c)]) = true.
  Proof using congrR refN refR symN symR.
    induction l.
    + intros ? ? Hm Hw Ht.
      simpl in Ht.
      congruence.
    + intros ? ? Hm Hw Ht.
      destruct l.
      destruct a as ((au, av), aw).
      simpl in * |-.
      exists au, [].
      simpl.
      apply Bool.andb_true_iff; split.
      apply Bool.andb_true_iff; split.
      apply Bool.andb_true_iff; split.
      all:(try (apply refN); try (apply refR)).
      apply symN; assumption.
      apply symR.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hw _].
      rewrite <-Hw.
      apply congrR.
      apply Hm.
      apply refN.
      exact Ht.
      apply refR.
      reflexivity.
      destruct a as ((au, av), aw).
      destruct p as ((pu, pv), pw).
      assert (Hwt: (well_formed_path_aux _ eqN _ eqR m ((au, av, aw) :: (pu, pv, pw) :: l) = 
        (m au av =r= aw) && ((av =n= pu) && well_formed_path_aux _ eqN _ eqR m ((pu, pv, pw) :: l)))%bool).
      simpl. reflexivity.
      rewrite Hwt in Hw; clear Hwt.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      assert (Hwt : target _ eqN R c ((au, av, aw) :: (pu, pv, pw) :: l) = 
      target _ eqN R c ((pu, pv, pw) :: l)). simpl. reflexivity.
      rewrite Hwt in Ht; clear Hwt.
      destruct (IHl c m Hm Hw Ht) as [d [lc Hlc]].
      exists d, ((au, av, aw) :: lc).
      rewrite <-List.app_comm_cons.
      remember ((pu, pv, pw) :: l) as pl.
      remember (lc ++ [(d, c, m d c)]) as ld.
      simpl. 
      apply Bool.andb_true_iff; split.
      apply Bool.andb_true_iff; split.
      apply Bool.andb_true_iff; split.
      all:(try (apply refN); try (apply refR)).
      exact Hlc.
  Qed.


  Lemma list_equality_cons_gen : 
    forall l ld le c d mcd e f mef,
    l <> [] -> 
    triple_elem_list _ _ _ eqN eqN eqR  l ((c, d, mcd) :: ld) = true ->
    triple_elem_list _ _ _ eqN eqN eqR  l (le ++ [(e, f, mef)]) = true ->
    (triple_elem_list _ _ _ eqN eqN eqR l [(c, d, mcd)] = true ∧ 
     triple_elem_list _ _ _ eqN eqN eqR l [(e, f, mef)] = true) 
     ∨ 
    (exists lm, 
      triple_elem_list _ _ _ eqN eqN eqR  
      l ((c, d, mcd) :: lm ++ [(e, f, mef)]) = true).
  Proof using lenN.
    induction l as [|((au, av), aw) l].
    + intros * H He Hf.
      congruence.
    + intros * H He Hf.
      destruct l as [|((bu, bv), bw) l].
      destruct ld as [|((ldu, ldv), ldw) ld].
      destruct le as [|((leu, lev), lew) le].
      left.
      simpl in * |-*.
      split. exact He.
      exact Hf.
      simpl in Hf.
      destruct le;
      simpl in Hf; lia.
      destruct ld;
      simpl in He; lia.
      destruct ld as [|((ldu, ldv), ldw) ld].
      simpl in He. 
      apply Bool.andb_true_iff in He.
      lia.
      destruct le as [|((leu, lev), lew) le].
      simpl in Hf.
      apply Bool.andb_true_iff in Hf.
      lia.
      remember ((bu, bv, bw) :: l) as bl.
      remember ((ldu, ldv, ldw) :: ld) as dl.
      assert (Hwt : (((leu, lev, lew) :: le) ++ [(e, f, mef)]) =
      ((leu, lev, lew) :: (le ++ [(e, f, mef)]))).
      simpl; reflexivity.
      rewrite Hwt in Hf; clear Hwt.
      simpl in He, Hf.
      apply Bool.andb_true_iff in He, Hf.
      destruct He as [He Her].
      destruct Hf as [Hf Hfr].
      subst.
      assert (Hwt : (bu, bv, bw) :: l ≠ []).
      intro Hff; congruence.
      specialize(IHl _ _ _ _ _ _ _ _ Hwt Her Hfr).
      destruct IHl as [[IHll IHlr] | [lm IHl]].
      right.
      exists [].
      remember ((bu, bv, bw) :: l) as bl.
      simpl.
      apply Bool.andb_true_iff; split.
      exact He. assumption.
      right.
      exists ((ldu, ldv, ldw) :: lm).
      remember ((bu, bv, bw) :: l) as bl.
      simpl.
      apply Bool.andb_true_iff; split.
      exact He.
      exact IHl.
  Qed.


  Lemma in_list_mem_collect : 
    forall l c d mcd, 
    in_list eqN 
      (collect_nodes_from_a_path _ R (l ++ [(c, d, mcd)])) d = true.
  Proof using refN.
    induction l.
    + intros ? ? ?.
      simpl.
      apply Bool.orb_true_iff.
      right. apply Bool.orb_true_iff.
      left. apply refN.
    + intros ? ? ?.
      destruct a as ((au, av), aw).
      rewrite <-List.app_comm_cons.
      remember (l ++ [(c, d, mcd)]) as lcd.
      simpl. 
      destruct lcd.
      assert (Hwt : exists w wl, l ++ [(c, d, mcd)] = w :: wl).
      destruct l. simpl.
      exists (c, d, mcd), [].
      reflexivity.
      simpl. exists p, (l ++ [(c, d, mcd)]).
      reflexivity.
      destruct Hwt as [w [wt Hwt]].
      rewrite Hwt in Heqlcd.
      congruence.
      rewrite Heqlcd.
      simpl.
      apply Bool.orb_true_iff.
      right.
      apply IHl.
  Qed.



  Lemma in_list_collect : 
    forall pl plw a b, 
    (a =n= b = true) ->
    triple_elem_list _ _ _ eqN eqN eqR pl plw = true ->
    in_list eqN (collect_nodes_from_a_path Node R pl) a =
    in_list eqN (collect_nodes_from_a_path Node R plw) b.
  Proof using symN trnN.
    induction pl as [|((au, av), aw) pl].
    + intros [|((bu, bv), bw) plw] ? ? Hab Ht.
      reflexivity.
      simpl in Ht; congruence.
    + intros [|((bu, bv), bw) plw] ? ? Hab Ht.
      simpl in Ht; congruence.
      simpl in Ht.
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrrr].
      specialize (IHpl plw a b Hab Htr).
      destruct pl as [|((cu, cv), cw) pl].
      destruct plw as [|((du, dv), dw) plw].
      simpl.
      f_equal.
      case (a =n= au) eqn:Hau;
      case (b =n= bu) eqn:Hbu.
      reflexivity.
      pose proof trnN _ _ _ Hau Ht as Hf.
      apply symN in Hab.
      pose proof trnN _ _ _ Hab Hf.
      rewrite H in Hbu.
      congruence.
      pose proof trnN _ _ _ Hab Hbu.
      pose proof trnN _ _ _ H (symN _ _ Ht) as Hf.
      rewrite Hf in Hau. congruence.
      reflexivity.
      f_equal.
      case (a =n= av) eqn:Hav;
      case (b =n= bv) eqn:Hbv.
      reflexivity.
      pose proof trnN _ _ _ (symN _ _ Hab) (trnN _ _ _ Hav Htrrr) as Hf.
      rewrite Hf in Hbv.
      congruence.
      pose proof trnN _ _ _ (trnN _ _ _ Hab Hbv) (symN _ _ Htrrr) as Hf.
      rewrite Hf in Hav.
      congruence.
      reflexivity.
      simpl in Htr.
      congruence.
      destruct plw as [|((du, dv), dw) plw].
      simpl in Htr.
      congruence.
      remember ((cu, cv, cw) :: pl) as cpl.
      remember ((du, dv, dw) :: plw) as dpl.
      simpl.
      rewrite Heqcpl, Heqdpl.
      rewrite <-Heqcpl, <-Heqdpl.
      simpl.
      f_equal.
      case (a =n= au) eqn:Hau;
      case (b =n= bu) eqn:Hbu.
      reflexivity.
      pose proof trnN _ _ _ Hau Ht as Hf.
      apply symN in Hab.
      pose proof trnN _ _ _ Hab Hf.
      rewrite H in Hbu.
      congruence.
      pose proof trnN _ _ _ Hab Hbu.
      pose proof trnN _ _ _ H (symN _ _ Ht) as Hf.
      rewrite Hf in Hau. congruence.
      reflexivity.
      exact IHpl.
  Qed.


  Lemma well_formed_path_rewrite :
    forall l lw m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m l = true ->
    triple_elem_list _ _ _ eqN eqN eqR l lw = true ->
    well_formed_path_aux Node eqN R eqR m lw = true.
  Proof using congrR lenN symN symR trnN.
    induction l as [|((au, av), aw) l].
    + intros [|((bu, bv), bw) lw] ? Hm Hw Ht.
      reflexivity.
      simpl in Ht. lia.
    + intros ? ? Hm Hw Ht.
      destruct lw as [|((bu, bv), bw) lw].
      simpl in Ht. congruence.
      simpl in Ht.
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrrr].
      (* Now, I need to know if l is well formed or not *)
      destruct l as [|((cu, cv), cw) l].
      destruct lw as [|((du, dv), dw) lw].
      simpl. simpl in Hw.
      apply Bool.andb_true_iff.
      split. 
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hw _].
      rewrite <-Hw.
      apply congrR.
      apply Hm.
      apply symN; assumption.
      apply symN; assumption.
      apply symR; assumption.
      reflexivity.
      simpl in Htr.
      congruence.
      assert (Hwt: (well_formed_path_aux Node eqN R eqR m ((au, av, aw) :: (cu, cv, cw) :: l) = 
        (m au av =r= aw) && ((av =n= cu) && 
        well_formed_path_aux Node eqN R eqR m ((cu, cv, cw) :: l)))%bool).
      simpl. reflexivity.
      rewrite Hwt in Hw; clear Hwt.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      specialize (IHl lw m Hm Hw Htr).
      simpl. apply Bool.andb_true_iff.
      split. 
      rewrite <-Hwl.
      apply congrR.
      apply Hm.
      apply symN; assumption.
      apply symN; assumption.
      apply symR; assumption.
      destruct lw. 
      reflexivity.
      destruct p as ((pu, pv), pw).
      simpl in Htr.
      apply Bool.andb_true_iff.
      split.
      apply Bool.andb_true_iff in Htr.
      destruct Htr as [Htr Htrv].
      apply Bool.andb_true_iff in Htr.
      destruct Htr as [Htr Htrw].
      apply Bool.andb_true_iff in Htr.
      destruct Htr as [Htr Htwx].
      apply trnN with cu.
      apply symN in Htrrr.
      apply trnN with av; assumption.
      exact Htr.
      exact IHl. 
  Qed.       


 
  Lemma collect_nodes_from_a_path_app : 
    forall l m a b mab,
    l <> [] -> 
    well_formed_path_aux Node eqN R eqR m 
      (l ++ [(a, b, mab)]) = true ->
    list_eqv _ eqN 
      (collect_nodes_from_a_path Node R (l ++ [(a, b, mab)]))
      (collect_nodes_from_a_path Node R l ++ [b]) = true.
  Proof using refN symN.
    induction l as [|((au, av), aw) l].
    + intros ? ? ? ? Hf Hw.
      congruence.
    + intros ? ? ? ? Hf Hw.
      destruct l as [|((bu, bv), bw) l].
      - simpl in * |- *.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hw _].
        repeat (apply Bool.andb_true_iff; split).
        apply refN.
        apply symN; assumption.
        apply refN.
        reflexivity.
      - (* induction case *)
        assert (Hwt: (bu, bv, bw) :: l ≠ []).
        intros H; congruence.
        rewrite <-List.app_comm_cons in Hw.
        remember (((bu, bv, bw) :: l) ++ [(a, b, mab)]) as blm.
        simpl in Hw. 
        rewrite <-List.app_comm_cons in Heqblm.
        rewrite Heqblm in Hw.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        specialize (IHl m a b mab Hwt Hw).
        simpl. 
        apply Bool.andb_true_iff; split.
        apply refN.
        exact IHl.
  Qed.
        

  Lemma well_formed_path_snoc : 
    forall ll lr m,
    well_formed_path_aux Node eqN R eqR m (ll ++ lr) = true ->
    well_formed_path_aux Node eqN R eqR m ll = true /\ 
    well_formed_path_aux Node eqN R eqR m lr = true.
  Proof using Type.
    induction ll.
    + intros ? ? Hw.
      simpl in Hw.
      split.
      reflexivity.
      exact Hw.
    + intros ? ? Hw.
      destruct a as ((au, av), aw).
      simpl in Hw.
      destruct ll;
        destruct lr.
      simpl in Hw.
      simpl. split.
      exact Hw.
      reflexivity.
      rewrite List.app_nil_l in Hw.
      destruct p as ((pu, pv), pw).
      split.
      simpl.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      rewrite Hwl. reflexivity.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      exact Hw.
      rewrite List.app_nil_r in Hw.
      destruct p as ((pu, pv), pw).
      split.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      specialize (IHll [] m).
      rewrite List.app_nil_r in IHll.
      specialize (IHll Hw).
      remember ((pu, pv, pw) :: ll) as pl.
      simpl. 
      rewrite Heqpl.
      apply Bool.andb_true_iff; split.
      assumption.
      apply Bool.andb_true_iff; split.
      assumption.
      rewrite <-Heqpl.
      assumption.
      reflexivity.
      rewrite <-List.app_comm_cons in Hw.
      destruct p as ((pu, pv), pw).
      specialize (IHll (p0 :: lr) m).
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      rewrite <-List.app_comm_cons in IHll.
      specialize (IHll Hw).
      remember ((pu, pv, pw) :: ll) as pll.
      split. simpl.
      rewrite Heqpll.
      apply Bool.andb_true_iff; split.
      assumption.
      apply Bool.andb_true_iff; split.
      assumption.
      destruct IHll as [IHlll IHllr].
      rewrite <-Heqpll.
      assumption.
      destruct IHll as [IHlll IHllr].
      assumption.
  Qed.


  
  Lemma construct_path_from_nodes_app : forall ll lr a b m,
    triple_elem_list _ _ _ eqN eqN eqR
      (construct_path_from_nodes _ R (a :: ll ++ [b]) m ++
        construct_path_from_nodes _ R (b :: lr) m)
      (construct_path_from_nodes _ R (a :: ll ++ b :: lr) m) = true.
  Proof using refN refR.
    induction ll as [|u ll IHll];
      destruct lr as [|v lr].
    + intros ? ? ?; simpl.
      repeat (apply Bool.andb_true_iff; split);
      try (apply refN); try (apply refR);
      reflexivity.
    + intros ? ? ?.
      remember (v :: lr) as vlr.
      simpl.
      rewrite Heqvlr. 
      repeat (apply Bool.andb_true_iff; split);
      try (apply refN); try (apply refR);
      try (apply triple_elem_eq_list_refl);
      try assumption.
    + intros ? ? ?.
      rewrite <-List.app_comm_cons.
      remember (ll ++ [b]) as llb.
      simpl.
      assert (Hwt : exists w wl, ll ++ [b] = w :: wl).
      destruct ll. simpl.
      exists b, [].
      reflexivity.
      simpl. exists n, (ll ++ [b]).
      reflexivity.
      destruct Hwt as [w [wt Hwt]].
      rewrite Hwt in Heqllb.
      rewrite Heqllb.
      rewrite List.app_nil_r.
      repeat (apply Bool.andb_true_iff; split);
      try (apply refN); try (apply refR);
      try (apply triple_elem_eq_list_refl);
      try assumption.
    + intros ? ? ?. 
      specialize (IHll (v :: lr) u b m).
      simpl in * |- *.
      repeat (apply Bool.andb_true_iff; split);
      try (apply refN); try (apply refR);
      try (apply IHll).
  Qed.
  
  
  
  Lemma keep_collecting_dropping_dual : 
    forall l au, 
    triple_elem_list _ _ _ eqN eqN eqR l
      (keep_collecting Node eqN R au l ++ 
      keep_dropping Node eqN R au l) = true.
  Proof using refN refR.
    induction l as [|((ah, bh), ch) l].
    + intros ?; simpl; reflexivity.
    + intros ?; simpl.
      case (au =n= bh) eqn:Ha.
      rewrite <-List.app_comm_cons.
      rewrite refN, refN, refR.
      simpl. 
      apply triple_elem_eq_list_refl;
      try assumption.
      rewrite <-List.app_comm_cons.
      rewrite refN, refN, refR.
      simpl.
      apply IHl.
  Qed.

 
  Lemma elem_path_triple_tail_true : forall l av,
    elem_path_triple_tail Node eqN R av l = true ->
    exists ll au aw lr, 
      triple_elem_list _ _ _ eqN eqN eqR l (ll ++ [(au, av, aw)] ++ lr) = true /\ 
      elem_path_triple_tail Node eqN R  av ll = false /\ 
      triple_elem_list _ _ _ eqN eqN eqR 
      (ll ++ [(au, av, aw)]) (keep_collecting Node eqN R av l) = true.
  Proof using refN refR symN.
    induction l as [|((ah, bh), ch) l].
    + intros ? He.
      simpl in He; congruence.
    + intros ? He.
      simpl in He.
      case (av =n= bh) eqn:Hb.
      exists [], ah, ch, l.
      split.
      rewrite List.app_nil_l.
      simpl. apply symN in Hb. 
      rewrite Hb.
      rewrite refN.
      rewrite refR.
      simpl.
      apply triple_elem_eq_list_refl;
      try assumption.
      split.
      simpl. reflexivity.
      simpl. 
      rewrite Hb.
      rewrite Hb, refN, refR.
      reflexivity.
      (* induction case *)
      destruct (IHl av He) as [ll [au [aw [lr [Hlra [Hlrb Hlrc]]]]]].
      exists ((ah, bh, ch) :: ll), au, aw, lr.
      split.
      rewrite <-List.app_comm_cons.
      simpl.
      repeat (rewrite refN).
      rewrite refR.
      simpl. exact Hlra.
      split.
      simpl. rewrite Hb.
      exact Hlrb.
      simpl. 
      rewrite Hb, refN, refR, refN.
      exact Hlrc.
  Qed.



  Lemma elem_path_triple_tail_simp : 
    forall l av, 
    elem_path_triple_tail  Node eqN R av l = true ->
    exists ll au aw, 
      triple_elem_list _ _ _ eqN eqN eqR 
      (ll ++ [(au, av, aw)]) 
      (keep_collecting _ eqN _ av l) = true.
  Proof using refN refR.
    induction l as [|((ah, bh), ch) l].
    + intros ? He.
      simpl in He; congruence.
    + intros ? He.
      simpl in He.
      case (av =n= bh) eqn:Hb.
      exists [], ah, ch.
      rewrite List.app_nil_l.
      simpl.  
      rewrite Hb.
      rewrite refN.
      rewrite refR.
      rewrite Hb.
      simpl. reflexivity.
  
      (* induction case *)
      simpl in He.
      destruct (IHl av He) as [ll [aut [awt Htr]]]. 
      exists ((ah, bh, ch) :: ll), aut, awt.
      rewrite <-List.app_comm_cons.
      simpl.
      rewrite Hb.
      repeat (rewrite refN).
      rewrite refR.
      simpl. exact Htr.
  Qed.


  
  Lemma keep_collecting_rewrite : 
    forall ll lr au, 
    triple_elem_list _ _ _ eqN eqN eqR ll lr = true ->
    target _ eqN R au ll = true -> 
    target _ eqN R au lr = true.
  Proof using trnN.
    induction ll as [|((au, av), aw) ll].
    + intros ? ? He Ht.
      simpl in Ht. congruence. 
    + intros [|((bu, bv), bw) lr] ? He Ht.
      simpl in He.  congruence.
      simpl in He.
      apply Bool.andb_true_iff in He.
      destruct He as [He Her].
      apply Bool.andb_true_iff in He.
      destruct He as [He Herr].
      apply Bool.andb_true_iff in He.
      destruct He as [He Herrr].
      destruct ll; destruct lr.
      simpl. simpl in Ht.
      apply trnN with av;
      assumption.
      simpl in Her.
      congruence.
      simpl in Her.
      destruct p as ((pu, pv), pw).
      congruence.
      remember (p :: ll) as pll.
      simpl in Ht.
      rewrite Heqpll in Ht.
      subst.
      specialize (IHll _ _ Her Ht).
      remember (p0 :: lr) as plr.
      simpl. rewrite Heqplr.
      subst.
      exact IHll.
  Qed.



  Lemma compute_loop_cycle : 
    forall l lc,
    Some lc = elem_path_triple_compute_loop Node eqN R l ->
    exists au av aw lcc, Some ((au, av, aw) :: lcc) = Some lc /\ 
    cyclic_path Node eqN R au lc.
  Proof using refN refR symN trnN.
    induction l.
    + intros ? Hl.
      simpl in Hl; congruence.
    + intros ? Hl.
      destruct a as ((au, av), aw).
      simpl in Hl.
      case (au =n= av) eqn:Hb.
      (* loop of 1 lenght *)
      exists au, av, aw, [].
      split. eauto.
      unfold cyclic_path.
      split. congruence.
      split. 
      inversion Hl; subst; clear Hl;
      simpl; apply refN.
      inversion Hl; subst; clear Hl.
      simpl. exact Hb.
      (* loop of 2 or more length *)
      case (elem_path_triple_tail Node eqN R au l) eqn:He.
      exists au, av, aw, (keep_collecting Node eqN R au l).
      split. symmetry.
      exact Hl.
      unfold cyclic_path.
      split.
      congruence.
      split. 
      inversion Hl; subst; 
      simpl; apply refN.
      destruct (elem_path_triple_tail_true l au He) 
        as [ll [aut [awt [lr [Hlra [Hlrb Hlrc]]]]]].
      inversion Hl; subst; clear Hl.
      apply target_tail_forward; simpl.
      eapply keep_collecting_rewrite with (ll ++ [(aut, au, awt)]).
      exact Hlrc.
      erewrite target_end.
      simpl; apply refN.
      destruct (IHl _ Hl) as [aut [avt [awt [lcc [Hsl Hcy]]]]].
      exists aut, avt, awt, lcc.
      split.
      exact Hsl.
      exact Hcy.
  Qed.


  Lemma compute_loop_cycle_tim : 
    forall l lcc au av aw,
    Some ((au, av, aw) :: lcc) = elem_path_triple_compute_loop Node eqN R l ->
    cyclic_path Node eqN R au ((au, av, aw) :: lcc).
  Proof using refN refR symN trnN.
    intros * Hs.
    destruct (compute_loop_cycle l ((au, av, aw) :: lcc) Hs)  as 
    (aut & avt & awt & lcct & Hss & Hcc).
    inversion Hss; subst; clear Hss.
    exact Hcc.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_true_first : 
    forall l,
    elem_path_triple Node eqN R l = true -> 
    elem_path_triple_compute_loop Node eqN R l = None.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + intros He; simpl in He.
      simpl. reflexivity.
    + intros He; simpl in * |- *.
      apply Bool.andb_true_iff in He.
      destruct He as [He Her].
      apply Bool.andb_true_iff in He.
      destruct He as [He Herr].
      apply Bool.negb_true_iff in Herr, He.
      rewrite He, Herr.
      apply IHl; assumption.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_true_second : 
    forall l,
    elem_path_triple_compute_loop Node eqN R l = None -> 
    elem_path_triple Node eqN R l = true.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + intros He; simpl in He.
      simpl. reflexivity.
    + intros He; simpl in * |- *.
      case (au =n= av) eqn:Hb.
      congruence.
      simpl.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hbe.
      congruence.
      simpl. 
      apply IHl; assumption.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_true_none_eqv : 
    forall l, 
    elem_path_triple_compute_loop Node eqN R l = None 
    <-> 
    elem_path_triple Node eqN R l = true.
  Proof using Type.
    intros ?; split; intro H.
    apply elim_path_triple_connect_compute_loop_true_second; assumption.
    apply elim_path_triple_connect_compute_loop_true_first; assumption.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_false_first : 
    forall l,
    elem_path_triple Node eqN R l = false -> 
    exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop Node eqN R l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path Node eqN R au lc. 
  Proof using refN refR trnN.
    induction l as [|((au, av), aw) l].
    + intro H; simpl in H.
      congruence.
    + intros He; simpl in He.
      case (au =n= av) eqn:Ha.
      simpl in He.
      (* loop of lenght 1, at the head itself *)
      exists au, av, aw, [(au, av, aw)], [].
      split. simpl.
      rewrite Ha.
      f_equal.
      split. 
      f_equal.
      unfold cyclic_path.
      split.
      congruence.
      split; simpl.
      apply refN.
      exact Ha.
      simpl in He.
      (* loop starts here but of >= lenght 2 *)
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
      simpl in He.
      repeat eexists.
      simpl. rewrite Ha, Hb.
      f_equal.
      congruence.
      simpl. 
      apply refN.
      apply target_tail_forward; simpl.
      destruct (elem_path_triple_tail_simp _ _ Hb) as (ll & aut & awt & Ht).
      erewrite keep_collecting_rewrite.
      reflexivity.
      exact Ht.
      erewrite target_end.
      simpl. apply refN.
      simpl in He.
      destruct (IHl He) as (aut & avt & awt & lc & lcc & Hlc & Haut & Hc).
      repeat eexists.
      simpl. rewrite Ha, Hb.
      rewrite <-Haut in Hlc.
      exact Hlc.
      congruence.
      simpl. apply refN.
      unfold cyclic_path in Hc.
      rewrite Haut.
      firstorder.
  Qed.



  Lemma elim_path_triple_connect_compute_loop_false_second : 
    forall l lc, 
    Some lc = elem_path_triple_compute_loop Node eqN R l ->
    elem_path_triple Node eqN R l = false.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + intros ? Hs; simpl in Hs;
      congruence.
    + intros ? Hs; simpl in * |- *.
      case (au =n= av) eqn:Ha.
      simpl. reflexivity.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
      simpl. reflexivity.
      simpl.
      eapply IHl; exact Hs.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_false_eqv : 
    forall l,
    elem_path_triple Node eqN R l = false <-> 
    exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop Node eqN R l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path Node eqN R au lc.
  Proof using refN refR trnN.
    intros *; split; intros He.
    apply  elim_path_triple_connect_compute_loop_false_first; assumption.
    destruct He as (au & av & aw & lc & lcc & Hs & Hlcc & Hc).
    eapply elim_path_triple_connect_compute_loop_false_second; 
    exact Hs.
  Qed.


  Lemma elem_path_triple_compute_loop_triple_middle_element : 
    forall l ll lm lr, 
    (ll, lm, lr) = elem_path_triple_compute_loop_triple Node eqN R l ->
    lm = elem_path_triple_compute_loop Node eqN R l.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + intros ? ? ? Hl; simpl in Hl; simpl;
      inversion Hl; subst; reflexivity.
    + intros ? ? ? Hl.
      simpl in * |- *.
      case (au =n= av) eqn:Ha.
      inversion Hl; subst; reflexivity.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
      inversion Hl; subst; reflexivity.
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as ((al, bl), cl).
      inversion Hl; subst; clear Hl.
      eapply IHl.
      reflexivity.
  Qed.


  Lemma elem_path_triple_compute_loop_triple_combined_list : forall l,
    match elem_path_triple_compute_loop_triple Node eqN R l with
    | (fp, None, tp) => triple_elem_list _ _ _ eqN eqN eqR l (fp ++ tp) = true
    | (fp, Some sp, tp) => triple_elem_list _ _ _ eqN eqN eqR l (fp ++ sp ++ tp) = true
    end. 
  Proof using refN refR.
    induction l as [|((au, av), aw) l].
    + simpl; reflexivity.
    + simpl. 
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as ((la, lb), lc).
      case (au =n= av) eqn:Ha.
      rewrite List.app_nil_l, 
      <-List.app_comm_cons.
      rewrite refN, refN, refR.
      simpl. 
      apply triple_elem_eq_list_refl;
      try assumption.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
      simpl. 
      rewrite refN, refN, refR.
      simpl. 
      apply keep_collecting_dropping_dual.
      destruct lb eqn:Hc.
      rewrite <-List.app_comm_cons.
      rewrite refN, refN, refR.
      simpl.
      exact IHl.
      rewrite <-List.app_comm_cons.
      rewrite refN, refN, refR.
      simpl.
      exact IHl.
  Qed.



  Lemma elem_path_triple_tail_rewrite : 
    forall l lr au, 
    triple_elem_list _ _ _ eqN eqN eqR l lr = true ->
    elem_path_triple_tail Node eqN R au l = false ->
    elem_path_triple_tail Node eqN R au lr = false.
  Proof using symN trnN.
    induction l as [|((au, av), aw) l].
    + intros [|((pur, pvr), pwr) lr] ? Ht He.
      simpl. reflexivity.
      simpl in Ht; congruence.
    + intros [|((pur, pvr), pwr) lr] ? Ht He.
      simpl in Ht; congruence.
      simpl in * |- *.
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrrr].
      apply Bool.orb_false_iff; split.
      case (au0 =n= pvr) eqn:Hau.
      apply symN in Htrrr.
      pose proof trnN _ _ _ Hau Htrrr as Hf.
      rewrite Hf in He. 
      simpl in He. congruence.
      reflexivity.
      case ((au0 =n= av)) eqn:Hau.
      simpl in He.
      congruence.
      simpl in He.
      eapply IHl.
      exact Htr.
      exact He.
  Qed.



  Lemma elem_path_triple_tail_false : forall l ll lr au, 
    elem_path_triple_tail Node eqN R au l = false ->
    triple_elem_list _ _ _ eqN eqN eqR l (ll ++ lr) = true ->
    elem_path_triple_tail Node eqN R au ll = false /\
    elem_path_triple_tail Node eqN R au lr = false.
  Proof using symN trnN.
    induction l as [|((au, av), aw) l].
    + intros ? ? ? He Ht.
      simpl in * |- *.
      destruct ll; destruct lr;
      simpl in * |- *; 
      split; try reflexivity;
      try congruence.
    + intros ? ? ? He Ht.
      destruct ll as [|((pu, pv), pw) ll].
      destruct lr as [|((pur, pvr), pwr) lr].
      simpl in Ht. congruence.
      rewrite List.app_nil_l in Ht.
      simpl.
      split. reflexivity.
      simpl in He, Ht.
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrrr].
      case (au0 =n= av) eqn:Ha.
      simpl in He.
      congruence.
      simpl in He.
      apply Bool.orb_false_iff.
      split.
      case (au0 =n= pvr) eqn:Hau.
      apply symN in Htrrr.
      pose proof trnN _ _ _ Hau Htrrr as Hf.
      rewrite Hf in Ha. congruence.
      reflexivity.
      eapply elem_path_triple_tail_rewrite.
      exact Htr.
      exact He.
      rewrite <-List.app_comm_cons in Ht.
      simpl in He, Ht.
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrrr].
      simpl.
      case (au0 =n= av) eqn:Ha.
      simpl in He. congruence.
      simpl in He.
      destruct (IHl _ _ _ He Htr) as [Hl Hr].
      split.
      apply Bool.orb_false_iff.
      split. 
      case (au0 =n= pv) eqn:Hau.
      apply symN in Htrrr.
      pose proof trnN _ _ _ Hau Htrrr as Hf.
      rewrite Hf in Ha. congruence.
      reflexivity.
      exact Hl.
      exact Hr.
  Qed.



  Lemma elem_path_triple_compute_loop_first_element_elementry : 
    forall l ll lm lr ,
    (ll, lm, lr) = elem_path_triple_compute_loop_triple Node eqN R l ->
    elem_path_triple Node eqN R ll = true.
  Proof using refN refR symN trnN.
    induction l as [|((au, av), aw) l].
    + intros ? ? ? Hl;
      simpl in Hl;
      inversion Hl; subst;
      reflexivity.
    + intros ? ? ? Hl.
      simpl in Hl.
      case (au =n= av) eqn:Ha.
      inversion Hl; subst;
      reflexivity.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
      inversion Hl; subst;
      reflexivity.
      remember (elem_path_triple_compute_loop_triple Node eqN R l) as elp.
      destruct elp as ((al, bl), cl).
      inversion Hl; subst; clear Hl.
      simpl.
      rewrite Ha; simpl.
      pose proof elem_path_triple_compute_loop_triple_combined_list l as Hep.
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as ((atl, btl), ctl).
      destruct btl.
      apply Bool.andb_true_iff; split.
      apply Bool.negb_true_iff.
      destruct (elem_path_triple_tail_false l atl (l0 ++ ctl) _ Hb Hep) as (Hept & _).
      inversion Heqelp.
      exact Hept.
      eapply IHl.
      reflexivity.
      apply Bool.andb_true_iff; split.
      apply Bool.negb_true_iff.
      destruct (elem_path_triple_tail_false l atl ctl _ Hb Hep) as (Hept & _).
      inversion Heqelp.
      exact Hept.
      eapply IHl.
      reflexivity.
  Qed.



  Lemma length_leq_lt : 
    ∀ (l : list (Node * Node * R)),
    l <> [] -> 
    ((List.length l) < 
      List.length 
        (collect_nodes_from_a_path Node R l))%nat.
  Proof using lenN.
    induction l as [|((au, av), aw) l].
    + simpl.
      intro H.
      congruence.
    + simpl. 
      intro H.
      destruct l as [|((bu, bv), bw) l].
      simpl.
      nia.
      remember ((bu, bv, bw) :: l) as bl.
      simpl.
      assert (Hne: bl <> []).
      intro Hf.
      congruence.
      specialize (IHl Hne);
      try nia.
  Qed.
 


  Lemma length_collect_node_gen :
    forall (c : list Node) 
    (l : list (Node * Node * R)),
    c <> [] ->  
    (List.length c <= List.length l)%nat ->
    (List.length c < 
    List.length (collect_nodes_from_a_path Node R l))%nat.
  Proof using lenN.
    intros ? ? Hne Hfin.
    pose proof length_leq_lt l as IHl.
    assert (Hlne: l <> []).
    destruct l. 
    intros Hf.
    destruct c.
    congruence.
    simpl in Hfin.
    nia.
    intro Hf.
    congruence.
    specialize (IHl Hlne).
    nia.
  Qed.


  Lemma elem_path_triple_tail_in_list : 
    forall (l : list (Node * Node * R)) m a,
    well_formed_path_aux Node eqN R eqR m l = true -> 
    elem_path_triple_tail Node eqN R a l = true ->
    in_list eqN (collect_nodes_from_a_path Node R l) a = true.
  Proof using trnN.
    induction l as [|((au, av), aw) l].
    + simpl.
      intros ? ? Hw Hf.
      congruence.
    + simpl.
      intros ? ? Hw Hf.
      destruct l as [|((bu, bv), bw) l].
      simpl in Hf.
      simpl.
      case (a =n= av) eqn:Haav.
      simpl.
      apply Bool.orb_true_iff.
      right.
      reflexivity.
      simpl in Hf.
      congruence.
      remember ((bu, bv, bw) :: l) as bl.
      simpl.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hw Hwr].
      case (a =n= av) eqn:Haav.
      simpl in Hf.
      case (a =n= au) eqn:Haau.
      simpl.
      reflexivity.
      simpl.
      rewrite Heqbl.
      simpl.
      destruct l as [|((cu, cv), cw) l].
      simpl.
      rewrite (trnN _ _ _ Haav Hw).
      reflexivity.
      simpl.
      simpl.
      rewrite (trnN _ _ _ Haav Hw).
      reflexivity.
      simpl in Hf.
      apply Bool.orb_true_iff.
      right.
      eapply IHl.
      exact Hwr.
      exact Hf.
  Qed.



  Lemma elem_path_collect_node_from_path_first :
    ∀ (l : list (Node * Node * R)) m, 
      well_formed_path_aux Node eqN R eqR m l = true -> 
      elem_path_triple Node eqN R l = false -> 
      no_dup Node eqN (collect_nodes_from_a_path Node R l) = false.
  Proof using trnN.
    induction l as [|((au, av), aw) l].
    + simpl.
      intros ? Ha Hb.
      congruence.
    + simpl.
      intros ? Ha Hb.
      destruct l as [|((bu, bv), bw) l].
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Ha _].
      simpl in Hb.
      simpl.
      case (au =n= av) eqn:Hauv.
      reflexivity.
      simpl in Hb.
      congruence.
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Ha Har].
      apply Bool.andb_true_iff in Har.
      destruct Har as [Hal Har].
      case (au =n= av) eqn:Hauv.
      remember ((bu, bv, bw) :: l) as bl.
      simpl.
      simpl in Hb.
      apply Bool.andb_false_iff.
      left.
      apply Bool.negb_false_iff.
      rewrite Heqbl.
      simpl.
      destruct l.
      simpl.
      rewrite (trnN _ _ _ Hauv Hal).
      reflexivity.
      simpl. 
      rewrite (trnN _ _ _ Hauv Hal).
      reflexivity.
      remember ((bu, bv, bw) :: l) as bl.
      simpl in Hb.
      simpl.
      case (elem_path_triple_tail Node eqN R au bl) eqn:Hep.
      simpl in Hb.
      apply Bool.andb_false_iff.
      left.
      apply Bool.negb_false_iff.
      eapply elem_path_triple_tail_in_list.
      exact Har.
      exact Hep.
      simpl in Hb.
      apply Bool.andb_false_iff.
      right.
      eapply IHl;
      try assumption.
      exact Har.
  Qed.


  Lemma elem_path_false_rewrite : 
    forall bl l bu bv bw m au, 
    bl = (bu, bv, bw) :: l ->
    au =n= bu = false ->
    well_formed_path_aux Node eqN R eqR m bl = true ->
    elem_path_triple_tail Node eqN R au bl = false ->
    in_list eqN (collect_nodes_from_a_path Node R bl) au = false.
  Proof using symN trnN.
    induction bl as [|((blbu, blbv), blbw) bl].
    + intros * Ha Hb Hw He.
      congruence.
    + intros * Ha Hb Hw He.
      inversion Ha; subst;
      clear Ha.
      (* check if l is empty or not? *)
      destruct l as [|((lcu, lcv), lcw) l].
      simpl in *.
      rewrite Hb.
      apply Bool.orb_false_iff in He.
      destruct He as [He _].
      rewrite He.
      reflexivity.
      (* inductive case *)
      remember ((lcu, lcv, lcw) :: l) as lbl.
      simpl in *.
      rewrite Heqlbl.
      rewrite Heqlbl in Hw.
      rewrite <-Heqlbl in Hw.
      rewrite <-Heqlbl.
      simpl.
      rewrite Hb.
      simpl.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hw Hwr].
      apply Bool.orb_false_iff in He.
      destruct He as [Hel Her].
      eapply IHbl.
      exact Heqlbl.
      case (au =n= lcu) eqn: Haul.
      apply symN in Hw.
      rewrite (trnN _ _ _ Haul Hw) in Hel.
      congruence.
      reflexivity.
      exact Hwr.
      exact Her.
  Qed.



  Lemma elem_path_collect_node_from_path_second :
    ∀ (l : list (Node * Node * R)) (m : Matrix Node R), 
      well_formed_path_aux Node eqN R eqR m l = true ->
      no_dup Node eqN (collect_nodes_from_a_path Node R l) = false -> 
      elem_path_triple Node eqN R l = false.
  Proof using symN trnN.
    induction l as [|((au, av), aw) l].
    + intros ? Ha Hb.
      simpl in Hb.
      congruence.
    + simpl.
      intros ? Ha Hb.
      destruct l as [|((bu, bv), bw) l].
      simpl in Hb.
      case (au =n= av) eqn:Hauv.
      simpl.
      reflexivity.
      simpl in Hb.
      congruence.
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Hal Ha].
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Har Ha].
      remember ((bu, bv, bw) :: l) as bl. 
      simpl in Hb.
      apply Bool.andb_false_iff in Hb.
      destruct Hb as [Hb | Hb].
      apply Bool.negb_false_iff in Hb.
      case (au =n= av) eqn:Hauv.
      reflexivity.
      simpl.
      case ((elem_path_triple_tail Node eqN R au bl)) eqn:Hep.
      reflexivity.
      simpl.

      assert (Ht: au =n= bu = false).
      case (au =n= bu) eqn:Ht.
      apply symN in Har.
      rewrite (trnN _ _ _ Ht Har) in Hauv.
      congruence.
      reflexivity.
      rewrite (elem_path_false_rewrite  bl l bu bv bw m au 
        Heqbl Ht Ha Hep) in Hb.
      congruence.
      apply Bool.andb_false_iff.
      right.
      eapply IHl.
      exact Ha.
      exact Hb.
  Qed.

  
  
  Lemma all_paths_in_klength_paths_cycle : 
    forall (c : list Node)
    (l : list (Node * Node * R)) m,
    well_formed_path_aux Node eqN R eqR m l = true ->
    covers _ eqN c (collect_nodes_from_a_path Node R l) -> 
    (List.length c < List.length (collect_nodes_from_a_path Node R l))%nat ->
    elem_path_triple Node eqN R l = false.
  Proof using refN symN trnN.
    intros * Hw Hc Hl.
    eapply elem_path_collect_node_from_path_second.
    exact Hw.
    destruct (covers_dup Node eqN refN symN trnN  
        _ _ Hc Hl) as 
    [a [l₁ [l₂ [l₃ Hll]]]].
    eapply list_eqv_no_dup_rewrite;
    try assumption.
    exact Hll.
    simpl.
    apply no_dup_false_one;
    try assumption.
  Qed.


  (* if you give me path of length >= finN then there is loop *)
  Lemma all_paths_in_klength_paths_cycle_finN : 
    forall (l : list (Node * Node * R)) m,
    (List.length finN <= List.length l)%nat ->
    well_formed_path_aux Node eqN R eqR m l = true ->
    exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop Node eqN R l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path Node eqN R au lc.
  Proof using dupN lenN memN refN refR symN trnN.
    intros ? ? Hfin Hw.
    assert(empN : finN <> []).
    destruct finN.
    simpl in lenN; try nia.
    intro H. congruence.
    pose proof length_collect_node_gen finN
      l empN Hfin as Hf.
    pose proof covers_list_elem Node eqN finN 
      (collect_nodes_from_a_path Node R l) memN as Hcov.
    pose proof all_paths_in_klength_paths_cycle
      finN l m Hw Hcov Hf as Hwt.
    eapply elim_path_triple_connect_compute_loop_false_first;
    try assumption.
  Qed.



  Lemma triple_compute_connect_with_triple_elem_forward : 
    forall l, 
    elem_path_triple Node eqN R l = false ->
    exists ll lm lr, (ll, Some lm, lr) = 
    elem_path_triple_compute_loop_triple Node eqN R l.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + simpl;
      intros Ha.
      congruence.
    + simpl.
      intros Ha.
      case (au =n= av) eqn:Hauv.
      eauto.
      simpl in Ha.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hel.
      eauto.
      simpl in Ha.
      destruct (IHl Ha) as 
      (ll & lm & lr & Hb).
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as 
      ((bu, bv), bw).
      exists ((au, av, aw) :: bu),
        lm, lr.
      f_equal.
      f_equal.
      inversion Hb; subst;
      reflexivity.
      inversion Hb; subst;
      reflexivity.
  Qed.



  Lemma triple_compute_connect_with_triple_elem_backward : 
    forall l ll lm lr, 
    (ll, Some lm, lr) = 
    elem_path_triple_compute_loop_triple Node eqN R l ->
    elem_path_triple Node eqN R l = false.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + simpl.
      intros * Ha.
      congruence.
    + simpl.
      intros * Ha.
      case (au =n= av) eqn:Hauv.
      reflexivity.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hel.
      reflexivity.
      simpl.
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as 
      ((bu, bv), bw).
      inversion Ha;
      subst; clear Ha.
      exact (IHl bu lm bw eq_refl).
  Qed.
      

  Lemma triple_compute_connect_with_triple_elem : 
    forall l, 
    elem_path_triple Node eqN R l = false <->
    exists ll lm lr, (ll, Some lm, lr) = 
    elem_path_triple_compute_loop_triple Node eqN R l.
  Proof using Type.
    intros ?; 
    split;
    intros He.
    eapply triple_compute_connect_with_triple_elem_forward;
    try assumption.
    destruct He as (ll & lm & lr & Hal).
    eapply triple_compute_connect_with_triple_elem_backward;
    try assumption.
    exact Hal.
  Qed.



  Lemma target_keep_collect_rewrite :
    forall lm ln a au av aw,  
    triple_elem_list _ _ _ eqN eqN eqR lm ln = true ->
    target Node eqN R a ((au, av, aw) :: ln) = true ->
    target Node eqN R a ((au, av, aw) :: lm) = true.
  Proof using symN trnN.
    induction lm as [|((au, av), aw) lm].
    + destruct ln as [|((bu, bv), bw) ln];
      simpl;
      intros ? ? ? ? Ha Hb;
      congruence.      
    + destruct ln as [|((bu, bv), bw) ln]. 
      intros ? ? ? ? Ha Hb.
      simpl in Ha.
      congruence.
      intros ? ? ? ? Ha Hb.
      simpl in Ha.
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Ha Har].
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Ha Harr].
      remember ((bu, bv, bw) :: ln) as cln.
      remember ((au, av, aw) :: lm) as alm.
      simpl in Hb.
      rewrite Heqcln in Hb.
      simpl.
      rewrite Heqalm.
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Halt Hart].
      eapply IHlm.
      exact Har.
      simpl in Hb.
      simpl.
      destruct ln. 
      eapply trnN.
      exact Hb.
      apply symN; 
      exact Hart.
      exact Hb.
  Qed.



  Lemma triple_compute_connect_with_triple_elem_stronger : 
    forall l, 
    elem_path_triple Node eqN R l = false ->
    exists ll au av aw lm lr, 
      (ll, Some ((au, av, aw) :: lm), lr) = 
      elem_path_triple_compute_loop_triple Node eqN R l /\ 
      cyclic_path Node eqN R au ((au, av, aw) :: lm) /\ 
      elem_path_triple Node eqN R ll = true /\ 
      triple_elem_list _ _ _ eqN eqN eqR 
        l (ll ++  ((au, av, aw) :: lm) ++ lr) = true.
  Proof using refN refR symN symR trnN.
    induction l as [|((au, av), aw) l].
    + simpl;
      intros Ha.
      congruence.
    + simpl.
      intros Ha.
      case (au =n= av) eqn:Hauv.
      exists [], au, av, aw, 
        [], l. 
      simpl.
      split.
      reflexivity.
      split.
      unfold cyclic_path; 
      simpl; split. 
      intro H; congruence.
      split. apply refN. 
      exact Hauv.
      split.
      reflexivity.
      repeat rewrite refN.
      rewrite refR.
      apply triple_elem_eq_list_refl;
      try assumption.
      simpl in Ha.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hel.
      simpl in Ha.
      exists [], au, av, aw,
      (keep_collecting Node eqN R au l),
      (keep_dropping Node eqN R au l).
      simpl.
      repeat split;
      try reflexivity.
      congruence.
      unfold source;
      apply refN.
      destruct (elem_path_triple_tail_true l au Hel) as 
      (ll & aut & awt & lrt & Hb & Hc & Hd).
      (* From Hd, 
        Hd: triple_elem_list (ll ++ [(aut, au, awt)]) (keep_collecting au l) = true,
        we can infer that target au (au, av, aw) :: keep_collecting au l) = true *)
      erewrite target_keep_collect_rewrite. 
      reflexivity.
      apply triple_elem_eq_list_sym;
      try assumption.
      exact Hd.
      eapply target_tail_forward.
      simpl.
      rewrite target_end.
      simpl. 
      apply refN.
      repeat rewrite refN.
      rewrite refR.
      rewrite keep_collecting_dropping_dual.
      reflexivity.
      (* Inductive case *)
      simpl in Ha.
      destruct (IHl Ha) as 
      (ll & aut & avt & awt & lmt & lrt & Hb & Hc & Hd & He).
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as 
      ((bu, bv), bw).
      exists ((au, av, aw) :: bu),
      aut, avt, awt, lmt, bw.
      split.
      f_equal.
      f_equal.
      inversion Hb;
      reflexivity.
      split.
      exact Hc.
      split.
      simpl.
      rewrite Hauv.
      simpl.
      (* This one is also tricky *)
      destruct(elem_path_triple_tail_false
        _ _ _ _ Hel He) as [Helt Hert].
      inversion Hb; subst.
      rewrite Helt, Hd.
      reflexivity.
      simpl.
      repeat (rewrite refN).
      rewrite refR.
      simpl.
      simpl in He.
      inversion Hb;
      subst.
      exact He.
  Qed.


  (* if you give me path of length >= finN then there is loop *)
  Lemma all_paths_in_klength_paths_cycle_finN_stronger : 
    forall (l : list (Node * Node * R)) m,
    (List.length finN <= List.length l)%nat ->
    well_formed_path_aux Node eqN R eqR m l = true ->
    exists ll au av aw lm lr, 
    (ll, Some ((au, av, aw) :: lm), lr) = 
    elem_path_triple_compute_loop_triple Node eqN R l /\ 
    cyclic_path Node eqN R au ((au, av, aw) :: lm) /\  (* Loop so we can remove this *)
    elem_path_triple Node eqN R ll = true /\ (* Elementry Path *)
    triple_elem_list _ _ _ eqN eqN eqR l (ll ++  ((au, av, aw) :: lm) ++ lr) = true. 
    (* lr is the rest of path *)
  Proof using dupN lenN memN refN refR symN symR trnN.
    intros ? ? Hfin Hw.
    assert(empN : finN <> []).
    destruct finN.
    simpl in lenN; try nia.
    intro H. congruence.
    pose proof length_collect_node_gen finN 
      l empN Hfin as Hf.
    pose proof covers_list_elem Node eqN finN 
      (collect_nodes_from_a_path Node R l) memN as Hcov.
    pose proof all_paths_in_klength_paths_cycle
      finN l m Hw Hcov Hf as Hwt.
    eapply triple_compute_connect_with_triple_elem_stronger.
    exact Hwt.
  Qed.



  Definition zwf (x y : list (Node * Node * R)) := 
      (List.length x < List.length y)%nat.

  Lemma zwf_well_founded : well_founded zwf.
  Proof.
    exact (Wf_nat.well_founded_ltof _ 
      (fun x => List.length x)).
  Defined.
  

    

  (* easy proof List.length finN <= List.length l -> loop *)
  Lemma elem_path_length : 
    forall (l : list (Node * Node * R)) m, 
    elem_path_triple Node eqN R l = true ->
    well_formed_path_aux Node eqN R eqR m l = true -> 
    (List.length l < List.length finN)%nat.
  Proof using dupN lenN memN refN symN trnN.
    intros l m He Hw.
    assert (Hwt : (length l < length finN)%nat \/ 
    (length finN <= length l)%nat).
    nia.
    destruct Hwt as [Hwt | Hwt].
    exact Hwt.
    assert(empN : finN <> []).
    destruct finN.
    simpl in lenN; try nia.
    intro H. congruence.
    pose proof length_collect_node_gen finN 
    l empN Hwt as Hf.
    pose proof covers_list_elem _ _ finN 
      (collect_nodes_from_a_path Node R l) memN as Hcov.
    pose proof all_paths_in_klength_paths_cycle
      finN l m Hw Hcov Hf as Hat.
    rewrite Hat in He.
    congruence.
  Qed.


  
  (* I can take any path l and turn it into elementry path 
      by keep applying *)
  Lemma reduce_path_into_elem_path : 
    forall (l : list (Node * Node * R)) m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m l = true ->
    exists lm, 
      well_formed_path_aux Node eqN R eqR m lm = true /\ 
      elem_path_triple Node eqN R lm = true.
  Proof using congrR lenN refN refR symN symR trnN.
    intros l.
    induction (zwf_well_founded l) as [l Hf IHl].
    unfold zwf in * |- *.
    intros ? Hm Hw.
    (* check if list is empty of not empty *)
    destruct l as [|((au, av), aw) l].
    + simpl.
      exists [].
      repeat split.
    + (*  *)
      destruct l as [|((bu, bv), bw) l].
      - simpl.
        case (au =n= av) eqn:Hauv.
        exists [].
        repeat split.
        simpl.
        exists [(au, av, aw)].
        simpl.
        repeat split.
        simpl in Hw.
        exact Hw.
        rewrite Hauv.
        reflexivity.
      - (* l is non-empty *)
        remember ((bu, bv, bw) :: l) as bl.
        simpl in Hw.
        rewrite Heqbl in Hw.
        rewrite <-Heqbl in Hw.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hw Hwr].
        case (au =n= av) eqn:Hauv.
        (* There is a loop of length 1 
        at the front. Discard it and call 
        the function/Induction hypothesis
        on the remaining list. *)
        assert (Hwt : (length bl < length ((au, av, aw) :: bl))%nat).
        simpl. nia.
        destruct (IHl bl Hwt m Hm Hwr) as 
        (lm & Hwe & He).
        exists lm.
        repeat split.
        exact Hwe.
        exact He.
        (* au <> av but au can appear inside bl *)
        case (elem_path_triple_tail Node eqN R au bl) eqn:Heab.
        destruct (elem_path_triple_tail_true bl _ Heab) as 
        (llt & aut & awt & lrt & Ha & Hb & Hc).
        (* discard (llt ++ [(aut, au, awt)]) and 
          call the recursive function on lrt *)
        assert (Hd : well_formed_path_aux Node eqN R eqR m lrt = true).
        pose proof well_formed_path_rewrite _ _ m Hm 
          Hwr Ha as Hwf.
        rewrite List.app_assoc in Hwf.
        destruct (well_formed_path_snoc _ _ _ 
          Hwf) as [Hwfl Hwfr].
        exact Hwfr.
        assert(Hwt : (length lrt < length ((au, av, aw) :: bl))%nat).
        simpl.
        eapply triple_elem_rewrite_le.
        exact Ha.
        destruct (IHl lrt Hwt m Hm Hd) as 
        (lm & Hwe & He).
        exists lm. 
        split.
        exact Hwe.
        exact He.
        (* no loop at the head so continue *)
        assert (Hwt : (length bl < length ((au, av, aw) :: bl))%nat).
        simpl. nia.
        destruct (IHl bl Hwt m Hm Hwr) as 
        (lm & Hwe & He).
        exists lm. 
        split.
        exact Hwe.
        exact He.
  Qed.



  (* Every well formed path can be reduced into 
      an well formed elementry path, i.e., path 
      without loop and it's length < finN *)
  Lemma reduce_path_into_elem_path_gen : 
    forall (l : list (Node * Node * R)) m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m l = true ->
    exists lm, 
      well_formed_path_aux Node eqN R eqR m lm = true /\ 
      elem_path_triple Node eqN R lm = true /\ 
      (List.length lm < List.length finN)%nat.
  Proof using congrR dupN lenN memN refN refR symN symR trnN.
    intros ? ? Hm Hw.
    destruct (reduce_path_into_elem_path l m Hm Hw) 
    as (lm & Hwa & Hwe).
    pose proof (elem_path_length lm m Hwe Hwa) as Hp.
    exists lm.
    repeat split; try assumption.
  Qed.


  Lemma well_founded_rev : 
    forall lm aut avt awt au av aw cut cvt cwt lr m,
    mat_cong Node eqN R eqR m ->
    well_formed_path_aux Node eqN R eqR m
      ([(aut, avt, awt)] ++ ((au, av, aw) :: lm) ++ (cut, cvt, cwt) :: lr) = true ->
    cyclic_path Node eqN R au ((au, av, aw) :: lm) ->
    avt =n= cut = true. 
  Proof using trnN.
    intros * Hm Hw Hc.
    unfold cyclic_path in Hc. 
    destruct Hc as (_ & Hcb & Hcc).
    assert (Hlt : lm = [] ∨ exists c d mcd lm',
      lm = lm' ++ [((c, d), mcd)]).
    destruct lm as [|((pa, pb), pc) lm]. 
    left; reflexivity.
    right.
    assert (Hne : (pa, pb, pc) :: lm  <> []).
    intro Hf; congruence.
    destruct (@exists_last _ ((pa, pb, pc) :: lm) Hne) 
    as (lm' & ((but, bvt), bwt) & Hc).
    exists but, bvt, bwt, lm'.
    exact Hc.
    destruct Hlt as [Hlt | Hlt].
    +
      rewrite Hlt in Hw, Hcb, Hcc.
      simpl in Hw. 
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwlll Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwllll Hw].
      apply trnN with au.
      exact Hwll.
      apply trnN with av;
      try assumption.
    +
      destruct Hlt as (c & d & mcd & lm' & Hlm).
      rewrite Hlm in Hw, Hcb, Hcc.
      assert (Htt : (au, av, aw) :: lm' ++ [(c, d, mcd)] = 
      ((au, av, aw) :: lm') ++ [(c, d, mcd)]).
      simpl; reflexivity.
      rewrite Htt in Hcc.
      rewrite target_end in Hcc.
      simpl in Hcc.
      clear Htt.
      assert (Htt : [(aut, avt, awt)] ++ ((au, av, aw) :: lm' ++ [(c, d, mcd)]) ++ (cut, cvt, cwt) :: lr =
      [(aut, avt, awt); (au, av, aw)] ++ (lm' ++ [(c, d, mcd)] ++ (cut, cvt, cwt) :: lr)).
      simpl. f_equal.
      f_equal.
      rewrite <-List.app_assoc.
      f_equal.
      rewrite Htt in Hw; 
      clear Htt. 
      destruct (well_formed_path_snoc [(aut, avt, awt); (au, av, aw)] _ 
        m Hw) as (Ha & Hb).
      simpl in Ha.
      destruct (well_formed_path_snoc lm' _
        m Hb) as (Hc & Hd).
      simpl in Hd.
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Hal Ha].
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Ha _].
      apply Bool.andb_true_iff in Hd.
      destruct Hd as [Hdl Hd].
      apply Bool.andb_true_iff in Hd.
      destruct Hd as [Hd _].
      apply trnN with au.
      exact Ha.
      apply trnN with d;
      try assumption.
  Qed.
      

    








  
  Lemma well_formed_loop_removal : 
    forall ll lr lm au av aw m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m 
      (ll ++ ((au, av, aw) :: lm) ++ lr) = true ->
    cyclic_path Node eqN R au ((au, av, aw) :: lm) ->
    well_formed_path_aux Node eqN R eqR m ((ll ++ lr)) = true.
  Proof using trnN.
    induction ll as [|((aut, avt), awt) ll].
    + intros * Hm Hw Hc.
      rewrite List.app_nil_l in Hw.
      rewrite List.app_nil_l.
      destruct (well_formed_path_snoc _ _ m Hw) as [_ Hwt].
      exact Hwt.
    + intros * Hm Hw Hc.
      simpl.
      destruct ll as [|((but, bvt), bwt) ll].
      simpl.
      destruct lr as [|((cut, cvt), cwt) lr].
      destruct (well_formed_path_snoc _ _ _ Hw) as [Ha Hb].
      simpl in Ha.
      exact Ha.
      apply Bool.andb_true_iff.
      split.
      simpl in Hw.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hw _].
      exact Hw.
      apply Bool.andb_true_iff.
      split.
      eapply well_founded_rev; 
      try assumption.
      exact Hm.
      exact Hw.
      exact Hc.

      apply well_formed_path_snoc in Hw.
      destruct Hw as [_ Hw].
      apply well_formed_path_snoc in Hw.
      destruct Hw as [_ Hw].
      exact Hw.
      assert(Hlt : ((but, bvt, bwt) :: ll) ++ lr = 
        (but, bvt, bwt) :: ll ++ lr).
      simpl; reflexivity.
      rewrite Hlt.
      assert (Hbt : (((aut, avt, awt) :: (but, bvt, bwt) :: ll) ++ ((au, av, aw) :: lm) ++ lr) = 
        (aut, avt, awt) :: ((but, bvt, bwt) :: ll ++ ((au, av, aw) :: lm) ++ lr)).
      simpl; reflexivity.
      rewrite Hbt in Hw.
      clear Hbt.
      remember ((but, bvt, bwt) :: ll ++ ((au, av, aw) :: lm) ++ lr) as bl.
      simpl in Hw.
      rewrite Heqbl in Hw.
      rewrite <-Heqbl in Hw.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      apply Bool.andb_true_iff.
      split.
      exact Hwl.
      apply Bool.andb_true_iff.
      split.
      exact Hwll.
      rewrite Heqbl in Hw.
      exact (IHll _ _ _ _ _ _ Hm Hw Hc).
  Qed.
      
      

  Lemma triple_well_formed_rewrite_gen :
    forall l lw m d,
    mat_cong Node eqN R eqR m ->
    well_formed_path_aux Node eqN R eqR m 
      (l ++ [(d, d, 1)]) = true ->
    triple_elem_list Node Node R eqN eqN eqR
      l lw = true ->
    well_formed_path_aux  Node eqN R eqR m 
      (lw ++ [(d, d, 1)]) = true.
  Proof using congrR lenN symN symR trnN.
    induction l as [|((au, av), aw) l].
      + intros [|((bu, bv), bw) lw] ? ? Hm Hw Ht.
        exact Hw.
        simpl in Ht. 
        lia.
      + intros ? ? ? Hm Hw Ht.
        destruct lw as [|((bu, bv), bw) lw].
        simpl in Ht. congruence.
        simpl in Ht.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrrr].
        (* Now, I need to know if l is well formed or not *)
        destruct l as [|((cu, cv), cw) l].
        destruct lw as [|((du, dv), dw) lw].
        simpl. simpl in Hw.
        apply Bool.andb_true_iff.
        split. 
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hw _].
        rewrite <-Hw.
        apply congrR.
        apply Hm.
        apply symN; assumption.
        apply symN; assumption.
        apply symR; assumption.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [_ Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hwr].
        apply Bool.andb_true_iff in Hwr.
        destruct Hwr as [Hwr _].
        rewrite Hwr.
        simpl.
        rewrite Bool.andb_true_r.
        apply symN in Htrrr.
        apply trnN with av;
        try assumption.
        simpl in Htr.
        congruence.
        assert (Hwt: (well_formed_path_aux _ eqN _ eqR m 
          (((au, av, aw) :: (cu, cv, cw) :: l) ++ [(d, d, 1)]) = 
          (m au av =r= aw) && ((av =n= cu) && 
          well_formed_path_aux _ eqN _ eqR m ((cu, cv, cw) :: l ++ [(d, d, 1)])))%bool).
        simpl. reflexivity.
        rewrite Hwt in Hw; clear Hwt.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        specialize (IHl lw m d Hm Hw Htr).
        simpl. apply Bool.andb_true_iff.
        split. 
        rewrite <-Hwl.
        apply congrR.
        apply Hm.
        apply symN; assumption.
        apply symN; assumption.
        apply symR; assumption.
        destruct lw.
        simpl in Htr;
        congruence. 
        destruct p as ((pu, pv), pw).
        simpl in Htr.
        apply Bool.andb_true_iff.
        split.
        apply Bool.andb_true_iff in Htr.
        destruct Htr as [Htr Htrv].
        apply Bool.andb_true_iff in Htr.
        destruct Htr as [Htr Htrw].
        apply Bool.andb_true_iff in Htr.
        destruct Htr as [Htr Htwx].
        apply trnN with cu.
        apply symN in Htrrr.
        apply trnN with av; assumption.
        exact Htr.
        exact IHl.
  Qed.


  Lemma triple_well_formed_rewrite :
    forall l ll lm lr m d au av aw,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m 
      (l ++ [(d, d, 1)]) = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      l (ll ++ ((au, av, aw) :: lm) ++ lr) = true ->
    well_formed_path_aux Node eqN R eqR m
      (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) = true.
  Proof using congrR lenN symN symR trnN.
    intros * Hm Hw Ht.
    simpl.
    assert (Htt : ll ++ (au, av, aw) :: lm ++ lr ++ [(d, d, 1)] = 
      (ll ++ (au, av, aw) :: lm ++ lr) ++ [(d, d, 1)]).
    rewrite <-List.app_assoc; simpl.
    f_equal.
    f_equal.
    rewrite <-List.app_assoc;
    reflexivity.
    rewrite Htt; clear Htt.
    eapply triple_well_formed_rewrite_gen;
    try assumption.
    exact Hw.
    exact Ht.
  Qed.



  Lemma source_loop_removal : 
    forall ll lr lm au av aw c d m,
    mat_cong Node eqN R eqR m ->
    well_formed_path_aux Node eqN R eqR m
      (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) = true -> 
    source Node eqN R c
      (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) = true ->
    cyclic_path Node eqN R au ((au, av, aw) :: lm) ->
    source Node eqN R c ((ll ++ lr) ++ [(d, d, 1)]) = true.
  Proof using trnN.
    intros * Hw Hm Hs Hc.
    assert (Hlt : lm = [] ∨ exists c d mcd lm',
      lm = lm' ++ [((c, d), mcd)]).
    destruct lm as [|((pa, pb), pc) lm]. 
    left; reflexivity.
    right.
    assert (Hne : (pa, pb, pc) :: lm  <> []).
    intro Hf; congruence.
    destruct (@exists_last _ ((pa, pb, pc) :: lm) Hne) 
    as (lm' & ((but, bvt), bwt) & Hd).
    exists but, bvt, bwt, lm'.
    exact Hd.

    destruct ll as [|((bu, bv), bw) ll];
    destruct lr as [|((cu, cv), cw) lr].
    destruct Hlt as [Hlt | Hlt].
    rewrite Hlt in Hc, Hs, Hm.
    simpl in * |- *.
    unfold cyclic_path in Hc.
    simpl in Hc.
    destruct Hc as (_ & _ & Hc).
    apply trnN with au;
    try assumption.
    apply trnN with av; 
    try assumption.
    apply Bool.andb_true_iff in Hm.
    destruct Hm as [_ Hm].
    apply Bool.andb_true_iff in Hm.
    destruct Hm as [Hm _].
    exact Hm.
    destruct Hlt as (cx & dx & mcd & lm' & Hlm).
    simpl.
    rewrite Hlm in Hm, Hc.
    simpl in Hs.
    rewrite List.app_nil_l in Hm.
    unfold cyclic_path in Hc.
    assert (Htt : ((au, av, aw) :: lm' ++ [(cx, dx, mcd)]) ++ [] ++ [(d, d, 1)] =
    ((au, av, aw) :: lm') ++ [(cx, dx, mcd)] ++ [(d, d, 1)]).
    simpl.
    f_equal.
    rewrite <-List.app_assoc.
    reflexivity.
    rewrite Htt in Hm;
    clear Htt.
    pose proof well_formed_path_snoc _ _ _ 
      Hm as (Ha & Hb).
    simpl in Hb.
    destruct Hc as (_ & _ & Hc).
    assert (Htt : (au, av, aw) :: lm' ++ [(cx, dx, mcd)] = 
    ((au, av, aw) :: lm') ++ [(cx, dx, mcd)]).
    simpl; reflexivity.
    rewrite Htt in Hc;
    clear Htt.
    rewrite target_end in Hc.
    simpl in Hc.
    apply trnN with au;
    try assumption.
    apply trnN with dx;
    try assumption.
    apply Bool.andb_true_iff in Hb.
    destruct Hb as [_ Hb].
    apply Bool.andb_true_iff in Hb.
    destruct Hb as [Hb _].
    exact Hb.
    destruct Hlt as [Hlt | Hlt].
    rewrite Hlt in Hm, Hs, Hc.
    simpl.
    simpl in Hs.
    rewrite List.app_nil_l in Hm.
    simpl in Hm.
    unfold cyclic_path in Hc.
    destruct Hc as (_ & _ & Hc).
    simpl in Hc.
    apply Bool.andb_true_iff in Hm.
    destruct Hm as [_ Hm].
    apply Bool.andb_true_iff in Hm.
    destruct Hm as [Hm _].
    apply trnN with au;
    try assumption.
    apply trnN with av;
    try assumption.
    destruct Hlt as (cx & dx & mcd & lm' & Hlm).
    simpl.
    rewrite Hlm in Hm, Hc.
    simpl in Hs.
    rewrite List.app_nil_l in Hm.
    assert (Htt : ((au, av, aw) :: lm' ++ [(cx, dx, mcd)]) ++ ((cu, cv, cw) :: lr) ++ [(d, d, 1)] = 
    ((au, av, aw) :: lm') ++ [(cx, dx, mcd)] ++ ((cu, cv, cw) :: lr) ++ [(d, d, 1)]).
    simpl.
    f_equal.
    rewrite <-List.app_assoc.
    simpl; reflexivity.
    rewrite Htt in Hm;
    clear Htt.
    pose proof well_formed_path_snoc _ _ _ 
      Hm as (Ha & Hb).
    simpl in Hb.
    unfold cyclic_path in Hc.
    destruct Hc as (_ & _ & Hc).
    assert (Htt : (au, av, aw) :: lm' ++ [(cx, dx, mcd)] = 
    ((au, av, aw) :: lm') ++ [(cx, dx, mcd)]).
    simpl; reflexivity.
    rewrite Htt in Hc;
    clear Htt.
    rewrite target_end in Hc.
    simpl in Hc.
    apply trnN with au;
    try assumption.
    apply trnN with dx;
    try assumption.
    apply Bool.andb_true_iff in Hb.
    destruct Hb as [_ Hb].
    apply Bool.andb_true_iff in Hb.
    destruct Hb as [Hb _].
    exact Hb.
    simpl.
    simpl in Hs.
    exact Hs.
    simpl.
    simpl in Hs.
    exact Hs.
  Qed.


  Lemma triple_source_rewrite_gen :
    forall l₁ l₂ c d,  
    source Node eqN R c 
      (l₁ ++ [(d, d, 1)]) = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      l₁ l₂ = true ->
    source Node eqN R c (l₂ ++ [(d, d, 1)]) = true.
  Proof using trnN.
    destruct l₁ as [|((au, av), aw) l₁];
    destruct l₂ as [|((bu, bv), bw) l₂];
    intros ? ? Hs Ht;
    simpl in * |- *;
    try assumption;
    try congruence.
    apply trnN with au;
    try assumption.
    case (au =n= bu) eqn:Haubu.
    reflexivity.
    simpl in Ht;
    congruence.
  Qed.
  


  Lemma triple_source_rewrite :
    forall l ll lm lr c d au av aw, 
    source Node eqN R c 
      (l ++ [(d, d, 1)]) = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      l (ll ++ ((au, av, aw) :: lm) ++ lr) = true ->
    source Node eqN R c
      (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) = true.
  Proof using trnN.
    intros * Hs Ht.
    simpl.
    assert (Htt : ll ++ (au, av, aw) :: lm ++ lr ++ [(d, d, 1)] = 
      (ll ++ (au, av, aw) :: lm ++ lr) ++ [(d, d, 1)]).
    rewrite <-List.app_assoc; simpl.
    f_equal.
    f_equal.
    rewrite <-List.app_assoc;
    reflexivity.
    rewrite Htt; clear Htt.
    eapply triple_source_rewrite_gen.
    exact Hs.
    exact Ht.
  Qed.
  

  Lemma cycle_path_dup_remove : 
    forall ll lm lr,
    Orel R plusR eqR
      (measure_of_path Node R oneR mulR (ll ++ lr))
      (measure_of_path Node R oneR mulR (ll ++ lm ++ lr)). 
  Proof using congrM congrP congrR left_distributive_mul_over_plus
    mul_associative one_left_identity_mul refN refR
    right_distributive_mul_over_plus symR zero_stable.
    intros *.
    unfold Orel.
    assert (Ht : (measure_of_path Node R oneR mulR (ll ++ lr) + 
      measure_of_path Node R oneR mulR (ll ++ lm ++ lr) =r=
      measure_of_path Node R oneR mulR (ll ++ lr)) = 
      ((measure_of_path Node R oneR mulR ll * measure_of_path Node R oneR mulR lr) + 
        (measure_of_path Node R oneR mulR ll * 
        (measure_of_path Node R oneR mulR lm * measure_of_path Node R oneR mulR lr)) =r= 
        (measure_of_path Node R oneR mulR ll * measure_of_path Node R oneR mulR lr))).
    apply congrR.
    apply congrP.
    apply path_split_measure;
    apply triple_elem_eq_list_refl;
    try assumption.
    rewrite <- (path_split_measure (ll ++ lm ++ lr)
      ll (lm ++ lr) (triple_elem_eq_list_refl _ _ _ eqN eqN eqR refN refN refR (ll ++ lm ++ lr))). 
    apply congrR.
    apply refR.
    apply congrM.
    apply refR.
    apply symR.
    apply path_split_measure;
    apply triple_elem_eq_list_refl;
    try assumption.
    apply path_split_measure;
    apply triple_elem_eq_list_refl;
    try assumption.
    rewrite Ht; clear Ht.
    remember (measure_of_path Node R oneR mulR ll) as a.
    remember (measure_of_path Node R oneR mulR lm) as b.
    remember (measure_of_path Node R oneR mulR lr) as c.
    assert (Ht : (a * c + a * (b * c) =r= a * c) = 
      (a * c + a * b * c =r= a * c)).
    apply congrR.
    apply congrP.
    apply refR.
    apply mul_associative.
    apply refR.
    rewrite Ht; clear Ht.
    eapply path_weight_rel;
      try assumption.
    eassumption.
    eassumption.
  Qed.
  

  Lemma orel_rewrite :
    forall l lm lr,  
    triple_elem_list Node Node R eqN eqN eqR
      l lm = true ->
    Orel R plusR eqR (measure_of_path Node R 1 mulR lr)
      (measure_of_path Node R 1 mulR lm) ->
    Orel R plusR eqR (measure_of_path Node R 1 mulR lr)
      (measure_of_path Node R 1 mulR l).
  Proof using congrM congrP congrR mul_associative
    one_left_identity_mul refR symR.
    induction l as [|((au, av), aw) l];
    destruct lm as [|((bu, bv), bw) lm];
    intros * Ht Horel;
    simpl in Ht; try congruence.
    simpl.
    simpl in Horel.
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htr].
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htrr].
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htrrr].
    unfold Orel in * |- *.
    rewrite <-Horel.
    apply congrR.
    apply congrP.
    apply refR.
    apply congrM.
    exact Htrr.
    pose proof path_split_measure l [] lm as Hlm.
    simpl in Hlm.
    specialize (Hlm Htr).
    rewrite <-Hlm.
    apply congrR.
    apply refR.
    apply symR.
    apply one_left_identity_mul.
    apply refR.
  Qed.


  Lemma reduce_path_into_simpl_path :
    forall (l : list (Node * Node * R)) m c d,
    (length finN <= length l)%nat ->
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m (l ++ [(d, d, 1)]) = true ->
    source _ eqN _ c (l ++ [(d, d, 1)]) = true -> 
    target _ eqN _ d (l ++ [(d, d, 1)]) = true ->
    exists ys, 
      (List.length ys < List.length finN)%nat ∧
      well_formed_path_aux Node eqN R eqR m (ys ++ [(d, d, 1)]) = true ∧
      source _ eqN _ c (ys ++ [(d, d, 1)]) = true ∧
      target _ eqN _ d (ys ++ [(d, d, 1)]) = true ∧
      Orel R plusR eqR 
        (measure_of_path Node R oneR mulR ys)
        (measure_of_path Node R oneR mulR l).
  Proof using congrM congrP congrR dupN left_distributive_mul_over_plus
    lenN memN mul_associative one_left_identity_mul plus_associative refN
    refR right_distributive_mul_over_plus symN symR trnN zero_stable.
    intros l.
    induction (zwf_well_founded l) as [l Hf IHl].
    unfold zwf in * |- *.
    intros ? ? ? Hfl Hm Hw Hs Ht.
    destruct (well_formed_path_snoc l ([(d, d, 1)]) m Hw) as 
    (Ha & Hb).
    destruct (all_paths_in_klength_paths_cycle_finN_stronger l 
      m Hfl Ha) as (ll & au & av & aw & lm & lr & He 
      & Hc & Hep & Hte).
    assert (Hlt : (length (ll ++ lr) < length l)%nat).
    pose proof (length_rewrite _ _ _ eqN eqN eqR _ _ Hte) as Hlf.
    rewrite Hlf. 
    simpl.
    rewrite app_length.
    rewrite app_length.
    simpl.
    rewrite app_length.
    nia.
    assert (Hdisj : (length (ll ++ lr) < length finN)%nat ∨ 
      (length finN <= length (ll ++ lr))%nat).
    nia.
    destruct Hdisj as [Hdisj | Hdisj].
    exists (ll ++ lr).
    repeat split.
    exact Hdisj.
    pose proof triple_well_formed_rewrite _ _ _ _ _ _ _ _ _ Hm Hw Hte as Hvt.
    pose proof well_formed_loop_removal _ _ _ _ _ _ _ Hm Hvt Hc as Han.
    rewrite <-List.app_assoc.
    exact Han.
    pose proof triple_source_rewrite _ _ _ _ _ _ _ _ _ Hs Hte as Hvta.
    pose proof triple_well_formed_rewrite _ _ _ _ _ _ _ _ _ Hm Hw Hte as Hvtb.
    pose proof source_loop_removal _ _ _ _ _ _ _ _ _ Hm Hvtb Hvta Hc as Han.
    exact Han.
    rewrite target_end.
    simpl; apply refN.
    eapply orel_rewrite.
    try assumption.
    exact Hte.
    eapply cycle_path_dup_remove.

    (* Now we are in Inductive case *)
    specialize (IHl (ll ++ lr) Hlt m c d Hdisj Hm).
    (* By same reasoning that I did in non inductive case *)
    assert (Hwt : well_formed_path_aux Node eqN R eqR m ((ll ++ lr) ++ [(d, d, 1)]) = true).
    pose proof triple_well_formed_rewrite _ _ _ _ _ _ _ _ _ Hm Hw Hte as Hvt.
    pose proof well_formed_loop_removal _ _ _ _ _ _ _ Hm Hvt Hc as Han.
    rewrite <-List.app_assoc.
    exact Han.
    assert (Hst : source Node eqN R c ((ll ++ lr) ++ [(d, d, 1)]) = true).
    pose proof triple_source_rewrite _ _ _ _ _ _ _ _ _ Hs Hte as Hvta.
    pose proof triple_well_formed_rewrite _ _ _ _ _ _ _ _ _ Hm Hw Hte as Hvtb.
    pose proof source_loop_removal _ _ _ _ _ _ _ _ _ Hm Hvtb Hvta Hc as Han.
    exact Han.
    assert (Htt: target Node eqN R d ((ll ++ lr) ++ [(d, d, 1)]) = true).
    rewrite target_end;
    simpl; apply refN.
    destruct (IHl Hwt Hst Htt) as 
    (ys & Hlfin & Hwf & Hsn & Htn & Horel).
    exists ys.
    repeat split.
    exact Hlfin.
    exact Hwf.
    exact Hsn.
    exact Htn.
    eapply orel_rewrite.
    exact Hte.
    pose proof cycle_path_dup_remove 
      ll ((au, av, aw) :: lm) lr as Hcp.
    eapply orel_trans;
    try assumption.
    exact Horel.
    exact Hcp.
  Qed.


  
  Lemma source_rewrite_gen : 
    ∀ (l₁ l₂ : list (Node * Node * R)) (c : Node),
    source Node eqN R c l₁ = true ->
    triple_elem_list Node Node R eqN eqN eqR l₁ l₂ = true ->
    source Node eqN R c l₂ = true.
  Proof using trnN.
    destruct l₁ as [|((au, av), aw) l₁];
    destruct l₂ as [|((bu, bv), bw) l₂];
    intros ? Hs Ht;
    simpl in * |- *;
    try assumption;
    try congruence.
    apply trnN with au;
    try assumption.
    case (au =n= bu) eqn:Haubu.
    reflexivity.
    simpl in Ht;
    congruence.
  Qed.
  


  Lemma target_rewrite_gen : 
    ∀ (l₁ l₂ : list (Node * Node * R)) (c : Node),
    target Node eqN R c l₁ = true ->
    triple_elem_list Node Node R eqN eqN eqR l₁ l₂ = true ->
    target Node eqN R c l₂ = true.
  Proof using trnN.
    induction l₁ as [|((au, av), aw) l₁];
    destruct l₂ as [|((bu, bv), bw) l₂];
    intros ? Htn Hte;
    simpl in Hte;
    try congruence.
    apply Bool.andb_true_iff in Hte.
    destruct Hte as [Hte Hter].
    apply Bool.andb_true_iff in Hte.
    destruct Hte as [Hte Hterr].
    destruct l₁ as [|((cu, cv), cw) l₁];
    destruct l₂ as [|((du, dv), dw) l₂].
    simpl.
    simpl in Htn.
    apply trnN with av;
    try assumption.
    apply Bool.andb_true_iff in Hte.
    destruct Hte as [_ Hte];
    exact Hte.
    simpl in Hter;
    congruence.
    simpl in Hter;
    congruence.
    remember ((cu, cv, cw) :: l₁) as cl.
    remember ((du, dv, dw) :: l₂) as dl.
    simpl.
    rewrite Heqdl.
    rewrite <-Heqdl.
    simpl in Htn.
    rewrite Heqcl in Htn.
    rewrite <-Heqcl in Htn.
    eapply IHl₁.
    exact Htn.
    exact Hter.
  Qed.
  
  
  Lemma reduce_path_gen_lemma : 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    (length finN <= n)%nat ->
    (forall c d, (c =n= d) = true -> (m c d =r= 1) = true) -> 
    mat_cong Node eqN R eqR m ->  
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ oneR 
        finN m n c d) = true ->
    exists ys, 
      (length ys < length finN)%nat ∧
      In_eq_bool Node Node R eqN eqN eqR (ys ++ [(d, d, 1)])
        (all_paths_klength Node eqN R 1 finN m (length ys) c d) = true ∧
      Orel R plusR eqR 
        (measure_of_path Node R oneR mulR ys)
        (measure_of_path Node R oneR mulR xs).
  Proof using congrM congrP congrR dupN left_distributive_mul_over_plus lenN
    memN mul_associative one_left_identity_mul one_right_identity_mul
    plus_associative refN refR right_distributive_mul_over_plus symN symR
    trnN trnR zero_stable.
    intros * Hfin Hcd Hm Hin.
    destruct (source_target_non_empty_kpath_and_well_formed 
      n m c d xs Hcd Hm Hin) as 
    (Hxs & Hsn & Htn & Hw & Hl & xs' & Hxs').
    pose proof reduce_path_into_simpl_path xs' m c d as Hpath.
    pose proof length_rewrite _ _ _ eqN eqN eqR _ _ Hxs' as Hlen.
    rewrite app_length in Hlen.
    simpl in Hlen.
    assert (Hxsp : length xs' = n).
    nia.
    assert (Hfn : (length finN <= length xs')%nat).
    nia.
    clear Hlen; clear Hxsp.
    destruct (Hpath Hfn Hm (well_formed_path_rewrite _ _ _ Hm Hw Hxs')
      (source_rewrite_gen _ _ _ Hsn Hxs')
      (target_rewrite_gen _ _ _ Htn Hxs')) as 
    (ys & Hly & Hwfy & Hsy & Hty & Horel).
    pose proof source_target_non_empty_kpath_and_well_formed_rev ys m 
      c d Hm Hsy Hty Hwfy.
    exists ys.
    repeat split;
    try assumption.
    eapply orel_rewrite.
    exact Hxs'.
    unfold Orel.
    assert(Htt: 
      (measure_of_path Node R 1 mulR ys + measure_of_path Node R 1 mulR (xs' ++ [(d, d, 1)]) =r=
      measure_of_path Node R 1 mulR ys) = 
      (measure_of_path Node R 1 mulR ys + 
      (measure_of_path Node R 1 mulR xs' * measure_of_path Node R 1 mulR [(d, d, 1)]) =r=
      measure_of_path Node R 1 mulR ys)).
    apply congrR.
    apply congrP.
    apply refR.
    eapply path_split_measure.
    apply triple_elem_eq_list_refl;
    try assumption.
    apply refR.
    rewrite Htt; clear Htt.
    simpl.
    unfold Orel in Horel.
    rewrite <-Horel.
    apply congrR.
    apply congrP.
    apply refR.
    remember (measure_of_path Node R 1 mulR xs') as axs.
    assert (Htt: (axs * (1 * 1) =r= axs) = 
    (axs * (1 * 1) =r= axs * 1)).
    apply congrR.
    apply refR.
    apply symR.
    apply one_right_identity_mul.
    rewrite Htt; clear Htt.
    apply congrM.
    apply refR.
    apply one_right_identity_mul.
    apply refR.
  Qed.


  Lemma fold_right_dist_eqr_aide :
    forall a b c d e : R, b =r= d + e = true ->
    a + b =r= a + d + e = true.
  Proof using congrP congrR plus_associative refR symR.
    intros ? ? ? ? ? H.
    assert (Ht : a + d + e =r= a + (d + e) = true).
    apply symR. 
    apply plus_associative.
    apply symR. 
    rewrite <-Ht; clear Ht.
    apply congrR. 
    apply refR.
    apply congrP. 
    apply refR.
    exact H.
  Qed.

  
  Lemma fold_right_dist_eqr : forall l₁ l₂ : list R, 
    (fold_right (fun u v : R => u + v) 0 (l₁ ++ l₂))
    =r= 
    (fold_right (fun u₁ v₁ : R => u₁ + v₁) 0 l₁ + 
    fold_right (fun u₂ v₂ : R => u₂ + v₂) 0 l₂) = true.
  Proof using congrP congrR plus_associative refR symR zero_left_identity_plus.
    induction l₁.
    - simpl; intros ?.
      apply symR.
      apply zero_left_identity_plus.
    - simpl; intros ?.
      apply fold_right_dist_eqr_aide. 
      exact a.
      apply IHl₁.
  Qed.


  (* x * l1 + x * l2 + x * l3 = x * (l1 + l2 + l3) *)
  Lemma fold_map_rel : forall l m n c d,
    mat_cong _ eqN _ eqR m ->  
    fold_right (λ u v : R, u + v) 0
      (map (measure_of_path Node R 1 mulR)
        (append_node_in_paths Node R m c
          (flat_map (λ x : Node, all_paths_klength _ eqN _ oneR finN m n x d) l))) 
    =r= 
    fold_right (fun x t => m c x * 
      (fold_right (fun b v => b + v) 0 
        (map (measure_of_path Node R 1 mulR) (all_paths_klength _ eqN _ oneR finN m n x d))) + t) 0 l 
    = true.
  Proof using congrM congrP congrR left_distributive_mul_over_plus plus_associative
    refN refR symN symR trnN trnR zero_left_identity_plus zero_right_anhilator_mul.
    induction l as [|a l IHL].
    - simpl; intros ? ? ? ? Hm.
      apply refR.
    - simpl; intros ? ? ? ? Hm.
      pose proof append_node_app (all_paths_klength _ eqN _ oneR finN m n a d)
        (flat_map (λ x : Node, all_paths_klength _ eqN _ oneR finN m n x d) l)
        m c as Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      rewrite map_app.
      pose proof fold_right_dist_eqr 
      (map (measure_of_path Node R 1 mulR)
        (append_node_in_paths Node R m c (all_paths_klength _ eqN _ oneR finN m n a d)))
      (map (measure_of_path Node R 1 mulR)
      (append_node_in_paths Node R m c
        (flat_map (λ x : Node, all_paths_klength _ eqN _ oneR finN m n x d) l))) as Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      apply congrP. 
      apply fold_right_measure.
      exact Hm.
      apply IHL.
      exact Hm.
  Qed.


  Lemma fold_right_cong : 
    forall l (g f: Node -> R -> R) a,
    (forall x u v, u =r= v = true -> f x u =r= g x v = true) -> 
    fold_right f a l =r= fold_right g a l = true.
  Proof using refR.
    induction l.
    - simpl; intros ? ? ? Hx.
      apply refR.
    - simpl; intros ? ? ? Hx.
      pose proof (IHl g f a0 Hx) as Hw.
      apply Hx. exact Hw.
  Qed.
  
  


  Lemma fold_right_rewrite : 
    forall l₁ l₂ x, 
    list_eqv _ eqR l₁ l₂ = true ->
    (fold_right (λ b a : R, b + a) 0 l₂ =r= 
    x + fold_right (λ b a : R, b + a) 0 l₂) = true ->
    (fold_right (λ b a : R, b + a) 0 l₁ =r= 
    x + fold_right (λ b a : R, b + a) 0 l₁) = true.
  Proof using congrP congrR refR.
    intros * Hl Hf.
    rewrite <-Hf.
    apply congrR.
    exact (fold_right_congr _ _ Hl).
    apply congrP.
    apply refR.
    exact (fold_right_congr _ _ Hl).
  Qed.

  


  Lemma fold_right_replace : 
    forall l a,
    fold_right (λ x y : R, x + y) a l =r= 
    a + fold_right (λ x y : R, x + y) 0 l = true.
  Proof using congrP congrR plus_associative plus_commutative refR
    symR zero_right_identity_plus.
    induction l.
    + intros *.
      simpl.
      apply symR.
      apply zero_right_identity_plus.
    + intros *.
      simpl. 
      specialize (IHl a0).
      remember (fold_right (λ x y : R, x + y) a0 l) as al0.
      remember (fold_right (λ x y : R, x + y) 0 l) as al. 
      assert (Htt : 
      (a + al0 =r= a0 + (a + al)) =
      (a + al0 =r= (a + al) + a0)).
      apply congrR.
      apply refR.
      apply plus_commutative.
      rewrite Htt; clear Htt.
      assert (Htt : 
      (a + al0 =r= a + al + a0) = 
      (a + al0 =r= a + (al + a0))).
      apply congrR.
      apply refR.
      apply symR.
      apply plus_associative.
      rewrite Htt; clear Htt.
      apply congrP.
      apply refR.
      rewrite <-IHl.
      apply congrR.
      apply refR.
      apply plus_commutative.
  Qed.
    

  
  Lemma sum_all_flat_paths_app : 
    forall l₁ l₂,
    sum_all_flat_paths Node R zeroR oneR plusR mulR (l₁ ++ l₂) =r= 
    sum_all_flat_paths Node R zeroR oneR plusR mulR l₁ + 
    sum_all_flat_paths Node R zeroR oneR plusR mulR l₂ = true.
  Proof using congrP congrR plus_associative refR symR zero_left_identity_plus.
    induction l₁ as [|((au, av), alp) l₁].
    + intros ?.
      simpl.
      assert(Htt: 
      (sum_all_flat_paths Node R 0 1 plusR mulR l₂ =r=
      0 + sum_all_flat_paths Node R 0 1 plusR mulR l₂) =
      (sum_all_flat_paths Node R 0 1 plusR mulR l₂ =r=
      sum_all_flat_paths Node R 0 1 plusR mulR l₂)).
      apply congrR.
      apply refR.
      apply zero_left_identity_plus.
      rewrite Htt; clear Htt.
      apply refR.
    + intros ?.
      simpl.
      assert(Htt:
      (measure_of_path Node R 1 mulR alp +
      sum_all_flat_paths Node R 0 1 plusR mulR (l₁ ++ l₂) =r=
      measure_of_path Node R 1 mulR alp +
      sum_all_flat_paths Node R 0 1 plusR mulR l₁ +
      sum_all_flat_paths Node R 0 1 plusR mulR l₂) = 
      (measure_of_path Node R 1 mulR alp +
      sum_all_flat_paths Node R 0 1 plusR mulR (l₁ ++ l₂) =r=
      measure_of_path Node R 1 mulR alp +
      (sum_all_flat_paths Node R 0 1 plusR mulR l₁ +
      sum_all_flat_paths Node R 0 1 plusR mulR l₂))).
      apply congrR.
      apply refR.
      apply symR.
      apply plus_associative.
      rewrite Htt; clear Htt.
      apply congrP.
      apply refR.
      eapply IHl₁.
  Qed.

      
  Lemma fold_right_sum_all_flat_paths : 
    forall al,   
    (sum_all_rvalues R 0 plusR
    (get_all_rvalues Node R 1 mulR al) =r=
    sum_all_flat_paths Node R 0 1 plusR mulR al) = true.
  Proof using congrP refR.
    induction al as [|((au, av), alh) al].
    + simpl.
      apply refR.
    + simpl.
      apply congrP.
      apply refR.
      apply IHal.
  Qed. 

  
  Lemma flat_map_path_partial_sum : 
    forall n m c d, 
    partial_sum_paths Node eqN R zeroR oneR plusR mulR finN m n c d =r= 
    sum_all_flat_paths Node R zeroR oneR plusR mulR
    (enum_all_paths_flat Node eqN R oneR finN m n c d) = true.
  Proof using congrP congrR one_left_identity_mul plus_associative
    plus_commutative refR symR zero_left_identity_plus zero_right_identity_plus.
      induction n.
      + intros ? ? ?.
        simpl.
        unfold construct_all_paths.
        simpl.
        case (c =n= d) eqn:Hcd.
        simpl.
        assert(Htt: (1 =r= 1 * 1 + 0) =
        (1 =r= 1 + 0)).
        apply congrR.
        apply refR.
        apply congrP.
        apply one_left_identity_mul.
        apply refR.
        rewrite Htt; clear Htt.
        apply symR.
        apply zero_right_identity_plus.
        simpl.
        apply refR.
      + intros ? ? ?.
        simpl.
        assert(Htt: 
        (partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d +
        sum_all_rvalues R 0 plusR
          (get_all_rvalues Node R 1 mulR
             (construct_all_paths Node eqN R 1 finN m (S n) c d)) =r=
        sum_all_flat_paths Node R 0 1 plusR mulR
          (construct_all_paths Node eqN R 1 finN m (S n) c d ++
           enum_all_paths_flat Node eqN R 1 finN m n c d)) =
        (partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d +
        sum_all_rvalues R 0 plusR
          (get_all_rvalues Node R 1 mulR
            (construct_all_paths Node eqN R 1 finN m (S n) c d)) =r=
        sum_all_flat_paths Node R 0 1 plusR mulR
          (construct_all_paths Node eqN R 1 finN m (S n) c d) +
        sum_all_flat_paths Node R 0 1 plusR mulR
          (enum_all_paths_flat Node eqN R 1 finN m n c d))).
        apply congrR.
        apply refR.
        apply sum_all_flat_paths_app.
        rewrite Htt; clear Htt.
        assert(Htt:
        (partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d +
        sum_all_rvalues R 0 plusR
          (get_all_rvalues Node R 1 mulR
             (construct_all_paths Node eqN R 1 finN m (S n) c d)) =r=
        sum_all_flat_paths Node R 0 1 plusR mulR
          (construct_all_paths Node eqN R 1 finN m (S n) c d) +
        sum_all_flat_paths Node R 0 1 plusR mulR
          (enum_all_paths_flat Node eqN R 1 finN m n c d)) =
        (partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d +
        sum_all_rvalues R 0 plusR
          (get_all_rvalues Node R 1 mulR
              (construct_all_paths Node eqN R 1 finN m (S n) c d)) =r=
        sum_all_flat_paths Node R 0 1 plusR mulR
          (enum_all_paths_flat Node eqN R 1 finN m n c d) + 
        sum_all_flat_paths Node R 0 1 plusR mulR
        (construct_all_paths Node eqN R 1 finN m (S n) c d))).
        apply congrR.
        apply refR.
        apply plus_commutative.
        rewrite Htt; clear Htt.
        apply congrP.
        apply IHn.
        apply fold_right_sum_all_flat_paths.
  Qed.

  
  Lemma in_eq_bool_path_measure : 
    forall lpp ys alph, 
    In_eq_bool Node Node R eqN eqN eqR ys
    (map (λ '(y, lt), let '(_, _) := y in lt) lpp) = true ->
    (measure_of_path Node R 1 mulR ys + measure_of_path Node R 1 mulR alph =r=
      measure_of_path Node R 1 mulR ys) = true -> 
    sum_all_flat_paths Node R 0 1 plusR mulR lpp + 
    measure_of_path Node R 1 mulR alph =r= 
    sum_all_flat_paths Node R 0 1 plusR mulR lpp = true.
  Proof using congrM congrP congrR mul_associative one_left_identity_mul
    plus_associative plus_commutative refR symR.
    induction lpp as [|((au, av), lpph) lpp].
    + intros ? ? Hin Hm.
      simpl in Hin.
      congruence.
    + intros ? ? Hin Hm.
      simpl in Hin.
      simpl.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin | Hin].
      pose proof path_split_measure ys [] lpph Hin as Ht.
      simpl in Ht.
      remember (measure_of_path Node R 1 mulR lpph) as a.
      remember (sum_all_flat_paths Node R 0 1 plusR mulR lpp) as b.
      remember (measure_of_path Node R 1 mulR alph) as c.
      remember (measure_of_path Node R 1 mulR ys) as d.
      assert (Htt: 
      (a + b + c =r= a + b) = (1 * a + b + c =r= 1 * a + b)).
      apply congrR.
      apply congrP.
      apply congrP.
      apply symR.
      apply one_left_identity_mul.
      apply refR.
      apply refR.
      apply congrP.
      apply symR.
      apply one_left_identity_mul.
      apply refR.
      rewrite Htt; clear Htt.
      assert(Htt:
      (1 * a + b + c =r= 1 * a + b) =  (d + b + c =r= d + b)).
      apply congrR.
      apply congrP.
      apply congrP.
      apply symR.
      exact Ht.
      apply refR.
      apply refR.
      apply congrP.
      apply symR.
      exact Ht.
      apply refR.
      rewrite Htt; clear Htt.
      assert (Htt: 
      (d + b + c =r= d + b) = 
      (d + (b + c) =r= d + b)).
      apply congrR.
      apply symR.
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      assert (Htt: (d + (b + c) =r= d + b) =
      (d + (c + b) =r= d + b)).
      apply congrR.
      apply congrP.
      apply refR.
      apply plus_commutative.
      apply refR.
      rewrite Htt; clear Htt.
      assert (Htt: 
      (d + (c + b) =r= d + b) =
      (d + c + b =r= d + b)).
      apply congrR.
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      apply congrP.
      exact Hm.
      apply refR.
      remember (measure_of_path Node R 1 mulR lpph) as a.
      assert (Htt: 
      (a + sum_all_flat_paths Node R 0 1 plusR mulR lpp +
      measure_of_path Node R 1 mulR alph =r=
      a + sum_all_flat_paths Node R 0 1 plusR mulR lpp) =
      (a + (sum_all_flat_paths Node R 0 1 plusR mulR lpp +
      measure_of_path Node R 1 mulR alph) =r=
      a + sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply symR.
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      apply congrP.
      apply refR.
      eapply IHlpp.
      exact Hin.
      exact Hm.
  Qed.



    


  Lemma sum_all_flat_paths_idempotence : 
    forall lp lpp, 
    (forall xs, In_path_membership Node eqN R eqR xs lp = true ->
     exists ys, 
      In_path_membership Node eqN R eqR ys lpp = true ∧ 
      measure_of_path Node R 1 mulR (tp Node R ys) +
      measure_of_path Node R 1 mulR (tp Node R xs) =r=
      measure_of_path Node R 1 mulR (tp Node R ys) = true) ->
    sum_all_flat_paths Node R 0 1 plusR mulR lp +
    sum_all_flat_paths Node R 0 1 plusR mulR lpp =r= 
    sum_all_flat_paths Node R 0 1 plusR mulR lpp = true.
  Proof using congrM congrP congrR mul_associative one_left_identity_mul plus_associative
    plus_commutative refN refR symR zero_left_identity_plus.
    induction lp as [|((au, av), alph) lp].
    + intros * Hin.
      simpl.
      apply zero_left_identity_plus.
    + intros * Hin.
      simpl.
      assert (Htt : In_path_membership Node eqN R eqR (au, av, alph) ((au, av, alph) :: lp) = true).
      simpl.
      rewrite triple_elem_eq_list_refl;
      try assumption.
      reflexivity.
      destruct (Hin _ Htt) as (ys & Ha & Hb).
      simpl in Hb; clear Htt.
      destruct ys as((ays, bys), ys).
      unfold In_path_membership in Ha.
      simpl in Hb.
      assert (Htt: 
      (measure_of_path Node R 1 mulR alph +
      sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) =
      (measure_of_path Node R 1 mulR alph +
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply symR.
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      assert (Htt:
      (measure_of_path Node R 1 mulR alph +
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
       sum_all_flat_paths Node R 0 1 plusR mulR lpp) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) = 
      ((sum_all_flat_paths Node R 0 1 plusR mulR lp +
        sum_all_flat_paths Node R 0 1 plusR mulR lpp) + 
        measure_of_path Node R 1 mulR alph =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply plus_commutative.
      apply refR.
      rewrite Htt; clear Htt.
      assert(Htt:
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp +
      measure_of_path Node R 1 mulR alph =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) =
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      (sum_all_flat_paths Node R 0 1 plusR mulR lpp +
      measure_of_path Node R 1 mulR alph) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply symR. 
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      pose proof (in_eq_bool_path_measure _ _ _ Ha Hb) as Hr.
      assert(Htt:
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      (sum_all_flat_paths Node R 0 1 plusR mulR lpp +
       measure_of_path Node R 1 mulR alph) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) =
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply congrP.
      apply refR.
      exact Hr.
      apply refR.
      rewrite Htt; clear Htt.
      eapply IHlp.
      intros ? Hinp.
      specialize (Hin xs).
      unfold In_path_membership in Hin, Hinp.
      destruct xs in * |- *.
      destruct p in * |- *.
      simpl in * |- *.
      rewrite Hinp in Hin.
      rewrite Bool.orb_true_r in Hin.
      specialize (Hin eq_refl).
      destruct Hin as (yst & Hc & Hd).
      exists yst.
      split;
      try assumption.
  Qed.


      


  
  Lemma in_eq_bool_enum_path :
    forall n w ys m c d, 
    (w <= n)%nat ->  
    In_eq_bool Node Node R eqN eqN eqR (ys ++ [(d, d, 1)])
    (all_paths_klength Node eqN R 1 finN m w c d) = true ->
    In_eq_bool Node Node R eqN eqN eqR (ys ++ [(d, d, 1)])
    (map (λ '(y, lt), let '(_, _) := y in lt)
     (enum_all_paths_flat Node eqN R 1 finN m n c d)) = true.
  Proof using lenN.
    induction n. 
    + intros * Hl Hin.
      destruct w.
      simpl in * |- *.
      unfold construct_all_paths.
      rewrite map_map.
      simpl.
      rewrite map_id.
      exact Hin.
      simpl in Hl.
      nia.
    + intros * Hl Hin.
      simpl.
      rewrite map_app.
      unfold construct_all_paths.
      rewrite map_map, map_id.
      apply in_eq_bool_mem_second.
      assert (Htw : w = S n \/ (w <= n)%nat).
      nia.
      destruct Htw as [Htw | Htw].
      left.
      rewrite <-Htw.
      exact Hin.
      right.
      specialize (IHn w ys m c d Htw Hin).
      exact IHn.
  Qed.





  Lemma sum_all_flat_paths_fixpoint : 
    forall k c d m, (∀ u v : Node, (u =n= v) = true → (m u v =r= 1) = true) ->
    mat_cong Node eqN R eqR m -> sum_all_flat_paths Node R zeroR oneR plusR mulR
      (enum_all_paths_flat Node eqN R oneR finN m (length finN - 1)%nat c d) =r=
    sum_all_flat_paths Node R zeroR oneR plusR mulR
      (enum_all_paths_flat Node eqN R oneR finN m (k + length finN - 1)%nat c d) = true.
  Proof using congrM congrP congrR dupN left_distributive_mul_over_plus lenN memN
    mul_associative one_left_identity_mul one_right_identity_mul plus_associative
    plus_commutative refN refR right_distributive_mul_over_plus symN symR trnN trnR
    zero_left_identity_plus zero_stable.
    induction k.
    + intros ? ? ? Huv Hm.
      simpl.
      apply refR. 
    + intros ? ? ? Huv Hm.
      assert (Htt : (S k + length finN - 1)%nat = 
      S (k + length finN - 1)). nia.
      rewrite Htt; clear Htt.
      simpl.
      remember (construct_all_paths Node eqN R 1 finN m (S (k + length finN - 1)) c d) as ls.
      remember (enum_all_paths_flat Node eqN R 1 finN m (k + length finN - 1) c d) as lss.
      assert(Htt:
      (sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR (ls ++ lss)) =
      (sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR ls +
      sum_all_flat_paths Node R 0 1 plusR mulR lss)).
      apply congrR.
      apply refR.
      apply sum_all_flat_paths_app.
      rewrite Htt; clear Htt.
      subst.
      assert(Hl : (length finN <= S (k + length finN - 1))%nat).
      nia.
      pose proof reduce_path_gen_lemma (S (k + length finN - 1))
        m c d as Hpl.
      unfold Orel in Hpl.
      specialize (IHk c d m Huv Hm).
      remember (construct_all_paths Node eqN R 1 finN m (S (k + length finN - 1)) c d) as lp.
      remember (enum_all_paths_flat Node eqN R 1 finN m (k + length finN - 1) c d) as lpp.
      remember (sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d)) as sc.
      assert(Htt: 
      (sc =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) = 
      (sc =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lp + sc)).
      apply congrR.
      apply refR.
      apply congrP.
      apply refR.
      apply symR.
      exact IHk.
      rewrite Htt; clear Htt.
      subst.
      remember (construct_all_paths Node eqN R 1 finN m (S (k + length finN - 1)) c d) as lp.
      remember (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d) as lpp.
      pose proof sum_all_flat_paths_idempotence lp lpp as Hsu.
      assert (Htt: ∀ xs : Path Node R,
      In_path_membership Node eqN R eqR xs lp = true
      → ∃ ys : Path Node R,
          In_path_membership Node eqN R eqR ys lpp = true
          ∧ (measure_of_path Node R 1 mulR (tp Node R ys) +
              measure_of_path Node R 1 mulR (tp Node R xs) =r=
              measure_of_path Node R 1 mulR (tp Node R ys)) = true).
      intros ? Hin.
      unfold In_path_membership in Hin.
      destruct xs.
      destruct p.
      rewrite Heqlp in Hin.
      unfold construct_all_paths in Hin.
      rewrite map_map in Hin.
      rewrite map_id in Hin.
      destruct (Hpl l Hl Huv Hm Hin) as 
      (ys & Hln & Hina & Hmb).
      exists (c, d, (ys ++ [(d, d, 1)])).
      split.
      rewrite Heqlpp.
      unfold In_path_membership.
      assert(Hlt: (length ys <= (length finN - 1))%nat).
      nia.
      eapply in_eq_bool_enum_path.
      exact Hlt.
      exact Hina.
      simpl.
      assert (Htt: (measure_of_path Node R 1 mulR (ys ++ [(d, d, 1)]) +
      measure_of_path Node R 1 mulR l =r=
      measure_of_path Node R 1 mulR (ys ++ [(d, d, 1)]))= 
      (measure_of_path Node R 1 mulR ys * (1 * 1) +
      measure_of_path Node R 1 mulR l =r=
      measure_of_path Node R 1 mulR ys * (1 * 1))).
      apply congrR.
      apply congrP.
      pose proof path_split_measure (ys ++ [(d, d, 1)]) ys [(d, d, 1)] as Htv.
      simpl in Htv.
      rewrite triple_elem_eq_list_refl in Htv;
      try assumption.
      exact (Htv eq_refl).
      apply refR.
      pose proof path_split_measure (ys ++ [(d, d, 1)]) ys [(d, d, 1)] as Htv.
      simpl in Htv.
      rewrite triple_elem_eq_list_refl in Htv;
      try assumption.
      exact (Htv eq_refl).
      rewrite Htt; clear Htt.
      rewrite <-Hmb.
      apply congrR.
      apply congrP.
      remember (measure_of_path Node R 1 mulR ys) as a.
      rewrite <- (one_right_identity_mul a).
      apply congrR.
      apply congrM.
      apply refR.
      apply one_left_identity_mul.
      apply refR.
      apply refR.
      remember (measure_of_path Node R 1 mulR ys) as a.
      rewrite <- (one_right_identity_mul a).
      apply congrR.
      apply congrM.
      apply refR.
      apply one_left_identity_mul.
      apply refR.
      specialize (Hsu Htt).
      apply symR.
      exact Hsu.
  Qed.


 
  Lemma zero_stable_partial_sum_path : 
    forall k m,
    (∀ u v : Node, (u =n= v) = true → (m u v =r= 1) = true) ->
    mat_cong Node eqN R eqR m -> 
    (forall (c d : Node), 
      partial_sum_paths _ eqN _  0 1 plusR mulR finN m (length finN - 1)%nat c d =r= 
      partial_sum_paths _ eqN _  0 1 plusR mulR finN m (k + length finN - 1)%nat c d = true).
  Proof using congrM congrP congrR dupN left_distributive_mul_over_plus lenN memN
    mul_associative one_left_identity_mul one_right_identity_mul plus_associative
    plus_commutative refN refR right_distributive_mul_over_plus symN symR trnN trnR
    zero_left_identity_plus zero_right_identity_plus zero_stable.
    intros * Huv Hm ? ?.
    assert (Htt: 
    (partial_sum_paths Node eqN R 0 1 plusR mulR finN m (length finN - 1) c d =r=
    partial_sum_paths Node eqN R 0 1 plusR mulR finN m (k + length finN - 1) c d) =
    (sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d) =r= 
    sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (k + length finN - 1) c d))).
    apply congrR.
    apply flat_map_path_partial_sum.
    apply flat_map_path_partial_sum.
    rewrite Htt; clear Htt.
    apply sum_all_flat_paths_fixpoint;
    try assumption.
  Qed.


End Pathprops.


  



    
    
    

   

