From Stdlib Require Import List Utf8
  BinNatDef Lia.
From Stdlib Require Import Classical_Prop.
From Semiring Require Import OrelN Structures.
Import ListNotations SemiringNotations.

Section Generic. 

  Context {A : Type} 
    {hdec : ∀ (x y : A), {x = y} + {x ≠ y}}.


  (* c covers l, i.e., every element of l appears in c *)
  Definition covers {A : Type} (l c : list A) : Prop :=
    forall (x : A), In x l -> In x c.


   Lemma covers_list_elem : 
    forall (c l : list A), (forall y : A, List.In y c) ->
    covers l c.
  Proof using Type.
    unfold covers.
    destruct c as [|a c].
    + intros ? Hy ? Hl.
      specialize (Hy x).
      simpl in Hy.
      inversion Hy.
    + intros ? Hy ? Hl.
      simpl in *.
      exact (Hy x). 
  Qed.

  (** Pigeonhole principle: if every element of [l] appears in [c]
      (i.e., [covers l c]) and [c] is shorter than [l], then some
      element [a] occurs at least twice in [l].  The proof uses
      to decide membership on the type [A] with decidable equality. *)
  Lemma covers_pigenhole : 
    forall (l c : list A), 
    covers l c ->  (length c < List.length l) -> 
    exists a l₁ l₂ l₃, l = (l₁ ++ [a] ++ l₂ ++ [a] ++ l₃).
  Proof.
    (** [In a l] implies [l = l₁ ++ a :: l₂] without needing decidable equality. *)
    assert (in_split' : forall (a : A) (l : list A), In a l ->
      exists l₁ l₂, l = l₁ ++ a :: l₂).
    { induction l as [|b l IH]; intros Hin.
      - inversion Hin.
      - destruct Hin as [Heq | Hin].
        + subst b. exists [], l. reflexivity.
        + destruct (IH Hin) as [l₁ [l₂ Hl]].
          exists (b :: l₁), l₂. cbn. f_equal. exact Hl. }
    induction l as [|a l' IH]; intros c Hcov Hlen.
    - (* l = [] *)
      cbn in Hlen. lia.
    - (* l = a :: l' *)
      cbn in Hlen.
      unfold covers in Hcov.
      assert (Ha_c : In a c) by (apply Hcov; left; reflexivity).
      apply in_split' in Ha_c. destruct Ha_c as [c₁ [c₂ Hc]].
      destruct (@in_dec A hdec a l') as [Hin | Hnotin].
      + (* a ∈ l': found the duplicate *)
        apply in_split' in Hin. destruct Hin as [l₁ [l₂ Hl']].
        exists a, [], l₁, l₂.
        cbn. f_equal. exact Hl'.
      + (* a ∉ l' *)
        assert (Hcov' : covers l' (c₁ ++ c₂)).
        { unfold covers. intros x Hx.
          pose proof (Hcov x (or_intror Hx)) as Hx_c.
          rewrite Hc in Hx_c.
          apply in_app_or in Hx_c.
          destruct Hx_c as [Hx_c | [Heq | Hx_c]].
          - apply in_or_app. left. exact Hx_c.
          - subst x. exfalso. apply Hnotin. exact Hx.
          - apply in_or_app. right. exact Hx_c. }
        (* Length inequality *)
        assert (Hlen' : length (c₁ ++ c₂) < length l').
        { rewrite Hc in Hlen.
          rewrite !length_app in Hlen. cbn in Hlen.
          assert (Htemp : length c₁ + length c₂ < length l') by lia.
          rewrite length_app. exact Htemp. }
        apply IH in Hcov'; [| exact Hlen'].
        destruct Hcov' as [a' [l₁ [l₂ [l₃ Hl']]]].
        exists a', (a :: l₁), l₂, l₃.
        cbn. f_equal. exact Hl'.
  Qed.


End Generic.

Section Path.

  Context 
    {Node : FinType.type}.

  (** A matrix over semiring [R] indexed by finite type [Node]. *)
  Let Matrix {R : Semiring.type} := @OrelN.Matrix Node R.
  (* a path is a triple *)
  Definition Path {R : Semiring.type} : Type := 
    Node * Node * list (Node * Node * R). 
  
  Definition source {R : Semiring.type} (c : Node) 
    (l : list (Node * Node * R)) : bool :=
    match l with 
    | [] => false
    | (x, _, _) :: _ => 
      match fin_eq_dec c x with 
      | left _ => true 
      | right _ => false
      end  
    end.

  Definition target_alt {R : Semiring.type} (d : Node) 
    (l : list (Node * Node * R)) := 
    match List.rev l with
    | [] => false
    | (x, y, r) :: t => 
      match fin_eq_dec d y with 
      | left _ => true 
      | right _ => false
      end 
    end. 


  Fixpoint target {R : Semiring.type} (d : Node) 
    (l : list (Node * Node * R)) : bool :=
    match l with
    | [] => false
    | (x, y, r) :: t => match t with 
      | [] => match fin_eq_dec d y with 
        | left _ => true 
        | right _ => false
        end
      | hs :: ts => target d t
      end
    end.


  (* path strength between c and d *)
  Fixpoint measure_of_path {R : Semiring.type} 
    (l : list (Node * Node * R)) : R :=
    match l with 
    | [] => 1
    | (_, _, v) :: t => v * measure_of_path t
    end.

  
  Fixpoint well_formed_path_aux {R : Semiring.type} 
    (m : @Matrix R) (l : list (Node * Node * R)) : Prop :=
    match l with 
    | [] => True
    | (c, x, v) :: tl => (m c x = v) ∧ match tl with 
      | [] => True
      | (y, _, _) :: _ => (x = y) ∧ well_formed_path_aux m tl
      end
    end.


  
  Definition f_proj {R : Semiring.type} (p : @Path R) : Node :=
    match p with
    |(a, _, _) => a
    end. 

  Definition s_proj {R : Semiring.type} (p : @Path R) : Node :=
    match p with
    |(_, b, _) => b
    end. 
  
  Definition t_proj {R : Semiring.type} (p : @Path R) : 
    list (Node * Node * R):=
    match p with
    |(_, _, l) => l
    end.


    
  (* stick a node 'c' in all the paths, represented by l *)
  Fixpoint append_node_in_paths {R : Semiring.type} 
    (m : @Matrix R) (c : Node) (l : list (list (Node * Node * R))) : 
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
  Fixpoint all_paths_klength {R : Semiring.type} (xs : list Node) 
    (m : @Matrix R) (k : nat) 
    (c d : Node) : list (list (Node * Node * R)) :=
    match k with
    | O => if fin_eq_dec c d then [[(c, d, 1)]] else []
    | S k' =>
        let lf := List.flat_map
          (fun x => all_paths_klength xs m k' x d) xs
        in append_node_in_paths m c lf
    end.

  
  Definition construct_all_paths {R : Semiring.type}  
    (xs : list Node) (m : Node -> Node -> R) (k : nat) 
    (c d : Node) : list Path :=
    let lp := all_paths_klength xs m k c d in 
    List.map (fun l => (c, d, l)) lp.

  (* get all the R values from path *)
  Definition get_all_rvalues {R : Semiring.type} 
    (pl : list Path) : list R :=
    List.map (fun '(_, _, l) => measure_of_path l) pl.


  Definition sum_all_rvalues {R : Semiring.type} (pl : list R) :=
    List.fold_right (fun b a => b + a) 0 pl.

  (* sum_fn using fold_right *)
  Definition sum_fn_fold {R : Semiring.type} (f : Node -> R) (l : list Node) : R :=
    List.fold_right (fun b a => f b + a) 0 l.
    
  Definition cyclic_path {R : Semiring.type} (c : Node) 
    (l : list (Node * Node * R)) : Prop :=
    l <> [] /\ source c l = true /\ 
    target c l = true.

  
  
  (* assume that path is well_founded *)
  Fixpoint collect_nodes_from_a_path {R : Semiring.type}
    (l : list (Node * Node * R)) : list Node :=
    match l with
    | [] => []
    | (a, b, _) :: t => match t with
      | [] => [a; b]
      | _ :: _ => a :: collect_nodes_from_a_path t
    end
    end.

  (* Constructs well founded path *)  
  Fixpoint construct_path_from_nodes {R : Semiring.type}
  (l : list Node) (m : @Matrix R) : 
  list (Node * Node * R) :=
  match l with 
  | [] => []
  | u :: t => match t with
    | [] => []
    | v :: _ => (u, v, m u v) :: construct_path_from_nodes t m
  end
  end.

  (* Checks if au is second element of path or not  *)      
  Fixpoint elem_path_triple_tail {R : Semiring.type} 
    (au : Node) (l : list (Node * Node * R)) : bool :=
    match l with
    | [] => false
    | (bu, bv, _) :: t => 
      if (fin_eq_dec au bv) then true 
      else elem_path_triple_tail au t
    end.


  
  Fixpoint keep_collecting {R : Semiring.type} (au : Node) (l : list (Node * Node * R)) :=
    match l with
    | [] => []
    | (bu, bv, bw) :: t => if fin_eq_dec au bv then [(bu, bv, bw)] else 
        (bu, bv, bw) :: keep_collecting au t
    end.
    
  Fixpoint keep_dropping {R : Semiring.type} (au : Node) (l : list (Node * Node * R)) :=
    match l with
    | [] => []
    | (bu, bv, bw) :: t => if (fin_eq_dec au bv) then t else 
      keep_dropping au t
    end.

  (* computes the loop in a path *)
  Fixpoint elem_path_triple_compute_loop {R : Semiring.type} (l : list (Node * Node * R)) := 
    match l with
    | [] => None
    | (au, av, aw) :: t => if fin_eq_dec au av then Some [(au, av, aw)] (* loop at the head, 1 length *)
      else 
          if elem_path_triple_tail au t then Some ((au, av, aw) :: keep_collecting au t)
          else elem_path_triple_compute_loop t
    end.

  (* This function is very similar to the above one, except it returns the 
    left over from the front ++ loop ++ rest of the list *)  
  Fixpoint elem_path_triple_compute_loop_triple {R : Semiring.type} 
    (l : list (Node * Node * R)) := 
    match l with
    | [] => ([], None, [])
    | (au, av, aw) :: t => if fin_eq_dec au av then ([], Some [(au, av, aw)], t) 
      else 
          if elem_path_triple_tail au t then 
          ([], Some ((au, av, aw) :: keep_collecting au t), keep_dropping au t)
          else match elem_path_triple_compute_loop_triple t with 
            | (fp, sp, tp) => ((au, av, aw) :: fp, sp, tp)
          end
    end.

  (* elem_path_triple l = true means l does not have any cycle *)     
  Fixpoint elem_path_triple {R : Semiring.type} (l : list (Node * Node * R)) : bool := 
    match l with
    | [] => true 
    | (au, av, _) :: t => 
        negb (if fin_eq_dec au av then true else false) && 
        negb (elem_path_triple_tail au t) && 
        elem_path_triple t 
    end.


  
  Fixpoint partial_sum_paths {R : Semiring.type} (l : list Node) 
    (m : @Matrix R) (n : nat) (c d : Node) : R :=
    match n with
    | O => if fin_eq_dec c d then 1 else 0 
    | S n' =>  partial_sum_paths l m n' c d + 
      sum_all_rvalues (get_all_rvalues (construct_all_paths l m n c d))
    end.

  
  
  (* Get all the paths in one big list *)
  Fixpoint enum_all_paths_flat {R : Semiring.type} (l : list Node) 
    (m : @Matrix R) (n : nat) (c d : Node) : list Path :=
  match n with
  | O => construct_all_paths l m O c d
  | S n' => 
    construct_all_paths l m n c d ++ 
    enum_all_paths_flat l m n' c d
  end.
  
  
  Fixpoint sum_all_flat_paths {R : Semiring.type} (l : list Path) : R :=
    match l with
    | [] => 0
    | (_, _, h) :: t => measure_of_path h + 
      sum_all_flat_paths t
    end.

  (* Checks if a path p appears in lpp or not *)
  Definition In_path_membership {R : Semiring.type} 
    (p : @Path R) (lpp : list Path) : Prop :=
    List.In p lpp.


  (* Proofs start from here *)

  (** [append_node_in_paths m c l] prepends the edge [(c, x, m c x)]
      to every non-empty path in [l], therefore every path in the result
      is non-empty. *)
  Lemma append_node_in_paths_nonempty {R : Semiring.type} : 
    forall (l : list (list (Node * Node * R))) 
    (m : @Matrix R) (c : Node),  
    forall (p : list (Node * Node * R)), 
    List.In p (append_node_in_paths m c l) -> 
    p ≠ [] ∧ ∃ (x : Node) pr, p = (c, x, m c x) :: pr.
  Proof.
    induction l as [|h t IH]; intros m c p Hin.
    - inversion Hin.
    - simpl in Hin.
      destruct h as [|ha ht].
      + apply (IH m c p Hin).
      + destruct ha as [[x y] r].
        destruct Hin as [Hin | Hin].
        * subst p. split. intro Hnil. inversion Hnil.
          repeat eexists.
        * apply (IH m c p Hin).
  Qed.

  (** If [xs] is produced by [append_node_in_paths m c l], then [xs]
      begins with the edge [(c, y, m c y)] for some [y], its tail [ys]
      is non-empty, and both [source c xs] and [source y ys] hold. *)
  Lemma append_node_in_paths_shape {R : Semiring.type} : 
    ∀ (l : list (list (Node * Node * R))) 
    (m : @Matrix R) (c : Node) 
    (xs : list (Node * Node * R)), 
    List.In xs (append_node_in_paths m c l) -> 
    ∃ (y : Node) (ys : list (Node * Node * R)), 
      xs = ((c, y, m c y) :: ys) ∧
      source c xs = true ∧
      source y ys = true ∧ 
      ys ≠ [].
  Proof.
    induction l as [|h t IH]; intros m c xs Hin.
    - inversion Hin.
    - simpl in Hin.
      destruct h as [|ha ht].
      + apply (IH m c xs Hin).
      + destruct ha as [[x y] r].
        destruct Hin as [Hin | Hin].
        * subst xs.
          exists x, ((x, y, r) :: ht).
          unfold source. simpl.
          destruct (fin_eq_dec c c) as [_|Hc]; [|exfalso; apply Hc; reflexivity].
          destruct (fin_eq_dec x x) as [_|Hx]; [|exfalso; apply Hx; reflexivity].
          split; [reflexivity|].
          split; [reflexivity|].
          split; [reflexivity|].
          intro Hnil. inversion Hnil.
        * apply (IH m c xs Hin).
  Qed.

  (** If [xs] is in [append_node_in_paths m c l], then [xs] is exactly
      [(c, y, m c y)] prepended to some [ys] that was already in [l]. *)
  Lemma append_node_in_paths_In {R : Semiring.type} (m : @Matrix R) (c : Node)
      (l : list (list (Node * Node * R))) (xs : list (Node * Node * R)) :
      In xs (append_node_in_paths m c l) ->
      exists (y : Node) (ys : list (Node * Node * R)),
        xs = (c, y, m c y) :: ys /\ In ys l.
  Proof.
    induction l as [|h t IH]; intros Hin.
    - inversion Hin.
    - simpl in Hin.
      destruct h as [|ha ht].
      + apply IH in Hin. destruct Hin as (y & ys & Heq & Hin').
        exists y, ys. split; [exact Heq | right; exact Hin'].
      + destruct ha as [[x y'] r].
        destruct Hin as [Hin | Hin].
        * subst xs. exists x, ((x, y', r) :: ht).
          split; [reflexivity | left; reflexivity].
        * apply IH in Hin. destruct Hin as (y & ys & Heq & Hin').
          exists y, ys. split; [exact Heq | right; exact Hin'].
  Qed.

  (** Every path returned by [all_paths_klength elements m n c d] is
      non-empty, starts at [c], and ends at [d]. *)
  Lemma non_empty_paths_in_kpath {R : Semiring.type} : 
    ∀ (n : nat) (m : @Matrix R) 
    (c d : Node) (xs : list (Node * Node * R)),
    List.In xs (all_paths_klength elements m n c d) -> 
    xs ≠ [] ∧ source c xs = true ∧ target d xs = true.
  Proof.
    induction n as [|n' IH]; intros m c d xs Hin.
    - (* n = 0 *)
      simpl in Hin.
      destruct (fin_eq_dec c d) as [Heq | Hneq].
      + subst d. destruct Hin as [Hin | []].
        subst xs.
        split; [intro Hnil; inversion Hnil | ].
        unfold source. simpl.
        destruct (fin_eq_dec c c) as [_|Hc]; [|exfalso; apply Hc; reflexivity].
        split; [reflexivity | ].
        unfold target. simpl.
        destruct (fin_eq_dec c c) as [_|Hc]; [|exfalso; apply Hc; reflexivity].
        reflexivity.
      + inversion Hin.
    - (* n = S n' *)
      simpl in Hin.
      apply append_node_in_paths_In in Hin.
      destruct Hin as (y & ys & Heq & Hin_flat).
      subst xs.
      apply in_flat_map in Hin_flat.
      destruct Hin_flat as (x & Hin_x & Hin_ys).
      apply (IH m x d) in Hin_ys.
      destruct Hin_ys as (Hys_ne & Hsrc & Htgt).
      split; [intro Hnil; inversion Hnil | ].
      unfold source. simpl.
      destruct (fin_eq_dec c c) as [_|Hc]; [|exfalso; apply Hc; reflexivity].
      split; [reflexivity | ].
      cbn [target].
      destruct ys as [|h ys']; [exfalso; apply Hys_ne; reflexivity | ].
      exact Htgt.
  Qed.
  

   (** If we prepend a well-formed edge [(c, y, m c y)] to a well-formed
       path [ys], the result is well-formed.  The condition [source y ys]
       ensures the new edge connects properly to the first edge of [ys]. *)
   Lemma well_formed_by_extending {R : Semiring.type} : 
    forall (xs ys : list (Node * Node * R)) (c y : Node) (m : @Matrix R), 
    ys <> [] ->  xs = ((c, y, m c y) :: ys)-> 
    source c xs = true -> source y ys = true ->
    well_formed_path_aux m (List.tl xs) -> 
    well_formed_path_aux m xs.
  Proof.
    intros xs ys c y m Hys_ne Heq Hsrc_xs Hsrc_ys Htl.
    subst xs. cbn.
    split; [reflexivity | ].
    destruct ys as [|h ys']; [exfalso; apply Hys_ne; reflexivity | ].
    destruct h as [[z w] r].
    unfold source in Hsrc_ys. simpl in Hsrc_ys.
    destruct (fin_eq_dec y z) as [Heq_yz | Hneq].
    - subst z. split; [reflexivity | exact Htl].
    - discriminate Hsrc_ys.
  Qed.

  (** Every path returned by [all_paths_klength elements m n c d] is
      well-formed with respect to [m], provided the diagonal of [m] is 1. *)
  Lemma all_paths_well_formed_in_kpaths {R : Semiring.type} : 
    forall (n : nat) (m : @Matrix R) 
    (c d : Node) (xs : list (Node * Node * R)),
    (forall c d, c = d -> m c d = 1) -> 
    List.In xs (all_paths_klength elements m n c d) ->
    well_formed_path_aux m xs.
  Proof.
    induction n as [|n' IH]; intros m c d xs Hdiag Hin.
    - (* n = 0 *)
      simpl in Hin.
      destruct (fin_eq_dec c d) as [Heq | Hneq].
      + subst d. destruct Hin as [Hin | []].
        subst xs. unfold well_formed_path_aux. cbn.
        split; [apply Hdiag; reflexivity | exact I].
      + inversion Hin.
    - (* n = S n' *)
      simpl in Hin.
      (* Keep a copy of Hin for the membership lemma *)
      assert (Hin_copy := Hin).
      (* Extract structural properties *)
      apply (append_node_in_paths_shape
        (List.flat_map (fun x => all_paths_klength elements m n' x d) elements)
        m c xs) in Hin.
      destruct Hin as (y & ys & Heq & Hsrc_xs & Hsrc_ys & Hys_ne).
      subst xs.
      (* Extract membership: ys is from the flat_map *)
      apply append_node_in_paths_In in Hin_copy.
      destruct Hin_copy as (y2 & ys2 & Heq2 & Hin_flat).
      (* Heq2: (c,y,m c y)::ys = (c,y2,m c y2)::ys2 *)
      inversion Heq2. subst y2 ys2.
      apply in_flat_map in Hin_flat.
      destruct Hin_flat as (x & Hin_el & Hin_ys).
      (* Get well-formedness of the tail via IH *)
      apply (IH m x d ys Hdiag) in Hin_ys.
      (* Assemble using the extension lemma *)
      apply (well_formed_by_extending ((c, y, m c y) :: ys) ys c y m
        Hys_ne eq_refl Hsrc_xs Hsrc_ys Hin_ys).
  Qed.


  (** Every path in [all_paths_klength elements m k c d] ends with the
      unit loop [(d, d, 1)], i.e., it can be written as a prefix followed
      by that loop. *)
  Lemma path_end_unit_loop {R : Semiring.type} : 
    forall k l (m : @Matrix R) (c d : Node), 
    List.In l (all_paths_klength elements m k c d) ->
    exists l', l = (l' ++ [(d, d, 1)]).
  Proof.
    induction k as [|k' IH]; intros l m c d Hin.
    - (* k = 0 *)
      simpl in Hin.
      destruct (fin_eq_dec c d) as [Heq | Hneq].
      + subst d. destruct Hin as [Hin | []].
        subst l. exists []. reflexivity.
      + inversion Hin.
    - (* k = S k' *)
      simpl in Hin.
      apply append_node_in_paths_In in Hin.
      destruct Hin as (y & ys & Heq & Hin_flat).
      subst l.
      apply in_flat_map in Hin_flat.
      destruct Hin_flat as (x & Hin_el & Hin_ys).
      apply (IH ys m x d) in Hin_ys.
      destruct Hin_ys as [l' Hl'].
      exists ((c, y, m c y) :: l').
      rewrite Hl'. reflexivity.
  Qed.

  (** If a list has two distinct source nodes, they must be equal —
      [source] is injective on the first element of a non-empty path. *)
  Lemma source_same_path {R : Semiring.type} : 
    forall (l₁ l₂ : list (Node * Node * R)) x y,
    l₁ = l₂ -> source x l₁ = true -> 
    source y l₂ = true -> x = y.
  Proof.
    intros l₁ l₂ x y Heq Hsrc_x Hsrc_y.
    subst l₂.
    unfold source in Hsrc_x, Hsrc_y.
    destruct l₁ as [|h t]; [discriminate Hsrc_x | ].
    destruct h as [[a b] r].
    simpl in Hsrc_x, Hsrc_y.
    destruct (fin_eq_dec x a) as [Heq_xa | Hneq_xa]; [| discriminate Hsrc_x].
    destruct (fin_eq_dec y a) as [Heq_ya | Hneq_ya]; [| discriminate Hsrc_y].
    subst x y. reflexivity.
  Qed.

  (** Every path in [all_paths_klength elements m k c d] has length
      [S k] (i.e., [k+1] edges). *)
  Lemma all_paths_in_klength {R : Semiring.type} : 
    ∀ (k : nat) (m : @Matrix R) (c d : Node) xs,
    List.In xs (all_paths_klength elements m k c d) ->
    List.length xs = S k.
  Proof.
    induction k as [|k' IH]; intros m c d xs Hin.
    - (* k = 0 *)
      simpl in Hin.
      destruct (fin_eq_dec c d) as [Heq | Hneq].
      + subst d. destruct Hin as [Hin | []].
        subst xs. reflexivity.
      + inversion Hin.
    - (* k = S k' *)
      simpl in Hin.
      apply (append_node_in_paths_In m c
        (List.flat_map (fun x => all_paths_klength elements m k' x d) elements)
        xs) in Hin.
      destruct Hin as (y & ys & Heq & Hin_flat).
      subst xs.
      apply in_flat_map in Hin_flat.
      destruct Hin_flat as (x & Hin_el & Hin_ys).
      apply (IH m x d ys) in Hin_ys.
      simpl. rewrite Hin_ys. reflexivity.
  Qed.


  (** Combined property: every path in [all_paths_klength] is non-empty,
      starts at [c], ends at [d], is well-formed, has length [S n], and
      ends with the unit loop [(d, d, 1)]. *)
  Lemma source_target_non_empty_kpath_and_well_formed {R : Semiring.type} : 
    ∀ (n : nat) (m : @Matrix R) 
    (c d : Node) (xs : list (Node * Node * R)),
    (forall c d, c = d-> m c d = 1) -> 
    List.In xs (all_paths_klength elements m n c d) ->
    xs ≠ [] ∧ source c xs = true ∧ target d xs = true ∧
    well_formed_path_aux m xs ∧ (List.length xs = S n)%nat ∧
    exists xs', xs = (xs' ++ [(d, d, 1)]).
  Proof.
    intros n m c d xs Hdiag Hin.
    assert (Hin1 := Hin). assert (Hin2 := Hin).
    assert (Hin3 := Hin). assert (Hin4 := Hin).
    apply non_empty_paths_in_kpath in Hin as (Hne & Hsrc & Htgt).
    apply all_paths_well_formed_in_kpaths in Hin1 as Hwf; [| exact Hdiag].
    apply all_paths_in_klength in Hin2 as Hlen.
    apply path_end_unit_loop in Hin3 as Hend.
    split; [exact Hne | ].
    split; [exact Hsrc | ].
    split; [exact Htgt | ].
    split; [exact Hwf | ].
    split; [exact Hlen | ].
    exact Hend.
  Qed.


   Lemma target_alt_end {R : Semiring.type} : 
    forall (l : list (Node * Node * R))
    (x : Node * Node * R) (d : Node),
    target_alt d (l ++ [x]) = 
    target_alt d [x].
  Proof.
    intros *. unfold target_alt.
    rewrite rev_unit.
    assert (Ht : rev [x] = [x]).
    reflexivity.
    rewrite Ht.
    reflexivity.
  Qed.

  Lemma target_end  {R : Semiring.type} : 
    forall (l : list (Node * Node * R))
    (x : Node * Node * R) (d : Node),
    target d (l ++ [x]) = 
    target d [x].
  Proof.
    induction l.
    - simpl; intros ? ?. reflexivity.
    - intros ? ?.
      assert (Ht : target d ((a :: l) ++ [x]) = 
        target d (l ++ [x])).
      simpl. destruct a. destruct p.
      destruct (l ++ [x]) eqn:Hv.
      pose proof app_eq_nil l [x] Hv as Hw.
      destruct Hw as [Hwl Hwr].
      congruence. reflexivity.
      rewrite Ht. apply IHl.
  Qed.


  Lemma target_target_alt_same {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) (d : Node), 
    target d l = target_alt d l.
  Proof.
    induction l using rev_ind.
    - unfold target_alt; simpl; intros ?.
      reflexivity.
    - intros ?. rewrite target_alt_end, target_end.
      reflexivity.
  Qed.


   (** If a well-formed path [xs] starts at [c] and its tail is known to
       be [(au, av, aw) :: ys], then the whole path is fully determined:
       [xs = (c, au, m c au) :: (au, av, aw) :: ys]. *)
   Lemma well_formed_path_reconstruct  {R : Semiring.type} :
    forall xs ys (m : @Matrix R) c au av aw,
    List.tl xs ≠ [] ->  source c xs = true ->
    well_formed_path_aux m xs  ->(List.tl xs) = ((au, av, aw) :: ys) ->
    xs = ((c, au, m c au) :: (au, av, aw) :: ys).
  Proof.
    intros xs ys m c au av aw Htl_ne Hsrc Hwf Htl_eq.
    (* xs must be non-empty since its tail is non-empty *)
    destruct xs as [|h rest]; [cbn in Htl_ne; exfalso; apply Htl_ne; reflexivity | ].
    destruct h as [[c' x] v].
    cbn [List.tl] in Htl_eq.
    (* Htl_eq : rest = (au, av, aw) :: ys *)
    subst rest.
    (* From the source condition, the head starts with c *)
    unfold source in Hsrc. simpl in Hsrc.
    destruct (fin_eq_dec c c') as [Heq_cc' | Hneq]; [| discriminate Hsrc].
    subst c'.
    (* Now xs = (c, x, v) :: (au, av, aw) :: ys *)
    unfold well_formed_path_aux in Hwf. cbn in Hwf.
    destruct Hwf as [Hmv [Heq_x Hwf_rest]].
    (* Hmv : m c x = v,  Heq_x : x = au *)
    subst x. subst v.
    reflexivity.
  Qed.

  (** If a well-formed path [xs] starts at [c] and its non-empty tail
      belongs to [l], then [xs] belongs to [append_node_in_paths m c l].
      This is the reverse direction of [append_node_in_paths_In]. *)
  Lemma In_append_node_in_paths_rev {R : Semiring.type} : 
    forall l (m : @Matrix R) c xs,
    source c xs = true -> 
    List.tl xs <> [] ->
    well_formed_path_aux m xs ->
    List.In (List.tl xs) l ->
    List.In xs (append_node_in_paths m c l).
  Proof.
    intros l m c xs Hsrc Htl_ne Hwf Hin_tl.
    (* Extract the structure of xs from the hypotheses *)
    unfold source in Hsrc.
    destruct xs as [|h rest]; [discriminate Hsrc | ].
    destruct h as [[c' x] v].
    simpl in Hsrc.
    destruct (fin_eq_dec c c') as [Heq | Hneq]; [| discriminate Hsrc].
    subst c'.
    (* xs = (c, x, v) :: rest *)
    cbn [List.tl] in Htl_ne, Hin_tl.
    (* Htl_ne : rest ≠ [],  Hin_tl : In rest l *)
    unfold well_formed_path_aux in Hwf. cbn in Hwf.
    destruct Hwf as [Hmv Hrest].
    destruct rest as [|h2 rest']; [exfalso; apply Htl_ne; reflexivity | ].
    destruct h2 as [[au av] aw].
    destruct Hrest as [Heq_x Hwf_rest].
    (* Hmv: m c x = v,  Heq_x: x = au *)
    subst x. subst v.
    (* xs = (c, au, m c au) :: (au, av, aw) :: rest' *)
    (* Goal: In ((c, au, m c au) :: (au, av, aw) :: rest')
             (append_node_in_paths m c l) *)
    induction l as [|h t IH].
    - inversion Hin_tl.
    - simpl.
      destruct h as [|h0 ht].
      + (* h = []: skip empty paths, recurse *)
        apply IH. destruct Hin_tl as [Hin | Hin].
        * discriminate Hin.
        * exact Hin.
      + (* h = (x0, y0, r0) :: ht *)
        destruct h0 as [[x0 y0] r0].
        destruct Hin_tl as [Hin | Hin].
        * (* rest = h: the prepended path is exactly xs *)
          inversion Hin. subst. left. reflexivity.
        * (* rest in t: recurse *)
          right. apply IH. exact Hin.
  Qed.


  (** Completeness: if a path ending with [(d, d, 1)] satisfies
      source, target, and well-formedness, then it belongs to
      [all_paths_klength] with the appropriate length. *)
  Lemma all_paths_klength_complete 
    {R : Semiring.type} : 
    ∀ (xs : list (Node * Node * R)) 
    (m : @Matrix R) (c d : Node),
    source c (xs ++ [(d, d, 1)]) = true ->
    target d (xs ++ [(d, d, 1)]) = true ->
    well_formed_path_aux m (xs ++ [(d, d, 1)]) ->
    List.In (xs ++ [(d, d, 1)])  
      (all_paths_klength elements m (List.length xs) c d).
  Proof.
    induction xs as [|h ys IH]; intros m c d Hsrc Htgt Hwf.
    - (* xs = []: path is [(d, d, 1)] *)
      simpl in Hsrc. unfold source in Hsrc.
      destruct (fin_eq_dec c d) as [Heq | Hneq]; [| discriminate Hsrc].
      subst c.
      simpl. destruct (fin_eq_dec d d) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
      left. reflexivity.
    - (* xs = h :: ys: path = h :: (ys ++ [(d, d, 1)]) *)
      destruct h as [[c' x] v].
      simpl in Hsrc. unfold source in Hsrc. simpl in Hsrc.
      destruct (fin_eq_dec c c') as [Heq | Hneq]; [| discriminate Hsrc].
      subst c'.
      (* path = (c, x, v) :: (ys ++ [(d, d, 1)]), use definitional equality *)
      set (tail := ys ++ [(d, d, 1)]).
      assert (Htail_eq : ((c, x, v) :: ys) ++ [(d, d, 1)] = (c, x, v) :: tail).
      { cbn. reflexivity. }
      rewrite Htail_eq.
      simpl.
      (* Match the S (length ys) case: append_node_in_paths m c (flat_map ...) *)
      apply (In_append_node_in_paths_rev
        (List.flat_map (fun z => all_paths_klength elements m (length ys) z d) elements)
        m c ((c, x, v) :: tail)).
      + (* source c ((c, x, v) :: tail) = true *)
        unfold source. simpl. destruct (fin_eq_dec c c) as [_|Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
      + (* tl of the path is non-empty: tail ≠ [] *)
        unfold tail. intro H. cbn in H.
        eapply app_eq_nil in H.
        destruct H as (Ha & Hb).
        congruence.
      + (* well_formed_path_aux holds *)
        rewrite <- Htail_eq. exact Hwf.
      + (* tail ∈ flat_map *)
        apply in_flat_map. exists x.
        split.
        * apply elements_complete.
        * (* tail = ys ++ [(d, d, 1)] is in all_paths_klength ... x d *)
          unfold tail. unfold well_formed_path_aux in Hwf. cbn in Hwf.
          destruct Hwf as [Hmv Hwf_tail].
          destruct ys as [|h2 ys'].
          { (* ys = []: tail = [(d, d, 1)] *)
            destruct Hwf_tail as [Heq_x _]. subst x.
            simpl. destruct (fin_eq_dec d d) as [_|Hc]; [|exfalso; apply Hc; reflexivity].
            left. reflexivity. }
          { (* ys = h2 :: ys' *)
            destruct h2 as [[au av] aw].
            destruct Hwf_tail as [Heq_x Hwf_rest]. subst x.
            cbn. eapply IH.
            - unfold source. simpl. destruct (fin_eq_dec au au) as [_|Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
            - rewrite Htail_eq in Htgt. simpl in Htgt. exact Htgt.
            - exact Hwf_rest. }
  Qed.

  (** The measure of a concatenated path equals the product of the
      measures of its parts: [measure (l₁ ++ l₂) = measure l₁ * measure l₂]. *)
  Lemma measure_of_path_app  {R : Semiring.type} : 
    forall (l l₁ l₂ : list (Node * Node * R)), l = (l₁ ++ l₂) -> 
    measure_of_path l = measure_of_path  l₁ * measure_of_path l₂.
  Proof.
    intros * ha. subst.
    induction l₁ as [|((la, lb), lp) lh ihn].
    + cbn. rewrite mul1r. reflexivity.
    + cbn. rewrite ihn. rewrite mulA. reflexivity.
  Qed.

  
  (** Factoring a scalar out of a mapped fold: [Σ w·f(y) = w·Σ f(y)]. *)
  Lemma fold_map_factor {R : Semiring.type} : 
    forall (l : list (list (Node * Node * R))) w,
    fold_right (fun a b => a + b) 0 
      (map (fun y => w * measure_of_path y) l) =
    w * fold_right (fun a b => a + b) 0 
      (map measure_of_path l).
  Proof.
    induction l as [|lh lt ihn]; intro w.
    + cbn. setoid_rewrite mulr0. reflexivity.
    + cbn. setoid_rewrite mulDl.
      f_equal. eapply ihn.
  Qed.

  (** When every path in [l] starts at [a], prepending the edge
      [(c, a, m c a)] to each path multiplies each measure by [m c a]. *)
  Lemma map_measure_append_node {R : Semiring.type} :
    forall (l : list (list (Node * Node * R))) 
    (m : @Matrix R) (c a : Node),
    (forall xs, List.In xs l -> xs <> [] /\ source a xs = true) ->
    (map measure_of_path (append_node_in_paths m c l)) = 
    (map (fun y => m c a * measure_of_path y) l).
  Proof.
    induction l as [|h t IH]; intros m c a Hprop.
    - reflexivity.
    - pose proof (Hprop h (or_introl eq_refl)) as (Hh_ne & Hh_src).
      destruct h as [|h0 ht]; [exfalso; apply Hh_ne; reflexivity | ].
      destruct h0 as [[x y] r].
      (* From source a h = true, we get x = a *)
      unfold source in Hh_src. simpl in Hh_src.
      destruct (fin_eq_dec a x) as [Heq_ax | Hneq]; [| discriminate Hh_src].
      subst x.
      (* Now h = (a, y, r) :: ht *)
      cbn [append_node_in_paths map measure_of_path].
      f_equal.
      apply IH. intros xs Hin. apply Hprop. right. exact Hin.
  Qed.


  (** Specialization of [map_measure_append_node] to paths from
      [all_paths_klength]. *)
  Lemma map_measure_append_node_kpaths {R : Semiring.type} : 
    forall (n : nat) (m : @Matrix R) c d a,
    (map measure_of_path
      (append_node_in_paths m c (all_paths_klength elements m n a d))) = 
    (map (fun y => m c a * measure_of_path y) 
      (all_paths_klength elements m n a d)).
  Proof.
    intros *.
    eapply map_measure_append_node.
    intros * ha.
    eapply non_empty_paths_in_kpath in ha.
    firstorder.
  Qed.


  (** The sum of measures through [append_node_in_paths] distributes
      over list concatenation: [Σ_{l₁++l₂} = Σ_{l₁} + Σ_{l₂}]. *)
  Lemma fold_measure_append_node_app {R : Semiring.type} : 
    forall (l₁ l₂ : list (list (Node * Node * R))) 
    (m : @Matrix R) (c : Node), 
    fold_right (λ u v : R, u + v) 0
      (map measure_of_path (append_node_in_paths m c (l₁ ++ l₂))) 
    = 
    fold_right (λ u v : R, u + v) 0
      (map measure_of_path
        (append_node_in_paths m c l₁ ++ 
        append_node_in_paths m c l₂)).
  Proof.
    induction l₁ as [|la lt ihl]; intros *.
    + cbn. reflexivity.
    + cbn. destruct la as [|((pa, pb), pc) laa].
      ++ eapply ihl.
      ++ cbn. rewrite ihl. reflexivity.
  Qed.

   (** Factoring [m c a] out of the sum of measures of paths from
       [append_node_in_paths] specialized to [all_paths_klength]. *)
  Lemma fold_measure_append_node_kpaths {R : Semiring.type} : 
    forall n (m : @Matrix R) c a d,
    fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
    (map measure_of_path 
      (append_node_in_paths m c (all_paths_klength elements m n a d))) 
    =
    m c a * fold_right (λ b v : R, b + v) 0
      (map measure_of_path (all_paths_klength elements m n a d)).
  Proof.
    intros *.
    rewrite map_measure_append_node_kpaths.
    setoid_rewrite fold_map_factor.
    reflexivity.
  Qed.


  (** Reconstructing a well-formed path from its collected nodes
      recovers the original path: [construct ∘ collect = id]. *)
  Lemma path_collect_construct_id {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) (m : @Matrix R),
    well_formed_path_aux m l -> 
    construct_path_from_nodes (collect_nodes_from_a_path l) m = l.
  Proof.
    induction l as [|((la, lb), lp) lh ihl]; intros m ha.
    - cbn. reflexivity.
    - cbn in ha. destruct ha as [Hmv Hrest].
      destruct lh as [|((pa, pb), pc) lhh].
      + (* lh = []: singleton path *)
        cbn. rewrite <- Hmv. reflexivity.
      + (* lh = (pa, pb, pc) :: lhh *)
        destruct Hrest as [Heq Hwf].
        subst lb. subst lp.
        destruct lhh as [|((qa, qb), qc) lhh'].
        * (* lhh = [] *)
          cbn. unfold well_formed_path_aux in Hwf. cbn in Hwf.
          destruct Hwf as [Hmv' _]. subst pc. reflexivity.
        * (* lhh = (qa, qb, qc) :: lhh' *)
          (* compute the LHS: collect then construct *)
          replace (collect_nodes_from_a_path ((la, pa, m la pa) :: (pa, pb, pc) :: (qa, qb, qc) :: lhh'))
            with (la :: pa :: collect_nodes_from_a_path ((qa, qb, qc) :: lhh'))
            by reflexivity.
          (* Now: construct (la :: pa :: collect_nodes_from_a_path ((qa, qb, qc) :: lhh')) m
                 = (la, pa, m la pa) :: (pa, pb, pc) :: (qa, qb, qc) :: lhh' *)
          simpl (construct_path_from_nodes (la :: pa :: collect_nodes_from_a_path ((qa, qb, qc) :: lhh')) m).
          (* (la, pa, m la pa) :: construct (pa :: collect_nodes_from_a_path ((qa, qb, qc) :: lhh')) m
             = (la, pa, m la pa) :: (pa, pb, pc) :: (qa, qb, qc) :: lhh' *)
          f_equal.
          (* construct (pa :: collect_nodes_from_a_path ((qa, qb, qc) :: lhh')) m
             = (pa, pb, pc) :: (qa, qb, qc) :: lhh' *)
          replace (pa :: collect_nodes_from_a_path ((qa, qb, qc) :: lhh'))
            with (collect_nodes_from_a_path ((pa, pb, pc) :: (qa, qb, qc) :: lhh'))
            by reflexivity.
          apply (ihl m Hwf).
  Qed.


   (** If a concatenated path [ll ++ lr] is well-formed, then both
       [ll] and [lr] are individually well-formed. *)
   Lemma well_formed_path_snoc {R : Semiring.type} : 
    forall ll lr (m : @Matrix R),
    well_formed_path_aux m (ll ++ lr)->
    well_formed_path_aux m ll ∧ 
    well_formed_path_aux m lr .
  Proof.
    induction ll as [|((c, x), v) ll' IH]; intros lr m Hwf.
    - (* ll = [] *)
      cbn in Hwf. split; [exact I | exact Hwf].
    - (* ll = (c, x, v) :: ll' *)
      cbn [app] in Hwf.
      (* Hwf : well_formed_path_aux m ((c, x, v) :: ll' ++ lr) *)
      cbn [well_formed_path_aux] in Hwf.
      destruct Hwf as [Hmv Hconn].
      (* Hmv : m c x = v *)
      (* Hconn : match (ll' ++ lr) with
                 | [] => True
                 | (y, _, _) :: _ => (x = y) ∧ well_formed_path_aux m (ll' ++ lr)
                 end *)
      destruct (ll' ++ lr) as [|h t] eqn:Happ.
      + (* ll' ++ lr = [] → ll' = [] ∧ lr = [] *)
        apply app_eq_nil in Happ. destruct Happ as [Hll' Hlr].
        subst ll' lr.
        cbn. split; [| exact I].
        cbn [well_formed_path_aux]. split; [exact Hmv | exact I].
      + (* ll' ++ lr = h :: t, so ll' ++ lr is non-empty *)
        destruct h as [[y z] w].
        destruct Hconn as [Heq Hwf_tail].
        (* Heq : x = y,  Hwf_tail : well_formed_path_aux m ((y, z, w) :: t) *)
        (* Rewrite using Happ to get the form the IH expects *)
        rewrite <- Happ in Hwf_tail.
        apply IH in Hwf_tail.
        destruct Hwf_tail as [Hwf_ll' Hwf_lr].
        split; [| exact Hwf_lr].
        (* prove well_formed_path_aux m ((c, x, v) :: ll') *)
        cbn [well_formed_path_aux]. split; [exact Hmv |].
        destruct ll' as [|h2 ll''].
        * (* ll' = []: no connection condition needed *)
          exact I.
        * (* ll' = h2 :: ll'' *)
          destruct h2 as [[y2 z2] w2].
          cbn. split.
          -- (* x = y2 *)
             rewrite Heq.
             simpl in Happ.
             inversion Happ. subst. reflexivity.
          -- (* well_formed_path_aux m ll' *)
             exact Hwf_ll'.
  Qed. 

  Lemma keep_collecting_dropping_dual {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) au, 
    l = (keep_collecting au l ++ keep_dropping au l).
  Proof.
    induction l as [|((la, lb), lc) lt ihl]; intros *.
    +reflexivity.
    +cbn. destruct (fin_eq_dec au lb) as [ha | ha].
      ++reflexivity.
      ++cbn. f_equal. now setoid_rewrite <-ihl.
  Qed.

  (** If [elem_path_triple_tail av l] holds, then [l] decomposes as
      [ll ++ [(au, av, aw)] ++ lr] where [(au, av, aw)] is the first
      element whose second component matches [av]. The prefix [ll]
      contains no such element, and [keep_collecting av l] returns
      exactly [ll ++ [(au, av, aw)]]. *)
  Lemma elem_path_triple_tail_true {R : Semiring.type} : 
    forall (l : list (Node * Node * R))  av,
    elem_path_triple_tail av l = true ->
    exists ll au aw lr, 
      l = (ll ++ [(au, av, aw)] ++ lr) /\ 
      elem_path_triple_tail av ll = false /\ 
      (ll ++ [(au, av, aw)]) = (keep_collecting av l).
  Proof.
    induction l as [|((bu, bv), bw) t IH]; intros av Htrue.
    - (* l = [] *)
      cbn in Htrue. discriminate Htrue.
    - (* l = (bu, bv, bw) :: t *)
      cbn [elem_path_triple_tail] in Htrue.
      destruct (fin_eq_dec av bv) as [Heq_av_bv | Hneq_av_bv].
      + (* av = bv: the current element is the first match *)
        subst bv.
        exists [], bu, bw, t.
        cbn [app elem_path_triple_tail keep_collecting].
        destruct (fin_eq_dec av av) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
        split; [reflexivity | split; [reflexivity | reflexivity]].
      + (* av ≠ bv: the first match is in t *)
        apply IH in Htrue.
        destruct Htrue as (ll' & au & aw & lr' & Hl & Hfalse & Hcoll).
        exists ((bu, bv, bw) :: ll'), au, aw, lr'.
        cbn [app elem_path_triple_tail keep_collecting].
        destruct (fin_eq_dec av bv) as [Heq' | _]; [exfalso; apply Hneq_av_bv; exact Heq' | ].
        split.
        * (* equality of lists *)
          rewrite Hl. reflexivity.
        * split.
          -- (* elem_path_triple_tail on the extended prefix *)
             exact Hfalse.
          -- (* keep_collecting equality *)
             rewrite Hcoll. reflexivity.
  Qed.


  (** Simplified form of [elem_path_triple_tail_true]: if
      [elem_path_triple_tail av l] holds, then [keep_collecting av l]
      equals some prefix ending with a matching element. *)
  Lemma elem_path_triple_tail_simp {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) av, 
    elem_path_triple_tail av l = true ->
    exists ll au aw, 
      (ll ++ [(au, av, aw)]) = (keep_collecting av l).
  Proof.
    intros l av H.
    apply elem_path_triple_tail_true in H.
    destruct H as (ll & au & aw & _ & _ & _ & Hcoll).
    exists ll, au, aw. exact Hcoll.
  Qed.


  (** If [elem_path_triple_tail au l] holds, then [keep_collecting au l]
      is non-empty (it contains at least the matching element). *)
  Lemma keep_collecting_nonempty {R : Semiring.type} :
    forall (l : list (Node * Node * R)) au,
    elem_path_triple_tail au l = true ->
    keep_collecting au l <> [].
  Proof.
    intros l au H.
    apply elem_path_triple_tail_true in H.
    destruct H as (ll & au' & aw' & lr & _ & _ & Hcoll).
    rewrite <- Hcoll. intro Hnil.
    apply app_eq_nil in Hnil. destruct Hnil as [_ Hnil'].
    inversion Hnil'.
  Qed.

  (** If [elem_path_triple_tail au l] holds, then the last element of
      [keep_collecting au l] has [au] as its second component, so
      [target au (keep_collecting au l)] holds. *)
  Lemma keep_collecting_target {R : Semiring.type} :
    forall (l : list (Node * Node * R)) au,
    elem_path_triple_tail au l = true ->
    target au (keep_collecting au l) = true.
  Proof.
    intros l au H.
    apply elem_path_triple_tail_true in H.
    destruct H as (ll & au' & aw' & lr & _ & _ & Hcoll).
    rewrite <- Hcoll.
    rewrite target_end. cbn.
    destruct (fin_eq_dec au au) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
  Qed.

  (** When the tail of a cons is non-empty, [target d (h :: t)] reduces
      to [target d t] — the head's second component is skipped. *)
  Lemma target_cons_nonempty_tail {R : Semiring.type} :
    forall (h : Node * Node * R) (t : list (Node * Node * R)) (d : Node),
    t <> [] -> target d (h :: t) = target d t.
  Proof.
    intros h t d Hne.
    destruct h as [[x y] r].
    cbn. destruct t as [|h2 t2]; [exfalso; apply Hne; reflexivity | ].
    reflexivity.
  Qed.

  (** If [elem_path_triple_compute_loop l] returns [Some lc], then
      [lc] is of the form [(au, av, aw) :: lcc] and is a cyclic path
      starting and ending at [au]. *)
  Lemma compute_loop_cycle {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) lc,
    Some lc = elem_path_triple_compute_loop l ->
    exists au av aw lcc, Some ((au, av, aw) :: lcc) = Some lc /\ 
    cyclic_path au lc.
  Proof.
    induction l as [|((au, av), aw) t IH]; intros lc H.
    - (* l = [] *)
      cbn in H. discriminate H.
    - (* l = (au, av, aw) :: t *)
      cbn [elem_path_triple_compute_loop] in H.
      destruct (fin_eq_dec au av) as [Heq_au_av | Hneq_au_av].
      + (* au = av: self-loop [(au, av, aw)] *)
        inversion H. subst lc.
        exists au, av, aw, [].
        split; [reflexivity | ].
        unfold cyclic_path.
        split; [intro Hnil; inversion Hnil | ].
        split.
        * unfold source. cbn.
          destruct (fin_eq_dec au au) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
        * unfold target. cbn.
          destruct (fin_eq_dec au av) as [_ | Hc]; [reflexivity | exfalso; apply Hc; exact Heq_au_av].
      + (* au ≠ av: check tail for a match *)
        destruct (elem_path_triple_tail au t) eqn:Htail.
        * (* match found in tail *)
          inversion H. subst lc.
          exists au, av, aw, (keep_collecting au t).
          split; [reflexivity | ].
          unfold cyclic_path.
          split; [intro Hnil; inversion Hnil | ].
          split.
          -- unfold source. cbn.
             destruct (fin_eq_dec au au) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
          -- assert (Hkeep_ne : keep_collecting au t <> [])
               by (eapply keep_collecting_nonempty; eauto).
             rewrite (target_cons_nonempty_tail (au, av, aw) (keep_collecting au t) au Hkeep_ne).
             apply keep_collecting_target. exact Htail.
        * (* no match in tail: recurse *)
          apply IH in H.
          destruct H as (au' & av' & aw' & lcc' & Hsome & Hcyclic).
          exists au', av', aw', lcc'. split; [exact Hsome | exact Hcyclic].
  Qed.


  (** If [elem_path_triple l] holds (i.e., [l] contains no cycle), then
      [elem_path_triple_compute_loop l] returns [None]. *)
  Lemma elim_path_triple_connect_compute_loop_true_first {R : Semiring.type} : 
    forall (l : list (Node * Node * R)),
    elem_path_triple l = true -> elem_path_triple_compute_loop l = None.
  Proof.
    induction l as [|((au, av), aw) t IH]; intros Htrue.
    - cbn. reflexivity.
    - cbn [elem_path_triple] in Htrue.
      destruct (fin_eq_dec au av) as [Heq | Hneq].
      + (* au = av: contradiction — first conjunct is negb true = false *)
        cbn in Htrue. discriminate Htrue.
      + (* au ≠ av *)
        cbn in Htrue. (* negb false → true *)
        cbn in Htrue. (* true && ... → ... *)
        destruct (elem_path_triple_tail au t) eqn:Htail.
        * (* Htail = true: contradiction — second conjunct is negb true = false *)
          cbn in Htrue. discriminate Htrue.
        * (* Htail = false *)
          cbn in Htrue. (* negb false → true, then true && ... → ... *)
          (* Htrue : elem_path_triple t = true *)
          cbn [elem_path_triple_compute_loop].
          destruct (fin_eq_dec au av) as [Heq' | _].
          { exfalso. apply Hneq. exact Heq'. }
          rewrite Htail. cbn.
          apply IH. exact Htrue.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_true_second {R : Semiring.type} : 
    forall (l : list (Node * Node * R)),
    elem_path_triple_compute_loop l = None -> 
    elem_path_triple l = true.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + intros He; simpl in He.
      simpl. reflexivity.
    + intros He; simpl in * |- *.
      case (fin_eq_dec au av) eqn:Hb.
      ++congruence.
      ++simpl. case (elem_path_triple_tail au l) eqn:Hbe.
        -congruence.
        -simpl. apply IHl; assumption.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_true_none_eqv {R : Semiring.type} : 
    forall (l : list (Node * Node * R)),
    elem_path_triple_compute_loop l = None <-> elem_path_triple l = true.
  Proof using Type.
    intros ?; split; intro H.
    apply elim_path_triple_connect_compute_loop_true_second; assumption.
    apply elim_path_triple_connect_compute_loop_true_first; assumption.
  Qed.


  (** If [elem_path_triple l] is false (i.e., [l] contains a cycle),
      then [elem_path_triple_compute_loop l] returns [Some lc] where
      [lc] is a cyclic path of the form [(au, av, aw) :: lcc]. *)
  Lemma elim_path_triple_connect_compute_loop_false_first {R : Semiring.type} : 
    forall (l : list (Node * Node * R)),
    elem_path_triple l = false -> 
    exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path au lc.
  Proof.
    induction l as [|((au, av), aw) t IH]; intros Hfalse.
    - (* l = [] *)
      cbn in Hfalse. discriminate Hfalse.
    - (* l = (au, av, aw) :: t *)
      cbn [elem_path_triple] in Hfalse.
      destruct (fin_eq_dec au av) as [Heq | Hneq].
      + (* Case 1: au = av — self-loop.  First conjunct is negb true = false,
           so elem_path_triple = false regardless of the rest. *)
        cbn [elem_path_triple_compute_loop].
        destruct (fin_eq_dec au av) as [_ | Hc]; [| exfalso; apply Hc; exact Heq].
        exists au, av, aw, [(au, av, aw)], [].
        split; [reflexivity | ].
        split; [reflexivity | ].
        unfold cyclic_path.
        split; [intro Hnil; inversion Hnil | ].
        split.
        * unfold source. cbn.
          destruct (fin_eq_dec au au) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
        * unfold target. cbn.
          destruct (fin_eq_dec au av) as [_ | Hc]; [reflexivity | exfalso; apply Hc; exact Heq].
      + (* au ≠ av: first conjunct is negb false = true.
           Hfalse reduces to (negb (elem_path_triple_tail au t) && elem_path_triple t) = false *)
        cbn in Hfalse.
        destruct (elem_path_triple_tail au t) eqn:Htail.
        * (* Case 2: elem_path_triple_tail au t = true.
             Second conjunct is negb true = false, so the whole expression is false. *)
          cbn in Hfalse. (* Hfalse becomes irrelevant (already used the destruct) *)
          cbn [elem_path_triple_compute_loop].
          destruct (fin_eq_dec au av) as [Heq' | _]; [exfalso; apply Hneq; exact Heq' | ].
          rewrite Htail. cbn.
          exists au, av, aw, ((au, av, aw) :: keep_collecting au t), (keep_collecting au t).
          split; [reflexivity | ].
          split; [reflexivity | ].
          (* cyclic_path au ((au, av, aw) :: keep_collecting au t) *)
          unfold cyclic_path.
          split; [intro Hnil; inversion Hnil | ].
          split.
          -- unfold source. cbn.
             destruct (fin_eq_dec au au) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
          -- assert (Hkeep_ne : keep_collecting au t <> [])
               by (eapply keep_collecting_nonempty; eauto).
             rewrite (target_cons_nonempty_tail (au, av, aw) (keep_collecting au t) au Hkeep_ne).
             apply keep_collecting_target. exact Htail.
        * (* Case 3: elem_path_triple_tail au t = false.
             Second conjunct is negb false = true.
             Hfalse reduces to (true && elem_path_triple t) = false,
             hence elem_path_triple t = false. *)
          cbn in Hfalse. (* true && ... → ... *)
          (* Hfalse : elem_path_triple t = false *)
          apply IH in Hfalse.
          destruct Hfalse as (au' & av' & aw' & lc' & lcc' & Hsome & Hlc & Hcyclic).
          cbn [elem_path_triple_compute_loop].
          destruct (fin_eq_dec au av) as [Heq' | _]; [exfalso; apply Hneq; exact Heq' | ].
          rewrite Htail. cbn.
          exists au', av', aw', lc', lcc'.
          split; [exact Hsome | split; [exact Hlc | exact Hcyclic]].
  Qed.


  Lemma elim_path_triple_connect_compute_loop_false_second {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) lc, 
    Some lc = elem_path_triple_compute_loop l ->
    elem_path_triple l = false.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + intros ? Hs; simpl in Hs;
      congruence.
    + intros ? Hs; simpl in * |- *.
      case (fin_eq_dec au av) eqn:Ha.
      simpl. reflexivity.
      case (elem_path_triple_tail au l) eqn:Hb.
      simpl. reflexivity.
      simpl.
      eapply IHl; exact Hs.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_false_eqv {R : Semiring.type} : 
    forall (l : list (Node * Node * R)),
    elem_path_triple l = false <-> 
    exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path au lc.
  Proof.
    intros *; split; intros He.
    apply  elim_path_triple_connect_compute_loop_false_first; assumption.
    destruct He as (au & av & aw & lc & lcc & Hs & Hlcc & Hc).
    eapply elim_path_triple_connect_compute_loop_false_second; 
    exact Hs.
  Qed.


  Lemma elem_path_triple_compute_loop_triple_middle_element {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) ll lm lr, 
    (ll, lm, lr) = elem_path_triple_compute_loop_triple l ->
    lm = elem_path_triple_compute_loop l.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + intros ? ? ? Hl; simpl in Hl; simpl;
      inversion Hl; subst; reflexivity.
    + intros ? ? ? Hl.
      simpl in * |- *.
      case (fin_eq_dec au av) eqn:Ha.
      inversion Hl; subst; reflexivity.
      case (elem_path_triple_tail au l) eqn:Hb.
      inversion Hl; subst; reflexivity.
      destruct (elem_path_triple_compute_loop_triple l) as ((al, bl), cl).
      inversion Hl; subst; clear Hl.
      eapply IHl.
      reflexivity.
  Qed.

  (** [elem_path_triple_compute_loop_triple l] splits [l] into
      [(fp, opt, tp)] where [l = fp ++ tp] when [opt = None], and
      [l = fp ++ sp ++ tp] when [opt = Some sp]. *)
  Lemma elem_path_triple_compute_loop_triple_combined_list {R : Semiring.type} : 
    forall (l : list (Node * Node * R)),
    match elem_path_triple_compute_loop_triple l with
    | (fp, None, tp) => l = (fp ++ tp)
    | (fp, Some sp, tp) => l = (fp ++ sp ++ tp)
    end. 
  Proof.
    induction l as [|((au, av), aw) t IH].
    - cbn. reflexivity.
    - cbn [elem_path_triple_compute_loop_triple].
      destruct (fin_eq_dec au av) as [Heq | Hneq].
      + (* au = av: self-loop.  Result is ([], Some [(au, av, aw)], t) *)
        cbn. reflexivity.
      + (* au ≠ av *)
        destruct (elem_path_triple_tail au t) eqn:Htail.
        * (* tail match: result is ([], Some ((au, av, aw) :: keep_collecting au t),
             keep_dropping au t) *)
          cbn. f_equal. apply (keep_collecting_dropping_dual t au).
        * (* no tail match: recurse.
             Result is ((au, av, aw) :: fp, sp, tp) where (fp, sp, tp) = IH t *)
          destruct (elem_path_triple_compute_loop_triple t) as [[fp sp_opt] tp].
          simpl in IH.
          destruct sp_opt as [sp | ].
          -- cbn. f_equal. apply IH.
          -- cbn. f_equal. apply IH.
  Qed.


  (** If no element in [l] has second component [au], and [l = ll ++ lr],
      then neither [ll] nor [lr] contains such an element either. *)
  Lemma elem_path_triple_tail_false {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) ll lr au, 
    elem_path_triple_tail au l = false -> l = ll ++ lr ->
    elem_path_triple_tail au ll = false /\
    elem_path_triple_tail au lr = false.
  Proof.
    intros l ll lr au Hfalse Heq. subst l.
    revert lr Hfalse.
    induction ll as [|((bu, bv), bw) ll' IH]; intros lr Hfalse.
    - (* ll = [] *)
      cbn. split; [reflexivity | exact Hfalse].
    - (* ll = (bu, bv, bw) :: ll' *)
      cbn [app] in Hfalse.
      cbn [elem_path_triple_tail] in Hfalse.
      destruct (fin_eq_dec au bv) as [Heq_au_bv | Hneq_au_bv].
      + (* au = bv: then the result would be true, contradiction *)
        discriminate Hfalse.
      + (* au ≠ bv: the result depends on the tail *)
        apply IH in Hfalse as [Hll' Hlr].
        split.
        * cbn [elem_path_triple_tail].
          destruct (fin_eq_dec au bv) as [Heq' | _]; [exfalso; apply Hneq_au_bv; exact Heq' | exact Hll'].
        * exact Hlr.
  Qed.

  Lemma length_leq_lt {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) ,
    l <> [] -> (List.length l) < List.length (collect_nodes_from_a_path l).
  Proof.
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
 


  Lemma length_collect_node_gen {R : Semiring.type} :
    forall (c : list Node) 
    (l : list (Node * Node * R)),
    c <> [] ->  
    (List.length c <= List.length l)%nat ->
    (List.length c < List.length (collect_nodes_from_a_path l)).
  Proof.
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



  (** If a well-formed path [l] has an element whose second component
      matches [a] (per [elem_path_triple_tail]), then [a] appears in
      the node list collected by [collect_nodes_from_a_path]. *)
  Lemma elem_path_triple_tail_in_list {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) m a,
    well_formed_path_aux m l -> elem_path_triple_tail a l = true ->
    List.In a (collect_nodes_from_a_path l).
  Proof.
    induction l as [|((bu, bv), bw) t IH]; intros m a Hwf Htail.
    - (* l = [] *)
      cbn in Htail. discriminate Htail.
    - (* l = (bu, bv, bw) :: t *)
      cbn [elem_path_triple_tail] in Htail.
      destruct (fin_eq_dec a bv) as [Heq_abv | Hneq_abv].
      + (* a = bv: the current element's second component matches *)
        subst a.
        cbn [well_formed_path_aux] in Hwf.
        destruct Hwf as [Hmv Hrest].
        destruct t as [|((cu, cv), cw) t'].
        * (* t = []: collect_nodes returns [bu; bv] *)
          cbn [collect_nodes_from_a_path]. right. left. reflexivity.
        * (* t ≠ []: from well-formedness, bv = cu, so bv is the head of the tail's collection *)
          destruct Hrest as [Heq_bv_cu Hwf_t].
          subst cu.
          cbn [collect_nodes_from_a_path].
          right. cbn [collect_nodes_from_a_path].
          destruct t' as [|h t'']; [left; reflexivity | left; reflexivity].
      + (* a ≠ bv: the match must be in t *)
        cbn [well_formed_path_aux] in Hwf.
        destruct Hwf as [Hmv Hrest].
        destruct t as [|((cu, cv), cw) t'].
        * (* t = []: elem_path_triple_tail a [] = false, contradiction *)
          cbn in Htail. discriminate Htail.
        * (* t ≠ []: from well-formedness, get well_formed_path_aux m t *)
          destruct Hrest as [Heq_bv_cu Hwf_t].
          cbn [collect_nodes_from_a_path].
          apply IH with (m := m) in Htail; [| exact Hwf_t].
          right. exact Htail.
  Qed.


  (** If [bl = (bu, bv, bw) :: l] is well-formed, [au ≠ bu], and
      [elem_path_triple_tail au bl = false], then [au] does not appear
      in [collect_nodes_from_a_path bl]. *)
  Lemma elem_path_false_rewrite {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) bl bu bv bw m au, 
    bl = (bu, bv, bw) :: l -> au <> bu ->
    well_formed_path_aux m bl -> elem_path_triple_tail au bl = false ->
    ~List.In au (collect_nodes_from_a_path bl).
  Proof.
    intros l bl bu bv bw m au Heq Hneq Hwf Htail.
    subst bl.
    revert bu bv bw Hneq Hwf Htail.
    induction l as [|((cu, cv), cw) t IH]; intros bu bv bw Hneq Hwf Htail.
    - (* l = [] *)
      cbn [elem_path_triple_tail] in Htail.
      destruct (fin_eq_dec au bv) as [Heq_au_bv | Hneq_au_bv].
      + discriminate Htail.
      + cbn [collect_nodes_from_a_path].
        intro Hin. destruct Hin as [Hin | Hin].
        * apply Hneq. symmetry. exact Hin.
        * destruct Hin as [Hin | Hin].
          -- apply Hneq_au_bv. symmetry. exact Hin.
          -- inversion Hin.
    - (* l = (cu, cv, cw) :: t *)
      cbn [well_formed_path_aux] in Hwf.
      destruct Hwf as [Hmv Hrest].
      destruct Hrest as [Heq_bv_cu Hwf_t].
      subst cu. (* now l = (bv, cv, cw) :: t *)
      cbn [elem_path_triple_tail] in Htail.
      destruct (fin_eq_dec au bv) as [Heq_au_bv | Hneq_au_bv].
      + discriminate Htail.
      + (* Htail : elem_path_triple_tail au ((bv, cv, cw) :: t) = false *)
        cbn [collect_nodes_from_a_path].
        intro Hin. destruct Hin as [Hin | Hin].
        * apply Hneq. symmetry. exact Hin.
        * exact (IH bv cv cw Hneq_au_bv Hwf_t Htail Hin).
  Qed.
  

  Lemma elem_path_collect_node_from_path_second {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) (m : @Matrix R), 
    well_formed_path_aux m l -> NoDup (collect_nodes_from_a_path l) -> 
    elem_path_triple l = true.
  Proof.
    induction l as [|((au, av), aw) t IH]; intros m Hwf Hnodup.
    - cbn. reflexivity.
    - cbn [well_formed_path_aux] in Hwf.
      destruct Hwf as [Hmv Hrest].
      destruct t as [|((cu, cv), cw) t'].
      (* t = [] *)
      cbn [collect_nodes_from_a_path elem_path_triple] in *.
      destruct (fin_eq_dec au av) as [Heq | Hneq].
      subst av. simpl in Hnodup. inversion Hnodup.
      cbn in H1 |- *. unfold not in H1.
      specialize (H1 (or_introl eq_refl)). 
      inversion H1.
      cbn. reflexivity. 
      (* t = (cu, cv, cw) :: t' *)
      destruct Hrest as [Heq_av_cu Hwf_t]. subst cu.
      destruct t' as [|h t''].
      (* t' = []: collected nodes are [au; av; cv] *)
      cbn [collect_nodes_from_a_path] in Hnodup.
      inversion Hnodup.
      cbn [elem_path_triple].
      destruct (fin_eq_dec au av) as [Heq_au_av | Hneq_au_av].
      subst av.
      unfold not in H1. specialize (H1 (or_introl eq_refl)). inversion H1.
      change (negb false) with true.
      rewrite Bool.andb_true_l.
      destruct (elem_path_triple_tail au [(av, cv, cw)]) eqn:Htail.
      { assert (Hin : List.In au (collect_nodes_from_a_path [(av, cv, cw)])).
        { apply (elem_path_triple_tail_in_list [(av, cv, cw)] m au Hwf_t). exact Htail. }
        cbn [collect_nodes_from_a_path] in Hin.
        exfalso. unfold not in H1. apply H1. exact Hin. }
      cbn [negb andb].
      apply IH with (m := m); [exact Hwf_t | exact H2].
      (* t' = h :: t'' *)
      cbn [collect_nodes_from_a_path] in Hnodup.
      inversion Hnodup.
      cbn [elem_path_triple].
      destruct (fin_eq_dec au av) as [Heq_au_av | Hneq_au_av].
      subst av.
      unfold not in H1. specialize (H1 (or_introl eq_refl)). inversion H1.
      change (negb false) with true.
      rewrite Bool.andb_true_l.
      destruct (elem_path_triple_tail au ((av, cv, cw) :: h :: t'')) eqn:Htail.
      { assert (Hin : List.In au (collect_nodes_from_a_path ((av, cv, cw) :: h :: t''))).
        { apply (elem_path_triple_tail_in_list ((av, cv, cw) :: h :: t'') m au Hwf_t). exact Htail. }
        cbn [collect_nodes_from_a_path] in Hin.
        exfalso. unfold not in H1. apply H1. exact Hin. }
      cbn [negb andb].
      apply IH with (m := m); [exact Hwf_t | exact H2].
  Qed.


  (** If a node [a] appears in the collected nodes of a well-formed path
      starting at [b], then either [a = b] or [a] appears as some
      element's second component. *)
  Lemma In_collect_nodes_implies_head_or_tail {R : Semiring.type} :
    forall (l : list (Node * Node * R)) (m : @Matrix R) (a b c : Node) (w : R),
      well_formed_path_aux m ((b, c, w) :: l) ->
      List.In a (collect_nodes_from_a_path ((b, c, w) :: l)) ->
      a = b \/ elem_path_triple_tail a ((b, c, w) :: l) = true.
  Proof.
    induction l as [|((du, dv), dw) l' IH]; intros m a b c w Hwf Hin.
    - (* l = [] *)
      cbn [collect_nodes_from_a_path] in Hin.
      simpl in Hin.
      destruct Hin as [Heq | Hin'].
      + subst a. left. reflexivity.
      + simpl in Hin'.
        destruct Hin' as [Heq | []].
        subst a. right. cbn [elem_path_triple_tail].
        destruct (fin_eq_dec c c) as [_ | Hneq]; [reflexivity | exfalso; apply Hneq; reflexivity].
    - (* l = (du, dv, dw) :: l' *)
      cbn [well_formed_path_aux] in Hwf.
      destruct Hwf as [Hmv [Heq_c_du Hwf_l]].
      subst du. (* l = (c, dv, dw) :: l' *)
      cbn [collect_nodes_from_a_path] in Hin.
      destruct Hin as [Heq | Hin].
      + subst a. left. reflexivity.
      + apply (IH m a c dv dw) in Hin; [| exact Hwf_l].
        destruct Hin as [Heq_ac | Htail].
        * subst a. right. cbn [elem_path_triple_tail].
          destruct (fin_eq_dec c c) as [_ | Hneq]; [reflexivity | exfalso; apply Hneq; reflexivity].
        * right. cbn [elem_path_triple_tail].
          destruct (fin_eq_dec a c) as [_ | _]; [reflexivity | exact Htail].
  Qed.

  Lemma not_NoDup_collect_implies_elem_path_triple_false {R : Semiring.type} :
    ∀ (l : list (Node * Node * R)) (m : @Matrix R), 
      well_formed_path_aux m l -> ~NoDup(collect_nodes_from_a_path l) -> 
      elem_path_triple l = false.
  Proof.
    induction l as [|((au, av), aw) t IH]; intros m Hwf Hnotnodup.
    - (* l = [] *)
      cbn in Hnotnodup. exfalso. apply Hnotnodup. constructor.
    - (* l = (au, av, aw) :: t *)
      cbn [well_formed_path_aux] in Hwf.
      destruct Hwf as [Hmv Hrest].
      cbn [elem_path_triple collect_nodes_from_a_path].
      destruct (fin_eq_dec au av) as [Heq_au_av | Hneq_au_av].
      + (* au = av: first conjunct is false *)
        cbn. reflexivity.
      + (* au ≠ av: first conjunct = true *)
        cbn.
        destruct t as [|((cu, cv), cw) t'].
        * (* t = []: collected nodes = [au; av], and au ≠ av, so NoDup holds — contradiction *)
          cbn in Hnotnodup.
          exfalso. apply Hnotnodup.
          apply NoDup_cons.
          -- intro Hin. simpl in Hin.
             destruct Hin as [Heq | []].
             apply Hneq_au_av. symmetry. exact Heq.
          -- constructor; [intro Hin; inversion Hin | constructor].
        * (* t = (cu, cv, cw) :: t' *)
          cbn in Hnotnodup.
          destruct Hrest as [Heq_av_cu Hwf_t]. subst cu.
          (* t = (av, cv, cw) :: t' *)
          (* Decision: is au in the tail's collected nodes? *)
          destruct (in_dec fin_eq_dec au (collect_nodes_from_a_path ((av, cv, cw) :: t'))) as [Hin | Hnin].
          -- (* au ∈ collect_nodes tail → elem_path_triple_tail au t = true *)
             pose proof (In_collect_nodes_implies_head_or_tail t' m au av cv cw Hwf_t Hin)
               as [Heq_au_av' | Htail].
             ++ exfalso. apply Hneq_au_av. exact Heq_au_av'.
             ++ rewrite Htail. cbn. reflexivity.
          -- (* au ∉ tail: ~NoDup must come from the tail *)
             assert (Hnotnd_tail : ~ NoDup (collect_nodes_from_a_path ((av, cv, cw) :: t'))).
             { intro Hnd. apply Hnotnodup. apply NoDup_cons; [exact Hnin | exact Hnd]. }
             apply (IH m) in Hnotnd_tail; [| exact Hwf_t].
             rewrite Hnotnd_tail. rewrite Bool.andb_false_r. reflexivity.
  Qed. 


  

  (** If a well-formed, acyclic path [l] is covered by a shorter list [c],
      then by the pigeonhole principle [l] must actually contain a cycle. *)
  Lemma all_paths_in_klength_paths_cycle  {R : Semiring.type} : 
    forall (c : list Node)
    (l : list (Node * Node * R)) (m : @Matrix R),
    well_formed_path_aux m l ->
    covers (collect_nodes_from_a_path l) c -> 
    (List.length c < List.length (collect_nodes_from_a_path l)) ->
    elem_path_triple l = false.
  Proof.
    intros * ha hb hc.
    eapply not_NoDup_collect_implies_elem_path_triple_false.
    exact ha.
    intro hd.
    destruct (@covers_pigenhole Node fin_eq_dec _ _ hb hc) as 
    (a & l₁ & l₂ & l₃ & he).
    rewrite he in hd. cbn in hd.
    eapply NoDup_remove_2 in hd.
    eapply hd. rewrite app_assoc.
    remember (l₁ ++ l₂) as la.
    eapply in_elt.
  Qed.


   (* if you give me path of length >= finN then there is loop *)
  Lemma all_paths_in_klength_paths_cycle_elements  {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) (m : @Matrix R),
    (List.length (@elements Node) <= List.length l) ->
    well_formed_path_aux m l ->
    exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path au lc.
  Proof.
    intros ? ? Hfin Hw.
    assert(ha : @elements Node <> []).
    destruct elements eqn:ha. pose proof 
    (@elements_two_or_more Node) as hb.
    rewrite ha in hb. cbn in hb. nia.
    intro hb. inversion hb.
    pose proof (@length_collect_node_gen R elements
      l ha Hfin) as Hf.
    pose proof covers_list_elem elements 
      (collect_nodes_from_a_path l) elements_complete as Hcov.
    pose proof all_paths_in_klength_paths_cycle
      elements l m Hw Hcov Hf as Hwt.
    eapply elim_path_triple_connect_compute_loop_false_first;
    try assumption.
  Qed.


  Lemma triple_compute_connect_with_triple_elem_forward 
    {R : Semiring.type} : forall (l : list (Node * Node * R)), 
    elem_path_triple l = false ->
    exists ll lm lr, (ll, Some lm, lr) = 
    elem_path_triple_compute_loop_triple l.
  Proof.
    induction l as [|((au, av), aw) l].
    + simpl;
      intros Ha.
      congruence.
    + simpl.
      intros Ha.
      case (fin_eq_dec au av) eqn:Hauv.
      eauto.
      simpl in Ha.
      case (elem_path_triple_tail au l) eqn:Hel.
      eauto.
      simpl in Ha.
      destruct (IHl Ha) as 
      (ll & lm & lr & Hb).
      destruct (elem_path_triple_compute_loop_triple l) as 
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


   Lemma triple_compute_connect_with_triple_elem_backward 
    {R : Semiring.type} : forall (l : list (Node * Node * R)) ll lm lr, 
    (ll, Some lm, lr) = 
    elem_path_triple_compute_loop_triple l ->
    elem_path_triple l = false.
  Proof using Type.
    induction l as [|((au, av), aw) l].
    + simpl.
      intros * Ha.
      congruence.
    + simpl.
      intros * Ha.
      case (fin_eq_dec au av) eqn:Hauv.
      reflexivity.
      case (elem_path_triple_tail au l) eqn:Hel.
      reflexivity.
      simpl.
      destruct (elem_path_triple_compute_loop_triple l) as 
      ((bu, bv), bw).
      inversion Ha;
      subst; clear Ha.
      exact (IHl bu lm bw eq_refl).
  Qed.
      

  Lemma triple_compute_connect_with_triple_elem {R : Semiring.type} : forall (l : list (Node * Node * R)),
    elem_path_triple l = false <->
    exists ll lm lr, (ll, Some lm, lr) = 
    elem_path_triple_compute_loop_triple l.
  Proof.
    intros ?; 
    split;
    intros He.
    eapply triple_compute_connect_with_triple_elem_forward;
    try assumption.
    destruct He as (ll & lm & lr & Hal).
    eapply triple_compute_connect_with_triple_elem_backward;
    exact Hal.
  Qed.


  Lemma triple_compute_connect_with_triple_elem_stronger 
    {R : Semiring.type} : forall (l : list (Node * Node * R)),
    elem_path_triple l = false ->
    exists ll au av aw lm lr, 
      (ll, Some ((au, av, aw) :: lm), lr) = 
      elem_path_triple_compute_loop_triple l /\ 
      cyclic_path au ((au, av, aw) :: lm) /\ 
      elem_path_triple ll = true /\ 
      l = (ll ++  ((au, av, aw) :: lm) ++ lr).
  Proof.
    induction l as [|((au, av), aw) t IH]; intros Hfalse.
    - cbn in Hfalse. discriminate Hfalse.
    - cbn [elem_path_triple] in Hfalse.
      cbn [elem_path_triple_compute_loop_triple].
      destruct (fin_eq_dec au av) as [Heq_au_av | Hneq_au_av].
      + (* au = av: self-loop *)
        exists [], au, av, aw, [], t.
        assert (Hcyc : cyclic_path au [(au, av, aw)]).
        { unfold cyclic_path.
          split; [intro Hnil; inversion Hnil | ].
          split.
          - unfold source. cbn.
            destruct (fin_eq_dec au au) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
          - unfold target. cbn.
            destruct (fin_eq_dec au av) as [_ | Hc]; [reflexivity | exfalso; apply Hc; exact Heq_au_av]. }
        split; [reflexivity | ].
        split; [exact Hcyc | ].
        split; [cbn; reflexivity | ].
        cbn. reflexivity.
      + (* au ≠ av *)
        cbn in Hfalse.
        destruct (elem_path_triple_tail au t) eqn:Htail.
        * (* Htail = true: cycle found starting at (au, av, aw) *)
          cbn in Hfalse.
          exists [], au, av, aw, (keep_collecting au t), (keep_dropping au t).
          assert (Hcyc : cyclic_path au ((au, av, aw) :: keep_collecting au t)).
          { assert (Heq_loop : Some ((au, av, aw) :: keep_collecting au t) =
              elem_path_triple_compute_loop ((au, av, aw) :: t)).
            { cbn [elem_path_triple_compute_loop].
              destruct (fin_eq_dec au av) as [Heq' | _]; [exfalso; apply Hneq_au_av; exact Heq' | ].
              rewrite Htail. reflexivity. }
            apply compute_loop_cycle in Heq_loop.
            destruct Heq_loop as (au' & av' & aw' & lcc' & Hsome & Hc).
            inversion Hsome. subst. exact Hc. }
          split; [reflexivity | ].
          split; [exact Hcyc | ].
          split; [cbn; reflexivity | ].
          cbn. f_equal. apply (keep_collecting_dropping_dual t au).
        * (* Htail = false: cycle is in the tail *)
          cbn in Hfalse.
          apply IH in Hfalse
            as (ll' & au' & av' & aw' & lm' & lr' & Htriple_eq & Hcyc & Helem_ll' & Hl_eq).
          rewrite <- Htriple_eq.
          exists ((au, av, aw) :: ll'), au', av', aw', lm', lr'.
          assert (Helem_cons : elem_path_triple ((au, av, aw) :: ll') = true).
          { cbn [elem_path_triple].
            destruct (fin_eq_dec au av) as [Heq' | _]; [exfalso; apply Hneq_au_av; exact Heq' | ].
            cbn.
            pose proof (elem_path_triple_tail_false t ll' (((au', av', aw') :: lm') ++ lr') au Htail Hl_eq)
              as [Htail_ll' _].
            rewrite Htail_ll'. cbn. exact Helem_ll'. }
          split; [reflexivity | ].
          split; [exact Hcyc | ].
          split; [exact Helem_cons | ].
          cbn. rewrite Hl_eq. reflexivity.
  Qed.


  (* if you give me path of length >= finN then there is loop *)
  Lemma all_paths_in_klength_paths_cycle_finN_stronger 
    {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) (m : @Matrix R),
    (List.length (@elements Node) <= List.length l)%nat ->
    well_formed_path_aux m l ->
    exists ll au av aw lm lr, 
    (ll, Some ((au, av, aw) :: lm), lr) = 
    elem_path_triple_compute_loop_triple l /\ 
    cyclic_path au ((au, av, aw) :: lm) /\  (* Loop so we can remove this *)
    elem_path_triple  ll = true /\ (* Elementry Path *)
    l = (ll ++  ((au, av, aw) :: lm) ++ lr). 
    (* lr is the rest of path *)
  Proof.
    intros ? ? Hfin Hw.
    assert(ha : @elements Node <> []).
    destruct elements eqn:ha. pose proof 
    (@elements_two_or_more Node) as hb.
    rewrite ha in hb. cbn in hb. nia.
    intro hb. inversion hb.
    pose proof length_collect_node_gen elements
      l ha Hfin as Hf.
    pose proof covers_list_elem elements
      (collect_nodes_from_a_path l) elements_complete as Hcov.
    pose proof all_paths_in_klength_paths_cycle
      elements l m Hw Hcov Hf as Hwt.
    eapply triple_compute_connect_with_triple_elem_stronger.
    exact Hwt.
  Qed.



  Definition zwf {R : Semiring.type} (x y : list (Node * Node * R)) := 
      (List.length x < List.length y).

  Lemma zwf_well_founded {R : Semiring.type} : well_founded 
  (@zwf R).
  Proof.
    exact (Wf_nat.well_founded_ltof _ 
      (fun x => List.length x)).
  Defined.


  (* easy proof List.length finN <= List.length l -> loop *)
  Lemma elem_path_length {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) m, 
    elem_path_triple l = true ->
    well_formed_path_aux m l  -> 
    (List.length l < List.length (@elements Node)).
  Proof.
    intros l m He Hw.
    assert (Hwt : (length l < length (@elements Node))%nat \/ 
    (length (@elements Node) <= length l)%nat).
    nia.
    destruct Hwt as [Hwt | Hwt].
    exact Hwt.
    assert(ha : @elements Node <> []).
    destruct elements eqn:ha. pose proof 
    (@elements_two_or_more Node) as hb.
    rewrite ha in hb. cbn in hb. nia.
    intro hb. inversion hb.
    pose proof length_collect_node_gen elements 
    l ha Hwt as Hf.
    pose proof covers_list_elem elements 
      (collect_nodes_from_a_path l) elements_complete as Hcov.
    pose proof all_paths_in_klength_paths_cycle
      elements l m Hw Hcov Hf as Hat.
    rewrite Hat in He.
    congruence.
  Qed.


  Lemma reduce_path_into_elem_path {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) m,
    well_formed_path_aux m l  ->
    exists lm, 
      well_formed_path_aux m lm  /\ 
      elem_path_triple lm = true.
  Proof.
    intros l.
    induction (zwf_well_founded l) as [l Hf IHl].
    unfold zwf in * |- *.
    intros m Hw.
    destruct (elem_path_triple l) eqn:He.
    - (* l is already acyclic *)
      exists l. split; [exact Hw | exact He].
    - (* l contains a cycle: extract the acyclic prefix *)
      apply triple_compute_connect_with_triple_elem_stronger in He
        as (ll & au & av & aw & loop & lr & _ & _ & Helem_ll & Hl_eq).
      rewrite Hl_eq in Hw.
      apply well_formed_path_snoc in Hw as [Hwf_ll _].
      exists ll. split; [exact Hwf_ll | exact Helem_ll].
  Qed.



  (* Every well formed path can be reduced into 
      an well formed elementry path, i.e., path 
      without loop and it's length < finN *)
  Lemma reduce_path_into_elem_path_gen {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) m,
    well_formed_path_aux m l ->
    exists lm, 
      well_formed_path_aux m lm /\ 
      elem_path_triple lm = true /\ 
      (List.length lm < List.length (@elements Node))%nat.
  Proof.
    intros ? ? Hw.
    destruct (reduce_path_into_elem_path l m Hw) 
    as (lm & Hwa & Hwe).
    pose proof (elem_path_length lm m Hwe Hwa) as Hp.
    exists lm.
    repeat split; try assumption.
  Qed.


  Lemma well_founded_rev {R : Semiring.type} : 
    forall lm aut avt awt au av aw cut cvt cwt lr (m : @Matrix R),
    well_formed_path_aux m
      ([(aut, avt, awt)] ++ ((au, av, aw) :: lm) ++ (cut, cvt, cwt) :: lr) ->
    cyclic_path au ((au, av, aw) :: lm) ->
    avt = cut.
  Proof.
    intros lm aut avt awt au av aw cut cvt cwt lr m Hwf Hcyc.
    unfold cyclic_path in Hcyc.
    destruct Hcyc as [Hne [Hsrc Htgt]].
    (* Decompose the well-formedness to get avt = au *)
    cbn [app] in Hwf.
    cbn [well_formed_path_aux] in Hwf.
    destruct Hwf as [Hmv1 Hconn1].
    destruct ((au, av, aw) :: lm ++ (cut, cvt, cwt) :: lr) as [|h t] eqn:Heq_rest.
    { (* cons can never be nil *) discriminate Heq_rest. }
    destruct h as [[y z] w].
    destruct Hconn1 as [Heq_avt_y Hwf_tail].
    inversion Heq_rest. subst y z w t. clear Heq_rest.
    (* Heq_avt_y: avt = au,  Hwf_tail: well_formed ((au, av, aw) :: lm ++ (cut, cvt, cwt) :: lr) *)
    subst avt. (* goal: au = cut *)
    (* Inner induction: for any target d and head (x,y,w), if the path is well-formed
       and target d finds d at the end, then d must equal cut (the next node). *)
    pose (P := fun (lm' : list (Node * Node * R)) =>
      forall (d x y : Node) (w : R),
        well_formed_path_aux m ((x, y, w) :: lm' ++ (cut, cvt, cwt) :: lr) ->
        target d ((x, y, w) :: lm') = true ->
        d = cut).
    assert (Hind : forall lm', P lm').
    { induction lm' as [|((xu, xv), xw) lm'' IH]; unfold P.
      - (* lm' = [] *)
        intros d x y w Hwf' Htgt'.
        cbn [app] in Hwf'.
        cbn [well_formed_path_aux] in Hwf'.
        destruct Hwf' as [_ Hconn2].
        destruct ((cut, cvt, cwt) :: lr) as [|h2 t2] eqn:Heq2.
        { discriminate. }
        destruct h2 as [[y2 z2] w2].
        destruct Hconn2 as [Heq_y_y2 _].
        inversion Heq2. subst y2 z2 w2 t2.
        (* Heq_y_y2: y = cut *)
        cbn [target] in Htgt'.
        destruct (fin_eq_dec d y) as [Heq_dy | Hneq].
        + subst d. subst y. reflexivity.
        + discriminate Htgt'.
      - (* lm' = (xu, xv, xw) :: lm'' *)
        intros d x y w Hwf' Htgt'.
        cbn [app] in Hwf'.
        cbn [well_formed_path_aux] in Hwf'.
        destruct Hwf' as [_ Hconn2].
        destruct ((xu, xv, xw) :: lm'' ++ (cut, cvt, cwt) :: lr) as [|h2 t2] eqn:Heq2.
        { discriminate Heq2. }
        destruct h2 as [[y2 z2] w2].
        destruct Hconn2 as [_ Hwf_lm_rest].
        inversion Heq2. subst y2 z2 w2 t2. clear Heq2.
        cbn [target] in Htgt'.
        (* Htgt': target d ((xu, xv, xw) :: lm'') = true *)
        exact (IH d xu xv xw Hwf_lm_rest Htgt'). }
    apply (Hind lm au au av aw Hwf_tail Htgt).
  Qed.


  Lemma well_formed_loop_removal {R : Semiring.type} : 
    forall ll lr lm au av aw (m : @Matrix R),
    well_formed_path_aux m 
      (ll ++ ((au, av, aw) :: lm) ++ lr) ->
    cyclic_path au ((au, av, aw) :: lm) ->
    well_formed_path_aux m ((ll ++ lr)).
  Proof.
    induction ll as [|((aut, avt), awt) ll' IH]; intros lr lm au av aw m Hwf Hcyc.
    - (* ll = [] *)
      apply well_formed_path_snoc in Hwf as [_ Hwf_cycle_lr].
      apply well_formed_path_snoc in Hwf_cycle_lr as [_ Hwf_lr].
      cbn. exact Hwf_lr.
    - (* ll = (aut, avt, awt) :: ll' *)
      destruct ll' as [|((but, bvt), bwt) ll''].
      + (* ll' = [] *)
        destruct lr as [|((cut, cvt), cwt) lr'].
        * (* lr = [] *)
          apply well_formed_path_snoc in Hwf as [Hwf_head _].
          simpl in Hwf_head. exact Hwf_head.
        * (* lr = (cut, cvt, cwt) :: lr' *)
          pose proof (well_founded_rev lm aut avt awt au av aw cut cvt cwt lr' m Hwf Hcyc) as Heq_avt_cut.
          apply well_formed_path_snoc in Hwf as [Hwf_head Hwf_rest].
          apply well_formed_path_snoc in Hwf_rest as [Hwf_cycle Hwf_lr'].
          (* Hwf_head: well_formed [(aut, avt, awt)] *)
          simpl in Hwf_head.
          destruct Hwf_head as [Hmv _].
          (* Hwf_lr': well_formed ((cut, cvt, cwt) :: lr') *)
          (* Build well_formed ((aut,avt,awt) :: (cut,cvt,cwt) :: lr') *)
          simpl.
          split; [exact Hmv | ].
          simpl.
          split; [rewrite Heq_avt_cut; reflexivity | exact Hwf_lr'].
      + (* ll' ≠ [] *)
        simpl in Hwf.
        destruct Hwf as [Hmv [Heq_avt_but Hwf_tail]].
        (* Hwf_tail: well_formed ((but,bvt,bwt) :: ll'' ++ ((au,av,aw)::lm) ++ lr) *)
        pose proof (IH lr lm au av aw m Hwf_tail Hcyc) as Hwf_ll''_lr.
        (* Hwf_ll''_lr: well_formed ((but,bvt,bwt) :: ll'' ++ lr) *)
        simpl.
        split; [exact Hmv | ].
        simpl.
        split; [exact Heq_avt_but | exact Hwf_ll''_lr].
  Qed.


  Lemma source_loop_removal {R : Semiring.type} : 
    forall ll lr lm au av aw c d (m : @Matrix R),
    well_formed_path_aux m
      (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) -> 
    source c
      (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) = true ->
    cyclic_path au ((au, av, aw) :: lm) ->
    source c ((ll ++ lr) ++ [(d, d, 1)]) = true.
  Proof.
    intros ll lr lm au av aw c d m Hwf Hsrc Hcyc.
    unfold source in *.
    destruct ll as [|((x, y), w) ll'].
    - (* ll = [] *)
      simpl in Hsrc.
      destruct (fin_eq_dec c au) as [Heq_c_au | Hneq_c_au]; [| discriminate Hsrc].
      subst c.
      destruct (lr ++ [(d, d, 1)]) as [|h t] eqn:Hlr.
      { (* impossible: lr ++ [(d,d,1)] is always non-empty *)
        exfalso. apply app_eq_nil in Hlr. destruct Hlr as [_ Hnil].
        discriminate Hnil. }
      destruct h as [[y2 z2] w2].
      simpl.
      (* Need: fin_eq_dec au y2 = true, i.e., au = y2 *)
      unfold cyclic_path in Hcyc. destruct Hcyc as [_ [_ Htgt]].
      (* Inner induction as in well_founded_rev *)
      pose (P := fun (lm' : list (Node * Node * R)) =>
        forall (d x y : Node) (w : R),
          well_formed_path_aux m ((x, y, w) :: lm' ++ (y2, z2, w2) :: t) ->
          target d ((x, y, w) :: lm') = true ->
          d = y2).
      assert (Hind : forall lm', P lm').
      { induction lm' as [|((xu, xv), xw) lm'' IH]; unfold P.
        - intros d0 x0 y0 w0 Hwf' Htgt'.
          simpl in Hwf'. destruct Hwf' as [_ [Heq_y0_y2 _]].
          simpl in Htgt'.
          destruct (fin_eq_dec d0 y0) as [Heq | Hneq]; [| discriminate Htgt'].
          subst d0. subst y0. reflexivity.
        - intros d0 x0 y0 w0 Hwf' Htgt'.
          simpl in Hwf'. destruct Hwf' as [_ [_ Hwf_lm_rest]].
          simpl in Htgt'. exact (IH d0 xu xv xw Hwf_lm_rest Htgt'). }
      assert (Heq_au_y2 : au = y2).
      { apply (Hind lm au au av aw).
        - replace (lm ++ lr ++ [(d, d, 1)]) with (lm ++ (y2, z2, w2) :: t) in Hwf.
          + exact Hwf.
          + f_equal. exact (eq_sym Hlr).
        - exact Htgt. }
      subst y2.
      rewrite Hlr. simpl.
      destruct (fin_eq_dec au au) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
    - (* ll ≠ [] *)
      simpl in Hsrc. simpl. exact Hsrc.
  Qed.




  Lemma cycle_path_dup_remove {R : BoundedSemiring.type} : 
    forall (ll : list (Node * Node * R)) lm lr,
    Orel 
      (measure_of_path (ll ++ lm ++ lr))
      (measure_of_path (ll ++ lr)).
  Proof.
    intros ll lm lr. unfold Orel. 
    erewrite measure_of_path_app with (l₁ := ll) (l₂ := lm ++ lr).
    assert (ha : measure_of_path (lm ++ lr) = 
    (measure_of_path lm * measure_of_path lr)).
    { rewrite measure_of_path_app with (l₁ := lm) (l₂ := lr). reflexivity. reflexivity. } 
    rewrite ha; clear ha.
    assert (ha : measure_of_path (ll ++ lr) = 
    (measure_of_path ll * measure_of_path lr)).
    { rewrite measure_of_path_app with (l₁ := ll) (l₂ := lr). reflexivity. reflexivity. }
    rewrite ha. rewrite <-mulA.
    apply path_weight_rel with (a := measure_of_path ll) (b := measure_of_path lm) (c := measure_of_path lr).
    reflexivity.
  Qed.

  (** In a BoundedSemiring, addition is idempotent: [a + a = a].
      Derived from [add_bound : 1 + a = 1] and distributivity. *)
  Lemma bounded_add_idem {R : BoundedSemiring.type} : forall (a : R), a + a = a.
  Proof.
    intro a.
    rewrite <- (mulr1 (s := R) a) at 1 2.
    apply (@eq_trans _ (a * 1 + a * 1) (a * (1 + 1)) a).
    - apply eq_sym, (mulDl (s := R) a 1 1).
    - apply (@eq_trans _ (a * (1 + 1)) (a * 1) a).
      + apply (f_equal (fun x => a * x)), (add_bound (s := R) 1).
      + apply (mulr1 (s := R) a).
  Qed.

  Lemma reduce_path_cycle_step {R : BoundedSemiring.type} :
    forall (l : list (Node * Node * R)) (m : @Matrix R) c d,
    (length (@elements Node) <= length l)%nat ->
    well_formed_path_aux m (l ++ [(d, d, 1)]) ->
    source c (l ++ [(d, d, 1)]) = true ->
    target d (l ++ [(d, d, 1)]) = true ->
    exists ys,
      (List.length ys < List.length l)%nat /\
      well_formed_path_aux m (ys ++ [(d, d, 1)]) /\
      source c (ys ++ [(d, d, 1)]) = true /\
      target d (ys ++ [(d, d, 1)]) = true /\
      Orel (measure_of_path l) (measure_of_path ys).
  Proof.
    intros l m c d Hlen Hwf Hsrc Htgt.
    destruct (well_formed_path_snoc l [(d, d, 1)] m Hwf) as [Hwf_l Hwf_d].
    simpl in Hwf_d. destruct Hwf_d as [Hdiag _].
    pose proof (all_paths_in_klength_paths_cycle_finN_stronger (R := R) l m Hlen Hwf_l) as Hcycle.
    destruct Hcycle as (ll & au & av & aw & lm & lr & _ & Hcyc & _ & Hpath).
    set (ys := ll ++ lr).
    assert (Hlen_ys : List.length ys < List.length l).
    { subst ys. rewrite Hpath. rewrite !length_app. cbn. lia. }
    assert (Hwf_ys : well_formed_path_aux m (ys ++ [(d, d, 1)])).
    { subst ys.
      pose proof Hwf as Hwf'.
      rewrite Hpath in Hwf'.
      repeat rewrite <- app_assoc in Hwf'.
      pose proof (well_formed_loop_removal ll (lr ++ [(d, d, 1)]) lm au av aw m Hwf' Hcyc)
        as Htmp.
      rewrite app_assoc in Htmp.
      exact Htmp. }
    assert (Hsrc_ys : source c (ys ++ [(d, d, 1)]) = true).
    { subst ys.
      pose proof Hwf as Hwf'.
      rewrite Hpath in Hwf'.
      repeat rewrite <- app_assoc in Hwf'.
      pose proof Hsrc as Hsrc'.
      rewrite Hpath in Hsrc'.
      repeat rewrite <- app_assoc in Hsrc'.
      pose proof (source_loop_removal ll lr lm au av aw c d m Hwf' Hsrc' Hcyc)
        as Htmp.
      exact Htmp. }
    assert (Htgt_ys : target d (ys ++ [(d, d, 1)]) = true).
    { subst ys. rewrite target_end. cbn.
      destruct (fin_eq_dec d d) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity]. }
    assert (Horel : Orel (measure_of_path l) (measure_of_path ys)).
    { subst ys.
      rewrite Hpath.
      apply (cycle_path_dup_remove ll ((au, av, aw) :: lm) lr). }
    exists ys. repeat split; try assumption.
  Qed.



  Lemma reduce_path_into_simpl_path {R : BoundedSemiring.type} :
    forall (l : list (Node * Node * R)) (m : @Matrix R) c d,
    (length (@elements Node) <= length l)%nat ->
    well_formed_path_aux m (l ++ [(d, d, 1)]) ->
    source c (l ++ [(d, d, 1)]) = true -> 
    target d (l ++ [(d, d, 1)]) = true ->
    exists ys, 
      (List.length ys < List.length (@elements Node))%nat ∧
      well_formed_path_aux m (ys ++ [(d, d, 1)])  ∧
      source c (ys ++ [(d, d, 1)]) = true ∧
      target d (ys ++ [(d, d, 1)]) = true ∧
      Orel
        (measure_of_path l) 
        (measure_of_path ys).
  Proof.
    intros l.
    induction (zwf_well_founded l) as [l Hf IHl].
    unfold zwf in * |- *.
    intros m c d Hlen Hwf Hsrc Htgt.
    assert (Hshort_or_long : (length l < length (@elements Node))%nat \/
      (length (@elements Node) <= length l)%nat) by lia.
    destruct Hshort_or_long as [Hshort | Hlong].
    - exists l.
      repeat split; try assumption.
      unfold Orel. apply bounded_add_idem.
    - pose proof (reduce_path_cycle_step l m c d Hlen Hwf Hsrc Htgt)
        as (ys & Hyslen & Hwf_ys & Hsrc_ys & Htgt_ys & Horel_ys).
      assert (Hys_short_or_long : (length ys < length (@elements Node))%nat \/
        (length (@elements Node) <= length ys)%nat) by lia.
      destruct Hys_short_or_long as [Hys_short | Hys_long].
      + exists ys.
        repeat split; try assumption.
      + specialize (IHl ys Hyslen m c d Hys_long Hwf_ys Hsrc_ys Htgt_ys)
          as (zs & Hzs_short & Hwf_zs & Hsrc_zs & Htgt_zs & Horel_zs).
        exists zs.
        repeat split; try assumption.
        eapply orel_trans; eauto.
  Qed.











  


  
  







  
  







End Path.