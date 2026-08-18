From Stdlib Require Import List Utf8
  BinNatDef Lia.
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

  (* Proofs start from here *)

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
    source y ys = true ->
    well_formed_path_aux m (List.tl xs) ->
    well_formed_path_aux m xs.
  Proof.
    intros xs ys c y m Hys_ne Heq Hsrc_ys Htl.
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
        Hys_ne eq_refl Hsrc_ys Hin_ys).
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


  (** [target] also depends only on the last element of a non-empty list. *)
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

  (** Splitting a path at a chosen node returns the collected prefix and the remainder. *)
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

  (** A non-empty path has strictly fewer edges than collected nodes. *)
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



  (** A long enough node list yields a longer collected-node list. *)
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

  (** A duplicate in the collected nodes forces a cycle witness. *)
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


  (** A cyclic path splits into a prefix, one loop, and a suffix. *)
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

  (** The length-based order on paths is well-founded. *)
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


  (** Every well-formed path can be reduced to an acyclic well-formed path. *)
  Lemma reduce_path_into_elem_path {R : Semiring.type} : 
    forall (l : list (Node * Node * R)) m,
    well_formed_path_aux m l ->
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


  (** Removing a loop preserves the next-node boundary relation. *)
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


  (** Removing a cyclic middle segment preserves well-formedness. *)
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


  (** Removing a loop also preserves the source predicate at the front. *)
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




  (** A duplicate-free cycle segment can be removed without changing the path measure. *)
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

  (** Removing one cycle step keeps the measure ordered by [Orel]. *)
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



  (** Any long enough path can be reduced to a short one with the same boundary loop. *)
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

  (** A path above the finite-node bound can be reduced while preserving the order relation. *)
  Lemma reduce_path_gen_lemma {R : BoundedSemiring.type} : 
    ∀ (n : nat) (m : @Matrix R) 
    (c d : Node) (xs : list (Node * Node * R)),
    (length (@elements Node) <= n)%nat ->
    (forall c d, c = d -> m c d = 1) -> 
    List.In xs (all_paths_klength elements m n c d)  ->
    exists ys, 
      (length ys < length (@elements Node))%nat ∧
      List.In (ys ++ [(d, d, 1)])
        (all_paths_klength elements m (length ys) c d) ∧
      Orel 
        (measure_of_path xs)
        (measure_of_path ys).
  Proof.
    intros n m c d xs Hfin Hdiag Hin.
    destruct (source_target_non_empty_kpath_and_well_formed
      n m c d xs Hdiag Hin)
      as (Hne & Hsrc & Htgt & Hwf & Hlen & [xs' Hxs]).
    assert (Hlen_xs' : length xs' = n).
    { rewrite Hxs in Hlen.
      rewrite length_app in Hlen.
      cbn in Hlen. rewrite PeanoNat.Nat.add_comm in Hlen.
      cbn in Hlen. inversion Hlen; subst; reflexivity. }
    assert (Hfin_xs' : (length (@elements Node) <= length xs')%nat) by lia.
    rewrite Hxs in Hwf, Hsrc, Htgt.
    pose proof (reduce_path_into_simpl_path _ m c d Hfin_xs' Hwf Hsrc Htgt)
      as (ys & Hlen_ys & Hwf_ys & Hsrc_ys & Htgt_ys & Horel_ys).
    pose proof (all_paths_klength_complete ys m c d Hsrc_ys Htgt_ys Hwf_ys)
      as Hin_ys.
    exists ys.
    split; [exact Hlen_ys | ].
    split; [exact Hin_ys | ].
    unfold Orel in *.
    rewrite Hxs.
    assert (Hxs_meas : measure_of_path (xs' ++ [(d, d, 1)]) = measure_of_path xs').
    { induction xs' as [|((a, b), v) t IH]; cbn.
      - rewrite mulr1. reflexivity.
      - rewrite measure_of_path_app with (l₁ := t) (l₂ := [(d, d, 1)]).
        cbn. rewrite !mul1r, mulr1. reflexivity. reflexivity. }
    rewrite Hxs_meas.
    exact Horel_ys.
  Qed.

  (** Concatenating flat-path sums splits over list append. *)
  Lemma sum_all_flat_paths_app {R : Semiring.type} : 
    forall (l₁ l₂ : list Path),
    @sum_all_flat_paths R (l₁ ++ l₂) = 
    sum_all_flat_paths l₁ + 
    sum_all_flat_paths l₂.
  Proof.
    induction l₁ as [|((a, b), l) t IH]; intros l₂.
    - cbn. symmetry. apply add0r.
    - cbn. rewrite IH. rewrite addA. reflexivity.
  Qed.

  (** Summing R-values matches summing the corresponding flat paths. *)
  Lemma sum_all_rvalues_get_all_rvalues {R : Semiring.type} :
    forall (l : list Path),
    sum_all_rvalues (get_all_rvalues l) = @sum_all_flat_paths R l.
  Proof.
    induction l as [|((a, b), h) t IH].
    - cbn. reflexivity.
    - cbn [get_all_rvalues sum_all_flat_paths].
      simpl.
      rewrite IH.
      reflexivity.
  Qed.

  (** The partial path sum equals the sum over the flattened enumeration. *)
  Lemma flat_map_path_partial_sum {R : Semiring.type} : 
    forall n (m : @Matrix R) c d, 
    partial_sum_paths elements m n c d = 
    @sum_all_flat_paths R (enum_all_paths_flat elements m n c d).
  Proof.
    induction n as [|n IH]; intros m c d.
    - cbn. destruct (fin_eq_dec c d) as [Hcd | Hcd]; cbn.
      + rewrite mul1r. rewrite addr0. reflexivity.
      + reflexivity.
    - cbn [partial_sum_paths enum_all_paths_flat].
      rewrite IH.
      rewrite sum_all_rvalues_get_all_rvalues.
      rewrite sum_all_flat_paths_app.
      rewrite addC.
      reflexivity.
  Qed.


  (** A witness in the right list absorbs into the left flat-path sum. *)
  Lemma in_eq_path_measure {R : Semiring.type} : 
    forall (lpp : list Path) ys alph, 
    List.In ys
    (map (λ '(y, lt), let '(_, _) := y in lt) lpp) ->
    (measure_of_path ys + measure_of_path alph = measure_of_path ys) -> 
    @sum_all_flat_paths R lpp + measure_of_path alph = sum_all_flat_paths lpp.
  Proof.
    induction lpp as [|((au, av), l) t IH]; intros ys alph Hin Hm.
    - simpl in Hin. contradiction.
    - simpl in Hin.
      destruct Hin as [Hys | Hin].
      + subst ys. simpl.
        rewrite addA.
        rewrite (addC (sum_all_flat_paths t) (measure_of_path alph)).
        rewrite <- addA.
        rewrite Hm.
        reflexivity.
      + simpl.
        rewrite addA.
        rewrite (IH ys alph); try assumption.
        reflexivity.
  Qed.


  (** Flat-path sums are idempotent under a covering hypothesis. *)
  Lemma sum_all_flat_paths_idempotence {R : Semiring.type} : 
    forall (lp lpp : list Path), 
    (forall xs, List.In xs lp ->
     exists (ys : Path), List.In ys lpp  ∧ 
      measure_of_path (t_proj ys) + measure_of_path (t_proj xs) =
      measure_of_path (t_proj ys)) ->
    @sum_all_flat_paths R lp + sum_all_flat_paths lpp = 
    sum_all_flat_paths lpp.
  Proof.
    induction lp as [|x lp IH]; intros lpp Hcov.
    - cbn. rewrite <- add0r. reflexivity.
    - destruct x as [[a b] h]. cbn in *.
      assert (Htail : sum_all_flat_paths lp + sum_all_flat_paths lpp =
        sum_all_flat_paths lpp).
      { apply IH. intros xs Hxs. apply Hcov. right. exact Hxs. }
      assert (Hassoc : (measure_of_path h + sum_all_flat_paths lp) +
        sum_all_flat_paths lpp = measure_of_path h +
        (sum_all_flat_paths lp + sum_all_flat_paths lpp)).
      { apply addA. }
      rewrite Hassoc.
      rewrite Htail.
      destruct (Hcov ((a, b, h)) (or_introl eq_refl)) as [y [Hy Habs]].
      assert (Hmem : List.In (t_proj y)
        (map (λ '(y0, lt), let '(_, _) := y0 in lt) lpp)).
      { apply in_map. exact Hy. }
      pose proof (in_eq_path_measure (R := R) lpp (t_proj y) h Hmem Habs) as Hstep.
      rewrite addC.
      exact Hstep.
  Qed.

  (** Every constructed path at a smaller length also appears in the flat enumeration. *)
  Lemma construct_all_paths_in_enum_all_paths_flat {R : Semiring.type} :
    forall n k (m : @Matrix R) c d (xs : Path),
    (k <= n)%nat ->
    List.In xs (construct_all_paths elements m k c d) ->
    List.In xs (enum_all_paths_flat elements m n c d).
  Proof.
    induction n as [|n IH]; intros k m c d xs Hle Hin.
    - assert (k = 0)%nat by lia. subst k. simpl in Hin. exact Hin.
    - destruct k as [|k']; simpl in *.
      + apply in_or_app. right.
        assert (H0 : (0 <= n)%nat) by lia.
        exact (IH (0%nat) m c d xs H0 Hin).
      + assert (Hcase : k' = n \/ (k' < n)%nat) by lia.
        destruct Hcase as [Heq | Hlt].
        * subst k'. apply in_or_app. left. exact Hin.
        * apply in_or_app. right.
          assert (Hle' : (S k' <= n)%nat) by lia.
          exact (IH (S k') m c d xs Hle' Hin).
  Qed.

  (** The flat-path sum stabilizes once the length exceeds the node bound. *)
  Lemma sum_all_flat_paths_fixpoint {R : BoundedSemiring.type} :
    forall k (m : @Matrix R) c d,
    (forall u v : Node, u = v -> m u v = 1) ->
    @sum_all_flat_paths R (enum_all_paths_flat elements m (length (@elements Node) - 1)%nat c d) =
    sum_all_flat_paths (enum_all_paths_flat elements m (k + length (@elements Node) - 1)%nat c d).
  Proof.
    induction k as [|k IH]; intros m c d Hdiag.
    - reflexivity.
    - assert (Hstep : (S k + length (@elements Node) - 1)%nat =
        S (k + length (@elements Node) - 1)).
      { destruct elements as [|a es] eqn:He.
        - pose proof (@elements_two_or_more Node) as hb.
          rewrite He in hb. cbn in hb. lia.
        - cbn. lia.
      }
      rewrite Hstep; clear Hstep.
      cbn [enum_all_paths_flat].
      rewrite sum_all_flat_paths_app.
      pose proof (@IH m c d Hdiag) as HIH.
      rewrite HIH.
      symmetry.
      apply sum_all_flat_paths_idempotence.
      intros xs Hin.
      apply in_map_iff in Hin.
      destruct Hin as [raw [Hxs Hin_raw]].
      subst xs.
      assert (Hn_ge : (length (@elements Node) <= S (k + length (@elements Node) - 1))%nat) by lia.
      pose proof (@reduce_path_gen_lemma R
        (S (k + length (@elements Node) - 1)) m c d raw
        Hn_ge Hdiag Hin_raw) as (ys & Hys_short & Hys_mem & Horel).
      assert (Hmeas : measure_of_path (ys ++ [(d, d, 1)]) = measure_of_path ys).
      { clear Hys_short Hys_mem Horel raw Hin_raw Hn_ge HIH.
        induction ys as [|((a, b), v) t IHys]; cbn.
        - rewrite mul1r. reflexivity.
        - f_equal. exact IHys.
      }
      exists (c, d, ys ++ [(d, d, 1)]).
      split.
      + apply construct_all_paths_in_enum_all_paths_flat with (k := List.length ys).
        * lia.
        * apply in_map. exact Hys_mem.
      + cbn [t_proj]. rewrite Hmeas. rewrite addC. exact Horel.
  Qed.

  (** The partial sum is stable after the finite-node bound is reached. *)
  Lemma zero_stable_partial_sum_path {R : BoundedSemiring.type} :
    forall k (m : @Matrix R),
    (∀ u v : Node, u = v → m u v = 1) ->
    forall (c d : Node), 
      partial_sum_paths elements m (length (@elements Node) - 1)%nat c d = 
      partial_sum_paths elements m (k + length (@elements Node) - 1)%nat c d.
  Proof.
    intros k m Hdiag c d.
    rewrite !flat_map_path_partial_sum.
    apply sum_all_flat_paths_fixpoint; exact Hdiag.
  Qed.



  (** ** 1.  Path bottleneck bound

      If every edge weight of the matrix [m] lies below [v] (in the
      [Orel] preorder), then the measure of any non-empty well-formed
      path is also below [v].  This holds in the max-min semiring
      (where multiplication is [min]) and more generally in any bounded
      semiring where multiplication is sub-idempotent with respect
      to [v].

      The [l ≠ []] hypothesis is necessary: for the empty path the
      measure is [1], and [1 ≤ v] is not true in general (it requires
      [v = 1] by [add_bound]).  In the Schulze-method context all
      paths are non-empty (they carry at least a terminal [(d, d, 1)]
      edge). *)
  Lemma path_bottleneck_bound {R : Semiring.type} :
    forall (m : @Matrix R) (l : list (Node * Node * R)) (v : R),
      well_formed_path_aux m l ->
      l <> [] ->
      (forall (x y : Node), Orel (m x y) v) ->
      (forall (a b : R), Orel a v -> Orel b v -> Orel (a * b) v) ->
      Orel (measure_of_path l) v.
  Proof.
    intros m l v Hwf Hne Hedge Hclose.
    induction l as [|h t IH].
    - contradiction.
    - destruct h as [[c x] w].
      cbn [measure_of_path].
      cbn [well_formed_path_aux] in Hwf.
      destruct Hwf as [Hw_eq Hconn].
      assert (Hw_le_v : Orel w v).
      { subst w. apply Hedge. }
      destruct t as [|h2 t2].
      + cbn [measure_of_path]. rewrite mulr1. exact Hw_le_v.
      + destruct h2 as [[c2 x2] w2].
        destruct Hconn as [Heq_x Hwf_t].
        assert (Ht_meas : Orel (measure_of_path ((c2, x2, w2) :: t2)) v).
        { apply IH.
          - exact Hwf_t.
          - intro Hnil; inversion Hnil. }
        apply (Hclose w (measure_of_path ((c2, x2, w2) :: t2))
                Hw_le_v Ht_meas).
  Qed.

  (** ** 2.  Path concatenation bound

      The measure of a concatenation is bounded by the product of the
      measures — the path-level analogue of [star_path_compose] in
      [SocialchoiceN.v].  No well-formedness or matching-endpoint condition
      is needed: [measure_of_path_app] already makes the two sides equal for
      arbitrary lists, and this is its order-theoretic weakening. *)
  Lemma path_concat_measure_bound {R : BoundedSemiring.type} :
    forall (p q : list (Node * Node * R)),
      Orel (measure_of_path (p ++ q)) (measure_of_path p * measure_of_path q).
  Proof.
    intros p q.
    rewrite (measure_of_path_app (p ++ q) p q eq_refl).
    unfold Orel. apply bounded_add_idem.
  Qed.

  (** ** 3.  Weakest-edge realisation

      In the max-min semiring ([*] = [min]), the measure of a path is
      exactly the minimum edge weight along the path.  In a general
      bounded semiring we only obtain an upper bound: there exists an
      edge [(x, y)] on the path such that the path measure is below
      [m x y]. *)
  Lemma measure_bounded_by_some_edge {R : BoundedSemiring.type} :
    forall (m : @Matrix R) (l : list (Node * Node * R)),
      well_formed_path_aux m l -> l <> [] ->
      exists (x y : Node),
        List.In (x, y, m x y) l /\
        Orel (measure_of_path l) (m x y).
  Proof.
    intros m l Hwf Hne.
    induction l as [|h t IH].
    - contradiction.
    - destruct h as [[c x] w].
      cbn [measure_of_path well_formed_path_aux] in *.
      destruct Hwf as [Hw_eq Hconn].
      destruct t as [|h2 t2].
      + (* singleton path: witness is the only edge *)
        exists c, x.
        split.
        { left. rewrite Hw_eq. reflexivity. }
        { cbn [measure_of_path]. rewrite mulr1. rewrite Hw_eq.
          unfold Orel. apply bounded_add_idem. }
      + (* multi-edge path: use the edge from the tail *)
        destruct h2 as [[c2 x2] w2].
        destruct Hconn as [Heq_x Hwf_t].
        assert (Ht_ne : (c2, x2, w2) :: t2 <> [])
          by (intro Hnil; inversion Hnil).
        destruct (IH Hwf_t Ht_ne) as [x' [y' [Hin_t Hmeas_t]]].
        exists x', y'.
        split.
        { right. exact Hin_t. }
        { pose proof (path_weight_rel (R := R) 1 w
            (measure_of_path ((c2, x2, w2) :: t2))) as Hpw.
          cbn in Hpw.
          rewrite !mul1r in Hpw.
          eapply orel_trans; [exact Hpw | exact Hmeas_t]. }
  Qed.


  (* ==================================================================== *)
  (*  Path enumeration over an arbitrary candidate list                    *)
  (*                                                                       *)
  (*  [all_paths_klength] is already parameterised by a node list, but the *)
  (*  lemmas above are all stated at [elements].  The generalisations below*)
  (*  replace [elements] by an arbitrary list [l], which is what lets two  *)
  (*  elections over different candidate sets be compared at a single      *)
  (*  ambient [Node] type.  Each original lemma is the [l := elements]     *)
  (*  instance of its [_gen] counterpart, with the side condition on [l]   *)
  (*  discharged by [covers_list_elem ... elements_complete].              *)
  (* ==================================================================== *)

  (** The source of the first edge is one of the nodes a path visits. *)
  Lemma collect_nodes_head {R : Semiring.type} (a b : Node) (w : R)
    (p : list (Node * Node * R)) :
    List.In a (collect_nodes_from_a_path ((a, b, w) :: p)).
  Proof.
    destruct p as [|h t]; cbn; left; reflexivity.
  Qed.

  (** Dropping the first edge of a non-trivial path keeps every remaining
      node inside [l]. *)
  Lemma collect_nodes_cons_covers {R : Semiring.type} (l : list Node)
    (a b : Node) (w : R) (p : list (Node * Node * R)) :
    p <> [] ->
    covers (collect_nodes_from_a_path ((a, b, w) :: p)) l ->
    covers (collect_nodes_from_a_path p) l.
  Proof.
    intros Hne Hcov z Hz.
    apply Hcov.
    destruct p as [|h t]; [exfalso; apply Hne; reflexivity |].
    cbn. right. exact Hz.
  Qed.

  (** [non_empty_paths_in_kpath] at an arbitrary candidate list. *)
  Lemma non_empty_paths_in_kpath_gen {R : Semiring.type} :
    ∀ (l : list Node) (n : nat) (m : @Matrix R)
    (c d : Node) (xs : list (Node * Node * R)),
    List.In xs (all_paths_klength l m n c d) ->
    xs ≠ [] ∧ source c xs = true ∧ target d xs = true.
  Proof.
    intros l. induction n as [|n' IH]; intros m c d xs Hin.
    - simpl in Hin.
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
    - simpl in Hin.
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

  (** [all_paths_well_formed_in_kpaths] at an arbitrary candidate list. *)
  Lemma all_paths_well_formed_in_kpaths_gen {R : Semiring.type} :
    forall (l : list Node) (n : nat) (m : @Matrix R)
    (c d : Node) (xs : list (Node * Node * R)),
    (forall c d, c = d -> m c d = 1) ->
    List.In xs (all_paths_klength l m n c d) ->
    well_formed_path_aux m xs.
  Proof.
    intros l. induction n as [|n' IH]; intros m c d xs Hdiag Hin.
    - simpl in Hin.
      destruct (fin_eq_dec c d) as [Heq | Hneq].
      + subst d. destruct Hin as [Hin | []].
        subst xs. unfold well_formed_path_aux. cbn.
        split; [apply Hdiag; reflexivity | exact I].
      + inversion Hin.
    - simpl in Hin.
      assert (Hin_copy := Hin).
      apply (append_node_in_paths_shape
        (List.flat_map (fun x => all_paths_klength l m n' x d) l)
        m c xs) in Hin.
      destruct Hin as (y & ys & Heq & Hsrc_xs & Hsrc_ys & Hys_ne).
      subst xs.
      apply append_node_in_paths_In in Hin_copy.
      destruct Hin_copy as (y2 & ys2 & Heq2 & Hin_flat).
      inversion Heq2. subst y2 ys2.
      apply in_flat_map in Hin_flat.
      destruct Hin_flat as (x & Hin_el & Hin_ys).
      apply (IH m x d ys Hdiag) in Hin_ys.
      apply (well_formed_by_extending ((c, y, m c y) :: ys) ys c y m
        Hys_ne eq_refl Hsrc_ys Hin_ys).
  Qed.

  (** [path_end_unit_loop] at an arbitrary candidate list. *)
  Lemma path_end_unit_loop_gen {R : Semiring.type} :
    forall (l : list Node) k p (m : @Matrix R) (c d : Node),
    List.In p (all_paths_klength l m k c d) ->
    exists p', p = (p' ++ [(d, d, 1)]).
  Proof.
    intros l. induction k as [|k' IH]; intros p m c d Hin.
    - simpl in Hin.
      destruct (fin_eq_dec c d) as [Heq | Hneq].
      + subst d. destruct Hin as [Hin | []].
        subst p. exists []. reflexivity.
      + inversion Hin.
    - simpl in Hin.
      apply append_node_in_paths_In in Hin.
      destruct Hin as (y & ys & Heq & Hin_flat).
      subst p.
      apply in_flat_map in Hin_flat.
      destruct Hin_flat as (x & Hin_el & Hin_ys).
      apply (IH ys m x d) in Hin_ys.
      destruct Hin_ys as [p' Hp'].
      exists ((c, y, m c y) :: p').
      rewrite Hp'. reflexivity.
  Qed.

  (** [all_paths_in_klength] at an arbitrary candidate list. *)
  Lemma all_paths_in_klength_gen {R : Semiring.type} :
    ∀ (l : list Node) (k : nat) (m : @Matrix R) (c d : Node) xs,
    List.In xs (all_paths_klength l m k c d) ->
    List.length xs = S k.
  Proof.
    intros l. induction k as [|k' IH]; intros m c d xs Hin.
    - simpl in Hin.
      destruct (fin_eq_dec c d) as [Heq | Hneq].
      + subst d. destruct Hin as [Hin | []].
        subst xs. reflexivity.
      + inversion Hin.
    - simpl in Hin.
      apply (append_node_in_paths_In m c
        (List.flat_map (fun x => all_paths_klength l m k' x d) l)
        xs) in Hin.
      destruct Hin as (y & ys & Heq & Hin_flat).
      subst xs.
      apply in_flat_map in Hin_flat.
      destruct Hin_flat as (x & Hin_el & Hin_ys).
      apply (IH m x d ys) in Hin_ys.
      simpl. rewrite Hin_ys. reflexivity.
  Qed.

  (** Soundness of the candidate list: an enumerated path only visits its
      own endpoints and nodes drawn from [l].  This has no counterpart at
      [elements], where it is vacuous, but it is what confines a path to a
      given set of alternatives. *)
  Lemma all_paths_klength_nodes {R : Semiring.type} :
    ∀ (l : list Node) (k : nat) (m : @Matrix R) (c d : Node)
    (xs : list (Node * Node * R)),
    List.In xs (all_paths_klength l m k c d) ->
    covers (collect_nodes_from_a_path xs) (c :: d :: l).
  Proof.
    intros l. induction k as [|k' IH]; intros m c d xs Hin.
    - simpl in Hin.
      destruct (fin_eq_dec c d) as [Heq | Hneq]; [| inversion Hin].
      subst d. destruct Hin as [Hin | []]. subst xs.
      intros z Hz. cbn in Hz.
      destruct Hz as [Hz | [Hz | []]]; subst z; left; reflexivity.
    - simpl in Hin.
      apply append_node_in_paths_In in Hin.
      destruct Hin as (y & ys & Heq & Hin_flat).
      subst xs.
      apply in_flat_map in Hin_flat.
      destruct Hin_flat as (x & Hin_x & Hin_ys).
      assert (Hys_ne : ys <> [])
        by exact (proj1 (non_empty_paths_in_kpath_gen l k' m x d ys Hin_ys)).
      pose proof (IH m x d ys Hin_ys) as Hcov_ys.
      intros z Hz.
      destruct ys as [|h t]; [exfalso; apply Hys_ne; reflexivity |].
      cbn in Hz. destruct Hz as [Hz | Hz].
      + subst z. left. reflexivity.
      + specialize (Hcov_ys z Hz).
        destruct Hcov_ys as [Hc | [Hc | Hc]].
        * subst z. right. right. exact Hin_x.
        * subst z. right. left. reflexivity.
        * right. right. exact Hc.
  Qed.

  (** Completeness at an arbitrary candidate list.  This is the one place
      where [elements_complete] was genuinely used, so it becomes the
      explicit hypothesis that every node the path visits lies in [l]. *)
  Lemma all_paths_klength_complete_gen {R : Semiring.type} :
    ∀ (l : list Node) (xs : list (Node * Node * R))
    (m : @Matrix R) (c d : Node),
    covers (collect_nodes_from_a_path (xs ++ [(d, d, 1)])) l ->
    source c (xs ++ [(d, d, 1)]) = true ->
    target d (xs ++ [(d, d, 1)]) = true ->
    well_formed_path_aux m (xs ++ [(d, d, 1)]) ->
    List.In (xs ++ [(d, d, 1)])
      (all_paths_klength l m (List.length xs) c d).
  Proof.
    intros l.
    induction xs as [|h ys IH]; intros m c d Hcov Hsrc Htgt Hwf.
    - simpl in Hsrc. unfold source in Hsrc.
      destruct (fin_eq_dec c d) as [Heq | Hneq]; [| discriminate Hsrc].
      subst c.
      simpl. destruct (fin_eq_dec d d) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
      left. reflexivity.
    - destruct h as [[c' x] v].
      simpl in Hsrc. unfold source in Hsrc. simpl in Hsrc.
      destruct (fin_eq_dec c c') as [Heq | Hneq]; [| discriminate Hsrc].
      subst c'.
      set (tail := ys ++ [(d, d, 1)]).
      assert (Htail_ne : tail <> []).
      { unfold tail. intro H. cbn in H.
        eapply app_eq_nil in H. destruct H as (Ha & Hb). congruence. }
      assert (Htail_eq : ((c, x, v) :: ys) ++ [(d, d, 1)] = (c, x, v) :: tail).
      { cbn. reflexivity. }
      rewrite Htail_eq in Hcov, Hwf, Htgt |- *.
      simpl.
      apply (In_append_node_in_paths_rev
        (List.flat_map (fun z => all_paths_klength l m (length ys) z d) l)
        m c ((c, x, v) :: tail)).
      + unfold source. simpl.
        destruct (fin_eq_dec c c) as [_|Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
      + exact Htail_ne.
      + exact Hwf.
      + apply in_flat_map. exists x.
        unfold well_formed_path_aux in Hwf. cbn in Hwf.
        destruct Hwf as [Hmv Hwf_tail].
        split.
        * apply Hcov. cbn.
          destruct ys as [|h2 ys'].
          { destruct Hwf_tail as [Heq_x _]. subst x.
            right. left. reflexivity. }
          { destruct h2 as [[au av] aw].
            destruct Hwf_tail as [Heq_x Hwf_rest]. subst x.
            right. apply collect_nodes_head. }
        * unfold tail.
          destruct ys as [|h2 ys'].
          { destruct Hwf_tail as [Heq_x _]. subst x.
            simpl. destruct (fin_eq_dec d d) as [_|Hc]; [|exfalso; apply Hc; reflexivity].
            left. reflexivity. }
          { destruct h2 as [[au av] aw].
            destruct Hwf_tail as [Heq_x Hwf_rest]. subst x.
            cbn. eapply IH.
            - eapply collect_nodes_cons_covers; [exact Htail_ne | exact Hcov].
            - unfold source. simpl.
              destruct (fin_eq_dec au au) as [_|Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
            - cbn in Htgt. exact Htgt.
            - exact Hwf_rest. }
  Qed.


  (* ==================================================================== *)
  (*  Confining a path to a candidate list                                 *)
  (*                                                                       *)
  (*  [covers (collect_nodes_from_a_path p) ns] is the natural way to say  *)
  (*  that [p] stays inside [ns], but it is awkward under loop removal,    *)
  (*  because the collected-node list of a sublist is not syntactically a  *)
  (*  sublist of the collected-node list of the whole.  The edge-endpoint  *)
  (*  formulation below says the same thing and is inherited by sublists   *)
  (*  immediately, so it is the form the reduction lemmas carry.           *)
  (* ==================================================================== *)

  Definition path_nodes_in {R : Semiring.type} (ns : list Node)
    (p : list (Node * Node * R)) : Prop :=
    forall a b w, List.In (a, b, w) p -> List.In a ns /\ List.In b ns.

  (** Every node a path visits is an endpoint of one of its edges. *)
  Lemma collect_nodes_spec {R : Semiring.type} :
    forall (p : list (Node * Node * R)) (z : Node),
    List.In z (collect_nodes_from_a_path p) ->
    exists a b w, List.In (a, b, w) p /\ (z = a \/ z = b).
  Proof.
    induction p as [|((a, b), w) t IH]; intros z Hz.
    - inversion Hz.
    - destruct t as [|h t'].
      + cbn in Hz. destruct Hz as [Hz | [Hz | []]].
        * exists a, b, w. split; [left; reflexivity | left; exact (eq_sym Hz)].
        * exists a, b, w. split; [left; reflexivity | right; exact (eq_sym Hz)].
      + cbn in Hz. destruct Hz as [Hz | Hz].
        * exists a, b, w. split; [left; reflexivity | left; exact (eq_sym Hz)].
        * destruct (IH z Hz) as (a' & b' & w' & Hin & Hor).
          exists a', b', w'. split; [right; exact Hin | exact Hor].
  Qed.

  Lemma path_nodes_in_covers {R : Semiring.type} (ns : list Node)
    (p : list (Node * Node * R)) :
    path_nodes_in ns p ->
    covers (collect_nodes_from_a_path p) ns.
  Proof.
    intros Hp z Hz.
    destruct (collect_nodes_spec p z Hz) as (a & b & w & Hin & [Hor | Hor]).
    - subst z. exact (proj1 (Hp a b w Hin)).
    - subst z. exact (proj2 (Hp a b w Hin)).
  Qed.

  Lemma path_nodes_in_sublist {R : Semiring.type} (ns : list Node)
    (p q : list (Node * Node * R)) :
    (forall e, List.In e q -> List.In e p) ->
    path_nodes_in ns p ->
    path_nodes_in ns q.
  Proof.
    intros Hsub Hp a b w Hin.
    exact (Hp a b w (Hsub _ Hin)).
  Qed.

  Lemma path_nodes_in_app {R : Semiring.type} (ns : list Node)
    (p q : list (Node * Node * R)) :
    path_nodes_in ns p -> path_nodes_in ns q ->
    path_nodes_in ns (p ++ q).
  Proof.
    intros Hp Hq a b w Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin]; [exact (Hp a b w Hin) | exact (Hq a b w Hin)].
  Qed.

  Lemma path_nodes_in_app_inv {R : Semiring.type} (ns : list Node)
    (p q : list (Node * Node * R)) :
    path_nodes_in ns (p ++ q) ->
    path_nodes_in ns p /\ path_nodes_in ns q.
  Proof.
    intros Hpq. split.
    - intros a b w Hin. apply (Hpq a b w). apply in_or_app. left. exact Hin.
    - intros a b w Hin. apply (Hpq a b w). apply in_or_app. right. exact Hin.
  Qed.

  (* ==================================================================== *)
  (*  Cycle elimination against an arbitrary candidate list                *)
  (*                                                                       *)
  (*  The pigeonhole step below counts against [length ns] rather than     *)
  (*  [length elements].  [all_paths_in_klength_paths_cycle] and           *)
  (*  [length_collect_node_gen] were already stated at an arbitrary list,  *)
  (*  so only the two wrappers that fixed it to [elements] need redoing.   *)
  (* ==================================================================== *)

  (** [all_paths_in_klength_paths_cycle_finN_stronger] at an arbitrary list. *)
  Lemma all_paths_in_klength_paths_cycle_finN_stronger_gen {R : Semiring.type} :
    forall (ns : list Node) (l : list (Node * Node * R)) (m : @Matrix R),
    ns <> [] ->
    path_nodes_in ns l ->
    (List.length ns <= List.length l)%nat ->
    well_formed_path_aux m l ->
    exists ll au av aw lm lr,
    (ll, Some ((au, av, aw) :: lm), lr) =
      elem_path_triple_compute_loop_triple l /\
    cyclic_path au ((au, av, aw) :: lm) /\
    elem_path_triple ll = true /\
    l = (ll ++ ((au, av, aw) :: lm) ++ lr).
  Proof.
    intros ns l m Hne Hnodes Hfin Hw.
    pose proof length_collect_node_gen ns l Hne Hfin as Hf.
    pose proof path_nodes_in_covers ns l Hnodes as Hcov.
    pose proof all_paths_in_klength_paths_cycle ns l m Hw Hcov Hf as Hwt.
    eapply triple_compute_connect_with_triple_elem_stronger.
    exact Hwt.
  Qed.

  (** [elem_path_length] at an arbitrary candidate list: a loop-free path
      confined to [ns] is shorter than [ns]. *)
  Lemma elem_path_length_gen {R : Semiring.type} :
    forall (ns : list Node) (l : list (Node * Node * R)) m,
    ns <> [] ->
    path_nodes_in ns l ->
    elem_path_triple l = true ->
    well_formed_path_aux m l ->
    (List.length l < List.length ns)%nat.
  Proof.
    intros ns l m Hne Hnodes He Hw.
    assert (Hwt : (length l < length ns)%nat \/ (length ns <= length l)%nat) by lia.
    destruct Hwt as [Hwt | Hwt]; [exact Hwt |].
    pose proof length_collect_node_gen ns l Hne Hwt as Hf.
    pose proof path_nodes_in_covers ns l Hnodes as Hcov.
    pose proof all_paths_in_klength_paths_cycle ns l m Hw Hcov Hf as Hat.
    rewrite Hat in He. congruence.
  Qed.

  (** [reduce_path_cycle_step] at an arbitrary candidate list.  The reduced
      path is still confined to [ns], which is what lets the reduction be
      iterated. *)
  Lemma reduce_path_cycle_step_gen {R : BoundedSemiring.type} :
    forall (ns : list Node) (l : list (Node * Node * R)) (m : @Matrix R) c d,
    ns <> [] ->
    path_nodes_in ns l ->
    (length ns <= length l)%nat ->
    well_formed_path_aux m (l ++ [(d, d, 1)]) ->
    source c (l ++ [(d, d, 1)]) = true ->
    target d (l ++ [(d, d, 1)]) = true ->
    exists ys,
      (List.length ys < List.length l)%nat /\
      path_nodes_in ns ys /\
      well_formed_path_aux m (ys ++ [(d, d, 1)]) /\
      source c (ys ++ [(d, d, 1)]) = true /\
      target d (ys ++ [(d, d, 1)]) = true /\
      Orel (measure_of_path l) (measure_of_path ys).
  Proof.
    intros ns l m c d Hne Hnodes Hlen Hwf Hsrc Htgt.
    destruct (well_formed_path_snoc l [(d, d, 1)] m Hwf) as [Hwf_l Hwf_d].
    simpl in Hwf_d. destruct Hwf_d as [Hdiag _].
    pose proof (all_paths_in_klength_paths_cycle_finN_stronger_gen
      ns l m Hne Hnodes Hlen Hwf_l) as Hcycle.
    destruct Hcycle as (ll & au & av & aw & lm & lr & _ & Hcyc & _ & Hpath).
    set (ys := ll ++ lr).
    assert (Hlen_ys : List.length ys < List.length l).
    { subst ys. rewrite Hpath. rewrite !length_app. cbn. lia. }
    assert (Hnodes_ys : path_nodes_in ns ys).
    { subst ys. eapply path_nodes_in_sublist; [| exact Hnodes].
      intros e He. rewrite Hpath. apply in_app_or in He.
      destruct He as [He | He].
      - apply in_or_app. left. exact He.
      - apply in_or_app. right. apply in_or_app. right. exact He. }
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
    exists ys.
    split; [exact Hlen_ys |].
    split; [exact Hnodes_ys |].
    split; [exact Hwf_ys |].
    split; [exact Hsrc_ys |].
    split; [exact Htgt_ys |].
    exact Horel.
  Qed.

  (** Every path confined to [ns] is dominated by a loop-free path confined
      to [ns] with the same endpoints.  Unlike [reduce_path_into_simpl_path]
      this needs no lower bound on the length of the input path, since the
      already-short case simply returns the path itself. *)
  Lemma reduce_path_into_simpl_path_gen {R : BoundedSemiring.type} :
    forall (ns : list Node) (l : list (Node * Node * R)) (m : @Matrix R) c d,
    ns <> [] ->
    path_nodes_in ns l ->
    well_formed_path_aux m (l ++ [(d, d, 1)]) ->
    source c (l ++ [(d, d, 1)]) = true ->
    target d (l ++ [(d, d, 1)]) = true ->
    exists ys,
      (List.length ys < List.length ns)%nat /\
      path_nodes_in ns ys /\
      well_formed_path_aux m (ys ++ [(d, d, 1)]) /\
      source c (ys ++ [(d, d, 1)]) = true /\
      target d (ys ++ [(d, d, 1)]) = true /\
      Orel (measure_of_path l) (measure_of_path ys).
  Proof.
    intros ns l.
    induction (zwf_well_founded l) as [l Hf IHl].
    unfold zwf in * |- *.
    intros m c d Hne Hnodes Hwf Hsrc Htgt.
    assert (Hshort_or_long : (length l < length ns)%nat \/
      (length ns <= length l)%nat) by lia.
    destruct Hshort_or_long as [Hshort | Hlong].
    - exists l.
      split; [exact Hshort |].
      split; [exact Hnodes |].
      split; [exact Hwf |].
      split; [exact Hsrc |].
      split; [exact Htgt |].
      unfold Orel. apply bounded_add_idem.
    - pose proof (reduce_path_cycle_step_gen ns l m c d Hne Hnodes Hlong Hwf Hsrc Htgt)
        as (ys & Hyslen & Hnodes_ys & Hwf_ys & Hsrc_ys & Htgt_ys & Horel_ys).
      specialize (IHl ys Hyslen m c d Hne Hnodes_ys Hwf_ys Hsrc_ys Htgt_ys)
        as (zs & Hzs_short & Hnodes_zs & Hwf_zs & Hsrc_zs & Htgt_zs & Horel_zs).
      exists zs.
      split; [exact Hzs_short |].
      split; [exact Hnodes_zs |].
      split; [exact Hwf_zs |].
      split; [exact Hsrc_zs |].
      split; [exact Htgt_zs |].
      eapply orel_trans; [exact Horel_ys | exact Horel_zs].
  Qed.


  (* ==================================================================== *)
  (*  The closure over a candidate list                                    *)
  (*                                                                       *)
  (*  [path_star ns m c d] sums the measures of every path from [c] to [d] *)
  (*  of length at most [length ns - 1] whose intermediate nodes are drawn *)
  (*  from [ns].  At [ns := elements] it agrees with [mat_star] by         *)
  (*  [connect_partial_sum_mat_paths], so this is the same closure viewed  *)
  (*  through its path characterisation rather than through matrix         *)
  (*  multiplication, and unlike [mat_star] it can speak about two         *)
  (*  different sets of alternatives at one ambient [Node] type.           *)
  (* ==================================================================== *)

  (** In a bounded semiring [Orel] has the least-upper-bound shape on [+],
      which is what makes [path_star] behave like a supremum over paths.
      [OrelN] proves these for [IdempotentSemiring], which [BoundedSemiring]
      does not coerce into, so they are rederived here from
      [bounded_add_idem]. *)
  Lemma bounded_orel_plus_left {R : BoundedSemiring.type} (a b : R) :
    Orel a (a + b).
  Proof.
    unfold Orel. rewrite <- addA. rewrite bounded_add_idem. reflexivity.
  Qed.

  Lemma bounded_orel_plus_mono {R : BoundedSemiring.type} (x y z : R) :
    Orel x y -> Orel x (z + y).
  Proof.
    unfold Orel. intros Hxy.
    rewrite <- addA. rewrite (addC x z). rewrite addA. rewrite Hxy. reflexivity.
  Qed.

  Lemma bounded_orel_plus_glb {R : BoundedSemiring.type} (x y v : R) :
    Orel x v -> Orel y v -> Orel (x + y) v.
  Proof.
    unfold Orel. intros Hx Hy.
    rewrite addA. rewrite Hy. exact Hx.
  Qed.

  (** Each summand is below the sum. *)
  Lemma sum_all_flat_paths_member {R : BoundedSemiring.type} :
    forall (lp : list (@Path R)) (a b : Node) (p : list (Node * Node * R)),
    List.In (a, b, p) lp ->
    Orel (measure_of_path p) (sum_all_flat_paths lp).
  Proof.
    induction lp as [|((a', b'), p') t IH]; intros a b p Hin.
    - inversion Hin.
    - cbn [sum_all_flat_paths].
      destruct Hin as [Heq | Hin].
      + inversion Heq. subst p'.
        apply bounded_orel_plus_left.
      + apply bounded_orel_plus_mono.
        exact (IH a b p Hin).
  Qed.

  (** A common bound on the summands bounds the sum. *)
  Lemma sum_all_flat_paths_bound {R : BoundedSemiring.type} :
    forall (lp : list (@Path R)) (v : R),
    (forall a b p, List.In (a, b, p) lp -> Orel (measure_of_path p) v) ->
    Orel (sum_all_flat_paths lp) v.
  Proof.
    induction lp as [|((a', b'), p') t IH]; intros v Hall.
    - cbn. unfold Orel. rewrite add0r. reflexivity.
    - cbn [sum_all_flat_paths].
      apply bounded_orel_plus_glb.
      + exact (Hall a' b' p' (or_introl eq_refl)).
      + apply IH. intros a b p Hin.
        exact (Hall a b p (or_intror Hin)).
  Qed.

  (** [flat_map_path_partial_sum] at an arbitrary candidate list. *)
  Lemma flat_map_path_partial_sum_gen {R : Semiring.type} :
    forall (ns : list Node) n (m : @Matrix R) c d,
    partial_sum_paths ns m n c d =
    @sum_all_flat_paths R (enum_all_paths_flat ns m n c d).
  Proof.
    intros ns. induction n as [|n IH]; intros m c d.
    - cbn. destruct (fin_eq_dec c d) as [Hcd | Hcd]; cbn.
      + rewrite mul1r. rewrite addr0. reflexivity.
      + reflexivity.
    - cbn [partial_sum_paths enum_all_paths_flat].
      rewrite IH.
      rewrite sum_all_rvalues_get_all_rvalues.
      rewrite sum_all_flat_paths_app.
      rewrite addC.
      reflexivity.
  Qed.

  (** A path of length at most [n] appears in the flattened enumeration. *)
  Lemma enum_all_paths_flat_member {R : Semiring.type} :
    forall (ns : list Node) (n k : nat) (m : @Matrix R) (c d : Node)
    (p : list (Node * Node * R)),
    (k <= n)%nat ->
    List.In p (all_paths_klength ns m k c d) ->
    List.In (c, d, p) (enum_all_paths_flat ns m n c d).
  Proof.
    intros ns. induction n as [|n IH]; intros k m c d p Hk Hin.
    - assert (Hk0 : k = 0%nat) by lia. subst k.
      cbn [enum_all_paths_flat]. unfold construct_all_paths.
      exact (in_map (fun l => (c, d, l)) _ p Hin).
    - cbn [enum_all_paths_flat].
      apply in_or_app.
      destruct (PeanoNat.Nat.eq_dec k (S n)) as [Heq | Hne].
      + subst k. left. unfold construct_all_paths.
        exact (in_map (fun l => (c, d, l)) _ p Hin).
      + right. apply (IH k m c d p); [lia | exact Hin].
  Qed.

  (** Conversely, everything in the flattened enumeration is a path of some
      length at most [n]. *)
  Lemma enum_all_paths_flat_inv {R : Semiring.type} :
    forall (ns : list Node) (n : nat) (m : @Matrix R) (c d a b : Node)
    (p : list (Node * Node * R)),
    List.In (a, b, p) (enum_all_paths_flat ns m n c d) ->
    exists k, (k <= n)%nat /\ List.In p (all_paths_klength ns m k c d).
  Proof.
    intros ns. induction n as [|n IH]; intros m c d a b p Hin.
    - cbn [enum_all_paths_flat] in Hin. unfold construct_all_paths in Hin.
      apply in_map_iff in Hin.
      destruct Hin as (q & Heq & Hq).
      inversion Heq. subst.
      exists 0%nat. split; [lia | exact Hq].
    - cbn [enum_all_paths_flat] in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + unfold construct_all_paths in Hin.
        apply in_map_iff in Hin.
        destruct Hin as (q & Heq & Hq).
        inversion Heq. subst.
        exists (S n). split; [lia | exact Hq].
      + destruct (IH m c d a b p Hin) as (k & Hk & Hq).
        exists k. split; [lia | exact Hq].
  Qed.

  Lemma path_measure_le_partial_sum {R : BoundedSemiring.type} :
    forall (ns : list Node) (n k : nat) (m : @Matrix R) (c d : Node)
    (p : list (Node * Node * R)),
    (k <= n)%nat ->
    List.In p (all_paths_klength ns m k c d) ->
    Orel (measure_of_path p) (partial_sum_paths ns m n c d).
  Proof.
    intros ns n k m c d p Hk Hin.
    rewrite flat_map_path_partial_sum_gen.
    exact (sum_all_flat_paths_member _ c d p
             (enum_all_paths_flat_member ns n k m c d p Hk Hin)).
  Qed.

  Lemma partial_sum_paths_bound {R : BoundedSemiring.type} :
    forall (ns : list Node) (n : nat) (m : @Matrix R) (c d : Node) (v : R),
    (forall k p, (k <= n)%nat -> List.In p (all_paths_klength ns m k c d) ->
       Orel (measure_of_path p) v) ->
    Orel (partial_sum_paths ns m n c d) v.
  Proof.
    intros ns n m c d v Hall.
    rewrite flat_map_path_partial_sum_gen.
    apply sum_all_flat_paths_bound.
    intros a b p Hin.
    destruct (enum_all_paths_flat_inv ns n m c d a b p Hin) as (k & Hk & Hq).
    exact (Hall k p Hk Hq).
  Qed.

  (** The path-strength closure over the candidate list [ns]. *)
  Definition path_star {R : Semiring.type} (ns : list Node)
    (m : @Matrix R) (c d : Node) : R :=
    partial_sum_paths ns m (List.length ns - 1) c d.

  (** Lower bound: any counted path is below the closure. *)
  Lemma path_star_lower {R : BoundedSemiring.type} :
    forall (ns : list Node) (m : @Matrix R) (c d : Node)
    (p : list (Node * Node * R)) (k : nat),
    (k <= List.length ns - 1)%nat ->
    List.In p (all_paths_klength ns m k c d) ->
    Orel (measure_of_path p) (path_star ns m c d).
  Proof.
    intros ns m c d p k Hk Hin.
    exact (path_measure_le_partial_sum ns _ k m c d p Hk Hin).
  Qed.

  (** Upper bound: a common bound on every counted path bounds the closure. *)
  Lemma path_star_upper {R : BoundedSemiring.type} :
    forall (ns : list Node) (m : @Matrix R) (c d : Node) (v : R),
    (forall k p, (k <= List.length ns - 1)%nat ->
       List.In p (all_paths_klength ns m k c d) ->
       Orel (measure_of_path p) v) ->
    Orel (path_star ns m c d) v.
  Proof.
    intros ns m c d v Hall.
    exact (partial_sum_paths_bound ns _ m c d v Hall).
  Qed.

  (** The form the lower bound is actually used in: exhibit a concrete
      well-formed path confined to [ns] and short enough, and its measure
      is below the closure.  Completeness does the work of showing the
      path is one of the counted ones. *)
  Lemma path_star_lower_of_path {R : BoundedSemiring.type} :
    forall (ns : list Node) (m : @Matrix R) (c d : Node)
    (xs : list (Node * Node * R)),
    path_nodes_in ns (xs ++ [(d, d, 1)]) ->
    (List.length xs <= List.length ns - 1)%nat ->
    source c (xs ++ [(d, d, 1)]) = true ->
    target d (xs ++ [(d, d, 1)]) = true ->
    well_formed_path_aux m (xs ++ [(d, d, 1)]) ->
    Orel (measure_of_path (xs ++ [(d, d, 1)])) (path_star ns m c d).
  Proof.
    intros ns m c d xs Hnodes Hlen Hsrc Htgt Hwf.
    apply (path_star_lower ns m c d _ (List.length xs) Hlen).
    apply all_paths_klength_complete_gen; try assumption.
    exact (path_nodes_in_covers ns _ Hnodes).
  Qed.



  (* ==================================================================== *)
  (*  Composing closures over a candidate list                             *)
  (*                                                                       *)
  (*  [path_star_compose] is the list-indexed analogue of                  *)
  (*  [star_path_compose] in SocialchoiceN.  The matrix proof there goes   *)
  (*  through [pow (M + I)] and its stabilization; that route is not       *)
  (*  available at an arbitrary candidate list, so the proof here is the   *)
  (*  direct path-level one: concatenate a path from [a] to [b] with a     *)
  (*  path from [b] to [c] and reduce the result.  Bounding a product of   *)
  (*  two path sums needs distributivity, which is what the three          *)
  (*  [_mul_bound] lemmas supply.                                          *)
  (* ==================================================================== *)

  (** The measure of a path is unchanged by its terminal unit loop. *)
  Lemma measure_snoc_unit {R : Semiring.type}
    (xs : list (Node * Node * R)) (e : Node) :
    measure_of_path (xs ++ [(e, e, 1)]) = measure_of_path xs.
  Proof.
    rewrite (measure_of_path_app (xs ++ [(e, e, 1)]) xs [(e, e, 1)] eq_refl).
    cbn. rewrite mulr1. rewrite mulr1. reflexivity.
  Qed.

  (** Every edge of a well-formed path carries the matrix entry of its
      endpoints. *)
  Lemma well_formed_edge {R : Semiring.type} (m : @Matrix R)
    (p : list (Node * Node * R)) (a b : Node) (w : R) :
    well_formed_path_aux m p -> List.In (a, b, w) p -> m a b = w.
  Proof.
    induction p as [|((x, y), v) t IH]; intros Hwf Hin.
    - inversion Hin.
    - cbn in Hwf. destruct Hwf as [Hxy Hrest].
      destruct Hin as [Heq | Hin].
      + inversion Heq; congruence.
      + apply IH; [| exact Hin].
        destruct t as [|((x', y'), v') t']; [exact Logic.I |].
        exact (proj2 Hrest).
  Qed.

  (** Converse of [path_nodes_in_covers], for well-formed paths: the target of
      each edge is the source of the next, so it is collected too. *)
  Lemma covers_path_nodes_in {R : Semiring.type} (m : @Matrix R)
    (ns : list Node) (p : list (Node * Node * R)) :
    well_formed_path_aux m p ->
    covers (collect_nodes_from_a_path p) ns ->
    path_nodes_in ns p.
  Proof.
    induction p as [|((a, b), w) t IH]; intros Hwf Hcov.
    - intros x y u Hin. inversion Hin.
    - cbn in Hwf. destruct Hwf as [Hab Hrest].
      destruct t as [|((b', c), w') t'].
      + intros x y u Hin. destruct Hin as [Heq | []].
        inversion Heq. subst.
        split; apply Hcov; cbn; [left; reflexivity | right; left; reflexivity].
      + destruct Hrest as [Heq_b Hwf_t]. subst b'.
        assert (Hcov_t : covers (collect_nodes_from_a_path ((b, c, w') :: t')) ns).
        { intros z Hz. apply Hcov. cbn. right. exact Hz. }
        pose proof (IH Hwf_t Hcov_t) as Hnodes_t.
        intros x y u Hin. destruct Hin as [Heq | Hin].
        * inversion Heq. subst.
          split.
          -- apply Hcov. cbn. left. reflexivity.
          -- apply Hcov_t. apply collect_nodes_head.
        * exact (Hnodes_t x y u Hin).
  Qed.

  (** The endpoints [all_paths_klength_nodes] adds are already in the list
      when both endpoints are candidates. *)
  Lemma covers_cons2_drop (X : list Node) (a b : Node) (ns : list Node) :
    List.In a ns -> List.In b ns ->
    covers X (a :: b :: ns) -> covers X ns.
  Proof.
    intros Ha Hb HX z Hz.
    destruct (HX z Hz) as [H | [H | H]];
      [rewrite <- H; exact Ha | rewrite <- H; exact Hb | exact H].
  Qed.

  Lemma source_app {R : Semiring.type} (a : Node)
    (p q : list (Node * Node * R)) :
    p <> [] -> source a (p ++ q) = source a p.
  Proof.
    intros Hne. destruct p as [|((x, y), w) t];
      [exfalso; apply Hne; reflexivity | reflexivity].
  Qed.

  Lemma target_app {R : Semiring.type} (c : Node)
    (p q : list (Node * Node * R)) :
    q <> [] -> target c (p ++ q) = target c q.
  Proof.
    intros Hne. induction p as [|((x, y), w) t IH]; [reflexivity |].
    cbn [app target].
    destruct (t ++ q) as [|h r] eqn:Htq.
    - exfalso. apply app_eq_nil in Htq. destruct Htq as [_ Hq].
      exact (Hne Hq).
    - exact IH.
  Qed.

  (** Concatenation: a path ending with the unit loop at [b] may have that
      loop replaced by any well-formed path starting at [b]. *)
  Lemma well_formed_replace_unit_tail {R : Semiring.type} (m : @Matrix R)
    (q : list (Node * Node * R)) (b : Node) :
    well_formed_path_aux m q ->
    source b q = true ->
    forall (p : list (Node * Node * R)),
    well_formed_path_aux m (p ++ [(b, b, 1)]) ->
    well_formed_path_aux m (p ++ q).
  Proof.
    intros Hwfq Hsrc.
    destruct q as [|((b', v0), z0) q']; [discriminate Hsrc |].
    cbn in Hsrc. destruct (fin_eq_dec b b') as [Hbb | Hbb]; [| discriminate Hsrc].
    subst b'.
    induction p as [|((x, y), w) t IH]; intros Hwf.
    - cbn. exact Hwfq.
    - destruct t as [|((u, v), z) t'].
      + cbn in Hwf. destruct Hwf as [Hxy [Hyb _]]. subst y.
        cbn. split; [exact Hxy | split; [reflexivity | exact Hwfq]].
      + cbn [app] in Hwf |- *.
        cbn in Hwf. destruct Hwf as [Hxy [Hyu Hwf_t]].
        cbn. split; [exact Hxy | split; [exact Hyu |]].
        exact (IH Hwf_t).
  Qed.

  (** Distributivity, in the two shapes the composition proof needs. *)
  Lemma mul_sum_all_flat_paths_bound {R : BoundedSemiring.type} (x : R)
    (lp : list (@Path R)) (v : R) :
    (forall a b p, List.In (a, b, p) lp -> Orel (x * measure_of_path p) v) ->
    Orel (x * sum_all_flat_paths lp) v.
  Proof.
    induction lp as [|((a, b), p) t IH]; intros Hall.
    - cbn. setoid_rewrite mulr0. apply zero_is_bottom.
    - cbn [sum_all_flat_paths]. setoid_rewrite mulDl.
      apply bounded_orel_plus_glb.
      + exact (Hall a b p (or_introl eq_refl)).
      + apply IH. intros a' b' p' Hin. exact (Hall a' b' p' (or_intror Hin)).
  Qed.

  Lemma sum_all_flat_paths_mul_bound {R : BoundedSemiring.type}
    (lp1 lp2 : list (@Path R)) (v : R) :
    (forall a1 b1 p1 a2 b2 p2,
       List.In (a1, b1, p1) lp1 -> List.In (a2, b2, p2) lp2 ->
       Orel (measure_of_path p1 * measure_of_path p2) v) ->
    Orel (sum_all_flat_paths lp1 * sum_all_flat_paths lp2) v.
  Proof.
    induction lp1 as [|((a, b), p) t IH]; intros Hall.
    - cbn. setoid_rewrite mul0r. apply zero_is_bottom.
    - cbn [sum_all_flat_paths]. setoid_rewrite mulDr.
      apply bounded_orel_plus_glb.
      + apply mul_sum_all_flat_paths_bound.
        intros a2 b2 p2 Hin2.
        exact (Hall a b p a2 b2 p2 (or_introl eq_refl) Hin2).
      + apply IH. intros a1 b1 p1 a2 b2 p2 Hin1 Hin2.
        exact (Hall a1 b1 p1 a2 b2 p2 (or_intror Hin1) Hin2).
  Qed.

  Lemma partial_sum_paths_mul_bound {R : BoundedSemiring.type} (ns : list Node)
    (m : @Matrix R) (n1 n2 : nat) (c1 d1 c2 d2 : Node) (v : R) :
    (forall k1 p1 k2 p2,
       (k1 <= n1)%nat -> List.In p1 (all_paths_klength ns m k1 c1 d1) ->
       (k2 <= n2)%nat -> List.In p2 (all_paths_klength ns m k2 c2 d2) ->
       Orel (measure_of_path p1 * measure_of_path p2) v) ->
    Orel (partial_sum_paths ns m n1 c1 d1 * partial_sum_paths ns m n2 c2 d2) v.
  Proof.
    intros Hall.
    rewrite !flat_map_path_partial_sum_gen.
    apply sum_all_flat_paths_mul_bound.
    intros a1 b1 p1 a2 b2 p2 Hin1 Hin2.
    destruct (enum_all_paths_flat_inv ns n1 m c1 d1 a1 b1 p1 Hin1) as (k1 & Hk1 & Hq1).
    destruct (enum_all_paths_flat_inv ns n2 m c2 d2 a2 b2 p2 Hin2) as (k2 & Hk2 & Hq2).
    exact (Hall k1 p1 k2 p2 Hk1 Hq1 Hk2 Hq2).
  Qed.

  (** Concatenating a strongest path from [a] to [b] with one from [b] to [c]
      gives a path from [a] to [c], so the closure composes. *)
  Lemma path_star_compose {R : BoundedSemiring.type} (ns : list Node)
    (m : @Matrix R) (a b c : Node) :
    ns <> [] ->
    (forall u v : Node, u = v -> m u v = 1) ->
    List.In a ns -> List.In b ns -> List.In c ns ->
    Orel (path_star ns m a b * path_star ns m b c) (path_star ns m a c).
  Proof.
    intros Hns Hdiag Ha Hb Hc.
    unfold path_star at 1 2.
    apply partial_sum_paths_mul_bound.
    intros k1 p1 k2 p2 Hk1 Hin1 Hk2 Hin2.
    pose proof (all_paths_well_formed_in_kpaths_gen ns k1 m a b p1 Hdiag Hin1) as Hwf1.
    pose proof (covers_path_nodes_in m ns p1 Hwf1
      (covers_cons2_drop _ a b ns Ha Hb
        (all_paths_klength_nodes ns k1 m a b p1 Hin1))) as Hn1.
    destruct (non_empty_paths_in_kpath_gen ns k1 m a b p1 Hin1)
      as (Hne1 & Hsrc1 & Htgt1).
    destruct (path_end_unit_loop_gen ns k1 p1 m a b Hin1) as [p1' Hp1].
    pose proof (all_paths_well_formed_in_kpaths_gen ns k2 m b c p2 Hdiag Hin2) as Hwf2.
    pose proof (covers_path_nodes_in m ns p2 Hwf2
      (covers_cons2_drop _ b c ns Hb Hc
        (all_paths_klength_nodes ns k2 m b c p2 Hin2))) as Hn2.
    destruct (non_empty_paths_in_kpath_gen ns k2 m b c p2 Hin2)
      as (Hne2 & Hsrc2 & Htgt2).
    destruct (path_end_unit_loop_gen ns k2 p2 m b c Hin2) as [p2' Hp2].
    assert (Hqeq : p1' ++ p2 = (p1' ++ p2') ++ [(c, c, 1)]).
    { rewrite Hp2 at 1. rewrite app_assoc. reflexivity. }
    assert (Hmeas : measure_of_path p1' * measure_of_path p2
                    = measure_of_path (p1' ++ p2')).
    { rewrite <- (measure_of_path_app (p1' ++ p2) p1' p2 eq_refl).
      rewrite Hqeq. apply measure_snoc_unit. }
    assert (Hwf_q : well_formed_path_aux m ((p1' ++ p2') ++ [(c, c, 1)])).
    { rewrite <- Hqeq.
      apply (well_formed_replace_unit_tail m p2 b Hwf2 Hsrc2 p1').
      rewrite <- Hp1. exact Hwf1. }
    assert (Hsrc_q : source a ((p1' ++ p2') ++ [(c, c, 1)]) = true).
    { rewrite <- Hqeq.
      destruct p1' as [|e p1''].
      - cbn in Hp1. cbn.
        rewrite Hp1 in Hsrc1. cbn in Hsrc1.
        destruct (fin_eq_dec a b) as [Hab | Hab]; [| discriminate Hsrc1].
        rewrite Hab. exact Hsrc2.
      - assert (Hne' : e :: p1'' <> []) by discriminate.
        rewrite (source_app a (e :: p1'') p2 Hne').
        rewrite Hp1 in Hsrc1.
        rewrite (source_app a (e :: p1'') [(b, b, 1)] Hne') in Hsrc1.
        exact Hsrc1. }
    assert (Htgt_q : target c ((p1' ++ p2') ++ [(c, c, 1)]) = true).
    { rewrite target_end. cbn.
      destruct (fin_eq_dec c c) as [_ | Hcc];
        [reflexivity | exfalso; apply Hcc; reflexivity]. }
    assert (Hn1' : path_nodes_in ns p1').
    { rewrite Hp1 in Hn1.
      exact (proj1 (path_nodes_in_app_inv ns p1' [(b, b, 1)] Hn1)). }
    assert (Hn2' : path_nodes_in ns p2').
    { rewrite Hp2 in Hn2.
      exact (proj1 (path_nodes_in_app_inv ns p2' [(c, c, 1)] Hn2)). }
    assert (Hn_q : path_nodes_in ns (p1' ++ p2'))
      by exact (path_nodes_in_app ns p1' p2' Hn1' Hn2').
    destruct (reduce_path_into_simpl_path_gen ns (p1' ++ p2') m a c
                Hns Hn_q Hwf_q Hsrc_q Htgt_q)
      as (ys & Hlen_ys & Hnodes_ys & Hwf_ys & Hsrc_ys & Htgt_ys & Horel_ys).
    assert (Hnodes_full : path_nodes_in ns (ys ++ [(c, c, 1)])).
    { apply path_nodes_in_app; [exact Hnodes_ys |].
      intros x y u Hin_e. destruct Hin_e as [Heq | []].
      inversion Heq. subst. split; exact Hc. }
    assert (Hlen_bound : (List.length ys <= List.length ns - 1)%nat) by lia.
    pose proof (path_star_lower_of_path ns m a c ys
                  Hnodes_full Hlen_bound Hsrc_ys Htgt_ys Hwf_ys) as Hlow.
    rewrite measure_snoc_unit in Hlow.
    rewrite Hp1. rewrite measure_snoc_unit. rewrite Hmeas.
    eapply orel_trans; [exact Horel_ys | exact Hlow].
  Qed.


End Path.
