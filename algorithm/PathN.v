From Stdlib Require Import List Utf8
  BinNatDef Lia.
From Semiring Require Import OrelN Structures.
Import ListNotations SemiringNotations.

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

  Lemma map_measure_simp {R : Semiring.type} : 
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


  






  
  







End Path.