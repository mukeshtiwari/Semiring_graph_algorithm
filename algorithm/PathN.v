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
    match p with
    | (_, _, lp) => List.In lp 
        (List.map (fun '(_, _, lt) => lt) lpp)
    end.

  (* Proofs start from here *)



End Path. 
