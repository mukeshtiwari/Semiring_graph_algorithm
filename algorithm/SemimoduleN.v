From Stdlib Require Import List Utf8
  Lia.
From Semiring Require Import PathN MatN 
  OrelN Structures.
Import ListNotations SemiringNotations.

Section Semimodule.
  Context 
    {Node : FinType.type}.


  Definition Vector {R : Semiring.type} 
    {U : Semimodule.type R} : Type := 
    Node -> Semimodule.sort R U. 

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


    

End Semimodule.




