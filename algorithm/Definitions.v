From Stdlib Require Import List Utf8
  Lia.
Import ListNotations.

Section Definitions.


  (* Binary relation *)
  Definition brel (A : Type) := A -> A -> bool.
  
  (* reflexivie *)
  Definition brel_reflexive 
    (A : Type) (eqA : brel A) :=
    forall (x : A), eqA x x = true.

  (* Symmetric *)
  Definition brel_symmetric 
    (A : Type) (eqA : brel A) := 
    forall (x y : A), eqA x y = true -> 
    eqA y x = true.
  
  (* transitive *)
  Definition brel_transitive 
    (A : Type) (eqA : brel A) :=
    forall (x y z : A), eqA x y = true ->
    eqA y z = true -> eqA x z = true.

  Definition brel_congruence (A : Type) 
    (eqA : brel A) (eqB : brel A) := 
    forall (s t u v : A), 
    eqA s u = true -> 
    eqA t v = true ->
    eqB s t = eqB u v.
  
 


  (* Equality of List *)
  Definition brel_list {A : Type} 
    (eqA : brel A) : list A -> list A -> bool.
  Proof.
    refine(fix Fn xs {struct xs} := 
      match xs with 
      | [] => fun ys => 
        match ys with 
        | [] => true
        | _ :: _ => false
        end 
      | x :: xss => fun ys => 
        match ys with 
        | [] => false
        | y :: yss => (andb (eqA x y) (Fn xss yss))
        end
      end).
  Defined.

  Definition in_list {A : Type} 
    (eqA : brel A) : list A -> A -> bool.
  Proof.
    refine(fix Fn xs {struct xs} := 
      match xs with 
      | [] => fun _ => false
      | y :: yss => fun x => orb (eqA x y) (Fn yss x)
      end).
  Defined.

  Definition binary_op (A : Type) := 
    A -> A -> A.

  Definition bop_congruence 
    (A : Type) (r : brel A) (b : binary_op A) := 
    ∀ (s₁ s₂ t₁ t₂ : A), 
    r s₁ t₁ = true -> 
    r s₂ t₂ = true -> 
    r (b s₁ s₂) (b t₁ t₂) = true.

End Definitions.
  
  




