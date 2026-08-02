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
  Fixpoint brel_list {A : Type} 
    (eqA : brel A) (xs ys : list A) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => eqA x y && brel_list eqA xs' ys'
    | _, _ => false
    end.

  Definition in_list {A : Type} 
    (eqA : brel A) (l : list A) (x : A) : bool :=
    List.existsb (eqA x) l.

  Definition binary_op (A : Type) := 
    A -> A -> A.

  Definition bop_congruence 
    (A : Type) (r : brel A) (b : binary_op A) := 
    ∀ (s₁ s₂ t₁ t₂ : A), 
    r s₁ t₁ = true -> 
    r s₂ t₂ = true -> 
    r (b s₁ s₂) (b t₁ t₂) = true.

  (* ----------------------------------------------------------------------- *)
  (*  Convert a boolean relation to a Prop-valued relation for setoid rewriting *)
  (* ----------------------------------------------------------------------- *)

  Definition brel_prop {A : Type} (r : brel A) : A -> A -> Prop :=
    fun x y => r x y = true.

  (* ----------------------------------------------------------------------- *)
  (*  Useful lemma: brel_list forces equal lengths                           *)
  (* ----------------------------------------------------------------------- *)

  Lemma brel_list_length {A : Type} (eqA : brel A) (xs ys : list A) :
    brel_list eqA xs ys = true -> List.length xs = List.length ys.
  Proof.
    revert ys.
    induction xs as [|x xs IH]; intros [|y ys]; simpl; auto; try congruence.
    intros H. apply Bool.andb_true_iff in H. destruct H as [_ H].
    apply f_equal. apply IH. exact H.
  Qed.

End Definitions.
  
  




