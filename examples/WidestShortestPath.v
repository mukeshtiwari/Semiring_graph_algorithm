Require Import Semiring.algorithm.Mat List BinNatDef
  Semiring.algorithm.Definitions Semiring.algorithm.Listprop
  Psatz Utf8 Coq.Arith.EqNat.
Import ListNotations.

Section Comp.

  (* Define Candidates *)
  Inductive Node := A | B | C. 
  
  (* Equality on Candidate *)
  Definition eqN (x y : Node) : bool :=
  match x, y with 
  | A, A => true 
  | B, B => true 
  | C, C => true 
  | _, _ => false
  end. 

   (* Nat extended with Infinity *)
  Inductive R := 
  | Left : nat -> R 
  | Infinity : R.

  Definition eqR (u v : R) : bool :=
  match u, v with 
  | Left x, Left y => Nat.eqb x y 
  | Infinity, Infinity => true 
  | _, _ => false 
  end. 

  Definition RR : Type := R * R. 

  Definition zeroR : RR := (Left 0, Infinity). 

  Definition oneR : RR := (Infinity, Left 0).

  Definition ltR (u v : R) : bool :=
  match u, v with 
  | Left x, Left y => Nat.ltb x y 
  | Left x, Infinity => true 
  | Infinity, Left _ => false 
  | _, _ => false
  end.

  Definition plusR (u v : R) : R :=
  match u, v with 
  | Left x, Left y => Left (Nat.add x y)
  | _, _ => Infinity 
  end. 

  (* Authors didn't make it clear how infinity in*)
  Definition mulR (u v : R) : R :=
  match u, v with 
  | Left x, Left y => Left (Nat.mul x y)
  | _, _ => Infinity 
  end.


  Definition plusRR (u v : RR) : RR :=
  match u, v with 
  | (au, bu), (av, bv) => 
    match orb (ltR au av) (andb (eqR au av) (ltR bu bv)) with 
    | true => (au, bu)
    | _ => (av, bv)
    end 
  end. 

  Definition minR (u v : R) : R :=
  match u, v with 
  | Left x, Left y => Left (Nat.min x y)
  | Left x, Infinity => Left x
  | Infinity, Left x => Left x 
  | _, _ => Infinity
  end. 


  Definition mulRR (u v : RR) : RR :=
  match u, v with 
  | (au, bu), (av, bv) => (plusR au av, minR bu bv)
  end.  


  Definition finN : list Node := [A; B; C].

  (* Now, configure the matrix *)
  Definition widest_shortest_path (m : Path.Matrix Node RR) : Path.Matrix Node RR :=
    matrix_exp_binary Node eqN finN RR zeroR oneR plusRR mulRR m 2%N.

End Comp. 

Section Proofs. 


End Proofs.
  

