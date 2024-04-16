# Semiring_graph_algorithm
Run `dune build` (ignore the warinings) in this directory to compile the project. It will compile the Coq code and 
generate OCaml code from it (see _CoqProject file). 
1. Run `dune exec _build/default/executable/schulzecode/main.exe` to run the Schulze method 
2. Run `dune exec _build/default/executable/shortestpath/main.exe` to run the shortest path code 
3. Run `dune exec _build/default/executable/widestpathcode/main.exe` to run the shortest-widest path algorithm. 
    
We have compiled this project with Coq 8.19.1 but if you want to use it with any other Coq version, please let us know. 


If you want to verify that your algebra is a semiring, do the following:
1. Define your `Set : R`, `plus : R -> R -> R`, `mul : R -> R -> R`, `0 : R`, and `1 : R` and configure your matrix of semiring values.
2. Call the function `matrix_exp_binary` with your configured matrix of semiring values.
3. Discharge all the axioms of semiring.
  ```
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

  ```
4. Moreover, this formalisation assumes bounded and idempotent semiring to compute the fixed-point.
  ```
   (zero_stable : forall a : R, 1 + a =r= 1 = true) 
   (plus_idempotence : forall a, a + a =r= a = true)
  ``` 
5. See the Coq files in [examples](./examples/) directory for more information.


Some design decisions: we have used function type (A -> B -> C) to model a matrix datatype but this may not be an efficient if your matrix size is large. 
If you are in this situation then you should encode your matrix datatype as a list, or a map, and write a simple search function to look for the values. 
See the OCaml code below. In this code, the matrix datatype `mat` and `fnmat` are same but from the execution point of view --I believe-- 
`fnmat` is much better. We hopefully would move this code from OCaml to Coq with some proofs so that it is more trustworthy. 

```
(* configure the matrix. *)
let mat (x : coq_Node) (y : coq_Node) : coq_RR = 
  match x, y with
  | A, A -> oneRR
  | A, B -> (Left 3, Left 5) 
  | B, A -> zeroRR 
  | A, C -> (Left 5, Left 4)
  | C, A -> zeroRR 
  | B, B -> oneRR
  | B, C -> (Left 2, Left 10) 
  | C, B -> zeroRR 
  | C, C -> oneRR  

(* Another way to encode the matrix mat but if you miss a value, 
  then it will throw an exception. 
*)
let listmat : (coq_Node * ((coq_Node * coq_RR) list)) list =
  [(A, [(A, oneRR); (B, (Left 3, Left 5)); (C, (Left 5, Left 4))]);
   (B, [(A, zeroRR); (B, oneRR); (C,  (Left 2, Left 10))]);
   (C, [(A, zeroRR); (B, zeroRR); (C, oneRR)])
  ]

let fnmat : coq_Node -> coq_Node -> coq_RR = 
  fun (x : coq_Node) -> fun (y : coq_Node) -> List.assoc y (List.assoc x listmat)  
```



