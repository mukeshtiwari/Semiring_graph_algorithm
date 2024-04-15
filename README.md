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



