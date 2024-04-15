# Semiring_graph_algorithm
Run `dune build` in this directory to compile the project. It will compile the Coq code and generate OCaml code 
from it (see _CoqProject file). Run `dune exec _build/default/executable/schulzecode/main.exe` to run the 
Schulze method, run `dune exec _build/default/executable/shortestpath/main.exe` to run the shortest path code, 
run `dune exec executable/widestpathcode/main.exe` to run the shortest-widest path algorithm, etc.


If you want to verify that your algebra is a semiring, do the following:
1. Define your `Set`, `plus`, `mul`, `0`, and `1`. 
2. Discharge all the axioms of semiring.
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
3. Moreover, this formalisation assumes bounded and idempotent semiring to compute a fixed-point.
  ```
   (zero_stable : forall a : R, 1 + a =r= 1 = true) 
   (plus_idempotence : forall a, a + a =r= a = true)
  ``` 
4. See the Coq files in [examples](./examples/) directory for more information.



