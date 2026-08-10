# Semiring_graph_algorithm
Run `dune build` (ignore the warinings) in this directory to compile the project. It will compile the Rocq code and 
generate OCaml code from it (see _RocqProject file). 
1. Run `dune exec _build/default/executable/schulzecode/main.exe` to run the Schulze method on the example used by Markus Schulze in his [paper](https://link.springer.com/content/pdf/10.1007/s00355-010-0475-4.pdf). The output shows the pairwise victory matrix, the strongest path strengths (A*), and the pairwise winners — candidate **D** is the Condorcet winner.
2. Run `dune exec _build/default/executable/shortestpath/main.exe` to run the shortest path code (min-plus semiring). Shows the adjacency matrix, all-pairs shortest distances (A*), and the fixed-point iteration converging from source node A..
3. Run `dune exec _build/default/executable/widestpathcode/main.exe` to run the widest-shortest path algorithm (lexicographic semiring: length first, then width). Shows adjacency matrix, all-pairs optimal paths (A*), and fixed-point iteration.
4. Run `dune exec _build/default/executable/wikimedia/main.exe` to run the [Wikipedia Schulze method](https://en.wikipedia.org/wiki/Schulze_method) example (18-candidate Board election). Shows strongest path strengths and fixed-point iteration converging in 17 steps.
5. Run `dune exec executable/fivegslicing/main.exe` to run the 5G Network Slicing example, which computes optimal routing paths through a 5G core network (UE → gNB → UPF → DN) using a **latency × bandwidth product semiring**. Each link has two attributes — latency (minimized, min-plus) and bandwidth (maximized, max-min) — and A* finds the Pareto-optimal end-to-end path weights.
    
We have compiled this project with Rocq 9.1.1 but if you want to use it with any other Rocq version, please let us know. 


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
5. See the Rocq files in [examples](./examples/) directory for more information.


Some design decisions: we have used function type (A -> B -> C) to model a matrix datatype but this may not be efficient if your matrix size is large. However, we use [refinement](https://link.springer.com/chapter/10.1007/978-3-642-32347-8_7) approach to make it efficient ([see matrix_exp_binary_eff_fun_binary_eqv](/algorithm/Mat.v)).
