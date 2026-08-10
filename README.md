# Semiring_graph_algorithm
Run `dune build` (ignore the warinings) in this directory to compile the project. It will compile the Rocq code and 
generate OCaml code from it (see _RocqProject file). 
1. Run `dune exec _build/default/executable/schulzecode/main.exe` to run the Schulze method on the example used by Markus Schulze in his [paper](https://link.springer.com/content/pdf/10.1007/s00355-010-0475-4.pdf). The output shows the pairwise victory matrix, the strongest path strengths (A*), and the pairwise winners — candidate **D** is the Condorcet winner.
2. Run `dune exec _build/default/executable/schulzepathcode/main.exe` to run the Schulze **language (trace) semiring** example. Unlike the max-min value semiring of `Schulze.v`, `Schulzepath.v` builds the language semiring of sets of paths (union + pairwise concatenation), where distributivity holds exactly. The output shows the pairwise victory matrix, the strongest beatpath strengths `schulze_star M = (M + I)³`, the pairwise winners (candidate **D**), the closure action `A*·b` (list-based vs functional), and verifies the language-semiring witness beatpaths against `schulze_star`.
3. Run `dune exec _build/default/executable/shortestpath/main.exe` to run the shortest path code (min-plus semiring). Shows the adjacency matrix, all-pairs shortest distances (A*), and the fixed-point iteration converging from source node A..
4. Run `dune exec _build/default/executable/widestpathcode/main.exe` to run the widest-shortest path algorithm (lexicographic semiring: length first, then width). Shows adjacency matrix, all-pairs optimal paths (A*), and fixed-point iteration.
5. Run `dune exec _build/default/executable/wikimedia/main.exe` to run the [Wikipedia Schulze method](https://en.wikipedia.org/wiki/Schulze_method) example (18-candidate Board election). Shows strongest path strengths and fixed-point iteration converging in 17 steps.
6. Run `dune exec executable/fivegslicing/main.exe` to run the 5G Network Slicing example, which computes optimal routing paths through a 5G core network (UE → gNB → UPF → DN) using a **latency × bandwidth product semiring**. Each link has two attributes — latency (minimized, min-plus) and bandwidth (maximized, max-min) — and A* finds the Pareto-optimal end-to-end path weights.
    
We have compiled this project with Rocq 9.1.1 but if you want to use it with any other Rocq version, please let us know. 


If you want to verify that your algebra is a semiring, do the following:
1. Define your carrier type `R` together with its operations — the zero element, addition, the one element, and multiplication — matching the fields of the HB mixins in [algorithm/Structures.v](./algorithm/Structures.v):
  ```
  Section MySemiring.
    Inductive R := ... .
    Definition zero : R := ... .
    Definition add  : R -> R -> R := ... .
    Definition one  : R := ... .
    Definition mul  : R -> R -> R := ... .
  End MySemiring.
  ```
2. Prove the semiring laws as lemmas — exactly the proof fields of `IsCommutativeMonoid` and `IsSemiring`:
  ```
  (* commutative monoid (additive) *)
  Lemma addA_proof  : forall x y z : R, add (add x y) z = add x (add y z).   (* associativity *)
  Lemma addC_proof  : forall x y : R, add x y = add y x.                     (* commutativity *)
  Lemma add0r_proof : forall x : R, add zero x = x.                          (* zero: left identity *)
  Lemma addr0_proof : forall x : R, add x zero = x.                          (* zero: right identity *)

  (* semiring (multiplicative, distributivity, annihilators) *)
  Lemma mulA_proof  : forall a b c : R, mul (mul a b) c = mul a (mul b c).   (* associativity *)
  Lemma mul1r_proof : forall a : R, mul one a = a.                           (* one: left identity *)
  Lemma mulr1_proof : forall a : R, mul a one = a.                           (* one: right identity *)
  Lemma mulDr_proof : forall a b c : R, mul (add a b) c = add (mul a c) (mul b c).  (* right distributivity *)
  Lemma mulDl_proof : forall a b c : R, mul a (add b c) = add (mul a b) (mul a c).  (* left distributivity *)
  Lemma mul0r_proof : forall a : R, mul zero a = zero.                       (* zero: left annihilator *)
  Lemma mulr0_proof : forall a : R, mul a zero = zero.                       (* zero: right annihilator *)
  ```
3. Register your algebra as an HB instance. Once the `Semiring` instance exists, the generic matrix machinery in [algorithm/MatN.v](./algorithm/MatN.v) (`pow`, `powN`, `powN_fun`, `geom_sum`, `matrix_mul`, …) works for `R`:
  ```
  HB.instance Definition _ := IsCommutativeMonoid.Build R
    zero add addA_proof addC_proof add0r_proof addr0_proof.

  HB.instance Definition _ := IsSemiring.Build R
    one mul mulA_proof mul1r_proof mulr1_proof
    mulDr_proof mulDl_proof mul0r_proof mulr0_proof.
  ```
4. The fixed-point and Kleene-closure theorems additionally require the semiring to be **bounded**: `1 + a = 1`. (Idempotence `a + a = a` then follows automatically — see `bounded_add_idem` in [algorithm/PathN.v](./algorithm/PathN.v).) Prove it and register the instance:
  ```
  Lemma add_bound_proof : forall a : R, add one a = one.
  HB.instance Definition _ := IsBoundedSemiring.Build R add_bound_proof.
  ```
5. You can now use the generic functions directly, e.g. the closure `powN_fun (matrix_add m (I : Node -> Node -> R)) n` and the matrix-vector iteration `matrix_vector_action m v` from [algorithm/SemimoduleN.v](./algorithm/SemimoduleN.v). For the full pattern — including the `IsFinType` instance on your node type and the `IsSemimodule` instance — see the concrete examples in [examples](./examples/): `Schulze.v` (max-min), `Shortestpath.v` (min-plus), `WidestShortestPath.v` (lexicographic length × width), and `Schulzepath.v` (language/trace semiring).


Some design decisions: we have used function type (A -> B -> C) to model a matrix datatype but this may not be efficient if your matrix size is large. However, we use [refinement](https://link.springer.com/chapter/10.1007/978-3-642-32347-8_7) approach to make it efficient ([see powN_eqv](/algorithm/MatN.v)).
