open Shortestpath


(* -------------------------------------------------------------------- *)
(*  String conversions for nodes and values                              *)
(* -------------------------------------------------------------------- *)

let string_node : coq_Node -> string = function
  | A -> "A"
  | B -> "B"
  | C -> "C"

let string_value : coq_R -> string = function
  | Infinity -> "∞"
  | Left n   -> string_of_int n


(* -------------------------------------------------------------------- *)
(*  Configure the adjacency matrix (edge weights = distances)             *)
(*                                                                        *)
(*  Row i = edges INTO node i:  A→B = 3, A→C = 3, B→C = 3               *)
(*  Self-loops = 0, unreachable = ∞                                     *)
(* -------------------------------------------------------------------- *)

let rank (n : coq_Node) : int =
  match n with A -> 0 | B -> 1 | C -> 2

let matrix : coq_R array array =
  (* Row i = edges INTO node i (column A row B = A→B distance) *)
  [|
    [| oneR;   zeroR;  zeroR  |];   (* into A: self=0, others unreachable *)
    [| Left 3; oneR;   zeroR  |];   (* into B: A→B=3, self=0 *)
    [| Left 3; Left 3; oneR   |]    (* into C: A→C=3, B→C=3, self=0 *)
  |]

let arraymat (x : coq_Node) (y : coq_Node) : coq_R =
  matrix.(rank x).(rank y)


(* -------------------------------------------------------------------- *)
(*  Print the adjacency matrix                                           *)
(* -------------------------------------------------------------------- *)

let print_matrix () =
  print_endline "\n=== Adjacency Matrix (edge distances) ===";
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = arraymat u v in
      if w <> zeroR then
        Printf.printf "  %-2s → %-2s : %s\n"
          (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN


(* -------------------------------------------------------------------- *)
(*  Compute and print shortest paths (A* — all-pairs shortest distances) *)
(* -------------------------------------------------------------------- *)

let print_shortest_paths () =
  print_endline "\n=== Shortest Paths — All-Pairs (A*) ===";
  let star = shortestpath arraymat in
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = star u v in
      Printf.printf "  %-2s → %-2s : %s\n"
        (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN


(* -------------------------------------------------------------------- *)
(*  Semimodule: fixed-point iteration from source node A                 *)
(*                                                                        *)
(*  Source vector b: b_A = 0 (start at A), others = ∞                    *)
(*  In min-plus: x_{k+1} = min(A·x_k, b) converges to A*·b               *)
(* -------------------------------------------------------------------- *)

let source_vector (n : coq_Node) : coq_R =
  match n with
  | A -> oneR     (* 0: start at A with zero distance *)
  | _ -> zeroR    (* ∞: unreachable initially *)

let print_vector (label : string) (v : coq_Node -> coq_R) =
  print_endline ("\n  " ^ label ^ ":");
  Stdlib.List.iter (fun u ->
    Printf.printf "    %-2s : %s\n"
      (string_node u) (string_value (v u))
  ) finN

let print_iteration () =
  print_endline "\n=== Semimodule: Fixed-Point Iteration  x_{k+1} = A·x_k + b ===";
  print_endline "  (Converges to shortest distances after 2 iterations for 3 nodes)";

  let x0 = source_vector in
  print_vector "x₀ = b (source)" x0;

  let x1 = mva_eff_fun arraymat x0 in
  print_vector "x₁ = A·b" x1;

  let x2 = mva_eff_fun arraymat x1 in
  print_vector "x₂ = A²·b  (≈ A*·b — converged!)" x2;

  print_endline "\n  Compare with A*·b (from shortest paths, column A):";
  let star = shortestpath arraymat in
  Stdlib.List.iter (fun u ->
    let star_val = star u A in
    let iter_val = x2 u in
    let match_str = if star_val = iter_val then "✓" else "✗" in
    Printf.printf "    %-2s : %-6s  (A*·b)  vs  %-6s  (A²·b)  %s\n"
      (string_node u) (string_value star_val) (string_value iter_val) match_str
  ) finN


(* -------------------------------------------------------------------- *)
(*  Main                                                                *)
(* -------------------------------------------------------------------- *)

let () =
  print_endline "╔═════════════════════════════════════════════╗";
  print_endline "║   Shortest Path — Min-Plus Semiring          ║";
  print_endline "║   Edge distances → All-pairs shortest paths   ║";
  print_endline "╚═════════════════════════════════════════════╝";
  print_matrix ();
  print_shortest_paths ();
  print_iteration ();
  print_endline "\nDone."
