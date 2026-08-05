open WidestShortestPath


(* ----------------------------------------------------------------------- *)
(*  String conversions                                                     *)
(* ----------------------------------------------------------------------- *)

let string_node : coq_Node -> string = function
  | A -> "A"
  | B -> "B"
  | C -> "C"

let string_r : coq_R -> string = function
  | Infinity -> "∞"
  | Left n   -> string_of_int n

let string_value : coq_R * coq_R -> string = function
  | (w, l) -> "(" ^ string_r w ^ ", " ^ string_r l ^ ")"


(* ----------------------------------------------------------------------- *)
(*  Widest-Shortest Path example: 3-node graph                             *)
(*                                                                         *)
(*  Each edge has (width, length).  Width is maximized (min-plus),         *)
(*  length is minimized (max-min).  Lexicographic: width first,            *)
(*  then length breaks ties.                                               *)
(*                                                                         *)
(*  Row i = edges INTO node i (for correct A·b propagation).               *)
(* ----------------------------------------------------------------------- *)

let rank (n : coq_Node) : int =
  match n with A -> 0 | B -> 1 | C -> 2

let matrix : (coq_R * coq_R) array array =
  [|
    [| oneRR;               (Left 3,  Left 5);   (Left 5,  Left 4)  |];
    [| zeroRR;              oneRR;               (Left 2,  Left 10) |];
    [| zeroRR;              zeroRR;              oneRR               |]
  |]

let arraymat (x : coq_Node) (y : coq_Node) : coq_R * coq_R =
  matrix.(rank x).(rank y)


(* ----------------------------------------------------------------------- *)
(*  Print the adjacency matrix                                             *)
(* ----------------------------------------------------------------------- *)

let print_matrix () =
  print_endline "\n=== Adjacency Matrix (width, length) ===";
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = arraymat u v in
      if w <> zeroRR then
        Printf.printf "  %-2s → %-2s : %s\n"
          (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN


(* ----------------------------------------------------------------------- *)
(*  Compute and print widest-shortest paths (A-star)                       *)
(* ----------------------------------------------------------------------- *)

let print_widest () =
  print_endline "\n=== Widest-Shortest Paths — All-Pairs (A*) ===";
  let star = widestshortestpath arraymat in
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = star u v in
      Printf.printf "  %-2s → %-2s : %s\n"
        (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN


(* ----------------------------------------------------------------------- *)
(*  Semimodule: fixed-point iteration from source node A                    *)
(* ----------------------------------------------------------------------- *)

let source_vector (n : coq_Node) : coq_R * coq_R =
  match n with
  | C -> oneRR     (* (0, ∞): best width, worst length starting point *)
  | _ -> zeroRR    (* unreachable *)

let print_vector (label : string) (v : coq_Node -> coq_R * coq_R) =
  print_endline ("\n  " ^ label ^ ":");
  Stdlib.List.iter (fun u ->
    Printf.printf "    %-2s : %s\n"
      (string_node u) (string_value (v u))
  ) finN

let print_iteration () =
  print_endline "\n=== Semimodule: Fixed-Point Iteration  x_{k+1} = A·x_k + b ===";
  print_endline "  (Lexicographic: width first, then length breaks ties — source C)";

  let x0 = source_vector in
  print_vector "x₀ = b (source)" x0;

  let x1 = mva_eff_fun arraymat x0 in
  print_vector "x₁ = A·b" x1;

  let x2 = mva_eff_fun arraymat x1 in
  print_vector "x₂ = A²·b  (≈ A*·b — converged!)" x2;

  print_endline "\n  Compare with A-star·b (from widest-shortest paths, column C):";
  let star = widestshortestpath arraymat in
  Stdlib.List.iter (fun u ->
    let star_val = star u C in
    let iter_val = x2 u in
    let match_str = if star_val = iter_val then "✓" else "✗" in
    Printf.printf "    %-2s : %-16s  (A*·b)  vs  %-16s  (A²·b)  %s\n"
      (string_node u) (string_value star_val) (string_value iter_val) match_str
  ) finN


(* ----------------------------------------------------------------------- *)
(*  Main                                                                   *)
(* ----------------------------------------------------------------------- *)

let () =
  print_endline "╔═════════════════════════════════════════════╗";
  print_endline "║   Widest-Shortest Path — Lexicographic        ║";
  print_endline "║   (width, length) → Optimal paths             ║";
  print_endline "╚═════════════════════════════════════════════╝";
  print_matrix ();
  print_widest ();
  print_iteration ();
  print_endline "\nDone."
