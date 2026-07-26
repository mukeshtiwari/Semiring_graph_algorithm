open FiveGNetworkSlicing


(* -------------------------------------------------------------------- *)
(*  String conversions for 5G nodes and values                          *)
(* -------------------------------------------------------------------- *)

let string_node : coq_Node -> string = function
  | UE       -> "UE"
  | Coq_gNB  -> "gNB"
  | UPF      -> "UPF"
  | DN       -> "DN"

let string_bw : coq_BW -> string = function
  | BW_fin n -> string_of_int n ^ " Mbps"
  | BW_inf   -> "∞"

let string_value : coq_R -> string = function
  | Rpair (lat, bw) ->
      "(lat=" ^ string_of_int lat ^ "ms, bw=" ^ string_bw bw ^ ")"
  | Unreachable -> "⊥ (unreachable)"

(* -------------------------------------------------------------------- *)
(*  Build the adjacency matrix from the Coq definition                  *)
(* -------------------------------------------------------------------- *)

(* fiveG_adj is extracted as a function Node -> Node -> R *)
(* We can call it directly *)

(* -------------------------------------------------------------------- *)
(*  Print the adjacency matrix (link weights)                           *)
(* -------------------------------------------------------------------- *)

let print_adjacency () =
  print_endline "\n=== 5G Network Adjacency Matrix ===";
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = fiveG_adj u v in
      if w <> zeroR then
        Printf.printf "  %-3s → %-3s : %s\n"
          (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN

(* -------------------------------------------------------------------- *)
(*  Compute and print the Kleene star A* (all-pairs optimal paths)      *)
(* -------------------------------------------------------------------- *)

let print_kleene () =
  print_endline "\n=== Kleene Star A* (optimal path weights) ===";
  let star = fiveG_kleene in
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = star u v in
      if w <> zeroR then
        Printf.printf "  %-3s → %-3s : %s\n"
          (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN

(* -------------------------------------------------------------------- *)
(*  Compute and print A·b (matrix-vector action)                        *)
(*  b = source vector: UE=(0,∞), others=⊥                              *)
(* -------------------------------------------------------------------- *)

let print_matrix_vector () =
  print_endline "\n=== A · b  (one-step reachable from UE) ===";
  let action = result_func in  (* functional version *)
  Stdlib.List.iter (fun u ->
    Printf.printf "  %-3s : %s\n"
      (string_node u) (string_value (action u))
  ) finN;
  print_endline "\n=== A · b  (efficient list-based) ===";
  let action_eff = result_eff in
  Stdlib.List.iter (fun u ->
    Printf.printf "  %-3s : %s\n"
      (string_node u) (string_value (action_eff u))
  ) finN

(* -------------------------------------------------------------------- *)
(*  Compute A* · b (Kleene fixed point from UE to all nodes)             *)
(* -------------------------------------------------------------------- *)

let print_star_vector () =
  print_endline "\n=== A* · b  (optimal paths from UE to all nodes) ===";
  (* A* · b = vector of optimal weights from source to each node *)
  (* We compute this using the Kleene star matrix and the source vector *)
  (* A*·b_i = Σ_j scale (A*_ij) (b_j) *)
  (* Since b only has UE = oneR, this is A*_iu * oneR = A*_iu for each i *)
  let star = fiveG_kleene in
  Stdlib.List.iter (fun u ->
    let w = star u UE in
    Printf.printf "  %-3s : %s\n"
      (string_node u) (string_value w)
  ) finN

(* -------------------------------------------------------------------- *)
(*  Main: run all computations                                          *)
(* -------------------------------------------------------------------- *)

let () =
  print_endline "╔══════════════════════════════════════════════════╗";
  print_endline "║   5G Network Slicing — Semiring Path Computations ║";
  print_endline "║   Semiring: (latency-ms × bandwidth-Mbps)         ║";
  print_endline "╚══════════════════════════════════════════════════╝";
  print_adjacency ();
  print_matrix_vector ();
  print_kleene ();
  print_star_vector ();
  print_endline "\nDone."
