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

  
let rank (n : coq_Node) : int =
  match n with UE -> 0 | Coq_gNB -> 1 | UPF -> 2 | DN -> 3

(* -------------------------------------------------------------------- *)
(*  5G Network Adjacency Matrix (hardcoded, order: UE, gNB, UPF, DN)    *)
(* -------------------------------------------------------------------- *)

let fiveG_adj_matrix : coq_R array array =
  [|
    (* UE *)   [| oneR;                  Rpair (1,  BW_fin 1000);  Rpair (10, BW_fin 100);  Unreachable |];
    (* gNB *)  [| Rpair (1,  BW_fin 1000);  oneR;                 Rpair (5,  BW_fin 10000); Rpair (8, BW_fin 2000) |];
    (* UPF *)  [| Rpair (10, BW_fin 100);   Rpair (5,  BW_fin 10000); oneR;                 Rpair (2, BW_fin 5000) |];
    (* DN *)   [| Unreachable;              Rpair (8,  BW_fin 2000);  Rpair (2,  BW_fin 5000);  oneR |]
  |]


let arraymat (x : coq_Node) (y : coq_Node) : coq_R =
  fiveG_adj_matrix.(rank x).(rank y)


(* -------------------------------------------------------------------- *)
(*  Print the adjacency matrix (link weights)                           *)
(* -------------------------------------------------------------------- *)

let print_adjacency () =
  print_endline "\n=== 5G Network Adjacency Matrix ===";
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = arraymat u v in
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
  let star = fiveG_kleene arraymat in
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = star u v in
      if w <> zeroR then
        Printf.printf "  %-3s → %-3s : %s\n"
          (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN

(* -------------------------------------------------------------------- *)
(*  Source vector: UE = oneR, others = Unreachable                      *)
(* -------------------------------------------------------------------- *)

let source_vec (n : coq_Node) : coq_R =
  match n with UE -> oneR | _ -> zeroR

(* -------------------------------------------------------------------- *)
(*  Matrix-vector action A·b (one-step from source)                     *)
(* -------------------------------------------------------------------- *)

let print_matrix_vector () =
  print_endline "\n=== A · b  (one-step reachable from UE) ===";
  let action = mva_func arraymat source_vec in
  Stdlib.List.iter (fun u ->
    Printf.printf "  %-3s : %s\n"
      (string_node u) (string_value (action u))
  ) finN;
  print_endline "\n=== A · b  (efficient list-based) ===";
  let action_eff = mva_eff_fun arraymat source_vec in
  Stdlib.List.iter (fun u ->
    Printf.printf "  %-3s : %s\n"
      (string_node u) (string_value (action_eff u))
  ) finN

(* -------------------------------------------------------------------- *)
(*  Compute A* · b (Kleene fixed point from UE to all nodes)             *)
(* -------------------------------------------------------------------- *)

let print_star_vector () =
  print_endline "\n=== A* · b  (optimal paths from UE to all nodes) ===";
  let star = fiveG_kleene arraymat in
  Stdlib.List.iter (fun u ->
    let w = star u UE in
    Printf.printf "  %-3s : %s\n"
      (string_node u) (string_value w)
  ) finN

(* -------------------------------------------------------------------- *)
(*  Verify A*·b via fixed-point iteration (converges in ≤3 steps)       *)
(* -------------------------------------------------------------------- *)

let print_comparison () =
  print_endline "\n=== Verification: A*·b vs A³·b (fixed point) ===";
  let star = fiveG_kleene arraymat in
  let b = source_vec in
  let a1b = mva_eff_fun arraymat b in
  let a2b = mva_eff_fun arraymat a1b in
  let a3b = mva_eff_fun arraymat a2b in
  Stdlib.List.iter (fun u ->
    let star_val = star u UE in
    let iter_val = a3b u in
    let tick = if star_val = iter_val then "✓" else "✗" in
    Printf.printf "  %-3s : %-30s  (A*·b)  vs  %-30s  (A³·b)  %s\n"
      (string_node u) (string_value star_val) (string_value iter_val) tick
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
  print_comparison ();
