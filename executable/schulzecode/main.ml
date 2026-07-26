open Schulze


(* -------------------------------------------------------------------- *)
(*  String conversions for candidates and values                         *)
(* -------------------------------------------------------------------- *)

let string_node : coq_Node -> string = function
  | A -> "A"
  | B -> "B"
  | C -> "C"
  | D -> "D"

let string_value : coq_R -> string = function
  | Infinity -> "∞"
  | Left n   -> string_of_int n


(* -------------------------------------------------------------------- *)
(*  Configure the pairwise victory matrix                                *)
(*                                                                       *)
(*  From Schulze's 2010 paper:  https://link.springer.com/content/pdf/   *)
(*  10.1007/s00355-010-0475-4.pdf                                        *)
(*                                                                       *)
(*  8 voters:  A ≻ C ≻ D ≻ B                                            *)
(*  2 voters:  B ≻ A ≻ D ≻ C                                            *)
(*  4 voters:  C ≻ D ≻ B ≻ A                                            *)
(*  4 voters:  D ≻ B ≻ A ≻ C                                            *)
(*  3 voters:  D ≻ C ≻ B ≻ A                                            *)
(* -------------------------------------------------------------------- *)

let rank (n : coq_Node) : int =
  match n with A -> 0 | B -> 1 | C -> 2 | D -> 3

let matrix : coq_R array array =
  [|
    [| oneR;     Left 8;  Left 14; Left 10 |];
    [| Left 13;  oneR;    Left 6;  Left 2  |];
    [| Left 7;   Left 15; oneR;    Left 12 |];
    [| Left 11;  Left 19; Left 9;  oneR    |]
  |]

let arraymat (x : coq_Node) (y : coq_Node) : coq_R =
  matrix.(rank x).(rank y)


(* -------------------------------------------------------------------- *)
(*  Print the pairwise victory matrix                                    *)
(* -------------------------------------------------------------------- *)

let print_matrix () =
  print_endline "\n=== Pairwise Victory Matrix ===";
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = arraymat u v in
      if w <> zeroR then
        Printf.printf "  %-2s → %-2s : %s\n"
          (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN


(* -------------------------------------------------------------------- *)
(*  Compute and print the Schulze ranking (A* — strongest paths)          *)
(* -------------------------------------------------------------------- *)

let print_schulze () =
  print_endline "\n=== Schulze Ranking — Strengths of the Strongest Paths ===";
  let star = schulze arraymat in
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = star u v in
      Printf.printf "  %-2s → %-2s : %s\n"
        (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN


(* -------------------------------------------------------------------- *)
(*  Print pairwise winners (A beats B if p[A,B] > p[B,A])                *)
(* -------------------------------------------------------------------- *)

let print_winners () =
  print_endline "\n=== Pairwise Winners ===";
  let star = schulze arraymat in
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      if u <> v then
        let p_uv = star u v in
        let p_vu = star v u in
        match p_uv, p_vu with
        | Left pu, Left pv when pu > pv ->
            Printf.printf "  %-2s beats %-2s  (%d > %d)\n"
              (string_node u) (string_node v) pu pv
        | _ -> ()
    ) finN
  ) finN


(* -------------------------------------------------------------------- *)
(*  Semimodule: iterate A·b, A²·b, A³·b → converge to A*·b               *)
(*                                                                        *)
(*  Source vector b: b_A = ∞ (start at A), others = 0                    *)
(*  The Kleene fixed-point theorem says: after ≤ 3 iterations on a       *)
(*  4-node graph, A^k·b converges to A*·b (the strongest path vector).   *)
(* -------------------------------------------------------------------- *)

let source_vector (n : coq_Node) : coq_R =
  match n with
  | A -> oneR     (* ∞: A starts with maximum strength *)
  | _ -> zeroR    (* 0 for all others *)

let print_vector (label : string) (v : coq_Node -> coq_R) =
  print_endline ("\n  " ^ label ^ ":");
  Stdlib.List.iter (fun u ->
    Printf.printf "    %-2s : %s\n"
      (string_node u) (string_value (v u))
  ) finN

let print_semimodule () =
  print_endline "\n=== Semimodule: Fixed-Point Iteration  x_{k+1} = A·x_k + b ===";
  print_endline "  (Converges to A*·b after at most |nodes|-1 = 3 iterations)";

  (* Iteration 0: the source vector b *)
  let x0 = source_vector in
  print_vector "x₀ = b (source vector)" x0;

  (* Iteration 1: A·b *)
  let x1 = mva_eff_fun arraymat x0 in
  print_vector "x₁ = A·b" x1;

  (* Iteration 2: A·(A·b) *)
  let x2 = mva_eff_fun arraymat x1 in
  print_vector "x₂ = A²·b" x2;

  (* Iteration 3: A·(A²·b) — should equal A*·b *)
  let x3 = mva_eff_fun arraymat x2 in
  print_vector "x₃ = A³·b  (≈ A*·b — converged!)" x3;

  (* Compare with the Kleene star result *)
  print_endline "\n  Compare with A*·b (from Schulze ranking matrix, column A):";
  let star = schulze arraymat in
  Stdlib.List.iter (fun u ->
    let star_val = star u A in
    let iter_val = x3 u in
    let match_str = if star_val = iter_val then "✓" else "✗" in
    Printf.printf "    %-2s : %-6s  (A*·b)  vs  %-6s  (A³·b)  %s\n"
      (string_node u) (string_value star_val) (string_value iter_val) match_str
  ) finN


(* -------------------------------------------------------------------- *)
(*  Main                                                                *)
(* -------------------------------------------------------------------- *)

let () =
  print_endline "╔═════════════════════════════════════════════╗";
  print_endline "║   Schulze Method — Max-Min Semiring          ║";
  print_endline "║   Pairwise victories → Strongest paths       ║";
  print_endline "╚═════════════════════════════════════════════╝";
  print_matrix ();
  print_schulze ();
  print_winners ();
  print_semimodule ();
  print_endline "\nDone."
