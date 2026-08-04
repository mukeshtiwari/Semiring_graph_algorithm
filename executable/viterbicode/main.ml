open Viterbi
open BinNums
open QArith_base


(* ----------------------------------------------------------------------- *)
(*  Helper: construct a Q value from integer numerator and denominator     *)
(* ----------------------------------------------------------------------- *)

let pos_of_int (n : int) : positive =
  let rec go n = if n <= 1 then Coq_xH
    else if n mod 2 = 0 then Coq_xO (go (n / 2))
    else Coq_xI (go (n / 2))
  in if n <= 0 then Coq_xH else go n

let q (num : int) (den : int) : coq_R =
  { coq_Qnum = (if num >= 0 then Zpos (pos_of_int num)
                else Zneg (pos_of_int (-num)));
    coq_Qden = pos_of_int den }


(* ----------------------------------------------------------------------- *)
(*  String conversions                                                     *)
(* ----------------------------------------------------------------------- *)

let string_node : coq_Node -> string = function
  | A -> "0"
  | B -> "1"
  | C -> "2"

let rec int_of_pos : positive -> int = function
  | Coq_xH -> 1
  | Coq_xO p -> 2 * int_of_pos p
  | Coq_xI p -> 2 * int_of_pos p + 1

let int_of_z : coq_Z -> int = function
  | Z0 -> 0
  | Zpos p -> int_of_pos p
  | Zneg p -> -(int_of_pos p)

let string_value : coq_R -> string = function
  | v ->
      let num = int_of_z v.coq_Qnum in
      let den = int_of_pos v.coq_Qden in
      if den = 1 then string_of_int num
      else Printf.sprintf "%.3f" (float_of_int num /. float_of_int den)


(* ----------------------------------------------------------------------- *)
(*  Viterbi example: 3-node Markov chain                                   *)
(*                                                                         *)
(*     (1/2)                                                               *)
(*  0 ------ 1                                                             *)
(*   \     /                                                               *)
(* (1/3)\ / (1/4)                                                           *)
(*      2                                                                  *)
(*                                                                         *)
(*  Row i = edges INTO node i (for correct A·b propagation).              *)
(* ----------------------------------------------------------------------- *)

let rank (n : coq_Node) : int =
  match n with A -> 0 | B -> 1 | C -> 2

let matrix : coq_R array array =
  (* Row i = edges INTO node i (for correct A·b propagation) *)
  [|
    [| oneR;    zeroR;  zeroR  |];   (* into 0: self=1 *)
    [| q 1 2;   oneR;   zeroR  |];   (* into 1: 0→1=1/2, self=1 *)
    [| q 1 3;   q 1 4;  oneR   |]    (* into 2: 0→2=1/3, 1→2=1/4, self=1 *)
  |]

let arraymat (x : coq_Node) (y : coq_Node) : coq_R =
  matrix.(rank x).(rank y)


(* ----------------------------------------------------------------------- *)
(*  Print the adjacency matrix                                             *)
(* ----------------------------------------------------------------------- *)

let print_matrix () =
  print_endline "\n=== Transition Probability Matrix ===";
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = arraymat u v in
      if w <> zeroR then
        Printf.printf "  %-2s → %-2s : %s\n"
          (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN


(* ----------------------------------------------------------------------- *)
(*  Compute and print Viterbi (A* — most likely paths)                     *)
(* ----------------------------------------------------------------------- *)

let print_viterbi () =
  print_endline "\n=== Viterbi — Most Likely Path Probabilities (A*) ===";
  let star = viterbi arraymat in
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      let w = star u v in
      Printf.printf "  %-2s → %-2s : %s\n"
        (string_node u) (string_node v) (string_value w)
    ) finN
  ) finN


(* ----------------------------------------------------------------------- *)
(*  Semimodule: fixed-point iteration from source node 0                    *)
(*                                                                          *)
(*  Viterbi = max-× semiring: x_{k+1} = max(A·x_k, b) → A*·b               *)
(* ----------------------------------------------------------------------- *)

let source_vector (n : coq_Node) : coq_R =
  match n with
  | A -> oneR     (* 1.0: start at node 0 with probability 1 *)
  | _ -> zeroR    (* 0.0: unreachable *)

let print_vector (label : string) (v : coq_Node -> coq_R) =
  print_endline ("\n  " ^ label ^ ":");
  Stdlib.List.iter (fun u ->
    Printf.printf "    %-2s : %s\n"
      (string_node u) (string_value (v u))
  ) finN

let print_iteration () =
  print_endline "\n=== Semimodule: Fixed-Point Iteration  x_{k+1} = A·x_k + b ===";
  print_endline "  (Converges to most likely path probabilities after ≤ 2 iterations)";

  let x0 = source_vector in
  print_vector "x₀ = b (source)" x0;

  let x1 = mva_eff_fun arraymat x0 in
  print_vector "x₁ = A·b" x1;

  let x2 = mva_eff_fun arraymat x1 in
  print_vector "x₂ = A²·b  (≈ A*·b — converged!)" x2;

  print_endline "\n  Compare with A*·b (from Viterbi, column 0):";
  let star = viterbi arraymat in
  Stdlib.List.iter (fun u ->
    let star_val = star u A in
    let iter_val = x2 u in
    let match_str = if star_val = iter_val then "✓" else "✗" in
    Printf.printf "    %-2s : %-8s  (A*·b)  vs  %-8s  (A²·b)  %s\n"
      (string_node u) (string_value star_val) (string_value iter_val) match_str
  ) finN


(* ----------------------------------------------------------------------- *)
(*  Main                                                                   *)
(* ----------------------------------------------------------------------- *)

let () =
  print_endline "╔═════════════════════════════════════════════╗";
  print_endline "║   Viterbi Algorithm — Max-× Semiring         ║";
  print_endline "║   Transition probabilities → Most likely path ║";
  print_endline "╚═════════════════════════════════════════════╝";
  print_matrix ();
  print_viterbi ();
  print_iteration ();
  print_endline "\nDone."
