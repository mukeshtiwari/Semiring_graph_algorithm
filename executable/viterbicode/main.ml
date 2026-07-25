open Viterbi
open BinNums
open QArith_base

(* ----------------------------------------------------------------------- *)
(*  Helper: convert OCaml int to Rocq positive (binary representation)     *)
(* ----------------------------------------------------------------------- *)

let rec pos_of_int (n : int) : positive =
  if n <= 0 then Coq_xH
  else if n = 1 then Coq_xH
  else if n mod 2 = 0 then Coq_xO (pos_of_int (n / 2))
  else Coq_xI (pos_of_int (n / 2))

let rec int_of_pos : positive -> int = function
| Coq_xH -> 1
| Coq_xO p -> 2 * int_of_pos p
| Coq_xI p -> 2 * int_of_pos p + 1

(* ----------------------------------------------------------------------- *)
(*  Helper: construct a Q value from integer numerator and denominator     *)
(* ----------------------------------------------------------------------- *)

let q (num : int) (den : int) : coq_R =
  let z =
    if num >= 0 then Zpos (pos_of_int num)
    else Zneg (pos_of_int (-num))
  in
  { coq_Qnum = z; coq_Qden = pos_of_int den }


(* ----------------------------------------------------------------------- *)
(*  Display helpers                                                         *)
(* ----------------------------------------------------------------------- *)

let string_candidates : coq_Node -> string = function
| A -> "A"
| B -> "B"
| C -> "C"

let rec string_of_pos : positive -> string = function
| Coq_xH -> "1"
| Coq_xO p -> string_of_int (2 * int_of_pos p)
| Coq_xI p -> string_of_int (2 * int_of_pos p + 1)

let string_z : coq_Z -> string = function
| Z0 -> "0"
| Zpos p -> string_of_pos p
| Zneg p -> "-" ^ string_of_pos p

let string_values (v : coq_R) : string =
  string_z v.coq_Qnum ^ "/" ^ string_of_pos v.coq_Qden


let string_list : (string * string * string) list -> string = 
  Stdlib.List.fold_left (fun acc (a, b, h) -> acc ^ "(" ^ a ^ ", " ^ b ^ ", " ^ h ^ ") ") ""
  

let rec cross_product (la : 'a list) (lb : 'b list) : ('a * 'b) list =
  match la with 
  | [] -> [] 
  | h :: t -> Stdlib.List.append (Stdlib.List.map (fun x -> (h, x)) lb) (cross_product t lb)

(* ----------------------------------------------------------------------- *)
(*  Viterbi example: small 3-node network                                  *)
(*                                                                         *)
(*     (1/2)                                                               *)
(*  0 ------ 1                                                             *)
(*   \     /                                                               *)
(* (1/3)\ / (1/4)                                                           *)
(*      2                                                                  *)
(*                                                                         *)
(*  Edge weights are probabilities (Q rationals).                           *)
(* ----------------------------------------------------------------------- *)

let rank (n : coq_Node) : int =
  match n with A -> 0 | B -> 1 | C -> 2 

let matrix : coq_R array array = 
  [|
    [| oneR; q 1 2; q 1 3 |];
    [| zeroR; oneR; q 1 4 |];
    [| zeroR; zeroR; oneR |]
  |]

let arraymat (x : coq_Node) (y : coq_Node) : coq_R = 
  matrix.(rank x).(rank y)

let _ = 
  let comp = vit_solver arraymat in 
  let ret = Stdlib.List.map (fun (x, y) -> (string_candidates x, string_candidates y, string_values (comp x y))) 
    (cross_product finN finN) in 
  print_endline (string_list ret)
