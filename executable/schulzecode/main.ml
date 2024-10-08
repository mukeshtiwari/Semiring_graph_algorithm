open Schulze

let string_candidates : coq_Node -> string = function
| A -> "A"
| B -> "B"
| C -> "C"
| D -> "D"


let string_values : coq_R -> string = function
| Infinity -> "Infinity"
| Left n -> "Left " ^ string_of_int n 


let string_list : (string * string * string) list -> string = 
  List.fold_left (fun acc (a, b, h) -> acc ^ "(" ^ a ^ ", " ^ b ^ ", " ^ h ^ ")") ""
  

let rec cross_product (la : 'a list) (lb : 'b list) : ('a * 'b) list =
  match la with 
  | [] -> [] 
  | h :: t -> List.append (List.map (fun x -> (h, x)) lb) (cross_product t lb)

(* configure the matrix. In this case, it should be 
   constructed from the ballots cast in an election

  Solution suggested by Xavier Leroy and the fast one if the matrix is big.
  Also, if your matrix is big then read it from a file then hardcoding it. *)

let rank (n : coq_Node) : int =
  match n with A -> 0 | B -> 1 | C -> 2 | D -> 3

  (* N Matrix https://link.springer.com/chapter/10.1007/978-3-642-32347-8_7 *)
let matrix : coq_R array array = 
  [|
    [| oneR; Left 8; Left 14; Left 10|];
    [| Left 13; oneR; Left 6; Left 2|];
    [| Left 7; Left 15; oneR; Left 12 |];
    [| Left 11; Left 19; Left 9; oneR |]
  |]

let arraymat (x : coq_Node) (y : coq_Node) : coq_R = 
  matrix.(rank x).(rank y) 

let _ = 
  let comp = schulze arraymat in 
  let ret = List.map (fun (x, y) -> (string_candidates x, string_candidates y, string_values (comp x y))) 
    (cross_product finN finN) in 
  print_endline (string_list ret)

  (* 
  
  (A, A, Infinity)(A, B, Left 14)(A, C, Left 14)(A, D, Left 12)
  (B, A, Left 13)(B, B, Infinity)(B, C, Left 13)(B, D, Left 12)
  (C, A, Left 13)(C, B, Left 15)(C, C, Infinity)(C, D, Left 12)
  (D, A, Left 13)(D, B, Left 19)(D, C, Left 13)(D, D, Infinity)

  *)