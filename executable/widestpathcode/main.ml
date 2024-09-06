open Widestshortestpath.WidestShortestPath


let string_candidates : coq_Node -> string = function
| A -> "A"
| B -> "B"
| C -> "C"


let string_values : coq_R -> string = function
| Infinity -> "Infinity"
| Left n -> "Left " ^ string_of_int n 

let string_pair : coq_R * coq_R -> string = function 
|(x, y) -> string_values x ^ ", " ^ string_values y 


let string_list : (string * string * string) list -> string = 
  List.fold_left (fun acc (a, b, h) -> acc ^ "(" ^ a ^ ", " ^ b ^ ", " ^ h ^ ")") ""
  

let rec cross_product (la : 'a list) (lb : 'b list) : ('a * 'b) list =
  match la with 
  | [] -> [] 
  | h :: t -> List.append (List.map (fun x -> (h, x)) lb) (cross_product t lb)

  
(* configure the matrix. *)
let mat (x : coq_Node) (y : coq_Node) : coq_RR = 
  match x, y with
  | A, A -> oneRR
  | A, B -> (Left 3, Left 5) 
  | B, A -> zeroRR 
  | A, C -> (Left 5, Left 4)
  | C, A -> zeroRR 
  | B, B -> oneRR
  | B, C -> (Left 2, Left 10) 
  | C, B -> zeroRR 
  | C, C -> oneRR  

(* Another way to encode the matrix mat but if you miss a value, 
  then it will throw an exception. 
*)
let listmat : (coq_Node * ((coq_Node * coq_RR) list)) list =
  [(A, [(A, oneRR); (B, (Left 3, Left 5)); (C, (Left 5, Left 4))]);
   (B, [(A, zeroRR); (B, oneRR); (C,  (Left 2, Left 10))]);
   (C, [(A, zeroRR); (B, zeroRR); (C, oneRR)])
  ]

let fnmat : coq_Node -> coq_Node -> coq_RR = 
  fun (x : coq_Node) -> fun (y : coq_Node) -> List.assoc y (List.assoc x listmat)  


(* Solution suggested by Xavier Leroy and the fast one if the matrix is big.
   Also, if your matrix is big then read it from a file then hardcoding it. *)
let rank (n : coq_Node) : int =
  match n with A -> 0 | B -> 1 | C -> 2 

let matrix : coq_RR array array = 
  [|
   [| oneRR; (Left 3, Left 5); (Left 5, Left 4) |];
   [| zeroRR; oneRR; (Left 2, Left 10) |];
   [| zeroRR; zeroRR; oneRR |]
  |]

let arraymat (x : coq_Node) (y : coq_Node) : coq_RR = 
  matrix.(rank x).(rank y)




let _ = 
    let comp = widest_shortest_path arraymat (* mat and fnmat are same *) in 
    let ret = List.map (fun (x, y) -> (string_candidates x, string_candidates y, 
      string_pair (comp x y))) (cross_product finN finN) in 
  print_endline (string_list ret)
