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


let _ = 
    let comp = widest_shortest_path mat in 
    let ret = List.map (fun (x, y) -> (string_candidates x, string_candidates y, 
      string_pair (comp x y))) (cross_product finN finN) in 
  print_endline (string_list ret)
