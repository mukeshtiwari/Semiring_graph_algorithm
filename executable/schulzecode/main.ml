open Schulze

let string_candidates : coq_Node -> string = function
| A -> "A"
| B -> "B"
| C -> "C"


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

   We have three ballots 3 : A > B > C 
*)
let mat (x : coq_Node) (y : coq_Node) : coq_R = 
  match x, y with
  | A, A -> oneR
  | A, B -> Left 3 
  | B, A -> zeroR 
  | A, C -> Left 3
  | C, A -> zeroR 
  | B, B -> oneR
  | B, C -> Left 3 
  | C, B -> zeroR 
  | C, C -> oneR  


let listmat : (coq_Node * ((coq_Node * coq_R) list)) list =
  [ (A, [(A, oneR); (B, Left 3); (C, Left 3)]);
    (B, [(A, zeroR); (B, oneR); (C,  Left 3)]);
    (C, [(A, zeroR); (B, zeroR); (C, oneR)])
  ]

let fnmat : coq_Node -> coq_Node -> coq_R = 
  fun (x : coq_Node) -> fun (y : coq_Node) -> List.assoc y (List.assoc x listmat)  

let _ = 
  let comp = schulze fnmat in 
  let ret = List.map (fun (x, y) -> (string_candidates x, string_candidates y, string_values (comp x y))) 
    (cross_product finN finN) in 
  print_endline (string_list ret)