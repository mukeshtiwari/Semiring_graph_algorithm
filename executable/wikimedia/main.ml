open Wikimedia

let string_candidates : coq_Node -> string = function
| A -> "A"
| B -> "B"
| C -> "C"
| D -> "D"
| E -> "E"


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
   constructed from the ballots cast in an election *) 

(* https://en.wikipedia.org/wiki/Schulze_method 
Matrix of pairwise preferences *)
let matrix : coq_R array array = 
[|
  [| oneR; Left 20; Left 26; Left 30; Left 22|];
  [| Left 25; oneR; Left 16; Left 33; Left 18|];
  [| Left 19; Left 29; oneR; Left 17; Left 24|];
  [| Left 15; Left 12; Left 28; oneR; Left 14|];
  [| Left 23; Left 27; Left 21; Left 31; oneR |]
|]

let rank (n : coq_Node) : int =
  match n with 
  | A -> 0 | B -> 1 | C -> 2 | D -> 3 | E -> 4


let arraymat (x : coq_Node) (y : coq_Node) : coq_R = 
  matrix.(rank x).(rank y) 
  

let _ = 
  let comp = wikimedia arraymat in 
  let ret = List.map (fun (x, y) -> (string_candidates x, string_candidates y, string_values (comp x y))) 
    (cross_product finN finN) in 
  print_endline (string_list ret)

  
