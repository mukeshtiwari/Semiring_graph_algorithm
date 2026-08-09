open Datatypes
open Schulze
open Schulzepath


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


(* All candidates (candidates is not extracted, so we define it here) *)
let finN : coq_Node list = [A; B; C; D] 

(* -------------------------------------------------------------------- *)
(*  Concrete example: the preference matrix M from Schulzepath           *)
(*  (the paper's 21-voter profile; M[a,b] = # voters preferring a to b)  *)
(* -------------------------------------------------------------------- *)

(* let arraymat (u : coq_Node) (v : coq_Node) : coq_R =
  coq_M u v *)


(* -------------------------------------------------------------------- *)
(*  Print the pairwise victory matrix                                    *)
(* -------------------------------------------------------------------- *)

let print_matrix () =
  print_endline "\n=== Pairwise Victory Matrix (coq_M) ===";
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      Printf.printf "  %-2s → %-2s : %s\n"
        (string_node u) (string_node v) (string_value (arraymat u v))
    ) finN
  ) finN


(* -------------------------------------------------------------------- *)
(*  Compute and print the Kleene closure schulze_star M = (M + I)³       *)
(*  — the strongest-path strengths between all candidate pairs.         *)
(* -------------------------------------------------------------------- *)

let print_star () =
  print_endline "\n=== Schulze Beatpath Strengths (schulze_star M) ===";
  print_endline "    (M + I)³ = I + M + M² + M³  — strongest paths up to 3 hops)";
  let star = schulze_star arraymat in
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      Printf.printf "  %-2s → %-2s : %s\n"
        (string_node u) (string_node v) (string_value (star u v))
    ) finN
  ) finN


(* -------------------------------------------------------------------- *)
(*  Print pairwise winners (a beats b iff star[a,b] > star[b,a])         *)
(* -------------------------------------------------------------------- *)

let print_winners () =
  print_endline "\n=== Pairwise Winners ===";
  let star = schulze_star arraymat in
  Stdlib.List.iter (fun u ->
    Stdlib.List.iter (fun v ->
      if u <> v then
        match star u v, star v u with
        | Left pu, Left pv when pu > pv ->
            Printf.printf "  %-2s beats %-2s  (%d > %d)\n"
              (string_node u) (string_node v) pu pv
        | _ -> ()
    ) finN
  ) finN


(* -------------------------------------------------------------------- *)
(*  Matrix-vector action of the beatpath closure: A*·b                   *)
(*  Compare the efficient (list-based) and the functional versions.     *)
(* -------------------------------------------------------------------- *)

let source_vector (n : coq_Node) : coq_R =
  match n with A -> oneR | _ -> zeroR

let print_vector (label : string) (v : coq_Node -> coq_R) =
  print_endline ("\n  " ^ label ^ ":");
  Stdlib.List.iter (fun u ->
    Printf.printf "    %-2s : %s\n" (string_node u) (string_value (v u))
  ) finN

let print_mva () =
  print_endline "\n=== Matrix-Vector Action of the Closure (A*·b) ===";
  let b = source_vector in
  let eff  = mva_star_eff_fun arraymat b in
  let func = mva_star_func     arraymat b in
  print_vector "eff  (mva_star_eff_fun, list-based)" eff;
  print_vector "func (mva_star_func, functional)"    func;
  let ok = Stdlib.List.for_all (fun u -> eff u = func u) finN in
  print_endline ("\n  eff = func ?  " ^ (if ok then "yes ✓" else "no ✗"))


(* -------------------------------------------------------------------- *)
(*  Language (trace) semiring demo from Schulzepath:                     *)
(*    L ⊗ M contains p1 ++ p2 whenever p1 ∈ L and p2 ∈ M                *)
(* -------------------------------------------------------------------- *)

let edge (u : coq_Node) (v : coq_Node) (w : coq_R) =
  Coq_pair (Coq_pair (u, v), w)

(* Decidable equality via the extracted Rocq predicates, rather than
   OCaml's polymorphic [=] -- safe here since [coq_Edge] is plain data,
   but polymorphic [=] silently breaks the moment an extracted type gains
   a function-typed field (e.g. a semimodule/semiring record), so it's
   worth not relying on it even where it happens to work today. *)
let edge_eq (Coq_pair (Coq_pair (u1, v1), w1)) (Coq_pair (Coq_pair (u2, v2), w2)) : bool =
  coq_Node_eqb u1 u2 && coq_Node_eqb v1 v2 && coq_R_eqb w1 w2

let rec edge_list_eq (p : coq_Edge) (q : coq_Edge) : bool =
  match p, q with
  | [], [] -> true
  | e1 :: xs, e2 :: ys -> edge_eq e1 e2 && edge_list_eq xs ys
  | _, _ -> false

let singleton (p : coq_Edge) : coq_Lang =
  fun q -> edge_list_eq p q

let print_lang_demo () =
  print_endline "\n=== Language (trace) Semiring Demo ===";
  let p1 = [ edge A C (Left 14) ] in
  let p2 = [ edge C B (Left 12) ] in
  let p  = p1 @ p2 in
  let l1 = singleton p1 in
  let l2 = singleton p2 in
  Printf.printf "  path p1 = [A→C], p2 = [C→B], p = p1 ++ p2\n";
  Printf.printf "  number of splits of p: %d\n"
    (Stdlib.List.length (split_path p));
  Printf.printf "  p ∈ lang_mul {p1} {p2} ?  %s\n"
    (if lang_mul l1 l2 p then "yes ✓" else "no ✗");
  Printf.printf "  p1 ∉ lang_mul {p1} {p2} (not a full concat) ?  %s\n"
    (if lang_mul l1 l2 p1 then "in (unexpected)" else "out ✓");
  Printf.printf "  lang_one [] = true ?  %s\n" (if lang_one [] then "yes ✓" else "no");
  Printf.printf "  lang_zero [] = true ?  %s\n" (if lang_zero [] then "yes" else "no ✓")


(* -------------------------------------------------------------------- *)
(*  Computable witness path: pow_witness_spec (proved in Rocq) says      *)
(*  measure_of_path (schulze_witness m i j) = schulze_witness_value,     *)
(*  and that this equals pow (M+I) 3 i j -- which coincides with         *)
(*  schulze_star m i j since the closure has already stabilised by 3    *)
(*  hops.  Not just the strength value: the actual path.                 *)
(* -------------------------------------------------------------------- *)

let string_edge (Coq_pair (Coq_pair (u, v), w)) : string =
  Printf.sprintf "%s→%s(%s)" (string_node u) (string_node v) (string_value w)

let string_path (p : coq_Edge) : string =
  Stdlib.String.concat " " (Stdlib.List.map string_edge p)

let print_witness_demo () =
  print_endline "\n=== Computable Witness Path (pow_witness) ===";
  Stdlib.List.iter (fun (src, dst) ->
    (match schulze_witness arraymat src dst with
     | Some p ->
         Printf.printf "  %s → %s strongest beatpath: %s\n"
           (string_node src) (string_node dst) (string_path p)
     | None ->
         Printf.printf "  %s → %s: no witness\n" (string_node src) (string_node dst));
    let wit_val = schulze_witness_value arraymat src dst in
    let star_val = schulze_star arraymat src dst in
    Printf.printf "    witness value = %-4s  schulze_star value = %-4s  %s\n"
      (string_value wit_val) (string_value star_val)
      (if wit_val = star_val then "✓" else "✗")
  ) [ (A, A); (A, B); (A, C); (A, D); (B, A); (B, B); (B, C); 
  (B, D); (C, A); (C, B); (C, C); (C, D); (D, A); (D, B); (D, C); (D, D) ]


(* -------------------------------------------------------------------- *)
(*  Main                                                                *)
(* -------------------------------------------------------------------- *)

let () =
  print_endline "╔══════════════════════════════════════════════════╗";
  print_endline "║   Schulze Path — Max-Min + Language Semiring      ║";
  print_endline "║   Concrete example, closure, matrix-vector, trace ║";
  print_endline "╚══════════════════════════════════════════════════╝";
  print_matrix ();
  print_star ();
  print_winners ();
  print_mva ();
  print_lang_demo ();
  print_witness_demo ();
  print_endline "\nDone."
