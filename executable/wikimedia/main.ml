open Wikimedia

 
let string_candidates : coq_Node -> string = function
| A -> "A"
| B -> "B"
| C -> "C"
| D -> "D"
| E -> "E"

(* 
let string_candidates : coq_Node -> string = function
  | TC  -> "Ting Chen (Wing)"
  | SK  -> "Samuel Klein"
  | KW  -> "Kat Walsh"
  | MR  -> "Milos Rancic"
  | LG  -> "Lodewijk Gelauff"
  | CB  -> "Claudi Balaguer"
  | HC  -> "Harel Cain"
  | JSR -> "Jane S. Richardson"
  | PL  -> "Patricio Lorente"
  | JG  -> "Joan Gomà"
  | JF  -> "James Forrester"
  | FSS -> "Ferdinando Scala"
  | GM  -> "Gerard Meijssen"
  | MP  -> "Marc-André Pelletier"
  | EZ  -> "Esteban Zárate"
  | WHD -> "William H. DuBay"
  | UW  -> "Urs Wäfler"
  | TM  -> "Tom Morton"
*)

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


(* 
let matrix : coq_R array array = 
[|
  [| oneR; Left 1010; Left 1052; Left 1132; Left 1180; Left 1229; Left 1198; Left 1222; Left 1218; Left 1231; Left 1176; Left 1226; Left 1274; Left 1289; Left 1328; Left 1352; Left 1315; Left 1345 |];
  [| Left 977; oneR; Left 969; Left 1068; Left 1131; Left 1153; Left 1118; Left 1187; Left 1152; Left 1148; Left 1142; Left 1207; Left 1217; Left 1239; Left 1281; Left 1262; Left 1292; Left 1310 |];
  [| Left 903; Left 874; oneR; Left 1022; Left 1083; Left 1122; Left 1080; Left 1056; Left 1108; Left 1154; Left 1052; Left 1142; Left 1139; Left 1158; Left 1210; Left 1202; Left 1241; Left 1219 |];
  [| Left 846; Left 817; Left 887; oneR; Left 943; Left 946; Left 885; Left 990; Left 950; Left 945; Left 969; Left 984; Left 1012; Left 1059; Left 1077; Left 1083; Left 1111; Left 1099 |];
  [| Left 721; Left 716; Left 789; Left 838; oneR; Left 920; Left 905; Left 921; Left 860; Left 935; Left 863; Left 908; Left 906; Left 984; Left 995; Left 1036; Left 1001; Left 1015 |];
  [| Left 811; Left 837; Left 887; Left 799; Left 888; oneR; Left 875; Left 886; Left 869; Left 760; Left 911; Left 883; Left 937; Left 932; Left 930; Left 953; Left 983; Left 983 |];
  [| Left 704; Left 645; Left 743; Left 783; Left 785; Left 842; oneR; Left 861; Left 784; Left 800; Left 831; Left 867; Left 915; Left 912; Left 960; Left 943; Left 972; Left 985 |];
  [| Left 716; Left 705; Left 728; Left 786; Left 860; Left 830; Left 818; oneR; Left 838; Left 843; Left 853; Left 849; Left 907; Left 909; Left 910; Left 876; Left 935; Left 957 |];
  [| Left 685; Left 670; Left 720; Left 718; Left 799; Left 813; Left 789; Left 832; oneR; Left 812; Left 802; Left 799; Left 866; Left 894; Left 880; Left 938; Left 961; Left 953 |];
  [| Left 706; Left 735; Left 747; Left 745; Left 792; Left 739; Left 783; Left 800; Left 734; oneR; Left 816; Left 796; Left 865; Left 891; Left 891; Left 905; Left 950; Left 933 |];
  [| Left 655; Left 589; Left 625; Left 706; Left 734; Left 813; Left 731; Left 761; Left 759; Left 763; oneR; Left 785; Left 821; Left 808; Left 879; Left 855; Left 900; Left 866 |];
  [| Left 676; Left 634; Left 713; Left 665; Left 738; Left 716; Left 713; Left 749; Left 691; Left 708; Left 749; oneR; Left 820; Left 789; Left 794; Left 850; Left 873; Left 854 |];
  [| Left 606; Left 584; Left 668; Left 647; Left 649; Left 779; Left 692; Left 766; Left 727; Left 729; Left 714; Left 751; oneR; Left 798; Left 834; Left 834; Left 829; Left 864 |];
  [| Left 548; Left 512; Left 539; Left 565; Left 614; Left 621; Left 605; Left 626; Left 597; Left 611; Left 599; Left 622; Left 661; oneR; Left 691; Left 722; Left 749; Left 704 |];
  [| Left 478; Left 486; Left 526; Left 466; Left 555; Left 530; Left 508; Left 574; Left 447; Left 482; Left 562; Left 521; Left 590; Left 590; oneR; Left 656; Left 637; Left 654 |];
  [| Left 482; Left 478; Left 512; Left 485; Left 558; Left 558; Left 533; Left 482; Left 553; Left 521; Left 548; Left 517; Left 628; Left 601; Left 603; oneR; Left 646; Left 628 |];
  [| Left 413; Left 465; Left 528; Left 487; Left 521; Left 536; Left 515; Left 546; Left 527; Left 510; Left 544; Left 482; Left 592; Left 554; Left 575; Left 599; oneR; Left 635 |];
  [| Left 458; Left 403; Left 423; Left 449; Left 489; Left 515; Left 458; Left 486; Left 484; Left 493; Left 455; Left 482; Left 543; Left 500; Left 535; Left 573; Left 585; oneR |]
|]
*)
  
let rank (n : coq_Node) : int =
  match n with 
  | A -> 0 | B -> 1 | C -> 2 | D -> 3 | E -> 4

(*  
let rank (n : coq_Node) : int =
  match n with 
  | TC  -> 0
  | SK  -> 1
  | KW  -> 2
  | MR  -> 3
  | LG  -> 4
  | CB  -> 5
  | HC  -> 6
  | JSR -> 7
  | PL  -> 8
  | JG  -> 9
  | JF  -> 10
  | FSS -> 11
  | GM  -> 12
  | MP  -> 13
  | EZ  -> 14
  | WHD -> 15
  | UW  -> 16
  | TM  -> 17
*)


let arraymat (x : coq_Node) (y : coq_Node) : coq_R = 
  matrix.(rank x).(rank y) 
  

let _ = 
  let comp = wikimedia arraymat in 
  let ret = List.map (fun (x, y) -> (string_candidates x, string_candidates y, string_values (comp x y))) 
    (cross_product finN finN) in 
  print_endline (string_list ret)

  
