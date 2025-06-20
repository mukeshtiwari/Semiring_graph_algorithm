
From Stdlib Require Import Extraction.
From Examples Require Import Schulze.
Set Extraction Output Directory ".". 

Extract Inductive nat => int [ "0" "Stdlib.Int.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Recursive Extraction Library Schulze.
