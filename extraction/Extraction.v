
From Coq Require Import Extraction.
From Examples Require Import Schulze WidestShortestPath.
(* 
Set Extraction Output Directory "./extraction/schulzecode". *)
Recursive Extraction Library Schulze.

(* 
Set Extraction Output Directory "./extraction/widestpathcode".
Recursive Extraction Library WidestShortestPath.

*)