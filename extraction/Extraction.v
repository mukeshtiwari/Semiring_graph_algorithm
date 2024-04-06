
From Coq Require Import Extraction.
From Examples Require Import Schulze WidestShortestPath.

Set Extraction Output Directory "_build/schulze". 
Recursive Extraction Library Schulze.

(* 
Set Extraction Output Directory "./extraction/widestpathcode".
Recursive Extraction Library WidestShortestPath.

*)