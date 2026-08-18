(* ===================================================================== *)
(*  Schulze over a semiring: aggregator.                                 *)
(*                                                                       *)
(*  This file used to hold the whole development.  It is now a facade:   *)
(*  every criterion lives in its own file over five shared base files,   *)
(*  and this one re-exports them, so existing clients are unaffected.    *)
(*                                                                       *)
(*  Base:                                                                *)
(*    SchulzeDefsN      the five definitions and the Kleene star         *)
(*    SchulzeOrderN     order and semiring algebra                       *)
(*    SchulzeClosureN   the closure, powers, and path measures           *)
(*    SchulzeBasicsN    order facts about beating and winning            *)
(*    SchulzeWitnessN   the triangle and four-cycle witness matrices     *)
(*                                                                       *)
(*  One file per criterion, in dependency order:                         *)
(*    ResolvabilityN, TransitivityN, WinnerexistenceN,                   *)
(*    CharacterisationsN, ReversalsymmetryN, MonotonicityN, ParetoN,     *)
(*    CondorcetN, SmithN, PrudenceN, MinMaxN, NeutralityN, IsolateN      *)
(*                                                                       *)
(*  Where the characterisation results live.  Each of the first three    *)
(*  sits beside the criterion it completes; the last three combine both  *)
(*  structural guarantees and belong to neither, so they are collected.  *)
(*                                                                       *)
(*    transitivity_characterisation            TransitivityN             *)
(*    winner_exists_characterisation           WinnerexistenceN          *)
(*    clone_characterisation                   CloneN                    *)
(*    clone_iff_winner_exists                  CloneN                    *)
(*    output_well_formed_characterisation      CharacterisationsN        *)
(*    strict_partial_order_characterisation    CharacterisationsN        *)
(*    winner_beats_nonwinner_characterisation  CharacterisationsN        *)
(*                                                                       *)
(*  CloneN and SmithiiaN sit above this facade and are not re-exported,  *)
(*  since they import it.                                                *)
(* ===================================================================== *)

From Semiring Require Export
  SchulzeDefsN SchulzeOrderN SchulzeClosureN
  SchulzeBasicsN SchulzeWitnessN ResolvabilityN
  TransitivityN WinnerexistenceN CharacterisationsN
  ReversalsymmetryN MonotonicityN ParetoN
  CondorcetN SmithN PrudenceN
  MinMaxN NeutralityN IsolateN.
