(** * The worked example of the paper, from actual ballots

    18 voters and the margin measure:

       7 voters  a1 > a2 > a3
       5 voters  a2 > a3 > a1
       6 voters  a3 > a1 > a2

    The support counts are N[a1,a2] = 13, N[a2,a1] = 5, N[a2,a3] = 12,
    N[a3,a2] = 6, N[a3,a1] = 11, N[a1,a3] = 7, so the margins round the
    cycle are 8, 6, 4. *)

From Stdlib Require Import Utf8 List Arith Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN OrderSemiring
  NormalizedOrder ExtendOrder MeasureN SocialchoiceN SchulzeOnNT BallotN.
From Examples Require Import MarginMeasure Profiles.
From Examples Require Import Shortestpath.
Import ListNotations.

Notation Node := Shortestpath.Node.
Notation a1 := Shortestpath.A.
Notation a2 := Shortestpath.B.
Notation a3 := Shortestpath.C.

Definition rank (x y z : Node) : Node -> nat := fun n : Node =>
  if fin_eq_dec n x then 0 else if fin_eq_dec n y then 1 else 2.

Definition worked_profile : list (Node -> nat) :=
  repeat (rank a1 a2 a3) 7 ++ repeat (rank a2 a3 a1) 5 ++ repeat (rank a3 a1 a2) 6.

Definition Mb : Node -> Node -> Margin := matrix_of margin_measure worked_profile.

Theorem worked_ballots_counts :
  count worked_profile a1 a2 = 13 /\ count worked_profile a2 a1 = 5 /\
  count worked_profile a2 a3 = 12 /\ count worked_profile a3 a2 = 6 /\
  count worked_profile a3 a1 = 11 /\ count worked_profile a1 a3 = 7.
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition mg (d : nat) : Margin := strength margin_measure (d, 0).

(** Equality on [Margin] is decided by the underlying element ([NT_eq]). *)
Local Ltac nt := apply (NT_eq margin_spec); vm_compute; reflexivity.
Local Ltac nt_refute H :=
  apply (f_equal (val margin_spec)) in H; vm_compute in H; discriminate H.
Local Ltac beat := split; [nt | let H := fresh in intro H; nt_refute H].

Theorem worked_ballots_links :
  Mb a1 a2 = mg 8 /\ Mb a2 a3 = mg 6 /\ Mb a3 a1 = mg 4.
Proof. repeat split; nt. Qed.

Theorem worked_ballots_star :
  mat_star Mb a1 a2 = mg 8 /\ mat_star Mb a1 a3 = mg 6 /\
  mat_star Mb a2 a3 = mg 6 /\ mat_star Mb a2 a1 = mg 4 /\
  mat_star Mb a3 a1 = mg 4 /\ mat_star Mb a3 a2 = mg 4.
Proof. repeat split; nt. Qed.

Theorem worked_ballots_order :
  schulze_beats Mb a1 a2 /\ schulze_beats Mb a1 a3 /\ schulze_beats Mb a2 a3.
Proof. repeat split; first [nt | let H := fresh in intro H; nt_refute H]. Qed.

Theorem worked_ballots_winner :
  schulze_winner Mb a1 /\ ~ schulze_winner Mb a2 /\ ~ schulze_winner Mb a3.
Proof.
  split; [| split].
  - intros b Hb [Hle Hne].
    destruct b; [congruence | nt_refute Hle | nt_refute Hle].
  - intro Hw. apply (Hw a1 ltac:(discriminate)). beat.
  - intro Hw. apply (Hw a1 ltac:(discriminate)). beat.
Qed.
