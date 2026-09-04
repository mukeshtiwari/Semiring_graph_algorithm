(** * Bench.v — functional versus tabulated matrix power

    Reproduces the timing table of the paper.  A matrix over an arbitrary
    semiring is a FUNCTION [Node -> Node -> R].  That is what makes the
    theory pleasant to state, but it is unusable as a program: evaluating
    an entry of [M^k] re-expands [M] along every walk of length [k], with
    nothing shared, so one entry costs Theta(n^(k-1)) semiring operations.

    [MatN.v] therefore carries a tabulated representation as well —
    [to_list], [of_list], [mul_list], [pow_list] — where each entry is
    computed once, and exponentiation is by repeated squaring.  The two
    are proved to agree ([of_list_pow_pos_list], [pow_fun_powN_fun_eqv]),
    so the statements may quantify over functions while the extracted
    program runs on lists.

    Below, [fun_pow] is the functional power and [list_pow] the tabulated
    one, over the max-min carrier of [Schulze.v] with n = 9 alternatives.
    The closure of an n-alternative election needs k = n - 1 = 8.

    Measured with Rocq 9.0.1 on an Apple M3 Pro:

        k     fun_pow (s)    list_pow (s)
        3       0.002           0.001
        4       0.016
        5       0.138           0.002
        6       1.246
        7      11.159           0.002
        8     102.364           0.002
       16                       0.005
       64                       0.021

    The functional column multiplies by nine at each step, which is
    Theta(n^(k-1)) with n = 9.  Uncomment a line at the bottom to re-run. *)

From Stdlib Require Import List Utf8 BinNatDef PeanoNat Lia.
From HB Require Import structures.
From Semiring Require Import MatN SemimoduleN Structures.
From Examples Require Import Schulze.
Import ListNotations SemiringNotations.

(** Nine alternatives. *)
Inductive BNode := N0 | N1 | N2 | N3 | N4 | N5 | N6 | N7 | N8.

Definition belements : list BNode := [N0;N1;N2;N3;N4;N5;N6;N7;N8].

Lemma bnodup : NoDup belements.
Proof. unfold belements. repeat constructor; cbn; intuition congruence. Qed.

Lemma bcomplete : forall x : BNode, In x belements.
Proof. unfold belements; intros []; cbn; tauto. Qed.

Lemma btwo : (2 <= List.length belements)%nat.
Proof. cbn. lia. Qed.

Definition beq_dec (x y : BNode) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

HB.instance Definition _ :=
  IsFinType.Build BNode belements bnodup bcomplete btwo beq_dec.

Definition idx (n : BNode) : nat :=
  match n with
  | N0=>0|N1=>1|N2=>2|N3=>3|N4=>4|N5=>5|N6=>6|N7=>7|N8=>8
  end.

(** A dense matrix over the max-min carrier of [Schulze.v]. *)
Definition m (i j : BNode) : Schulze.R :=
  Schulze.Left (1 + Nat.modulo (idx i * 7 + idx j * 3) 11).

(** The functional power: nothing is tabulated, nothing is shared. *)
Definition fun_pow (k : nat) : BNode -> BNode -> Schulze.R := pow m k.

(** The tabulated power: [to_list], then [pow_list], then [of_list]. *)
Definition list_pow (k : nat) : BNode -> BNode -> Schulze.R := pow_fun m k.

(** Re-run the table by uncommenting these, one at a time.
    [fun_pow 8] takes about a minute and a half. *)

(* Time Eval vm_compute in (fun_pow 3 N0 N8). *)
(* Time Eval vm_compute in (fun_pow 8 N0 N8). *)
(* Time Eval vm_compute in (list_pow 8 N0 N8). *)
(* Time Eval vm_compute in (list_pow 64 N0 N8). *)
