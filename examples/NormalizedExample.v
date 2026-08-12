(* ========================================================================= *)
(*  Smoke test for NormalizedOrder: a total preorder with a genuine tie      *)
(*  class becomes a bounded commutative semiring.                            *)
(*                                                                           *)
(*  Carrier: nat, compared after capping at 2, so 2, 3, 4, ... are all       *)
(*  equivalent but not equal.  That is exactly the situation that defeats    *)
(*  [le_antisym] for Schulze's strength measures — where every pairwise tie  *)
(*  (k,k) is equivalent to every other — reproduced in miniature.            *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 Arith Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN OrderSemiring NormalizedOrder.

(* ------------------------------------------------------------------ *)
(*  The preorder                                                       *)
(* ------------------------------------------------------------------ *)

Definition cap (x : nat) : nat := Nat.min x 2.
Definition cle (x y : nat) : bool := Nat.leb (cap x) (cap y).

Lemma cle_refl : forall a, cle a a = true.
Proof. intro a. apply Nat.leb_refl. Qed.

Lemma cle_trans : forall a b c, cle a b = true -> cle b c = true -> cle a c = true.
Proof.
  intros a b c H1 H2. unfold cle in *.
  apply Nat.leb_le in H1, H2. apply Nat.leb_le. lia.
Qed.

Lemma cle_total : forall a b, cle a b = true \/ cle b a = true.
Proof.
  intros a b. unfold cle.
  destruct (Nat.le_ge_cases (cap a) (cap b)) as [H|H];
    [left | right]; apply Nat.leb_le; lia.
Qed.

Lemma cap_idem : forall a, cap (cap a) = cap a.
Proof. intro a. unfold cap. lia. Qed.

Lemma cap_le : forall a, cle a (cap a) = true.
Proof. intro a. unfold cle, cap. apply Nat.leb_le. lia. Qed.

Lemma cap_ge : forall a, cle (cap a) a = true.
Proof. intro a. unfold cle, cap. apply Nat.leb_le. lia. Qed.

Lemma cap_compl : forall a b, cle a b = true -> cle b a = true -> cap a = cap b.
Proof.
  intros a b H1 H2. unfold cle in *.
  apply Nat.leb_le in H1, H2. unfold cap in *. lia.
Qed.

Lemma cap_bot : cap 0 = 0. Proof. reflexivity. Qed.
Lemma cap_top : cap 2 = 2. Proof. reflexivity. Qed.

Lemma cbot_least : forall a, cle 0 a = true.
Proof. intro a. unfold cle, cap. apply Nat.leb_le. lia. Qed.

Lemma ctop_greatest : forall a, cle a 2 = true.
Proof. intro a. unfold cle, cap. apply Nat.leb_le. lia. Qed.

(* The tie class is real: 2 and 3 are equivalent but not equal, and they
   share a canonical representative. *)
Example ties_are_equivalent : cle 2 3 = true /\ cle 3 2 = true /\ 2 <> 3.
Proof. repeat split; try reflexivity; discriminate. Qed.

Example ties_share_normal_form : cap 2 = cap 3.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  The normalised carrier and its algebra                             *)
(*                                                                     *)
(*  Everything below is assembled from the generic results; no          *)
(*  algebraic law is proved here.                                       *)
(* ------------------------------------------------------------------ *)

(* Everything a client supplies: one record literal.  The bounded commutative
   semiring instance is declared once and for all in NormalizedOrder.v, so
   there are no per-carrier instance blocks. *)
Definition cap_spec : CanonSpec nat :=
  {| cs_eq_dec       := Nat.eq_dec;
     cs_le           := cle;
     cs_norm         := cap;
     cs_bot          := 0;
     cs_top          := 2;
     cs_refl         := cle_refl;
     cs_trans        := cle_trans;
     cs_total        := cle_total;
     cs_norm_idem    := cap_idem;
     cs_norm_le      := cap_le;
     cs_norm_ge      := cap_ge;
     cs_norm_compl   := cap_compl;
     cs_bot_canon    := cap_bot;
     cs_top_canon    := cap_top;
     cs_bot_least    := cbot_least;
     cs_top_greatest := ctop_greatest |}.

Definition C : Type := NT cap_spec.

(* The payoff: [C] is recognised as a bounded semiring, so everything in the
   development that is parametric in the carrier applies to it. *)
Check (C : BoundedSemiring.type).
Check (C : BoundedCommutativeSemiring.type).

(* …and the order it was built from is the derived order the theorems use. *)
Check (Orel_iff_leN cap_spec
        : forall x y : C, Orel x y <-> leN cap_spec x y = true).
