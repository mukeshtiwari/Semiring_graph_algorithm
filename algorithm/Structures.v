(* ========================================================================= *)
(*  Algebraic Structures via Hierarchy Builder                               *)
(*                                                                           *)
(*  Follows the Wikipedia definition of a semiring:                          *)
(*    https://en.wikipedia.org/wiki/Semiring                                 *)
(*                                                                           *)
(*  Hierarchy:                                                               *)
(*    - CommutativeMonoid   (additive, reused for both R and V)              *)
(*    - Semiring            = CommutativeMonoid + multiplicative + distrib   *)
(*    - IdempotentSemiring  = Semiring + idempotence                         *)
(*    - BoundedSemiring     = Semiring + boundedness                         *)
(*    - IsSemimodule        (two-sorted typeclass over the above)            *)
(*                                                                           *)
(*  Key design choice: IsSemiring extends CommutativeMonoid, so the additive *)
(*  commutative monoid is defined once and shared by both the semiring (R)   *)
(*  and the vector space (V).  Operations are disambiguated by type.         *)
(* ========================================================================= *)

From HB Require Import structures.
From Stdlib Require Import Utf8 List.

(* ========================================================================= *)
(*  1. Commutative Monoid — additive structure, shared by R and V            *)
(* ========================================================================= *)

HB.mixin Record IsCommutativeMonoid V := {
  zero : V;
  add  : V -> V -> V;

  addA  : forall x y z : V, add (add x y) z = add x (add y z);
  addC  : forall x y : V, add x y = add y x;
  add0r : forall x : V, add zero x = x;
  addr0 : forall x : V, add x zero = x;
}.

HB.structure Definition CommutativeMonoid := { V of IsCommutativeMonoid V }.

Module CMonoidNotations.
  Notation "x ⊕ y" := (add x y) (at level 50, left associativity).
  Notation "0V" := zero.
End CMonoidNotations.

(* ========================================================================= *)
(*  2. Semiring = CommutativeMonoid (additive) + multiplicative + distrib    *)
(* ========================================================================= *)

HB.mixin Record IsSemiring R of CommutativeMonoid R := {
  one : R;
  mul : R -> R -> R;

  mulA  : forall a b c : R, mul (mul a b) c = mul a (mul b c);
  mul1r : forall a : R, mul one a = a;
  mulr1 : forall a : R, mul a one = a;

  mulDr : forall a b c : R, mul (add a b) c = add (mul a c) (mul b c);
  mulDl : forall a b c : R, mul a (add b c) = add (mul a b) (mul a c);

  mul0r : forall a : R, mul zero a = zero;
  mulr0 : forall a : R, mul a zero = zero;
}.

HB.structure Definition Semiring :=
  { R of IsSemiring R & CommutativeMonoid R }.

Module SemiringNotations.
  Notation "a + b" := (add a b) (at level 50, left associativity).
  Notation "a * b" := (mul a b) (at level 40, left associativity).
  Notation "0" := zero.
  Notation "1" := one.
End SemiringNotations.

(* ========================================================================= *)
(*  3. Commutative Semiring (extends Semiring)                               *)
(* ========================================================================= *)

HB.mixin Record IsCommutativeSemiring R of Semiring R := {
  mulC : forall a b : R, mul a b = mul b a;
}.

HB.structure Definition CommutativeSemiring :=
  { R of IsCommutativeSemiring R & Semiring R }.

(* ========================================================================= *)
(*  4. Idempotent Semiring (extends Semiring)                                *)
(* ========================================================================= *)

HB.mixin Record IsIdempotentSemiring R of Semiring R := {
  add_idem : forall a : R, add a a = a;
}.

HB.structure Definition IdempotentSemiring :=
  { R of IsIdempotentSemiring R & Semiring R }.

(* ========================================================================= *)
(*  5. Bounded Semiring (extends Semiring)                                   *)
(* ========================================================================= *)

HB.mixin Record IsBoundedSemiring R of Semiring R := {
  add_bound : forall a : R, add one a = one;
}.

HB.structure Definition BoundedSemiring :=
  { R of IsBoundedSemiring R & Semiring R }.

(* ========================================================================= *)
(*  5b. Bounded Commutative Semiring                                          *)
(*       Combines BoundedSemiring + CommutativeSemiring.                      *)
(*       Since both share the Semiring ancestor, mulC and add_bound live     *)
(*       in the same HB sort, so [rewrite mulC] works on bounded semiring    *)
(*       terms directly.                                                      *)
(* ========================================================================= *)

HB.structure Definition BoundedCommutativeSemiring :=
  { R of IsBoundedSemiring R & IsCommutativeSemiring R & Semiring R }.

(* ========================================================================= *)
(*  6. Semimodule (two-sorted, parameterized HB structure)                   *)

HB.mixin Record IsSemimodule {R : Semiring.type} V
    of CommutativeMonoid V := {

  scale : R -> V -> V;

  scale_distr_v : forall (a : R) (x y : V),
    scale a (add x y) = add (scale a x) (scale a y);

  scale_distr_r : forall (a b : R) (x : V),
    scale (add a b) x = add (scale a x) (scale b x);

  scale_assoc : forall (a b : R) (x : V),
    scale a (scale b x) = scale (mul a b) x;

  scale_one : forall (x : V), scale one x = x;

  scale_zero_r : forall (x : V), scale zero x = zero;

  scale_zero_v : forall (a : R), scale a zero = zero;
}.

HB.structure Definition Semimodule (R : Semiring.type) :=
  { V of IsSemimodule R V & CommutativeMonoid V }.

Module SemimoduleNotations.
  Notation "a ⊙ v" := (scale a v) (at level 40).
End SemimoduleNotations.

(* ========================================================================= *)
(*  7. Finite Type — a type with a decidable, complete, duplicate-free       *)
(*     enumeration of all its elements.                                      *)
(* ========================================================================= *)

HB.mixin Record IsFinType T := {
  elements : list T;
  elements_nodup : NoDup elements;
  elements_complete : forall x : T, In x elements;
  elements_two_or_more : (2 <= List.length elements)%nat;
  fin_eq_dec : forall x y : T, {x = y} + {x <> y};
}.

HB.structure Definition FinType := { T of IsFinType T }.
