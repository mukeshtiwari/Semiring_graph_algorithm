(* ========================================================================= *)
(*  Setoid Infrastructure for Boolean Equivalence Relations                   *)
(*                                                                           *)
(*  This module provides the bridge between the boolean-valued relations      *)
(*  (brel : A -> A -> bool) used throughout the codebase and Coq's setoid     *)
(*  rewriting machinery, which operates on Prop-valued relations.            *)
(*                                                                           *)
(*  After importing this file and declaring the appropriate instances,       *)
(*  you can use [setoid_rewrite] and [rewrite] with hypotheses of the form   *)
(*  [eqR x y = true] or [eqN x y = true].                                     *)
(* ========================================================================= *)

From Stdlib Require Import RelationClasses Morphisms Setoid.
From Semiring Require Import Definitions.

(* ------------------------------------------------------------------------- *)
(*  If r is an equivalence (as a brel), then brel_prop r is an Equivalence   *)
(* ------------------------------------------------------------------------- *)

Section BrelEquiv.

  Variables
    (A : Type)
    (r : brel A)
    (ref_r : brel_reflexive A r)
    (sym_r : brel_symmetric A r)
    (trn_r : brel_transitive A r).

  Lemma brel_prop_refl : forall x, brel_prop r x x.
  Proof. unfold brel_prop. apply ref_r. Qed.


  Lemma brel_prop_sym : forall x y, brel_prop r x y -> brel_prop r y x.
  Proof. unfold brel_prop. intros. apply sym_r. assumption. Qed.

  Lemma brel_prop_trans : forall x y z,
    brel_prop r x y -> brel_prop r y z -> brel_prop r x z.
  Proof. unfold brel_prop. intros. eapply trn_r; eassumption. Qed.

  #[export]
  Instance brel_prop_equiv : Equivalence (brel_prop r).
  Proof.
    split.
    - exact brel_prop_refl.
    - exact brel_prop_sym.
    - exact brel_prop_trans.
  Qed.

End BrelEquiv.

(* ------------------------------------------------------------------------- *)
(*  Proper instance builders for common operations                           *)
(* ------------------------------------------------------------------------- *)

(* If a binary operation is congruent w.r.t. a boolean relation, it is       *)
(* Proper w.r.t. the corresponding Prop relation.                             *)
Lemma bop_congruence_proper {A : Type} (r : brel A) (b : binary_op A) :
  bop_congruence A r b ->
  Proper (brel_prop r ==> brel_prop r ==> brel_prop r) b.
Proof.
  unfold bop_congruence, brel_prop, Proper, respectful.
  intros H x1 x2 Hx y1 y2 Hy.
  apply H; assumption.
Qed.

(* If eqB is congruent in eqA (brel_congruence), then it is Proper.          *)
Lemma brel_congruence_proper {A : Type} (eqA eqB : brel A) :
  brel_congruence A eqA eqB ->
  Proper (brel_prop eqA ==> brel_prop eqA ==> eq) (fun s t => eqB s t).
Proof.
  unfold brel_congruence, brel_prop, Proper, respectful.
  intros H s1 s2 Hs t1 t2 Ht.
  apply H; assumption.
Qed.

(* ========================================================================= *)
(*  Typeclass-based setoid infrastructure                                    *)
(*                                                                           *)
(*  Instead of manually declaring #[local] Equivalence and Proper instances  *)
(*  in every section, we introduce two typeclasses that bundle the boolean   *)
(*  proofs together.  Once you declare an instance of [BrelEquivalence] or   *)
(*  [BopCongruence], the corresponding Coq setoid instances are resolved     *)
(*  automatically via typeclass search — no duplication needed.             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*  [BrelEquivalence A eqA] bundles the reflexivity, symmetry, and           *)
(*  transitivity proofs for a boolean relation [eqA : brel A].                *)
(* ------------------------------------------------------------------------- *)
Class BrelEquivalence (A : Type) (eqA : brel A) : Type := {
  brel_equiv_refl  : brel_reflexive A eqA;
  brel_equiv_sym   : brel_symmetric A eqA;
  brel_equiv_trans : brel_transitive A eqA;
}.

#[export]
Instance brel_equiv_from_class {A : Type} {eqA : brel A}
  `{BrelEquivalence A eqA} : Equivalence (brel_prop eqA).
Proof.
  apply brel_prop_equiv;
    [apply brel_equiv_refl
    |apply brel_equiv_sym
    |apply brel_equiv_trans].
Qed.

(* ------------------------------------------------------------------------- *)
(*  [BopCongruence A eqA b] bundles the congruence proof for a binary        *)
(*  operation [b] w.r.t. the boolean relation [eqA].                          *)
(* ------------------------------------------------------------------------- *)
Class BopCongruence (A : Type) (eqA : brel A) (b : binary_op A) : Type := {
  bop_congr_proof : bop_congruence A eqA b;
}.

#[export]
Instance bop_proper_from_class {A : Type} {eqA : brel A} {b : binary_op A}
  `{BopCongruence A eqA b} :
  Proper (brel_prop eqA ==> brel_prop eqA ==> brel_prop eqA) b.
Proof.
  apply bop_congruence_proper; apply bop_congr_proof.
Qed.

(* ------------------------------------------------------------------------- *)
(*  [BrelCongruence A eqA eqB] bundles the congruence proof for a boolean    *)
(*  relation [eqB] w.r.t. [eqA].                                              *)
(* ------------------------------------------------------------------------- *)
Class BrelCongruence (A : Type) (eqA eqB : brel A) : Type := {
  brel_congr_proof : brel_congruence A eqA eqB;
}.

#[export]
Instance brel_congruence_proper_from_class {A : Type} {eqA eqB : brel A}
  `{BrelCongruence A eqA eqB} :
  Proper (brel_prop eqA ==> brel_prop eqA ==> eq) (fun s t => eqB s t).
Proof.
  apply brel_congruence_proper; apply brel_congr_proof.
Qed.
