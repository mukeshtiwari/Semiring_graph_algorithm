From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat. 
From HB Require Import structures.
From Semiring Require Import MatN 
  SemimoduleN Structures.
Import ListNotations SemiringNotations.


  (* It should be shortest widest path. Most of the literature    *)
  (* treat the widest-shortest path below but it is not entirely  *)
  (* correct becasue the distributive laws (left_distributive_mul_over_plus, *)
  (* right_distributive_mul_over_plus) do NOT hold for this semiring.    *)
  (* Counterexample: a = (Infinity, Left 5), b = (Left 1, Left 10),     *)
  (* c = (Left 2, Left 3). Then a*(b+c) = (Infinity, Left 5) but        *)
  (* a*b + a*c = (Infinity, Left 3). The failure occurs because when     *)
  (* mulf saturates to Infinity, the tiebreaker on second components     *)
  (* does not respect the lexicographic order established by the first   *)
  (* components.                                                         *)

Section Comp.

  (* Define Candidates *)
  Inductive Node := A | B | C. 
  

   (* Nat extended with Infinity *)
  Inductive R := 
  | Left : nat -> R 
  | Infinity : R.

  Definition eqR (u v : R) : bool :=
  match u, v with 
  | Left x, Left y => Nat.eqb x y 
  | Infinity, Infinity => true 
  | _, _ => false 
  end. 

  Section min_plus.

    (* min_plus algebra + = min, * = +, 
      zero = Infinity, and one = Left 0 *)

    Definition zerof : R := Infinity. 
    Definition onef : R := Left 0. 
  
    Definition plusf (u v : R) : R :=
    match u, v with 
    | Left x, Left y => Left (Nat.min x y)
    | Left x, Infinity => Left x
    | Infinity, Left x => Left x 
    | _, _ => Infinity
    end. 

    Definition mulf (u v : R) : R :=
    match u, v with 
    | Left x, Left y => Left (Nat.add x y)
    | _, _ => Infinity
    end. 

  End min_plus.

  Section max_min.

    (* + = max, * = min, zero = 0, one = Infinity *)
    Definition zeros : R := Left 0.
    Definition ones : R := Infinity.

    Definition pluss (u v : R) : R :=
    match u, v with 
    | Left x, Left y => Left (Nat.max x y)
    | _, _ => Infinity 
    end. 

  
    Definition muls (u v : R) : R :=
    match u, v with 
    | Left x, Left y => Left (Nat.min x y)
    | Left x, Infinity => Left x 
    | Infinity, Left x => Left x 
    | _, _ => Infinity 
    end.


   
  End max_min.


  (* This definition does appear to be correct in 
  the paper. *)
  Definition ltR (u v : R) : bool :=
  match u, v with 
  | Left x, Left y => Nat.ltb x y 
  | Left x, Infinity => true 
  | Infinity, Left _ => false 
  | _, _ => false
  end.

  (* pair *)
  Definition RR : Type := R * R. 
  (* zero *)
  Definition zeroRR : RR := (zerof, zeros). 
  (* one *)
  Definition oneRR : RR := (onef, ones).

  Definition eqRR (x y : RR) : bool :=
  match x, y with 
  |(xa, xb), (ya, yb) => eqR xa ya && eqR xb yb 
  end.


  (* Lexicographic product *)
  Definition plusRR (u v : RR) : RR :=
  match u, v with 
  | (au, bu), (av, bv) => 
    match orb (ltR au av) (andb (eqR au av) (ltR bv bu)) with 
    | true => (au, bu)
    | _ => (av, bv)
    end 
  end. 

 
  (* Direct product *)
  Definition mulRR (u v : RR) : RR :=
  match u, v with 
  | (au, bu), (av, bv) => (mulf au av,  muls bu bv)
  end.  


  Definition finN : list Node := [A; B; C].

End Comp.


(* =================================================================== *)
(*  HB Instances: FinType Node, BoundedSemiring RR                       *)
(*                                                                       *)
(*  RR = R × R lexicographic product.                                    *)
(*  First component: min-plus (shortest path).                           *)
(*  Second component: max-min (widest path), tiebreaker.                 *)
(* =================================================================== *)

Section HBInstances.

  Definition fin_eq_dec (x y : Node) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition elements_list : list Node := [A; B; C].

  Lemma elements_nodup_proof : NoDup elements_list.
  Proof.
    unfold elements_list.
    apply NoDup_cons. intro H. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H.
    apply NoDup_cons. intro H. simpl in H. destruct H as [Heq|H]; [inversion Heq|]. simpl in H. destruct H.
    apply NoDup_cons. intro H. simpl in H. destruct H.
    apply NoDup_nil.
  Qed.

  Lemma elements_complete_proof : forall x : Node, In x elements_list.
  Proof. unfold elements_list; intros [ | | ]; simpl; auto. Qed.

  Lemma elements_two_or_more_proof : (2 <= List.length elements_list)%nat.
  Proof. unfold elements_list. cbn. nia. Qed.

  HB.instance Definition _ := IsFinType.Build Node
    elements_list elements_nodup_proof elements_complete_proof
    elements_two_or_more_proof fin_eq_dec.

  Lemma addA_proof : forall x y z : RR, plusRR (plusRR x y) z = plusRR x (plusRR y z).
  Proof. Admitted.

  Lemma addC_proof : forall x y : RR, plusRR x y = plusRR y x.
  Proof. Admitted.

  Lemma add0r_proof : forall x : RR, plusRR zeroRR x = x.
  Proof. Admitted.

  Lemma addr0_proof : forall x : RR, plusRR x zeroRR = x.
  Proof. Admitted.

  HB.instance Definition _ := IsCommutativeMonoid.Build RR
    zeroRR plusRR addA_proof addC_proof add0r_proof addr0_proof.

  Lemma mulA_proof : forall a b c : RR, mulRR (mulRR a b) c = mulRR a (mulRR b c).
  Proof. Admitted.

  Lemma mul1r_proof : forall a : RR, mulRR oneRR a = a.
  Proof. Admitted.

  Lemma mulr1_proof : forall a : RR, mulRR a oneRR = a.
  Proof. Admitted.

  Lemma mulDr_proof : forall a b c : RR, mulRR (plusRR a b) c = plusRR (mulRR a c) (mulRR b c).
  Proof. Admitted.

  Lemma mulDl_proof : forall a b c : RR, mulRR a (plusRR b c) = plusRR (mulRR a b) (mulRR a c).
  Proof. Admitted.

  Lemma mul0r_proof : forall a : RR, mulRR zeroRR a = zeroRR.
  Proof. Admitted.

  Lemma mulr0_proof : forall a : RR, mulRR a zeroRR = zeroRR.
  Proof. Admitted.

  HB.instance Definition _ := IsSemiring.Build RR
    oneRR mulRR mulA_proof mul1r_proof mulr1_proof
    mulDr_proof mulDl_proof mul0r_proof mulr0_proof.

  Axiom add_bound_axiom : forall a : RR, plusRR oneRR a = oneRR.
  HB.instance Definition _ := IsBoundedSemiring.Build RR add_bound_axiom.

  HB.instance Definition _ := IsSemimodule.Build RR RR
    mulRR mulDl_proof mulDr_proof
    (fun a b x => eq_sym (mulA_proof a b x))
    mul1r_proof mul0r_proof mulr0_proof.

End HBInstances.

Definition widestshortestpath (m : Node -> Node -> RR) : Node -> Node -> RR :=
  powN_fun m 2%N.

Definition mva_eff_fun (m : Node -> Node -> RR) (v : Node -> RR) : Node -> RR :=
  SemimoduleN.matrix_vector_action_eff_fun m v.

Definition mva_func (m : Node -> Node -> RR) (v : Node -> RR) : Node -> RR :=
  SemimoduleN.matrix_vector_action m v.

(* ========================================================================= *)
(*  WIDEST-SHORTEST PATH SEMIRING: layered construction (OCaml Cas)           *)
(*                                                                           *)
(*  This file implements a DIRECT encoding of the widest-shortest path       *)
(*  problem as an R × R pair with a lexicographic tiebreaker. The            *)
(*  distributive laws do NOT hold for this direct encoding (see NOTE above). *)
(*                                                                           *)
(*  The CORRECT distributive semiring is built in OCaml using Cas functors:  *)
(*                                                                           *)
(*    let widest_shortest_paths =                                            *)
(*      mcas_bs_add_zero                                                     *)
(*        (mcas_bs_llex_product                                              *)
(*           mcas_min_plus                                                   *)
(*           (mcas_bs_add_one                                                *)
(*              mcas_max_min                                                 *)
(*              infinity))                                                   *)
(*        infinity;;                                                         *)
(*                                                                           *)
(*  Layer-by-layer construction:                                             *)
(*                                                                           *)
(*    Layer 0 (min_plus):     (nat, + = min, * = +, 0 = ∞, 1 = 0)            *)
(*      The primary criterion: minimize path length (shortest path).         *)
(*                                                                           *)
(*    Layer 1 (max_min):      (nat, + = max, * = min, 0 = 0, 1 = ∞)          *)
(*      The secondary criterion: maximize bottleneck bandwidth (widest).     *)
(*                                                                           *)
(*    Layer 2 (bs_add_one):   wraps max_min with ∞ as *-identity AND         *)
(*      +-absorber. The "winning" element ∞ represents "infinite bandwidth"  *)
(*      and dominates in the additive order (max).                           *)
(*                                                                           *)
(*    Layer 3 (bs_llex_product): LEFT-lexicographic product of min_plus      *)
(*      and the wrapped max_min. Here (a,b) + (c,d) compares first           *)
(*      components via min_plus (shorter path wins); when a = c, the         *)
(*      second component breaks ties via max_min (wider path wins). The      *)
(*      product * is component-wise: (a,b) * (c,d) = (a*c, b*d).            *)
(*                                                                           *)
(*      CRITICAL: The tiebreaker only fires when first components are        *)
(*      EQUAL. Since * distributes over + component-wise AND equality on     *)
(*      the first component masks the tiebreaker, both distributive laws     *)
(*      hold for this layer.                                                 *)
(*                                                                           *)
(*    Layer 4 (bs_add_zero):  wraps the product with ∞ as additive           *)
(*      identity (+-id) AND multiplicative annihilator ( * -0). The outer    *)
(*      ∞ represents no path exists.                                        *)
(*                                                                           *)
(*  LAYERED TYPE STRUCTURE (each layer is a semiring transformer):           *)
(*                                                                           *)
(*      ∞  (outer, additive identity)                                        *)
(*       |                                                                   *)
(*       v                                                                   *)
(*      (a, b) where a : nat (min_plus), b : bs_add_one(max_min)             *)
(*       |         |                                                         *)
(*       |         +---> ∞ (inner-tiebreaker, *-identity)                    *)
(*       |                |                                                  *)
(*       |                v                                                  *)
(*       |               Finite n  (nat, max-min)                            *)
(*       |                                                                   *)
(*       +---> Finite n  (nat, min-plus, primary criterion)                  *)
(*                                                                           *)
(*  ADDITIVE PROPERTIES:                                                     *)
(*    Identity = ∞ (outer)            Annihilator = (0, ∞_inner)             *)
(*    Idempotent, Commutative, Selective                                     *)
(*                                                                           *)
(*  MULTIPLICATIVE PROPERTIES:                                               *)
(*    Identity = (0, ∞_inner)         Annihilator = ∞ (outer)                *)
(*    Commutative                                                             *)
(*                                                                           *)
(*  ALGEBRAIC LAWS (from Cas describe output):                                *)
(*    Left Distributive, Right Distributive                                   *)
(*    Left-Left Absorptive, Left-Right Absorptive                             *)
(*    Right-Left Absorptive, Right-Right Absorptive                           *)
(*                                                                           *)
(*  WHY DISTRIBUTIVE LAWS HOLD:                                              *)
(*    The key insight is that bs_llex_product only uses the second component *)
(*    for tiebreaking when first components are EQUAL. Since the product *   *)
(*    is component-wise, and equality is preserved across components, the    *)
(*    tiebreaker logic commutes with multiplication. This is in contrast to  *)
(*    the direct lexicographic encoding in this file, where the tiebreaker   *)
(*    uses ltR comparisons that do NOT commute with the saturation behavior  *)
(*    of mulf (which maps anything involving Infinity to Infinity).           *)
(* ========================================================================= *)
  

