From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat. 
From HB Require Import structures.
From Semiring Require Import MatN
  SemimoduleN Structures OrderSemiring.
Import ListNotations SemiringNotations.


  (* Widest-shortest path: minimise the path length, and among equal       *)
  (* lengths maximise the bottleneck (minimal) width.                       *)
  (*                                                                        *)
  (* A naive direct encoding as an R x R pair (min-plus length, max-min    *)
  (* width) is NOT a semiring: the distributive laws fail when mulf        *)
  (* saturates the length to Infinity and the tiebreaker then compares the *)
  (* widths of two "no path" pairs, e.g. a = (Infinity, 5), b = (1, 3),    *)
  (* c = (2, 10) gives a*(b+c) = (Infinity, 3) but a*b + a*c = (Infinity, 5).*)
  (*                                                                        *)
  (* The CORRECT encoding below makes "no path" a single canonical element *)
  (* (NoneW) rather than a length-Infinity pair, so multiplying by a       *)
  (* no-path value yields NoneW regardless of widths and the distributive  *)
  (* laws hold: the tiebreaker only fires when the two lengths are equal,  *)
  (* and component-wise multiplication preserves that.                     *)

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

  (* Widest-shortest value: [NoneW] = no path; [SomeW l w] = a path of   *)
  (* length [l] (nat, minimise) and bottleneck width [w] (max-min, max.). *)
  Inductive WS := NoneW : WS | SomeW : nat -> R -> WS.
  Definition zeroWS : WS := NoneW.
  Definition oneWS : WS := SomeW 0 Infinity.

  (* [ws_le u v] : [u] is no better than [v].  Lexicographic: smaller    *)
  (* length is better; equal lengths are broken by larger width.          *)
  Definition ws_le (u v : WS) : bool :=
    match u, v with
    | NoneW, _ => true
    | SomeW _ _, NoneW => false
    | SomeW l1 w1, SomeW l2 w2 =>
        if Nat.ltb l1 l2 then false
        else if Nat.ltb l2 l1 then true
        else negb (ltR w2 w1)
    end.

  (* Lexicographic maximum: pick the better of the two, [NoneW] is worst. *)
  Definition plusWS (u v : WS) : WS := if ws_le v u then u else v.

  (* Component-wise product; [NoneW] is the multiplicative annihilator.   *)
  Definition mulWS (u v : WS) : WS :=
    match u, v with
    | NoneW, _ => NoneW
    | _, NoneW => NoneW
    | SomeW l1 w1, SomeW l2 w2 => SomeW (l1 + l2) (muls w1 w2)
    end.


  Definition finN : list Node := [A; B; C].

End Comp.


(* =================================================================== *)
(*  HB Instances: FinType Node, BoundedSemiring WS                       *)
(*                                                                       *)
(*  WS = NoneW | SomeW nat R — the widest-shortest semiring.             *)
(*  NoneW is "no path" (additive identity and multiplicative             *)
(*  annihilator).  SomeW l w is a path of length l (nat, minimise) and   *)
(*  width w (max-min, maximise).  plusWS is the lexicographic maximum    *)
(*  (shorter length first, then wider), mulWS is component-wise.         *)
(*  Making "no path" canonical (NoneW) is what makes the distributive    *)
(*  laws hold — they fail for the naive R × R encoding (see top).        *)
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

  (* ==================================================================== *)
  (*  Order theory for the width component R (Left nat | Infinity).        *)
  (*  [ltR] is a strict total order, [r_le a b] is "a <= b".              *)
  (* ==================================================================== *)

  Lemma ltR_irrefl : forall w, ltR w w = false.
  Proof. intros [n|]; cbn; [apply PeanoNat.Nat.ltb_irrefl | reflexivity]. Qed.

  Lemma eqR_refl : forall w, eqR w w = true.
  Proof. intros [n|]; cbn; [apply PeanoNat.Nat.eqb_refl | reflexivity]. Qed.

  Lemma eqR_eq : forall w1 w2, eqR w1 w2 = true -> w1 = w2.
  Proof. intros [n1|] [n2|] H; cbn in H; try discriminate; try reflexivity.
    apply PeanoNat.Nat.eqb_eq in H. subst. reflexivity. Qed.

  Lemma eqR_trans : forall w1 w2 w3, eqR w1 w2 = true -> eqR w2 w3 = true -> eqR w1 w3 = true.
  Proof. intros w1 w2 w3 H12 H23. apply eqR_eq in H12, H23. subst w2. rewrite H23. apply eqR_refl. Qed.

  Lemma ltR_total : forall w1 w2, ltR w1 w2 = true \/ ltR w2 w1 = true \/ eqR w1 w2 = true.
  Proof.
    intros [n1|] [n2|].
    - change (Nat.ltb n1 n2 = true \/ Nat.ltb n2 n1 = true \/ Nat.eqb n1 n2 = true).
      destruct (PeanoNat.Nat.ltb_spec n1 n2) as [Hlt|Hge].
      + left. reflexivity.
      + destruct (PeanoNat.Nat.eqb_spec n1 n2) as [Heq|Hne].
        * right; right. reflexivity.
        * right; left. apply PeanoNat.Nat.ltb_lt. lia.
    - left. reflexivity.
    - right; left. reflexivity.
    - right; right. reflexivity.
  Qed.

  Lemma ltR_trans : forall w1 w2 w3, ltR w1 w2 = true -> ltR w2 w3 = true -> ltR w1 w3 = true.
  Proof.
    intros [n1|] [n2|] [n3|] H12 H23.
    - apply PeanoNat.Nat.ltb_lt in H12, H23. apply PeanoNat.Nat.ltb_lt. nia.
    - reflexivity.
    - discriminate.
    - reflexivity.
    - discriminate.
    - discriminate.
    - discriminate.
    - discriminate.
  Qed.

  Definition r_le (a b : R) : bool := negb (ltR b a).

  Lemma r_le_refl : forall w, r_le w w = true.
  Proof. intros w. unfold r_le. rewrite ltR_irrefl. reflexivity. Qed.

  Lemma r_le_top : forall w, r_le w Infinity = true.
  Proof. intros [n|]; unfold r_le; cbn; reflexivity. Qed.

  Lemma r_le_lt_or_eq : forall a b, r_le a b = true -> (ltR a b = true) \/ (eqR a b = true).
  Proof.
    intros a b H. unfold r_le in H.
    destruct (ltR b a) eqn:E; cbn in H; [discriminate |].
    destruct (ltR_total a b) as [Hab | [Hba | Hab']].
    - left. exact Hab.
    - exfalso. rewrite Hba in E. discriminate.
    - right. exact Hab'.
  Qed.

  Lemma lt_or_eq_r_le : forall a b, (ltR a b = true) \/ (eqR a b = true) -> r_le a b = true.
  Proof.
    intros a b [Hab | Hab].
    - unfold r_le. destruct (ltR b a) eqn:E; [| reflexivity].
      exfalso. assert (Hbb : ltR b b = true) by (apply (ltR_trans _ _ _ E Hab)).
      rewrite ltR_irrefl in Hbb. discriminate.
    - unfold r_le. apply eqR_eq in Hab. subst b. rewrite ltR_irrefl. reflexivity.
  Qed.

  Lemma r_le_trans : forall w1 w2 w3, r_le w1 w2 = true -> r_le w2 w3 = true -> r_le w1 w3 = true.
  Proof.
    intros w1 w2 w3 H12 H23.
    apply r_le_lt_or_eq in H12. apply r_le_lt_or_eq in H23.
    apply lt_or_eq_r_le.
    destruct H12 as [H12 | H12]; destruct H23 as [H23 | H23].
    - left. apply (ltR_trans _ _ _ H12 H23).
    - left. apply eqR_eq in H23. subst w3. exact H12.
    - left. apply eqR_eq in H12. subst w2. exact H23.
    - right. apply (eqR_trans w1 w2 w3); assumption.
  Qed.

  Lemma r_le_antisym : forall a b, r_le a b = true -> r_le b a = true -> a = b.
  Proof.
    intros a b Hab Hba.
    apply r_le_lt_or_eq in Hab. apply r_le_lt_or_eq in Hba.
    destruct Hab as [Hab | Hab]; destruct Hba as [Hba | Hba].
    - exfalso. assert (Haa : ltR a a = true) by (apply (ltR_trans _ _ _ Hab Hba)).
      rewrite ltR_irrefl in Haa. discriminate.
    - apply eqR_eq in Hba. exact (eq_sym Hba).
    - apply eqR_eq in Hab. exact Hab.
    - apply eqR_eq in Hab. exact Hab.
  Qed.

  (* ==================================================================== *)
  (*  Order theory for WS.  [ws_le u v] is a total order (with [NoneW]    *)
  (*  the least element), and [plusWS] is its maximum.                    *)
  (* ==================================================================== *)

  Lemma ws_le_unfold (l1 l2 : nat) (w1 w2 : R) :
    ws_le (SomeW l1 w1) (SomeW l2 w2) =
    if Nat.ltb l1 l2 then false
    else if Nat.ltb l2 l1 then true
    else r_le w1 w2.
  Proof. reflexivity. Qed.

  Lemma ws_le_refl : forall u, ws_le u u = true.
  Proof.
    intros [|l w]; [reflexivity |].
    rewrite ws_le_unfold. rewrite PeanoNat.Nat.ltb_irrefl. apply r_le_refl.
  Qed.

  Lemma ws_le_length (l1 l2 : nat) (w1 w2 : R) :
    ws_le (SomeW l1 w1) (SomeW l2 w2) = true -> l2 <= l1.
  Proof.
    rewrite ws_le_unfold. intro H.
    destruct (PeanoNat.Nat.ltb l1 l2) eqn:E1.
    - apply PeanoNat.Nat.ltb_lt in E1. cbn in H. discriminate.
    - destruct (PeanoNat.Nat.ltb l2 l1) eqn:E2.
      + apply PeanoNat.Nat.ltb_lt in E2. lia.
      + apply (PeanoNat.Nat.ltb_ge l1 l2). exact E1.
  Qed.

  Lemma ws_le_width (l1 l2 : nat) (w1 w2 : R) :
    ws_le (SomeW l1 w1) (SomeW l2 w2) = true -> l1 = l2 -> r_le w1 w2 = true.
  Proof.
    rewrite ws_le_unfold. intros H Hl. subst l2.
    destruct (PeanoNat.Nat.ltb l1 l1) eqn:E1; [apply PeanoNat.Nat.ltb_lt in E1; lia |].
    destruct (PeanoNat.Nat.ltb l1 l1) eqn:E2; [apply PeanoNat.Nat.ltb_lt in E2; lia |].
    cbn in H. exact H.
  Qed.

  Lemma ws_le_intro (l1 l2 : nat) (w1 w2 : R) :
    l2 <= l1 -> (l1 = l2 -> r_le w1 w2 = true) -> ws_le (SomeW l1 w1) (SomeW l2 w2) = true.
  Proof.
    intros Hge Hw. rewrite ws_le_unfold.
    destruct (PeanoNat.Nat.ltb l1 l2) eqn:E1.
    - apply PeanoNat.Nat.ltb_lt in E1. exfalso. lia.
    - destruct (PeanoNat.Nat.ltb l2 l1) eqn:E2.
      + apply PeanoNat.Nat.ltb_lt in E2. cbn. reflexivity.
      + apply PeanoNat.Nat.ltb_ge in E1, E2.
        assert (Hl : l1 = l2) by lia. subst l2. cbn.
        apply Hw. reflexivity.
  Qed.

  Lemma ws_le_total : forall u v, ws_le u v = true \/ ws_le v u = true.
  Proof.
    intros [|l1 w1] [|l2 w2];
    [ left; reflexivity
    | left; reflexivity
    | right; reflexivity
    | rewrite !ws_le_unfold;
      destruct (PeanoNat.Nat.ltb_spec l1 l2) as [Hlt12 | Hge21];
      [ (* l1 < l2: [u] strictly better, so [v <= u] *)
        right;
        assert (Hb' : Nat.ltb l2 l1 = false) by (apply PeanoNat.Nat.ltb_ge; lia);
        rewrite Hb'; cbn; reflexivity
      | destruct (PeanoNat.Nat.ltb_spec l2 l1) as [Hlt21 | Hge12];
        [ (* l2 < l1: [v] strictly better, so [u <= v] *)
          left; cbn; reflexivity
        | (* l1 = l2: the width decides *)
          destruct (ltR_total w1 w2) as [Hw12 | [Hw21 | Hw12']];
          [ (* w1 < w2: [u] narrower, so [u <= v] *)
            left; cbn; apply lt_or_eq_r_le; left; exact Hw12
          | (* w2 < w1: [v] narrower, so [v <= u] *)
            right; cbn; apply lt_or_eq_r_le; left; exact Hw21
          | (* w1 = w2: equal, both hold *)
            left; cbn; apply lt_or_eq_r_le; right; exact Hw12' ] ] ] ].
  Qed.

  Lemma ws_le_antisym : forall u v, ws_le u v = true -> ws_le v u = true -> u = v.
  Proof.
    intros [|l1 w1] [|l2 w2] Huv Hvu.
    - reflexivity.
    - cbn in Hvu. discriminate.
    - cbn in Huv. discriminate.
    - rewrite ws_le_unfold in Huv, Hvu.
      destruct (PeanoNat.Nat.ltb l1 l2) eqn:E1;
      destruct (PeanoNat.Nat.ltb l2 l1) eqn:E2; cbn in Huv, Hvu.
      + apply PeanoNat.Nat.ltb_lt in E1, E2. lia.
      + discriminate.
      + discriminate.
      + apply PeanoNat.Nat.ltb_ge in E1, E2.
        assert (Hl : l1 = l2) by lia. subst l2.
        assert (Hw : w1 = w2) by (apply r_le_antisym; assumption). subst w2. reflexivity.
  Qed.

  Lemma ws_le_trans : forall u v w, ws_le u v = true -> ws_le v w = true -> ws_le u w = true.
  Proof.
    intros [|l1 w1] [|l2 w2] [|l3 w3] Huv Hvw.
    - reflexivity.
    - reflexivity.
    - discriminate.
    - reflexivity.
    - discriminate.
    - discriminate.
    - discriminate.
    - apply ws_le_length in Huv as H21.
      apply ws_le_length in Hvw as H32.
      rewrite ws_le_unfold.
      destruct (PeanoNat.Nat.ltb l1 l3) eqn:E13.
      + apply PeanoNat.Nat.ltb_lt in E13. exfalso. lia.
      + destruct (PeanoNat.Nat.ltb l3 l1) eqn:E31.
        * apply PeanoNat.Nat.ltb_lt in E31. cbn. reflexivity.
        * apply PeanoNat.Nat.ltb_ge in E13, E31.
          assert (H13 : l1 = l3) by lia. subst l3.
          assert (H12 : l1 = l2) by lia.
          assert (Hr1 : r_le w1 w2 = true) by (apply (ws_le_width l1 l2 w1 w2); [exact Huv | exact H12]).
          assert (Hr2 : r_le w2 w3 = true)
            by (apply (ws_le_width l2 l1 w2 w3); [exact Hvw | exact (eq_sym H12)]).
          apply r_le_trans with (w2 := w2); assumption.
  Qed.

  (* [plusWS] is literally [add_max ws_le], so the additive commutative     *)
  (* monoid comes from OrderSemiring: nothing about WS is involved beyond   *)
  (* [ws_le] being a total order.                                           *)

  Lemma addA_proof : forall x y z : WS, plusWS (plusWS x y) z = plusWS x (plusWS y z).
  Proof. exact (add_max_assoc ws_le ws_le_trans ws_le_antisym ws_le_total). Qed.

  Lemma addC_proof : forall x y : WS, plusWS x y = plusWS y x.
  Proof. exact (add_max_comm ws_le ws_le_antisym ws_le_total). Qed.

  Lemma add0r_proof : forall x : WS, plusWS zeroWS x = x.
  Proof. intros x. destruct x; unfold plusWS, zeroWS; cbn; reflexivity. Qed.

  Lemma addr0_proof : forall x : WS, plusWS x zeroWS = x.
  Proof. intros x. unfold plusWS, zeroWS. cbn. reflexivity. Qed.

  HB.instance Definition _ := IsCommutativeMonoid.Build WS
    zeroWS plusWS addA_proof addC_proof add0r_proof addr0_proof.

  (** [min] is associative and monotone on the width order. *)
  Lemma muls_assoc : forall a b c, muls (muls a b) c = muls a (muls b c).
  Proof.
    intros [a|] [b|] [c|]; cbn; try reflexivity.
    f_equal. symmetry. apply PeanoNat.Nat.min_assoc.
  Qed.

  Lemma muls_le_r : forall a b c, r_le b c = true -> r_le (muls a b) (muls a c) = true.
  Proof.
    intros [a|] [b|] [c|] H.
    - (* Left a, Left b, Left c *)
      unfold r_le in H. change (negb (Nat.ltb c b) = true) in H.
      destruct (PeanoNat.Nat.ltb c b) eqn:E; cbn in H; [discriminate |].
      apply PeanoNat.Nat.ltb_ge in E.            (* E : b <= c *)
      unfold r_le. change (negb (Nat.ltb (Nat.min a c) (Nat.min a b)) = true).
      destruct (PeanoNat.Nat.ltb (Nat.min a c) (Nat.min a b)) eqn:E2;
        [ apply PeanoNat.Nat.ltb_lt in E2; exfalso;
          assert (H1 : Nat.min a b <= a) by apply PeanoNat.Nat.le_min_l;
          assert (H2 : Nat.min a b <= c)
            by (apply PeanoNat.Nat.le_trans with b; [apply PeanoNat.Nat.le_min_r | exact E]);
          assert (Hm : Nat.min a b <= Nat.min a c)
            by (apply (PeanoNat.Nat.min_glb a c (Nat.min a b)); [exact H1 | exact H2]);
          lia
        | reflexivity ].
    - (* Left a, Left b, Infinity *)
      unfold r_le. change (negb (Nat.ltb a (Nat.min a b)) = true).
      destruct (PeanoNat.Nat.ltb a (Nat.min a b)) eqn:E;
        [ apply PeanoNat.Nat.ltb_lt in E; exfalso;
          assert (H1 : Nat.min a b <= a) by apply PeanoNat.Nat.le_min_l; lia
        | reflexivity ].
    - unfold r_le in H. cbn in H. discriminate.
    - unfold r_le. change (negb (Nat.ltb a a) = true).
      rewrite PeanoNat.Nat.ltb_irrefl. reflexivity.
    - cbn. exact H.
    - cbn. exact H.
    - cbn in H. discriminate.
    - cbn. exact H.
  Qed.

  Lemma muls_le_l : forall a b c, r_le a b = true -> r_le (muls a c) (muls b c) = true.
  Proof.
    intros [a|] [b|] [c|] H.
    - (* Left a, Left b, Left c *)
      unfold r_le in H. change (negb (Nat.ltb b a) = true) in H.
      destruct (PeanoNat.Nat.ltb b a) eqn:E; cbn in H; [discriminate |].
      apply PeanoNat.Nat.ltb_ge in E.            (* E : a <= b *)
      unfold r_le. change (negb (Nat.ltb (Nat.min b c) (Nat.min a c)) = true).
      destruct (PeanoNat.Nat.ltb (Nat.min b c) (Nat.min a c)) eqn:E2;
        [ apply PeanoNat.Nat.ltb_lt in E2; exfalso;
          assert (H1 : Nat.min a c <= c) by apply PeanoNat.Nat.le_min_r;
          assert (H2 : Nat.min a c <= b)
            by (apply PeanoNat.Nat.le_trans with a; [apply PeanoNat.Nat.le_min_l | exact E]);
          assert (Hm : Nat.min a c <= Nat.min b c)
            by (apply (PeanoNat.Nat.min_glb b c (Nat.min a c)); [exact H2 | exact H1]);
          lia
        | reflexivity ].
    - (* Left a, Left b, Infinity *)
      cbn. exact H.
    - (* Left a, Infinity, Left c *)
      unfold r_le. change (negb (Nat.ltb c (Nat.min a c)) = true).
      destruct (PeanoNat.Nat.ltb c (Nat.min a c)) eqn:E;
        [ apply PeanoNat.Nat.ltb_lt in E; exfalso;
          assert (H1 : Nat.min a c <= c) by apply PeanoNat.Nat.le_min_r; lia
        | reflexivity ].
    - (* Left a, Infinity, Infinity *)
      cbn. exact H.
    - unfold r_le in H. cbn in H. discriminate.
    - unfold r_le in H. cbn in H. discriminate.
    - cbn. apply r_le_refl.
    - cbn. reflexivity.
  Qed.

  (** [mulWS] is monotone in the [ws_le] order (both arguments). *)
  Lemma mulWS_mono_r : forall a b c, ws_le b c = true -> ws_le (mulWS a b) (mulWS a c) = true.
  Proof.
    intros [|la wa] [|lb wb] [|lc wc] Hbc.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn. discriminate.
    - apply ws_le_intro.
      + apply ws_le_length in Hbc. lia.
      + intro Heq.
        assert (Hl : lb = lc) by nia.
        assert (Hw : r_le wb wc = true)
          by (apply (ws_le_width lb lc wb wc); [exact Hbc | exact Hl]).
        apply (muls_le_r wa wb wc). exact Hw.
  Qed.

  Lemma mulWS_mono_l : forall a b c, ws_le a b = true -> ws_le (mulWS a c) (mulWS b c) = true.
  Proof.
    intros [|la wa] [|lb wb] [|lc wc] Hab.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn. discriminate.
    - reflexivity.
    - apply ws_le_intro.
      + apply ws_le_length in Hab. lia.
      + intro Heq.
        assert (Hl : la = lb) by nia.
        assert (Hw : r_le wa wb = true)
          by (apply (ws_le_width la lb wa wb); [exact Hab | exact Hl]).
        apply (muls_le_l wa wb wc). exact Hw.
  Qed.

  Lemma mulA_proof : forall a b c : WS, mulWS (mulWS a b) c = mulWS a (mulWS b c).
  Proof.
    intros [|l1 w1] [|l2 w2] [|l3 w3]; cbn; try reflexivity.
    f_equal; [lia | apply muls_assoc].
  Qed.

  Lemma mul1r_proof : forall a : WS, mulWS oneWS a = a.
  Proof.
    intros [|l w].
    - reflexivity.
    - change (SomeW (0 + l) (muls Infinity w) = SomeW l w).
      f_equal; destruct w; reflexivity.
  Qed.

  Lemma mulr1_proof : forall a : WS, mulWS a oneWS = a.
  Proof.
    intros [|l [w|]].
    - reflexivity.
    - change (SomeW (l + 0) (muls (Left w) Infinity) = SomeW l (Left w)).
      f_equal; lia.
    - change (SomeW (l + 0) (muls Infinity Infinity) = SomeW l Infinity).
      f_equal; lia.
  Qed.

  Lemma mul0r_proof : forall a : WS, mulWS zeroWS a = zeroWS.
  Proof. intros a. unfold zeroWS. destruct a; cbn; reflexivity. Qed.

  Lemma mulr0_proof : forall a : WS, mulWS a zeroWS = zeroWS.
  Proof. intros a. unfold zeroWS. destruct a; cbn; reflexivity. Qed.

  (** [plusWS X Y] is the maximum of [X] and [Y] under [ws_le]. *) 
  (* Both distributive laws follow from monotonicity of [mulWS] alone.  This *)
  (* is the one obligation OrderSemiring leaves: the naive R×R encoding      *)
  (* rejected at the top of this file is exactly a failure of monotonicity.  *)

  Lemma mulDl_proof : forall a b c : WS, mulWS a (plusWS b c) = plusWS (mulWS a b) (mulWS a c).
  Proof.
    exact (mul_add_max_distr_l ws_le ws_le_antisym ws_le_total mulWS mulWS_mono_r).
  Qed.

  Lemma mulDr_proof : forall a b c : WS, mulWS (plusWS a b) c = plusWS (mulWS a c) (mulWS b c).
  Proof.
    exact (mul_add_max_distr_r ws_le ws_le_antisym ws_le_total mulWS mulWS_mono_l).
  Qed.

  HB.instance Definition _ := IsSemiring.Build WS
    oneWS mulWS mulA_proof mul1r_proof mulr1_proof
    mulDr_proof mulDl_proof mul0r_proof mulr0_proof.

  (** [oneWS] (length 0, width ∞) is the greatest element of the order. *)
  Lemma ws_le_top : forall a : WS, ws_le a oneWS = true.
  Proof.
    intros [|l w]; unfold oneWS; [reflexivity |].
    rewrite ws_le_unfold.
    destruct (PeanoNat.Nat.ltb l 0) eqn:E1.
    - apply PeanoNat.Nat.ltb_lt in E1. lia.
    - destruct (PeanoNat.Nat.ltb 0 l) eqn:E2; [reflexivity | apply r_le_top].
  Qed.

  (** Bounded: the greatest element absorbs. *)
  Lemma add_bound_proof : forall a : WS, plusWS oneWS a = oneWS.
  Proof. exact (add_max_top_l ws_le oneWS ws_le_top). Qed.

  HB.instance Definition _ := IsBoundedSemiring.Build WS add_bound_proof.

  HB.instance Definition _ := IsSemimodule.Build WS WS
    mulWS mulDl_proof mulDr_proof
    (fun a b x => eq_sym (mulA_proof a b x))
    mul1r_proof mul0r_proof mulr0_proof.

End HBInstances.

Definition widestshortestpath (m : Node -> Node -> WS) : Node -> Node -> WS :=
  powN_fun m 2%N.

Definition mva_eff_fun (m : Node -> Node -> WS) (v : Node -> WS) : Node -> WS :=
  SemimoduleN.matrix_vector_action_eff_fun m v.

Definition mva_func (m : Node -> Node -> WS) (v : Node -> WS) : Node -> WS :=
  SemimoduleN.matrix_vector_action m v.

(* ========================================================================= *)
(*  WIDEST-SHORTEST PATH SEMIRING (this file)                                *)
(*                                                                           *)
(*  This file defines the widest-shortest-path semiring DIRECTLY in Rocq,    *)
(*  as the layered CAS construction collapsed into one concrete type:        *)
(*                                                                           *)
(*      WS  :=  NoneW | SomeW l w        (l : nat, w : R)                    *)
(*      R   :=  Left n | Infinity        (max-min widths + inner ∞)          *)
(*                                                                           *)
(*  The mapping to the CAS layered construction (the OCaml functors          *)
(*  sketched in the NOTE at the top of the file) is:                         *)
(*                                                                           *)
(*    NoneW  = outer ∞ (mcas_bs_add_zero ... infinity): the additive         *)
(*             identity AND multiplicative annihilator — "no path exists".   *)
(*    SomeW l w = the pair (l, w) of mcas_bs_llex_product:                   *)
(*             l : nat is the min-plus path length (mcas_min_plus),          *)
(*             w : R   is the wrapped max-min bottleneck width               *)
(*                     (mcas_bs_add_one mcas_max_min infinity).              *)
(*                                                                           *)
(*  Operations:                                                              *)
(*    zeroWS = NoneW ;  oneWS = SomeW 0 Infinity                             *)
(*    ws_le u v : lexicographic order — a smaller length wins; equal         *)
(*      lengths are broken by the LARGER width.  The width tiebreaker only   *)
(*      ever compares paths of the SAME length.                              *)
(*    plusWS u v : the maximum of u and v under ws_le (selective join).      *)
(*    mulWS (SomeW l1 w1) (SomeW l2 w2) = SomeW (l1 + l2) (muls w1 w2),      *)
(*      component-wise (lengths add under min-plus; widths meet via          *)
(*      muls = min under max-min); NoneW absorbs on either side.             *)
(*                                                                           *)
(*  WHY THE DISTRIBUTIVE LAWS HOLD:                                          *)
(*    The tiebreaker only fires when the two lengths are EQUAL, and          *)
(*    multiplication is component-wise: lengths add and widths are combined  *)
(*    with muls, so multiplying by a fixed path maps equal-length pairs to   *)
(*    equal-length pairs.  Hence the lexicographic comparison commutes with  *)
(*    multiplication and both distributive laws hold.  This is exactly the   *)
(*    CAS insight for bs_llex_product.  The canonical NoneW removes the      *)
(*    failure mode of the naive R×R pair described in the NOTE at the top:   *)
(*    there, the tiebreaker compared the widths of two length-Infinity       *)
(*    "no path" pairs and distributivity broke.                              *)
(*                                                                           *)
(*  PROOFS (no admitted goals):                                              *)
(*    Commutative monoid: addA_proof addC_proof add0r_proof addr0_proof      *)
(*    Semiring:           mulA_proof mul1r_proof mulr1_proof                 *)
(*                        mulDr_proof mulDl_proof mul0r_proof mulr0_proof    *)
(*    Bounded:            add_bound_proof   (oneWS + a = oneWS)              *)
(*    Semimodule:         IsSemimodule instance of WS acting on itself.      *)
(*                                                                           *)
(*    [plusWS] is [add_max ws_le], so associativity, commutativity, both     *)
(*    distributive laws and boundedness are discharged by the generic        *)
(*    results in algorithm/OrderSemiring.v.  What remains specific to WS is  *)
(*    the backbone those results consume: ws_le is a total order             *)
(*    (ws_le_total, ws_le_antisym, ws_le_trans, ws_le_top), multiplication   *)
(*    is monotone in it (mulWS_mono_r, mulWS_mono_l), and the scalar facts   *)
(*    muls_le_r, muls_le_l over the max-min width semiring R.  Monotonicity  *)
(*    is the whole content: it is exactly what the naive R×R encoding lacks. *)
(* ========================================================================= *)
  

