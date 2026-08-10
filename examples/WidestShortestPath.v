From Stdlib Require Import List BinNatDef
  Psatz Utf8 EqNat. 
From HB Require Import structures.
From Semiring Require Import MatN 
  SemimoduleN Structures.
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

  (** [plusWS x y] is the maximum of [x] and [y] under [ws_le]. *)
  Lemma ws_join_lub (x y : WS) : ws_le x (plusWS x y) = true.
  Proof.
    unfold plusWS. destruct (ws_le y x) eqn:E.
    - apply ws_le_refl.
    - destruct (ws_le_total x y) as [H | H']; [exact H | rewrite H' in E; discriminate].
  Qed.

  Lemma ws_join_lub2 (x y : WS) : ws_le y (plusWS x y) = true.
  Proof.
    unfold plusWS. destruct (ws_le y x) eqn:E; [exact E | apply ws_le_refl].
  Qed.

  Lemma ws_join_least (x y z : WS) : ws_le x z = true -> ws_le y z = true -> ws_le (plusWS x y) z = true.
  Proof.
    intros Hx Hy. unfold plusWS. destruct (ws_le y x) eqn:E; assumption.
  Qed.

  Lemma addA_proof : forall x y z : WS, plusWS (plusWS x y) z = plusWS x (plusWS y z).
  Proof.
    intros x y z. apply ws_le_antisym.
    - (* plusWS (plusWS x y) z <= plusWS x (plusWS y z)  =: d *)
      apply (ws_join_least (plusWS x y) z (plusWS x (plusWS y z))).
      + apply (ws_join_least x y (plusWS x (plusWS y z))).
        * apply ws_join_lub.
        * apply (ws_le_trans y (plusWS y z) (plusWS x (plusWS y z)));
          [apply ws_join_lub | apply ws_join_lub2].
      + apply (ws_le_trans z (plusWS y z) (plusWS x (plusWS y z)));
        [apply ws_join_lub2 | apply ws_join_lub2].
    - (* plusWS x (plusWS y z) <= plusWS (plusWS x y) z  =: c *)
      apply (ws_join_least x (plusWS y z) (plusWS (plusWS x y) z)).
      + apply (ws_le_trans x (plusWS x y) (plusWS (plusWS x y) z));
        [apply ws_join_lub | apply (ws_join_lub (plusWS x y) z)].
      + apply (ws_join_least y z (plusWS (plusWS x y) z)).
        * apply (ws_le_trans y (plusWS x y) (plusWS (plusWS x y) z));
          [apply ws_join_lub2 | apply (ws_join_lub (plusWS x y) z)].
        * apply (ws_join_lub2 (plusWS x y) z).
  Qed.

  Lemma addC_proof : forall x y : WS, plusWS x y = plusWS y x.
  Proof. intros x y. apply ws_le_antisym.
    - apply ws_join_least; [apply ws_join_lub2 | apply ws_join_lub].
    - apply ws_join_least; [apply ws_join_lub2 | apply ws_join_lub].
  Qed.

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
  Lemma plusWS_ge : forall X Y : WS, ws_le X Y = true -> plusWS X Y = Y.
  Proof.
    intros X Y H. unfold plusWS. destruct (ws_le Y X) eqn:E2.
    - apply ws_le_antisym; assumption.
    - reflexivity.
  Qed.

  Lemma plusWS_ge_l : forall X Y : WS, ws_le Y X = true -> plusWS X Y = X.
  Proof.
    intros X Y H. unfold plusWS. destruct (ws_le Y X) eqn:E2.
    - reflexivity.
    - rewrite H in E2. discriminate.
  Qed.

  Lemma mulDl_proof : forall a b c : WS, mulWS a (plusWS b c) = plusWS (mulWS a b) (mulWS a c).
  Proof.
    intros a b c.
    destruct (ws_le_total b c) as [Hbc | Hcb].
    - (* ws_le b c = true : plusWS b c = c, and a*b <= a*c *)
      assert (Hmono : ws_le (mulWS a b) (mulWS a c) = true)
        by (apply mulWS_mono_r; exact Hbc).
      rewrite (plusWS_ge b c Hbc).
      rewrite (plusWS_ge (mulWS a b) (mulWS a c) Hmono).
      reflexivity.
    - (* ws_le c b = true : plusWS b c = b, and a*c <= a*b *)
      assert (Hmono : ws_le (mulWS a c) (mulWS a b) = true)
        by (apply mulWS_mono_r; exact Hcb).
      rewrite (plusWS_ge_l b c Hcb).
      rewrite (plusWS_ge_l (mulWS a b) (mulWS a c) Hmono).
      reflexivity.
  Qed.

  Lemma mulDr_proof : forall a b c : WS, mulWS (plusWS a b) c = plusWS (mulWS a c) (mulWS b c).
  Proof.
    intros a b c.
    destruct (ws_le_total a b) as [Hab | Hba].
    - (* ws_le a b = true : plusWS a b = b, and a*c <= b*c *)
      assert (Hmono : ws_le (mulWS a c) (mulWS b c) = true)
        by (apply mulWS_mono_l; exact Hab).
      rewrite (plusWS_ge a b Hab).
      rewrite (plusWS_ge (mulWS a c) (mulWS b c) Hmono).
      reflexivity.
    - (* ws_le b a = true : plusWS a b = a, and b*c <= a*c *)
      assert (Hmono : ws_le (mulWS b c) (mulWS a c) = true)
        by (apply mulWS_mono_l; exact Hba).
      rewrite (plusWS_ge_l a b Hba).
      rewrite (plusWS_ge_l (mulWS a c) (mulWS b c) Hmono).
      reflexivity.
  Qed.

  HB.instance Definition _ := IsSemiring.Build WS
    oneWS mulWS mulA_proof mul1r_proof mulr1_proof
    mulDr_proof mulDl_proof mul0r_proof mulr0_proof.

  (** Bounded: [1] (length 0, width ∞) is the top of the order. *)
  Lemma add_bound_proof : forall a : WS, plusWS oneWS a = oneWS.
  Proof.
    intros [|l w]; unfold plusWS, oneWS.
    - cbn. reflexivity.
    - change ((if ws_le (SomeW l w) (SomeW 0 Infinity) then SomeW 0 Infinity else SomeW l w)
              = SomeW 0 Infinity).
      rewrite ws_le_unfold.
      destruct (PeanoNat.Nat.ltb l 0) eqn:E1.
      + apply PeanoNat.Nat.ltb_lt in E1. lia.
      + destruct (PeanoNat.Nat.ltb 0 l) eqn:E2.
        * apply PeanoNat.Nat.ltb_lt in E2. cbn. reflexivity.
        * apply PeanoNat.Nat.ltb_ge in E2. assert (Hl : l = 0%nat) by lia. subst l.
          change ((if r_le w Infinity then SomeW 0 Infinity else SomeW 0 w) = SomeW 0 Infinity).
          rewrite r_le_top. reflexivity.
  Qed.

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
  

