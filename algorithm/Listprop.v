(* This file contains list proofs which is not in the 
   coq/eqv/list.v
*)
From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory coq.sg.properties
  coq.eqv.list.
Import ListNotations.


Section Listsingledefs.

  Variables
    (A : Type)
    (eqA : brel A).

  
  Definition list_eqv (l₁ l₂ : list A) : bool := 
    brel_list eqA l₁ l₂.
  
  
  Fixpoint no_dup (l : list A) : bool :=
    match l with
    | [] => true
    | h :: t => negb (in_list eqA t h) &&
      no_dup t
    end.
    
  (* c covers l, i.e., every element of l appears in c *)
  Definition covers (c l : list A) : Prop :=
    forall x, 
    in_list eqA l x = true ->  
    in_list eqA c x = true.

  Fixpoint enum_list_inc (n : nat) : list nat :=
    match n with
    | O => [O]
    | S n' => enum_list_inc n' ++ [n]
    end.

  Fixpoint enum_list_dec (n : nat) : list nat :=
    match n with
    | O => [O]
    | S n' => n :: enum_list_dec n' 
    end.
 
End Listsingledefs.

Section Listsingleprops.
  
  Variables
    (A : Type)
    (eqA : brel A)
    (refA : brel_reflexive A eqA)
    (symA : brel_symmetric A eqA)
    (trnA : brel_transitive A eqA).
  

  Lemma list_eqv_refl : 
    forall l : list A, 
    list_eqv _ eqA l l = true.
  Proof.
    induction l.
    + simpl; reflexivity.
    + simpl. 
      apply Bool.andb_true_iff.
      split; 
      [apply refA |  
       apply IHl].
  Qed.

  

  Lemma list_eqv_sym : 
    forall l₁ l₂ : list A, 
    list_eqv _ eqA l₁ l₂ = true -> 
    list_eqv _ eqA l₂ l₁ = true.
  Proof.
    induction l₁; simpl.
    + intros ? Hl. 
      destruct l₂.
      reflexivity. 
      inversion Hl.
    + intros ? Hl. 
      destruct l₂.
      inversion Hl.
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Ha Hb].
      simpl. 
      apply Bool.andb_true_iff.
      split; 
      [apply symA; exact Ha |
       apply IHl₁; exact Hb ].
  Qed.



  Lemma list_eqv_trans : 
    forall l₁ l₂ l₃ : list A, 
    list_eqv _ eqA l₁ l₂ = true -> 
    list_eqv _ eqA l₂ l₃ = true ->
    list_eqv _ eqA l₁ l₃ = true.
  Proof.
    induction l₁ as [|a l₁];
    destruct l₂ as [|b l₂];
    destruct l₃ as [|c l₃];
    intros Ha Hb; simpl in Ha, 
    Hb; try congruence; 
    try reflexivity.
    simpl.
    apply Bool.andb_true_iff in Ha, Hb.
    apply Bool.andb_true_iff; split.
    apply trnA with b; firstorder.
    eapply IHl₁ with l₂; firstorder.
  Qed.



  Lemma list_mem_not : 
    forall (l : list A) (c a : A), 
    eqA c a = true ->
    in_list eqA l a = false -> 
    in_list eqA l c = false.
  Proof.
    induction l; 
    simpl; 
    intros ? ? Heq Hf.
    + reflexivity.
    + apply Bool.orb_false_iff in Hf.
      destruct Hf as [Hfa Hfb].
      apply Bool.orb_false_iff.
      split.
      case_eq (eqA c a); 
      intro Hf; auto.
      apply symA in Hf.
      assert (Ht := trnA a c a0 Hf Heq).
      apply symA in Ht. 
      rewrite Hfa in Ht.
      inversion Ht.
      apply IHl with (a := a0).
      exact Heq. 
      exact Hfb.
  Qed.

  Lemma enum_list_inc_dec_rev : 
    forall n : nat,
    enum_list_inc n = List.rev (enum_list_dec n).
  Proof.
    induction n.
    + simpl.
      reflexivity.
    + simpl;
      rewrite IHn; 
      reflexivity.
  Qed.

  
  Lemma enum_list_dec_inc_rev : 
    forall n : nat,
    enum_list_dec n = List.rev (enum_list_inc n).
  Proof.
    induction n. 
    + simpl.
      reflexivity.
    + simpl.
      rewrite rev_app_distr;
      simpl;
      rewrite IHn; 
      reflexivity.
  Qed.

  
  

  Lemma list_mem_true_false : 
    forall (l : list A) (a c : A),
    in_list eqA l a = false -> 
    in_list eqA l c = true -> 
    eqA c a = false.
  Proof.
    induction l; 
    simpl; 
    intros ? ? Ha Hb.
    + inversion Hb.
    + apply Bool.orb_false_iff in Ha.
      apply Bool.orb_true_iff in Hb.
      destruct Ha as [Ha₁ Ha₂].
      destruct Hb as [Hb | Hb].
      apply symA in Hb.

      case_eq (eqA c a0); intros Hf; auto.
      pose proof (trnA _ _ _ Hb Hf) as Ht.
      apply symA in Ht. 
      rewrite Ha₁ in Ht.
      inversion Ht.
      apply IHl; assumption.
  Qed.



  Lemma list_split : 
    forall (l : list A) (c : A),
    l <> [] -> in_list eqA l c = true -> 
    no_dup _ eqA l = true -> exists l₁ l₂ : list A, 
    list_eqv _ eqA l (l₁ ++ [c] ++ l₂) = true /\ 
    in_list eqA l₁ c = false /\ 
    in_list eqA l₂ c = false.
  Proof.
    induction l; simpl.
    + intros ? H₁ H₂ H₃.
      inversion H₂.
    + intros c H₁ H₂ H₃.
      apply Bool.andb_true_iff in H₃.
      destruct H₃ as [Hl₃ Hr₃].
      apply Bool.orb_true_iff in H₂.
      destruct H₂ as [H₂ | H₂].
      exists [], l; simpl; subst.
      apply Bool.negb_true_iff in Hl₃.
      split. apply Bool.andb_true_iff.
      split. apply symA. apply H₂.
      apply list_eqv_refl.
      split. auto.
      apply list_mem_not with (a := a).
      exact H₂. exact Hl₃.
      (* l = [] \/ l <> []*)
      destruct l as [|b l].
      - inversion H₂.
      - assert (Ht : b :: l <> []).
        intro Hf. inversion Hf.
        destruct (IHl c Ht H₂ Hr₃) as 
         [la [lb [Ha [Hb Hc]]]].
        exists (a :: la), lb.
        assert (Hlf : (a :: la) ++ c :: lb = a :: la ++ c :: lb).
        simpl. reflexivity.
        rewrite Hlf. clear Hlf.
        apply Bool.negb_true_iff in Hl₃.
        split. apply Bool.andb_true_iff.
        split. apply refA.
        exact Ha.
        split. simpl.
        apply Bool.orb_false_iff.
        split. apply list_mem_true_false with (l := b :: l).
        exact Hl₃. exact H₂.
        exact Hb. exact Hc.
  Qed.
      

  Lemma list_split_gen : 
    forall (l : list A) (c : A),
    in_list eqA l c = true -> 
    exists l₁ l₂ : list A, 
    list_eqv _ eqA l (l₁ ++ [c] ++ l₂) = true.
  Proof.
    induction l; simpl.
    + intros ? H₁.
      congruence.
    + intros c H₁.
      apply Bool.orb_true_iff in H₁.
      destruct H₁ as [H₁ | H₁].
      exists [], l.
      simpl.
      apply Bool.andb_true_iff.
      split. apply symA; assumption.
      apply list_eqv_refl.
      destruct (IHl c H₁) as [l₁ [l₂ Hl]].
      exists (a :: l₁), l₂.
      simpl.
      apply Bool.andb_true_iff; split.
      apply refA. exact Hl.
  Qed.

  Lemma list_equiv_simp : forall lf lr pu pv au, 
      list_eqv _ eqA [pu; pv] (lf ++ [au] ++ lr) = true ->
      (list_eqv _ eqA lf [] = true /\ 
      eqA pu au = true /\ 
      list_eqv _ eqA lr [pv] = true) ∨
      (list_eqv _ eqA lf [pu] = true /\ 
      eqA pv au = true /\ 
      list_eqv _ eqA lr [] = true).
    Proof.
      intros [|u lf] [|v lr] ? ? ? Hle.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      lia.
      left.
      split. 
      reflexivity.
      split.
      simpl in Hle.
      destruct lr.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [Hle _].
      exact Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [Hle _].
      exact Hle.
      destruct lr.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      simpl.  apply Bool.andb_true_iff in Hle.
      destruct Hle as [Hle _].
      apply Bool.andb_true_iff; split.
      apply symA; assumption.
      reflexivity.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      congruence.
      rewrite List.app_nil_r in Hle.
      right. split.
      destruct lf.
      simpl in Hle.
      simpl.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [Hle _].
      apply Bool.andb_true_iff; split.
      apply symA; assumption.
      reflexivity.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      destruct lf; simpl in Hle; 
      congruence.
      split.
      destruct lf.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [Hle _].
      exact Hle.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      destruct lf; simpl in Hle; 
      congruence.
      reflexivity.
      rewrite <-List.app_comm_cons in Hle.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      assert (Hwt : exists a b l, lf ++ au :: v :: lr = a :: b :: l).
      destruct lf.
      exists au, v, lr. 
      reflexivity.
      destruct lf.
      exists a, au, (v :: lr).
      simpl. reflexivity.
      exists a, a0, (lf ++ [au] ++ v :: lr).
      reflexivity.
      destruct Hwt as (a & b & l & Hwt).
      rewrite Hwt in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      congruence.
    Qed.



    Lemma list_eqv_snoc : 
      forall t pl xb,
      list_eqv _ eqA t (pl ++ [xb]) = true ->
      exists tp, list_eqv _ eqA t (tp ++ [xb]) = true /\ 
      list_eqv _ eqA tp pl = true.
    Proof.
      intros ? ? ? Hl.
      exists pl.
      split. exact Hl.
      apply list_eqv_refl; 
      assumption.
    Qed.



    Lemma list_eqv_in_list_rewrite :
      forall l c x, 
      list_eqv _ eqA c l = true ->
      in_list eqA c x = true ->
      in_list eqA l x = true.
    Proof.
      induction l; 
      destruct c; 
      simpl;
      intros ? Ha Hb.
      + congruence.
      + congruence.
      + congruence.
      + apply Bool.andb_true_iff in Ha.
        destruct Ha as [Hal Har].
        case (eqA x a0) eqn:Hxn.
        rewrite (trnA _ _ _ Hxn Hal).
        reflexivity.
        simpl in Hb.
        erewrite IHl.
        apply Bool.orb_true_iff.
        right.
        reflexivity.
        exact Har.
        exact Hb.
    Qed.



    Lemma length_le_Sn : 
      forall l c n, 
      (length c < n)%nat -> 
      list_eqv _ eqA c l = true ->
      (length l < n)%nat.
    Proof.
      induction l.
      + simpl;
        intros * Ha Hb.
        nia.
      + simpl; 
        intros * Ha Hb.
        simpl in *.
        destruct c.
        - simpl in Hb.
          congruence.
        - simpl in Ha, Hb.
          apply Bool.andb_true_iff in Hb.
          destruct Hb as [Hbl Hbr].
          destruct n.
          nia.
          assert (Hc: (length c < n)%nat).
          nia.
          specialize (IHl _ _ Hc Hbr).
          nia.
    Qed.


    Lemma covers_list_elem : 
      forall (c l : list A), 
      (forall y : A, in_list eqA c y = true) ->
      covers _ eqA c l.
    Proof.
      unfold covers.
      destruct c as [|a c].
      + intros ? Hy ? Hl.
        specialize (Hy x).
        simpl in Hy.
        congruence.
      + intros ? Hy ? Hl.
        simpl in *.
        exact (Hy x). 
    Qed.



    Lemma in_list_mem_ex_one : 
      forall l₁ l₂ a x, 
      eqA x a = false -> 
      in_list eqA (l₁ ++ a :: l₂) x = true ->
      in_list eqA (l₁ ++ l₂) x = true.
    Proof.
      induction l₁;
      simpl; 
      intros ? ? ? Hxa Hlx.
      + rewrite Hxa in Hlx.
        simpl in Hlx.
        exact Hlx.
      + case (eqA x a) eqn:Ha.
        reflexivity.
        simpl.
        eapply IHl₁.
        exact Hxa.
        simpl in Hlx.
        exact Hlx.   
    Qed.


    Lemma covers_dup : 
      forall l (c : list A), 
      covers _ eqA c l ->  (length c < List.length l)%nat -> 
      exists a l₁ l₂ l₃, 
        list_eqv _ eqA l (l₁ ++ [a] ++ l₂ ++ [a] ++ l₃) = true.
    Proof.
      induction l. 
      + simpl.
        intros * Ha Hb.
        nia.
      +
        (* a can be repeated or not *)
        simpl.
        intros * Ha Hb.
        unfold covers in Ha.
        destruct (in_list eqA l a) eqn:Hal.
        (* a in in the list and we have loop *)
        destruct (list_split_gen l a Hal) as 
          [l₁ [l₂ Hlt]].
        exists a, [], l₁, l₂.
        simpl in *.
        rewrite refA, Hlt.
        reflexivity.
        (* a is not in l *)
        pose proof (Ha a) as Hw.
        simpl in Hw.
        rewrite refA in Hw.
        simpl in Hw.
        specialize (Hw eq_refl).
        destruct (list_split_gen c a Hw) as 
        [l₁ [l₂ Hlt]].
        specialize (IHl (l₁ ++ l₂)).
        assert (Hcov : covers _ eqA (l₁ ++ l₂) l).
        unfold covers.
        intros ? Hin.
        (* from Hal and Hin, we know that x <> a *)
        pose proof list_mem_true_false l _ _ Hal Hin as Hax.
        (* get a concrete instance *)
        pose proof (Ha x) as Hx.
        simpl in Hx.
        rewrite Hax, Hin in Hx.
        specialize (Hx eq_refl).
        pose proof list_eqv_in_list_rewrite _ _ _ 
          Hlt Hx as Hinc.
        eapply in_list_mem_ex_one;
        [exact Hax|
        simpl in Hinc;
        exact Hinc].
        specialize (IHl Hcov).
        pose proof length_le_Sn  
          _ _ _ Hb Hlt as Hwt.
        simpl in Hwt.
        rewrite app_length in Hwt.
        simpl in Hwt.
        rewrite PeanoNat.Nat.add_succ_r in Hwt.
        rewrite <-app_length in Hwt.
        assert (Hvt : (length (l₁ ++ l₂) < length l)%nat).
        nia.
        destruct (IHl Hvt) as
          (av & lv₁ & lv₂ & lv₃ & Hlp).
        exists av, (a :: lv₁), lv₂, lv₃.
        simpl.
        rewrite refA.
        simpl in *.
        exact Hlp.
    Qed.


    Lemma list_eqv_in_list_rewrite_gen :
      forall l₁ l₂ a n,
      eqA a n = true ->  
      list_eqv _ eqA l₁ l₂ = true ->
      in_list eqA l₂ n = true ->
      in_list eqA l₁ a = true.
    Proof.
      induction l₁ as [|a₁ l₁]; 
      destruct l₂ as [|b₂ l₂]; 
      simpl;
      intros ? ? Ha Hb Hc.
      + congruence.
      + congruence.
      + congruence.
      + apply Bool.andb_true_iff in Hb.
        destruct Hb as [Hbl Hbr].
        case (eqA n b₂) eqn:Hxn.
        pose proof (trnA _ _ _ Ha Hxn) as Han.
        apply symA in Hbl.
        rewrite (trnA _ _ _ Han Hbl).
        reflexivity.
        simpl in Hc.
        erewrite IHl₁.
        apply Bool.orb_true_iff.
        right.
        reflexivity.
        exact Ha.
        exact Hbr.
        exact Hc.
    Qed.


    Lemma list_eqv_no_dup_rewrite :
      forall l₁ l₂, 
      list_eqv _ eqA l₁ l₂ = true ->
      no_dup _ eqA l₂ = false ->
      no_dup _ eqA l₁ = false.
    Proof.
      induction l₁.
      + simpl.
        intros ? Ha Hb.
        destruct l₂.
        ++ simpl in Hb.
           congruence.
        ++ congruence.
      + (* inductive case *)
        simpl.
        intros ? Ha Hb.
        destruct l₂.
        ++ simpl in Hb.
           congruence.
        ++ simpl in Hb.
           apply Bool.andb_true_iff in Ha.
           destruct Ha as [Hal Har].
           apply Bool.andb_false_iff in Hb.
           destruct Hb as [Hb | Hb].
           apply Bool.negb_false_iff in Hb.
           rewrite (list_eqv_in_list_rewrite_gen _ _ 
           _ _ Hal Har Hb).
           reflexivity.
           erewrite IHl₁.
           apply Bool.andb_false_iff.
           right.
           reflexivity.
           exact Har.
           exact Hb.
    Qed.


End Listsingleprops.




  


Section Listtripledefs.

  Variables
    (A B C : Type)
    (rA : brel A)
    (rB : brel B)
    (rC : brel C).


   
  Definition non_empty_list (l : list A) : bool :=
    match l with 
    | [] => false
    | _ => true
    end.


  Fixpoint all_elems_non_empty_list (l : list (list A)) : bool :=
    match l with 
    | [] => true
    | h :: t => match h with 
      | [] => false
      | _ => all_elems_non_empty_list t
    end 
    end.
  
  
  
  (* This function compares two lists for boolean equality *)
  Fixpoint triple_elem_list (l₁ l₂ : list (A * B * C)) :=
    match l₁ with 
    | [] => match l₂ with 
      | [] => true
      | _ => false
      end
    | (a, b, c) :: t₁ => match l₂ with 
      | [] => false
      | (d, e, f) :: t₂ => ((rA a d) && (rB b e) && (rC c f) && 
        triple_elem_list t₁ t₂)%bool
      end
    end.

  (* This function tests if l₁ in l₂ or not *)
  Fixpoint In_eq_bool (l₁ : list (A * B * C))
    (l₂ : list (list (A * B * C))) : bool :=
    match l₂ with
    | [] => false
    | h :: t => ((triple_elem_list l₁ h) || (In_eq_bool l₁ t))%bool 
    end.

End Listtripledefs.

Section Listtripleprops.

  Variables
    (A B C : Type)
    (rA : brel A)
    (rB : brel B)
    (rC : brel C)
    (refA : brel_reflexive A rA)
    (symA : brel_symmetric A rA)
    (trnA : brel_transitive A rA)
    (refB : brel_reflexive B rB)
    (symB : brel_symmetric B rB)
    (trnB : brel_transitive B rB)
    (refC : brel_reflexive C rC)
    (symC : brel_symmetric C rC)
    (trnC : brel_transitive C rC).


 
  (* triple_elem_list is equivalence relation *)
  Lemma triple_elem_eq_list_refl : 
    forall l, @triple_elem_list _ _ _ rA rB rC l l = true.
  Proof.
    induction l as [|((au, av), aw) l].
    - simpl. reflexivity.
    - simpl.
      repeat (apply Bool.andb_true_iff; split;
      try (apply IHl)).
      apply refA.
      apply refB. 
      apply refC.
  Qed.


  Lemma triple_elem_eq_list_sym : forall xs ys, 
      @triple_elem_list _ _ _ rA rB rC xs ys = true -> 
      @triple_elem_list _ _ _ rA rB rC ys xs = true.
  Proof.
    induction xs.
    + intros * Ht.
      destruct ys.
      reflexivity.
      simpl in Ht.
      congruence.
    + intros * Ht.
      destruct ys.
      simpl in Ht.
      destruct a as ((u, v), w).
      congruence.
      destruct a as ((au, av), aw).
      destruct p as ((pu, pv), pw).
      simpl in * |- *.
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrr].
      apply Bool.andb_true_iff in Ht.
      destruct Ht as [Ht Htrrr].
      apply Bool.andb_true_iff; split.
      apply Bool.andb_true_iff; split.
      apply Bool.andb_true_iff; split.
      apply symA; assumption.
      apply symB; assumption.
      apply symC; assumption.
      apply IHxs; assumption.
  Qed.


  Lemma triple_elem_eq_list_trans : 
    forall xs ys zs, 
    @triple_elem_list _ _ _ rA rB rC xs ys = true -> 
    @triple_elem_list _ _ _ rA rB rC ys zs = true ->
    @triple_elem_list _ _ _ rA rB rC xs zs = true.
  Proof.
    induction xs.
    + intros * Hy Hz.
      destruct ys; 
      destruct zs;
      simpl in * |- *;
      try reflexivity; 
      try congruence.
    + intros * Hy Hz.
      destruct ys; 
      destruct zs;
      simpl in * |- *;
      destruct a as ((au, av), aw);
      try congruence.
      destruct p as ((pu, pv), pw);
      try congruence.
      destruct p as ((pu, pv), pw).
      destruct p0 as ((put, pvt), pwt).
      apply Bool.andb_true_iff in Hy.
      destruct Hy as [Hy Hyr].
      apply Bool.andb_true_iff in Hy.
      destruct Hy as [Hy Hyrr].
      apply Bool.andb_true_iff in Hy.
      destruct Hy as [Hy Hyrrr].
      apply Bool.andb_true_iff in Hz.
      destruct Hz as [Hz Hzr].
      apply Bool.andb_true_iff in Hz.
      destruct Hz as [Hz Hzrr].
      apply Bool.andb_true_iff in Hz.
      destruct Hz as [Hz Hzrrr].
      apply Bool.andb_true_iff; split.
      apply Bool.andb_true_iff; split.
      apply Bool.andb_true_iff; split.
      apply trnA with pu; assumption.
      apply trnB with pv; assumption.
      apply trnC with pw; assumption.
      apply IHxs with ys; assumption.
  Qed.
      
  (* end of triple_elem_list equivalence relation *)


  Lemma length_rewrite : forall xs ys,
    @triple_elem_list _ _ _ rA rB rC xs ys = true ->
    List.length xs = List.length ys.
  Proof.
    induction xs.
    + intros * Hin.
      destruct ys.
      reflexivity.
      simpl in Hin.
      congruence.
    + intros * Hin.
      destruct ys.
      simpl in Hin.
      destruct a as ((u, v), w).
      congruence.
      simpl in * |- *.
      destruct a as ((au, av), aw).
      destruct p as ((pu, pv), pw).
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [_ Hin].
      apply f_equal.
      apply IHxs; assumption.
  Qed.

  
  Lemma path_tl_rewrite : forall lss xs ys, 
      @triple_elem_list _ _ _ rA rB rC xs ys = true ->
      In_eq_bool _ _ _ rA rB rC xs lss = true -> 
      In_eq_bool _ _ _ rA rB rC ys lss = true.
    Proof.
      induction lss.
      + intros * Ht Hin.
        simpl in Hin.
        congruence.
      + intros * Ht Hin.
        simpl in Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        simpl.
        apply Bool.orb_true_iff.
        left.
        apply triple_elem_eq_list_trans with xs.
        apply triple_elem_eq_list_sym; assumption.
        exact Hin.
        simpl. apply Bool.orb_true_iff. 
        right.
        apply IHlss with xs; assumption.
    Qed.

    Lemma triple_trim_tail : forall (xs : list (A * B * C)) 
      (a b : A * B * C) (c : list (A * B * C)),
      triple_elem_list _ _ _ rA rB rC xs (a :: b :: c) = true ->
      triple_elem_list _ _ _ rA rB rC (List.tl xs) (b :: c) = true.
    Proof.
      destruct xs.
      - simpl; intros ? ? ? He.
        congruence.
      - simpl; intros ? ? ? He.
        repeat destruct p in He.
        destruct a in He.
        destruct p in He.
        apply Bool.andb_true_iff in He.
        destruct He as [Hel Her].
        exact Her.
    Qed.

    Lemma in_eq_bool_mem_first : 
      forall (l₁ l₂ : list (list (A * B * C)))
      (y : list (A * B * C)), 
      In_eq_bool _ _ _ rA rB rC y (l₁ ++ l₂) = true -> 
      In_eq_bool _ _ _ rA rB rC y l₁ = true \/ 
      In_eq_bool _ _ _ rA rB rC y l₂ = true.
    Proof.
      induction l₁.
      - simpl; intros ? ? Hin.
        right. exact Hin.
      - simpl; intros ? ? Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        left. 
        apply Bool.orb_true_iff.
        left. exact Hin.
        destruct (IHl₁ _ _ Hin) as [H | H].
        left. 
        apply Bool.orb_true_iff.
        right. exact H.
        right.
        exact H.
    Qed.


    Lemma in_eq_bool_mem_second : 
      forall (l₁ l₂ : list (list (A * B * C)))
      (y : list (A * B * C)),
      In_eq_bool _ _ _ rA rB rC y l₁ = true \/ 
      In_eq_bool _ _ _ rA rB rC y l₂ = true -> 
      In_eq_bool _ _ _ rA rB rC y (l₁ ++ l₂) = true.
    Proof.
      induction l₁.
      - simpl; intros ? ? [Hin | Hin]; 
        congruence.
      - simpl; intros ? ? [Hin | Hin].
        apply Bool.orb_true_iff in Hin.
        apply Bool.orb_true_iff.
        destruct Hin as [Hin | Hin].
        left. exact Hin.
        right. 
        exact (IHl₁ l₂ y (or_introl Hin)).
        apply Bool.orb_true_iff.
        right.
        exact (IHl₁ l₂ y (or_intror Hin)).
    Qed.


    Lemma in_flat_map_bool_first : 
      forall (l : list A) (y : list (A * B * C))
      (f : A -> list (list (A * B * C))),
      In_eq_bool _ _ _ rA rB rC y (flat_map f l) = true -> 
      (exists x : A, in_list rA l x = true /\ 
      In_eq_bool _ _ _ rA rB rC y (f x) = true).
    Proof.
      induction l.
      - simpl; intros ? ? Hin.
        congruence.
      - simpl; intros ? ? Hin.
        apply in_eq_bool_mem_first in Hin.
        destruct Hin as [Hin | Hin].
        exists a. split.
        apply Bool.orb_true_iff.
        left. apply refA.
        exact Hin.
        destruct (IHl _ _ Hin) as [x [Hl Hr]].
        exists x. split.
        apply Bool.orb_true_iff.
        right. exact Hl.
        exact Hr.
    Qed.



    Lemma in_flat_map_bool_second : 
      forall (l : list A) 
      (f : A -> list (list (A * B * C)))
      (y : list (A * B * C)) (x : A),
      (forall (x a : A) (y : list (A * B * C)),  
        rA x a = true -> 
        In_eq_bool _ _ _ rA rB rC y (f a) = 
        In_eq_bool _ _ _ rA rB rC y (f x)) ->
      in_list rA l x = true -> 
      In_eq_bool _ _ _ rA rB rC y (f x) = true ->
      In_eq_bool _ _ _ rA rB rC y (flat_map f l) = true.
    Proof.
      induction l.
      - simpl; intros ? ? ? Hc Hin Hf.
        congruence.
      - simpl; intros ? ? ? Hc Hin Hf.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        apply in_eq_bool_mem_second.
        left. rewrite <-Hf.
        apply Hc. exact Hin.
        apply in_eq_bool_mem_second.
        right. apply IHl with (x := x).
        exact Hc.
        exact Hin.
        exact Hf.
    Qed.


    (* boolean equivalent of in_flat_map *)
    Lemma in_flat_map_bool : 
      forall (l : list A) (y : list (A * B * C))
      (f : A -> list (list (A * B * C))),
      (forall (x a : A) (y : list (A * B * C)),  
        rA x a = true -> 
        In_eq_bool _ _ _ rA rB rC y (f a) = 
        In_eq_bool _ _ _ rA rB rC y (f x)) ->
      In_eq_bool _ _ _ rA rB rC y (flat_map f l) = true <-> 
      (exists x : A, in_list rA l x = true /\ 
      In_eq_bool _ _ _ rA rB rC y (f x) = true).
    Proof.
      intros ? ? ? Hc; split; intros H.
      apply in_flat_map_bool_first; exact H.
      destruct H as [x [Hl Hr]].
      apply in_flat_map_bool_second with (x := x).
      exact Hc. exact Hl. exact Hr.
    Qed.


    Lemma orb_eq : forall (a b c : bool), 
      a = c -> (a || b = c || b)%bool.
    Proof using -All.
      intros [|] [|] [|] H; simpl;
      try reflexivity; try congruence.
    Qed.

    Lemma andb_eq : forall (a b c d e f g: bool), 
      (a && b && c = e && f && g)%bool -> 
      (a && b && c && d = e && f && g && d)%bool.
    Proof using -All.
      intros [|] [|] [|] [|] [|] [|] [|] H; simpl in * |- *;
      try reflexivity; try congruence.
    Qed.




    Lemma triple_eq_cong : forall l v y a₁ a₂
      b₁ b₂ r₁ r₂,
      rA a₁ a₂ = true -> 
      rB b₁ b₂ = true -> 
      rC r₁ r₂ = true ->
      triple_elem_list _ _ _ rA rB rC y ((a₁, b₁, r₁) :: v :: l) =
      triple_elem_list _ _ _ rA rB rC y ((a₂, b₂, r₂) :: v :: l).
    Proof.
      intros ? ? ? ? ? ? ? ? ? H₁ H₂ H₃.
      destruct y; simpl. reflexivity.
      repeat destruct p. 
      apply andb_eq.
      
      (* 
        God, give me strenght to prove
        this lemma! 
      *)
      case (rA a a₁) eqn:Hn₁;
      case (rB b b₁) eqn:Hn₂;
      case (rC c r₁) eqn:Hr₁;
      case (rA a a₂) eqn:Hn₃;
      case (rB b b₂) eqn:Hn₄;
      case (rC c r₂) eqn:Hr₂; simpl;
      auto.
      pose proof (trnC _ _ _ Hr₁ H₃) as Hf.
      rewrite Hf in Hr₂. congruence.
      pose proof (trnB _ _ _ Hn₂ H₂) as Hf.
      rewrite Hf in Hn₄. congruence.
      pose proof (trnC _ _ _ Hr₁ H₃) as Hf.
      rewrite Hf in Hr₂. congruence.
      pose proof (trnA _ _ _ Hn₁ H₁) as Hf.
      rewrite Hf in Hn₃. congruence.
      pose proof (trnC _ _ _ Hr₁ H₃) as Hf.
      rewrite Hf in Hr₂. congruence.
      pose proof (trnA _ _ _ Hn₁ H₁) as Hf.
      rewrite Hf in Hn₃. congruence.
      pose proof (trnA _ _ _ Hn₁ H₁) as Hf.
      rewrite Hf in Hn₃. congruence.
      apply symC in H₃.
      pose proof (trnC _ _ _ Hr₂ H₃) as Hf.
      rewrite Hf in Hr₁. congruence.
      apply symB in H₂.
      pose proof (trnB _ _ _ Hn₄ H₂) as Hf.
      rewrite Hf in Hn₂. congruence.
      apply symB in H₂.
      pose proof (trnB _ _ _ Hn₄ H₂) as Hf.
      rewrite Hf in Hn₂. congruence.
      apply symA in H₁.
      pose proof (trnA _ _ _ Hn₃ H₁) as Hf.
      rewrite Hf in Hn₁; congruence.
      apply symC in H₃.
      pose proof (trnC _ _ _ Hr₂ H₃) as Hf.
      rewrite Hf in Hr₁. congruence.
      apply symB in H₂.
      pose proof (trnB _ _ _ Hn₄ H₂) as Hf.
      rewrite Hf in Hn₂. congruence.
      apply symB in H₂.
      pose proof (trnB _ _ _ Hn₄ H₂) as Hf.
      rewrite Hf in Hn₂. congruence.
      (* Thank you, God! *)
    Qed.

    Lemma list_equality_cons_gen : 
      forall l ld le c d mcd e f mef,
      l <> [] -> 
      triple_elem_list _ _ _ rA rB rC l ((c, d, mcd) :: ld) = true ->
      triple_elem_list _ _ _ rA rB rC l (le ++ [(e, f, mef)]) = true ->
      (triple_elem_list _ _ _ rA rB rC l [(c, d, mcd)] = true ∧ 
      triple_elem_list _ _ _ rA rB rC l [(e, f, mef)] = true) ∨ 
      (exists lm, 
      triple_elem_list _ _ _ rA rB rC l ((c, d, mcd) :: lm ++ [(e, f, mef)]) = true).
    Proof.
      induction l as [|((au, av), aw) l].
      + intros * H He Hf.
        congruence.
      + intros * H He Hf.
        destruct l as [|((bu, bv), bw) l].
        destruct ld as [|((ldu, ldv), ldw) ld].
        destruct le as [|((leu, lev), lew) le].
        left.
        simpl in * |-*.
        split. exact He.
        exact Hf.
        simpl in Hf.
        destruct le;
        simpl in Hf; lia.
        destruct ld;
        simpl in He; lia.
        destruct ld as [|((ldu, ldv), ldw) ld].
        simpl in He. 
        apply Bool.andb_true_iff in He.
        lia.
        destruct le as [|((leu, lev), lew) le].
        simpl in Hf.
        apply Bool.andb_true_iff in Hf.
        lia.
        remember ((bu, bv, bw) :: l) as bl.
        remember ((ldu, ldv, ldw) :: ld) as dl.
        assert (Hwt : (((leu, lev, lew) :: le) ++ [(e, f, mef)]) =
        ((leu, lev, lew) :: (le ++ [(e, f, mef)]))).
        simpl; reflexivity.
        rewrite Hwt in Hf; clear Hwt.
        simpl in He, Hf.
        apply Bool.andb_true_iff in He, Hf.
        destruct He as [He Her].
        destruct Hf as [Hf Hfr].
        subst.
        assert (Hwt : (bu, bv, bw) :: l ≠ []).
        intro Hff; congruence.
        specialize(IHl _ _ _ _ _ _ _ _ Hwt Her Hfr).
        destruct IHl as [[IHll IHlr] | [lm IHl]].
        right.
        exists [].
        remember ((bu, bv, bw) :: l) as bl.
        simpl.
        apply Bool.andb_true_iff; split.
        exact He. assumption.
        right.
        exists ((ldu, ldv, ldw) :: lm).
        remember ((bu, bv, bw) :: l) as bl.
        simpl.
        apply Bool.andb_true_iff; split.
        exact He.
        exact IHl.
    Qed.

    Lemma triple_elem_eq : 
      forall bl lrt, 
      triple_elem_list _ _ _ rA rB rC bl lrt = true ->
      (length lrt < S (S (length bl)))%nat.
    Proof.
      (* proof by nia? *)
      induction bl as [|((bau, bav), baw) bl].
      + intros [|((aau, aav), aaw) lrt].
        intros Ha.
        simpl.
        nia.
        intros Ha.
        simpl in Ha.
        congruence.
      + intros [|((aau, aav), aaw) lrt].
        intros Ha.
        simpl.
        nia.
        intros Ha.
        simpl in Ha.
        simpl.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [_ Ha].
        specialize (IHbl _ Ha).
        nia.
    Qed.


    Lemma triple_elem_rewrite_le : 
      forall bl llt awt lrt, 
      triple_elem_list _ _ _ rA rB rC bl (llt ++ [awt] ++ lrt) = true ->
      (length lrt < S (length bl))%nat.
    Proof.
      induction bl as [|((bau, bav), baw) bl].
      + simpl.
        intros * Ha.
        assert (Hlt : exists avt llw, llt ++ awt :: lrt = avt :: llw).
        destruct llt.
        simpl.
        exists awt, lrt.
        reflexivity.
        simpl.
        exists p, (llt ++ awt :: lrt).
        reflexivity.
        destruct Hlt as [avt [llw Hlw]].
        rewrite Hlw in Ha.
        congruence.
      + 
        intros * Ha.
        simpl.
        destruct llt as [|((llta, lltb), lltc) llt].
        simpl in Ha.
        destruct awt as ((awta, awtb), awtc).
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [_ Ha].
        eapply triple_elem_eq.
        exact Ha.
        simpl in Ha.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [_ Ha].
        specialize (IHbl _ _ _ Ha).
        nia.
    Qed.

    Lemma list_tl_lia : forall (xs : list A) k, 
      List.tl xs <> [] -> (length (List.tl xs) = S k)%nat ->
      (length xs = S (S k))%nat.
    Proof using -All.
      induction xs.
      + intros * Hf Hin.
        simpl in * |- *.
        congruence.
      + intros * Hf Hin.
        simpl in * |- *.
        lia.
    Qed.

  Lemma elem_path_aux_true : 
    forall (l : list A) (a : A),
    in_list rA l a = true -> 
    exists l₁ l₂ : list A, 
    list_eqv _ rA l (l₁ ++ [a] ++ l₂) = true.
  Proof using A rA refA symA.
    induction l.
    - simpl; intros ? H; 
      congruence.
    - simpl; intros ? H.
      apply Bool.orb_true_iff in H.
      destruct H as [H | H].
      exists [], l; simpl.
      apply Bool.andb_true_iff.
      split.
      apply symA; exact H.
      apply list_eqv_refl; assumption.
      destruct (IHl a0 H) as [l₁ [l₂ Ht]].
      exists (a :: l₁), l₂.
      simpl. apply Bool.andb_true_iff.
      split. apply refA.
      exact Ht.
  Qed.

 
  Lemma in_list_true : 
    forall l₁ l₂ a, 
    in_list rA (l₁ ++ a :: l₂) a = true.
  Proof.
    induction l₁.
    + simpl.
      intros ? ?.
      rewrite refA.
      reflexivity.
    + simpl.
      intros ? ?.
      rewrite IHl₁.
      apply Bool.orb_true_iff.
      right.
      reflexivity.
  Qed.


  Lemma no_dup_false_one : 
    forall l₁ l₂ l₃ a, 
    no_dup A rA (l₁ ++ a :: l₂ ++ a :: l₃) = false.
  Proof.
    induction l₁.
    + simpl.
      intros *.
      rewrite in_list_true.
      simpl.
      reflexivity.
    + simpl.
      intros *.
      rewrite IHl₁.
      apply Bool.andb_false_iff.
      right.
      reflexivity.
  Qed.
  

    
End Listtripleprops.
    

    

    




