(* ================================================================= *)
(*  Matrix Operations over a Finite Semiring (list-based)             *)
(*  File: MatN.v                                                     *)
(*  Matrix is `Node -> Node -> R` where `Node` is a finite type      *)
(*  and `R` is a semiring.  This file provides both functional       *)
(*  (high‑level) and list‑based (computationally efficient) matrix   *)
(*  operations together with proofs of their equivalence.            *)
(* ================================================================= *)

From Stdlib Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia PeanoNat PArith.
From Semiring Require Import OrelN Structures.
Import ListNotations SemiringNotations.

(* ================================================================= *)
(*  Section: Generic Definitions                                     *)
(*  General‑purpose combinators on lists used by the matrix          *)
(*  operations below.  These are polymorphic in the element type.    *)
(* ================================================================= *)

Section GenericDef.

  (** [zip_with f xs ys] applies `f` pointwise to the elements of `xs`
      and `ys`, stopping at the shorter list.  This is the standard
      "zipWith" from functional programming. *)

  (** Element-wise combination of two lists; stops at the shorter list. *)
  Fixpoint zip_with {A B C : Type} 
    (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
    match xs, ys with
    | x :: xs, y :: ys => f x y :: zip_with f xs ys
    | _, _ => []
    end.

  (** [transpose_list xss] transposes a rectangular list of lists.
      For a singleton row [[r]] it returns the column list
      [[x₁];[x₂];…]; for multiple rows it uses [zip_with cons]
      to build the transposed rows incrementally. *)

  (** Transpose a rectangular list-of-lists (matrix). *)
  Fixpoint transpose_list {A : Type} (xss : list (list A)) : list (list A) :=
    match xss with
    | [] => []
    | xssh :: xsst => 
      match xsst with 
      | [] =>  map (fun y => [y]) xssh 
      | _ :: _ => zip_with List.cons xssh (transpose_list xsst)
      end 
    end.

End GenericDef.

(* ================================================================= *)
(*  Section: Proofs about the generic list combinators                *)
(* ================================================================= *)

Section GenericDefProofs.

  (** The length of [zip_with f xs ys] is the minimum of the lengths
      of [xs] and [ys]. *)

  (** The length of [zip_with] is the minimum of the two input lengths. *)
  Theorem zip_with_length {A B C : Type} 
    (f : A -> B -> C) : ∀ (xs : list A) (ys : list B), 
    List.length (zip_with f xs ys) = 
    Nat.min (List.length xs) (List.length ys).
  Proof.
    induction xs as [|xsh xst ih].
    +
      intros ys; reflexivity. 
    +
      intros *.
      destruct ys as [|ysh yst].
      ++
        cbn; reflexivity.
      ++
        cbn. f_equal.
        eapply ih.
  Qed.

  
  (** Transpose of a column of singletons is a row: transpose [[a₁];[a₂];…] = [[a₁;a₂;…]]. *)
  Theorem transpose_map {A : Type} : ∀ (xs : list A ), 
    xs <> [] -> transpose_list (map (λ y : A, [y]) xs) = [xs].
  Proof.
    induction xs as [|xsh xst ih]; intros ha; try congruence.
    destruct xst as [|xsth xstt].
    ++
      cbn; reflexivity.
    ++
      remember (xsth :: xstt) as xst.
      assert(hb : map (λ y : A, [y]) xst = [xsth] :: map (λ y : A, [y]) xstt).
      rewrite Heqxst. cbn. reflexivity.
      cbn. rewrite hb; clear hb.
      assert (hb : xst <> []). rewrite Heqxst. 
      intro hb. congruence.
      specialize(ih hb).
      rewrite Heqxst in ih.
      assert (hc : map (λ y : A, [y]) (xsth :: xstt) = [xsth] :: 
        map (λ y : A, [y]) xstt).
      cbn. reflexivity. rewrite hc in ih; clear hc.
      rewrite ih. subst. reflexivity.
  Qed.

  
  

  (** Transpose distributes over [zip_with cons]: prepending a row then transposing equals the row followed by the transposed rest. *)
  Theorem transpose_zip {A : Type} : ∀ (xss : list (list A)) (xs : list A),
    xss <> [] -> length xs = length xss -> 
    transpose_list (zip_with cons xs xss) = xs :: transpose_list xss.
  Proof. 
    induction xss as [|xssh xsst ih].
    +
      intros * ha hb.
      congruence.
    +
      intros * ha hb.
      destruct xsst as [|xssth xsttt].
      ++
        cbn in hb |- *.
        assert (hc : ∃ y : A, xs = [y]).
        {
          destruct xs as [|xsh xst]; 
          cbn in hb; try nia.
          exists xsh.
          destruct xst. cbn in hb.
          reflexivity.
          cbn in hb. nia.
        }
        destruct hc as (y & hc).
        subst. cbn.
        reflexivity.
      ++
        remember (xssth :: xsttt) as xst.
        cbn in hb |- *.
        rewrite Heqxst.
        rewrite <- Heqxst.
        destruct xs as [|xsa xsb]; 
        [cbn in hb; nia | ].
        assert (hc : zip_with cons (xsa :: xsb) (xssh :: xst) = 
          cons xsa xssh :: zip_with cons xsb xst). reflexivity.
        rewrite hc; clear hc.
        inversion hb as [hbb]; clear hb.
        rewrite Heqxst in hbb |- * .
        assert (hb : transpose_list ((xsa :: xssh) :: 
          zip_with cons xsb (xssth :: xsttt)) = 
          zip_with cons (xsa :: xssh) 
          (transpose_list (zip_with cons xsb (xssth :: xsttt)))). 
        {
           destruct xsb as [|xsbh xsbt];
          [cbn in hbb; try nia | reflexivity].
        }
        rewrite hb; clear hb.
        assert (hb : xst <> []). subst. 
        intro hb; congruence.
        rewrite <-Heqxst in hbb |- *.
        pose proof (ih xsb hb hbb) as hc.
        rewrite hc. cbn; reflexivity.
  Qed.



  (** [zip_with cons] of two non-empty lists is non-empty. *)
  Theorem zip_non_empty {A : Type} :
    ∀ (xss : list (list A)) (xs : list A), 
    xss <> [] -> xs <> [] ->
    zip_with cons xs xss ≠ [].
  Proof.
    destruct xss as [|xssh xsst].
    +
      intros * ha hb.
      congruence.
    +
      intros [|xsh xst] ha hb.
      ++
        congruence.
      ++
        intro hc. cbn in hc.
        congruence.
  Qed.



  (** The transpose of a non-empty rectangular matrix is non-empty. *)
  Theorem transpose_eff_non_empty {A : Type} : 
    ∀ (xss : list (list A)), xss <> [] -> 
    (∀ (xs : list A), In xs xss -> ∀ (ys : list A), 
      In ys xss -> List.length xs = List.length ys ∧ 0 < List.length xs) -> 
     transpose_list xss ≠ [].
  Proof.
    induction xss as [|xssh xsst ih].
    +
      intros ha hb; try congruence.
    +
      destruct xsst as [|xssth xsstt].
      ++
        intros ha hb.
        cbn. intro hc.
        specialize (hb xssh (or_introl eq_refl)
          xssh (or_introl eq_refl)).
        destruct hb as (_ & hbr).
        assert(hb : xssh <> []).
        { 
          destruct xssh as [|xsshh xssht];
          cbn in hbr; try nia.
          intro hb. congruence.
        }
        eapply hb.
        eapply map_eq_nil; exact hc.
      ++
        (* inductive case *)
        remember (xssth :: xsstt) as xst.
        intros * ha hb.
        assert(hc : xst <> []).
        {
          subst; intro hc; congruence.
        }
        assert(hd : ∀ xs : list A, In xs xst → ∀ ys : list A, In ys xst →
          length xs = length ys ∧ 0 < length xs).
        {
          intros * he * hf.
          eapply hb; cbn; right; 
          assumption.
        }
        (* i know that  transpose_eff xst ≠ [] 
        and xssh <> [] *)
        specialize(ih hc hd).
        pose proof (hb xssh (or_introl eq_refl) xssh 
        (or_introl eq_refl)) as he.
        destruct he as (_ & her).
        assert (he : xssh <> []).
        {
          destruct xssh as [|xsshh xssht];
          cbn in her; try nia.
          intro he; congruence.
        }
        assert (hf : transpose_list (xssh :: xst) = 
        zip_with List.cons xssh (transpose_list xst)).
        { 
          rewrite Heqxst; reflexivity.
        }
        rewrite hf; clear hf.
        eapply zip_non_empty; assumption.
  Qed.



  (** [zip_with cons ys (map singleton zs)] has the same length as [ys] when [|ys|=|zs|]. *)
  Theorem zip_length_map {A : Type} : 
    ∀ (ys zs : list A), 
    List.length ys = List.length zs -> 
    length (zip_with cons ys (map (λ y : A, [y]) zs)) = length ys.
  Proof.
    induction ys as [|ysh yst ih].
    +
      intros * ha. cbn; reflexivity.
    +
      intros [|zsh zst] ha.
      ++
        cbn in ha; nia.
      ++
        cbn. rewrite ih.
        reflexivity.
        cbn in ha. inversion ha; subst;
        reflexivity.
  Qed.


  (** If three lists have equal length, [zip_with cons] preserves that length. *)
  Theorem zip_transpose_length {A : Type} : 
    ∀ (xs ys : list A) zs,
    List.length xs = List.length ys -> 
    List.length ys = List.length zs -> 
    length xs = length (zip_with cons ys zs).
  Proof.
    induction xs as [|xsh xst ih].
    +
      intros [|ysh yst] [|zsh zst] ha hb;
      cbn in ha, hb; try congruence; 
      try reflexivity.
    +
      intros [|ysh yst] [|zsh zst] ha hb;
      cbn in ha, hb; try congruence.
      cbn. erewrite <-ih.
      reflexivity.
      inversion ha; 
      reflexivity.
      inversion hb; reflexivity.
  Qed.



  (** In a rectangular matrix, row length equals the length of the transpose. *)
  Theorem transpose_length {A : Type} : 
    ∀ (xst : list (list A)) (xsh : list A),
    0 < List.length xst -> 0 < List.length xsh -> 
    (∀ xs : list A, In xs (xsh :: xst) → ∀ ys : list A, 
    In ys (xsh :: xst) → length xs = length ys ∧ 0 < length xs) ->
    (* transpose_eff (transpose_eff xst) = xst -> *)
    length xsh = length (transpose_list xst).
  Proof.
    induction xst as [|xsth xstt ih].
    +
      intros * ha hb hc.
      cbn in ha; nia.
    +
      destruct xstt as [|xsstth xssttt].
      ++
        intros [|xshh xsht] ha hb hc.
        *
          cbn in hb; nia.
        *
          pose proof (hc (xshh :: xsht)  (or_introl eq_refl)
            xsth (or_intror (or_introl eq_refl))) as he.
          destruct he as (hel & her).
          cbn. rewrite length_map, <-hel;
          reflexivity.
      ++
        (* induction case *)
        assert (hd : transpose_list (xsth :: xsstth :: xssttt) = 
          zip_with List.cons xsth (transpose_list (xsstth :: xssttt))).
        cbn. reflexivity.
        remember (xsstth :: xssttt) as xst.
        intros * ha hb hc.
        rewrite hd.
        destruct (hc xsh (or_introl eq_refl) xsth 
          (or_intror (or_introl eq_refl))) as (hel & her).
        rewrite Heqxst in hc.
        destruct (hc xsth (or_intror (or_introl eq_refl)) 
          xsstth (or_intror (or_intror (or_introl eq_refl)))) as 
          (hfl & hfr).
        assert (hg : 0 < length xst). subst; cbn; nia.
        assert(hf : (∀ xs : list A, In xs (xsh :: xst) → ∀ ys : list A, 
          In ys (xsh :: xst) → length xs = length ys ∧ 0 < length xs)).
        {
          intros * hf * hi.
          apply hc.
          rewrite <- Heqxst.
          firstorder.
          rewrite <-Heqxst.
          firstorder. 
        }
        specialize (ih xsh hg hb hf).
        rewrite Heqxst.
        eapply zip_transpose_length.
        assumption.
        rewrite <-Heqxst.
        nia.
  Qed.
   



  (** Transpose is involutive for rectangular matrices: [transpose (transpose M) = M]. *)
  Theorem transpose_eff_involutive {A : Type} :
    ∀ (xss : list (list A)), 
    (forall (xs : list A), In xs xss -> ∀ (ys : list A), 
      In ys xss -> List.length xs = List.length ys ∧ 0 < List.length xs) -> 
    transpose_list (transpose_list xss) = xss.
  Proof.
    induction xss as [| xsh xsst ih].
    +
      intro ha. reflexivity.
    +
      destruct xsst as [|xssth xsstt].
      ++
        intro ha. cbn.
        eapply transpose_map.
        specialize (ha xsh (or_introl eq_refl)).
        intro hb. subst. simpl in ha.
        specialize (ha [] (or_introl eq_refl)). 
        nia.
      ++
        intro ha.
        assert (hb : transpose_list (xsh :: xssth :: xsstt) = 
          zip_with List.cons xsh (transpose_list (xssth :: xsstt))).
        cbn. reflexivity.
        rewrite hb; clear hb.
        (* induction part *)
        remember (xssth :: xsstt) as xst.
        rewrite transpose_zip.
        *
          rewrite ih;
          [reflexivity | intros * hb * hc].
          eapply ha; cbn; right; assumption.
        *
          eapply transpose_eff_non_empty;
          [intro hb; congruence | intros * hb * hc].
          eapply ha; cbn; right; assumption.
        *
          assert(hb : (∀ xs : list A, In xs xst → ∀ ys : list A, 
          In ys xst → length xs = length ys ∧ 0 < length xs)).
          {
            intros * hb * hc.
            eapply ha; cbn; right;
            assumption.
          }
          specialize(ih hb).
          assert(hc : 0 < List.length xsh).
          {
            destruct (ha xsh (or_introl eq_refl) 
            xsh (or_introl eq_refl)) as (hal & har);
            assumption.
          }
          assert(hd : 0 < List.length xst).
          {
            subst; cbn; nia.
          }
          eapply transpose_length; 
          assumption.
  Qed.

  (* Helper: nth does not depend on default when index is in bounds.    *)
  Lemma nth_default_indep :
    forall (A : Type) (idx : nat) (l : list A) (d1 d2 : A),
    (idx < List.length l)%nat -> List.nth idx l d1 = List.nth idx l d2.
  Proof.
    intros A idx l d1 d2 Hlt.
    generalize dependent idx.
    induction l as [|a l' IH]; intros idx Hlt.
    - inversion Hlt.
    - destruct idx as [|idx'].
      + reflexivity.
      + simpl in Hlt. cbn. 
        eapply IH. nia.
  Qed.

  (* Lemma: transpose swaps indices under nth, as a plain equality.      *)
  Lemma nth_nil (A : Type) (n : nat) (d : A) : List.nth n [] d = d.
  Proof.
    induction n; simpl; reflexivity.
  Qed.


  (** Looking up any index in a singleton containing the empty list yields the empty list. *)
  Lemma nth_singleton_nil (A : Type) (n : nat) : List.nth n [ [] ] ([] : list A) = [].
  Proof.
    induction n; simpl; [reflexivity | destruct n; reflexivity].
  Qed.

  (* Helper lemma: nth 0 of nth i on map singletons = nth i on original *)
  Lemma nth_0_map_singleton :
    forall (A : Type) (l : list A) (i : nat) (d : A),
    List.nth 0 (List.nth i (List.map (fun y => [y]) l) ([] : list A)) d =
    List.nth i l d.
  Proof.
    intros A l i d. revert i.
    induction l as [|x l' IHl]; intros i; simpl.
    - destruct i; reflexivity.
    - destruct i as [|i']; simpl; [reflexivity | apply IHl].
  Qed.
  
End GenericDefProofs.

Section Matrix.
  Context 
    {Node : FinType.type}
    {R : Semiring.type}.


  (** A matrix over semiring [R] indexed by finite type [Node]. *)
  Definition Matrix := Node -> Node -> R.

  (* returns the cth row of m *)
  Definition row (m : Matrix) (c : Node) : Node -> R := 
    fun d => m c d.

  (* returns the cth column of m *)
  Definition col (m : Matrix) (c : Node) : Node -> R :=
    fun d => m d c.

  (* zero matrix, additive identity of plus *)
  Definition zeroM : Matrix := 
    fun _ _ => 0.

  (* identity matrix, mulitplicative identity of mul *)
  (* Idenitity Matrix *)
  Definition I : Matrix := 
    fun (c d : Node) =>
    match fin_eq_dec c d with 
    | left _ => 1
    | right _ => 0 
    end.

  
  (* transpose the matrix m *)
  Definition transpose (m : Matrix) : Matrix  := 
    fun (c d : Node) => m d c.

  

  (* pointwise addition to two matrices *)
  Definition addM (m₁ m₂ : Matrix) : Matrix :=
    fun c d => (m₁ c d + m₂ c d).

 

  (** Finite sum of a [Node]-indexed family over the semiring. *)
  Definition sum (f : Node -> R) : R :=
    List.fold_right (fun x y => f x + y) 0 elements.

  (* sum of the elements of a matrix *)

 
  (* generalised matrix multiplication *)
  Definition matrix_mul 
    (m₁ m₂ : Matrix) : Matrix:=
    fun (c d : Node) => 
      sum (fun y => (m₁ c y * m₂ y d)).

  (* ----------------------------------------------------------------- *)
  (*  Matrix exponentiation                                             *)
  (* ----------------------------------------------------------------- *)

  Local Infix "+M" := addM (at level 50).


  (** Linear matrix exponentiation: [pow m n = m * m * ... * m] (n times). *)
  Fixpoint pow (m : Matrix) (n : nat) : Matrix :=
    match n with 
    | 0%nat => I 
    | S n' => matrix_mul m (pow m n')
    end.


  (** Linear matrix exponentiation: [pow m n = m * m * ... * m] (n times). *)
  Fixpoint pow_pos (e : Matrix) (n : positive) : Matrix :=
    match n with
    | xH => e
    | xO p => let ret := pow_pos e p in matrix_mul ret ret
    | xI p => 
      let reta := pow_pos e p in 
      let retb := matrix_mul reta reta in
      matrix_mul e retb
    end.


  (** Matrix exponentiation for [N] (binary for positive, identity for zero). *)
  Definition powN (e : Matrix) (n : N) : Matrix :=
    match n with
    | N0 => I
    | Npos p => pow_pos e p 
    end.

  (* ----------------------------------------------------------------- *)
  (*  Scalar exponentiation and partial sums                           *)
  (* ----------------------------------------------------------------- *)

  Fixpoint scalar_pow (a : R) (n : nat) : R :=
    match n with 
    | O => 1
    | S n' => a * scalar_pow a n'
    end.


  (** Scalar geometric series: [1 + a + a² + ... + aⁿ]. *)
  Fixpoint scalar_geom_sum (a : R) (n : nat) : R :=
    match n with
    | O => 1
    | S n' => (scalar_geom_sum a n') + scalar_pow a n
    end.


  (** Matrix geometric series: [I + M + M² + ... + Mⁿ]. *)
  Fixpoint geom_sum (m : Matrix) (n : nat) : Matrix :=
    match n with
    | O => I 
    | S n' => (geom_sum m n') +M (pow m n)
    end.

  (* ----------------------------------------------------------------- *)
  (*  Efficient list-based matrix operations                           *)
  (* ----------------------------------------------------------------- *)

  (* Dot product of two lists *)
  Definition dot_product (v1 v2 : list R) : R :=
    fold_left add (map (fun '(x, y) => mul x y) 
    (combine v1 v2)) zero.


  (* Matrix multiplication (list-based) *)
  Definition mul_list (la lb : list (list R)) : list (list R) :=
    let lbT := transpose_list lb in
    map (fun row =>
      map (fun col => dot_product row col) lbT) la.


  (** Linear matrix exponentiation: [pow m n = m * m * ... * m] (n times). *)
  Fixpoint pow_list (m : list (list R)) 
    (n : nat) : list (list R) :=
    match n with 
    | 0%nat => List.map (fun r => List.map (fun c => I r c) elements) elements 
    | S n' => mul_list m (pow_list m n')
    end.


  (** Linear matrix exponentiation: [pow m n = m * m * ... * m] (n times). *)
  Fixpoint pow_pos_list (e : list (list R)) 
    (n : positive) : list (list R) :=
    match n with
    | xH => e
    | xO p => let ret := pow_pos_list e p in 
      mul_list ret ret
    | xI p => let reta := pow_pos_list e p in
      let retb := mul_list reta reta in
      mul_list e retb
    end.


  (** Matrix exponentiation for [N] (binary for positive, identity for zero). *)
  Definition powN_list (e : list (list R)) (n : N) : list (list R) :=
    match n with
    | N0 => List.map (fun r => List.map (fun c => I r c) elements) elements 
    | Npos p => pow_pos_list e p
    end.

  (* ----------------------------------------------------------------- *)
  (*  Lookup & conversion helpers (mirrors list_lookup in Semimodule)   *)
  (* ----------------------------------------------------------------- *)

  (* Boolean decidable equality on Node *)
  Definition eq_decb (x y : Node) : bool :=
    match fin_eq_dec x y with left _ => true | right _ => false end.

  (* Parallel list lookup keyed by finN with a default value *)
  Fixpoint list_lookup {A : Type} (def : A)
    (keys : list Node) (vals : list A) (key : Node) : A :=
    match keys, vals with
    | k :: ks, v :: vs => if eq_decb key k then v else list_lookup def ks vs key
    | _, _ => def
    end.

  (* Convert between functional and list-of-lists representations *)
  Definition to_list (m : Node -> Node -> R) : list (list R) :=
    List.map (fun r => List.map (fun c => m r c) elements) elements.


  (** Reconstruct a functional matrix from a list-of-lists representation. *)
  Definition of_list (me : list (list R)) : Matrix :=
    fun r c =>
      let row := list_lookup [] elements me r in
      list_lookup 0 elements row c.


  (** Functional matrix multiplication via the list-based implementation. *)
  Definition mul_fun (m₁ m₂ : Node -> Node -> R) : Node -> Node -> R :=
    of_list (mul_list (to_list m₁) (to_list m₂)).


  (** Functional matrix exponentiation via the list-based implementation. *)
  Definition pow_fun (m : Node -> Node -> R) (n : nat)
    : Node -> Node -> R :=
    of_list (pow_list (to_list m) n).


  (** Matrix exponentiation for [N] (binary for positive, identity for zero). *)
  Definition powN_fun (m : Node -> Node -> R) (n : N)
    : Node -> Node -> R :=
    of_list (powN_list (to_list m) n).


  (* ----------------------------------------------------------------- *)
  (*  Correctness: looking up a tabulated matrix returns the original    *)
  (* ----------------------------------------------------------------- *)

  Lemma list_lookup_map_aux : forall (A : Type) (def : A) (f : Node -> A) 
    (y : Node) (l : list Node), NoDup l -> In y l ->
    list_lookup def l (List.map f l) y = f y.
  Proof.
    intros A def f y l Hnd Hin.
    revert y Hnd Hin.
    induction l as [|k ks IH]; intros y Hnd Hin.
    - inversion Hin.
    - inversion Hnd as [|nd_x nd_l Hnin Hnd_ks]; subst.
      simpl in Hin. destruct Hin as [Hx | Hin_ks].
      + subst y.
        unfold list_lookup, eq_decb.
        destruct (fin_eq_dec k k) as [Heq | Hneq].
        * reflexivity.
        * exfalso. apply Hneq; reflexivity.
      + unfold list_lookup, eq_decb.
        destruct (fin_eq_dec y k) as [Heq | Hneq].
        * subst y. exfalso. exact (Hnin Hin_ks).
        * apply IH; [exact Hnd_ks | exact Hin_ks].
  Qed.


  (** Looking up in a tabulated list returns the function value. *)
  Lemma list_lookup_map : forall (A : Type) (def : A) (f : Node -> A) 
    (x : Node), list_lookup def elements (List.map f elements) x = f x.
  Proof.
    intros A def f x.
    apply list_lookup_map_aux.
    - apply (elements_nodup (s := Node)).
    - apply elements_complete.
  Qed.


  (** Round-trip: [of_list (to_list m) = m]. *)
  Lemma of_list_to_list : forall (m : Matrix) (r c : Node),
    of_list (to_list m) r c = m r c.
  Proof.
    intros m r c.
    unfold of_list, to_list.
    simpl.
    (* list_lookup 0 elements (list_lookup [] elements 
       (map (fun r0 => map (fun c0 => m r0 c0) elements) elements) r) c = m r c *)
    rewrite list_lookup_map with (def := []) 
    (f := fun r => List.map (fun c => m r c) elements).
    (* Now: list_lookup 0 elements (map (fun c0 => m r c0) elements) c = m r c *)
    apply list_lookup_map.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  pow = pow_fun  (mathematical = efficient, unary case)             *)
  (* ----------------------------------------------------------------- *)

  (* ----------------------------------------------------------------- *)
  (*  Helper: positional index of a node in elements                    *)
  (* ----------------------------------------------------------------- *)

  Fixpoint index_of_aux (k : Node) (xs : list Node) : nat :=
    match xs with
    | [] => 0
    | x :: xs' => if fin_eq_dec k x then 0 else S (index_of_aux k xs')
    end.


  (** Positional index of a node in the canonical element list. *)
  Definition index_of (k : Node) : nat := 
    index_of_aux k (elements (s := Node)).


  (** The index of any node is within the element list length. *)
  Lemma index_of_bound : forall (k : Node),
    (index_of k < List.length (elements (s := Node)))%nat.
  Proof.
    intros k. unfold index_of.
    assert (Hin : In k (elements (s := Node))) by apply elements_complete.
    revert k Hin.
    induction (elements (s := Node)) as [|e es IH]; intros k Hin; simpl.
    - inversion Hin.
    - destruct (fin_eq_dec k e) as [Heq | Hneq].
      + subst; simpl; nia.
      + simpl in Hin. destruct Hin as [Heq' | Hin']; [exfalso; apply Hneq; symmetry; exact Heq' |].
        simpl. specialize (IH k Hin'). nia.
  Qed.

  (* Helper: nth at index_of position returns the element itself *)
  Lemma index_of_aux_nth_same : forall (xs : list Node) (k : Node),
    In k xs -> List.nth (index_of_aux k xs) xs k = k.
  Proof.
    induction xs as [|e es IH]; intros k Hin; simpl in *.
    - inversion Hin.
    - destruct Hin as [Hk | Hin'].
      + (* k = e *)
        subst k.
        destruct (fin_eq_dec e e).
        * reflexivity.
        * exfalso. apply n. reflexivity.
      + (* k ∈ es *)
        destruct (fin_eq_dec k e).
        * (* k = e, but also k ∈ es: this means e ∈ es, which is fine *)
          subst k. simpl. reflexivity.
        * (* k ≠ e *)
          simpl. apply IH. exact Hin'.
  Qed.


  (** Distinct nodes have distinct indices (injectivity). *)
  Lemma index_of_nodup : forall (k1 k2 : Node),
    index_of k1 = index_of k2 -> k1 = k2.
  Proof.
    intros k1 k2 Hidx.
    unfold index_of in Hidx.
    set (elts := elements (s := Node)) in *.
    assert (Hin1 : In k1 elts) by apply elements_complete.
    assert (Hin2 : In k2 elts) by apply elements_complete.
    pose proof (index_of_aux_nth_same elts k1 Hin1) as Hnth1.
    pose proof (index_of_aux_nth_same elts k2 Hin2) as Hnth2.
    rewrite Hidx in Hnth1.
    (* Hnth1 : nth (index_of_aux k2 elts) elts k1 = k1 *)
    (* Hnth2 : nth (index_of_aux k2 elts) elts k2 = k2 *)
    set (i := index_of_aux k2 elts) in *.
    assert (Hbound : (i < List.length elts)%nat).
    { unfold i. subst elts. apply index_of_bound. }
    rewrite (nth_default_indep Node i elts k1 k2 Hbound) in Hnth1.
    rewrite Hnth2 in Hnth1. symmetry. exact Hnth1.
  Qed.


  (** Equality of nodes is equivalent to equality of their indices. *)
  Lemma index_of_inj : forall (k1 k2 : Node),
    k1 = k2 <-> index_of k1 = index_of k2.
  Proof.
    split; [intros; subst; reflexivity | apply index_of_nodup].
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  list_lookup expressed via nth + index_of                          *)
  (* ----------------------------------------------------------------- *)

  Lemma list_lookup_nth_gen_aux : forall (A : Type) (d : A) (xs : list Node) (l : list A) (k : Node),
    NoDup xs -> In k xs ->
    list_lookup d xs l k = List.nth (index_of_aux k xs) l d.
  Proof.
    induction xs as [|e es IH]; intros l k Hnd Hin.
    - inversion Hin.
    - simpl in Hin. destruct Hin as [Hk | Hin'].
      + (* k = e *)
        subst k.
        destruct l as [|a l']; simpl.
        * destruct (fin_eq_dec e e); reflexivity.
        * unfold list_lookup, eq_decb. simpl.
          destruct (fin_eq_dec e e) as [_ | Hneq]; [reflexivity | exfalso; apply Hneq; reflexivity].
      + (* k ∈ es *)
        inversion Hnd as [|? ? Hnin Hnd']; subst.
        destruct l as [|a l']; simpl.
        * destruct (fin_eq_dec k e); reflexivity.
        * unfold list_lookup, eq_decb. simpl.
          destruct (fin_eq_dec k e) as [Heq | Hneq].
          -- subst k. exfalso. apply Hnin. exact Hin'.
          -- simpl. apply (IH l' k Hnd' Hin').
  Qed.


  (** [list_lookup] is equivalent to [nth] at the index position. *)
  Lemma list_lookup_nth_gen : forall (A : Type) (d : A) (l : list A) (k : Node),
    list_lookup d elements l k = List.nth (index_of k) l d.
  Proof.
    intros A d l k.
    unfold index_of.
    apply list_lookup_nth_gen_aux.
    - apply (elements_nodup (s := Node)).
    - apply elements_complete.
  Qed.

  (* Use the lemma to get specialized versions *)
  Lemma list_lookup_nth_list (l : list (list R)) (k : Node) :
    list_lookup [] elements l k = List.nth (index_of k) l [].
  Proof. apply list_lookup_nth_gen. Qed.


  (** Specialization of [list_lookup_nth_gen] for scalar lists. *)
  Lemma list_lookup_nth_R (l : list R) (k : Node) :
    list_lookup 0 elements l k = List.nth (index_of k) l 0.
  Proof. apply list_lookup_nth_gen. Qed.

  (* ----------------------------------------------------------------- *)
  (*  nth_map with custom defaults (in-bounds version)                   *)
  (* ----------------------------------------------------------------- *)

  Lemma nth_map_inbound : forall (A B : Type) (f : A -> B) (l : list A) (i : nat) (dA : A) (dB : B),
    (i < List.length l)%nat ->
    List.nth i (List.map f l) dB = f (List.nth i l dA).
  Proof.
    intros A B f l i dA dB Hbound.
    (* Use nth_indep to switch default, then nth_map *)
    assert (Heq_default : List.nth i (List.map f l) dB = List.nth i (List.map f l) (f dA)).
    { apply nth_default_indep. rewrite List.length_map. exact Hbound. }
    rewrite Heq_default.
    apply List.map_nth.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  fold_left add = fold_right add for the additive monoid            *)
  (* ----------------------------------------------------------------- *)

  Lemma fold_left_add_acc : forall (l : list R) (a : R),
    List.fold_left add l a = a + List.fold_right add 0 l.
  Proof.
    induction l as [|x l' IH]; intros a; simpl.
    - rewrite addr0. reflexivity.
    - rewrite IH.
      (* (a + x) + fold_right add 0 l' = a + (x + fold_right add 0 l') *)
      rewrite addA. reflexivity.
  Qed.


  (** [fold_left add] over a list equals [fold_right add 0]. *)
  Lemma fold_left_add_fold_right_add : forall (l : list R),
    List.fold_left add l 0 = List.fold_right add 0 l.
  Proof.
    intros l. rewrite fold_left_add_acc. rewrite add0r. reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  combine distributes over map                                      *)
  (* ----------------------------------------------------------------- *)

  Lemma combine_map : forall (A B C : Type) (f : A -> B) (g : A -> C) (l : list A),
    List.combine (List.map f l) (List.map g l) = List.map (fun x => (f x, g x)) l.
  Proof.
    induction l as [|x l' IH]; simpl; [reflexivity |].
    rewrite IH. reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  dot_product of tabulated lists = sum of pointwise products        *)
  (* ----------------------------------------------------------------- *)

  Lemma fold_right_add_map : forall (h : Node -> R),
    List.fold_right add 0 (List.map h elements) =
    List.fold_right (fun x y => h x + y) 0 elements.
  Proof.
    intro h.
    induction elements as [|e es IH]; simpl; [reflexivity |].
    f_equal. apply IH.
  Qed.


  (** Dot product of tabulated vectors equals the sum of pointwise products. *)
  Lemma dot_product_map_eq_sum : forall (f g : Node -> R),
    dot_product (List.map f elements) (List.map g elements) =
    sum (fun x => f x * g x).
  Proof.
    intros f g.
    unfold dot_product, sum.
    rewrite combine_map.
    rewrite List.map_map.
    rewrite (fold_left_add_fold_right_add (List.map (fun x => f x * g x) elements)).
    rewrite fold_right_add_map.
    reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Re-tabulation lemma: map over elements reconstructs the list     *)
  (* ----------------------------------------------------------------- *)

  Lemma list_lookup_tabulate : forall (A : Type) (d : A) (l : list A),
    NoDup (elements (s := Node)) ->
    List.length l = List.length (elements (s := Node)) ->
    List.map (fun k => list_lookup d elements l k) (elements (s := Node)) = l.
  Proof.
    intros A d l Hnd Hlen.
    revert l Hlen.
    induction (elements (s := Node)) as [|e es IH]; intros l Hlen; simpl.
    - destruct l; simpl in Hlen; try nia; reflexivity.
    - destruct l as [|a l']; simpl in Hlen; [nia |].
      simpl. f_equal.
      + unfold list_lookup, eq_decb.
        destruct (fin_eq_dec e e) as [_ | Hneq]; [reflexivity | exfalso; apply Hneq; reflexivity].
      + inversion Hnd as [|? ? Hnin Hnd']; subst.
        assert (Hext : forall z, In z es ->
          (if eq_decb z e then a else list_lookup d es l' z) = list_lookup d es l' z).
        { intros z Hin_es. unfold eq_decb.
          destruct (fin_eq_dec z e) as [Heq | Hneq]; [subst z; exfalso; apply Hnin; exact Hin_es | reflexivity]. }
        rewrite (map_ext_in (fun z => if eq_decb z e then a else list_lookup d es l' z)
                            (fun z => list_lookup d es l' z) es Hext).
        apply (IH Hnd' l').
        nia.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Helper lemmas for transpose_list via nth                          *)
  (* ----------------------------------------------------------------- *)

  Lemma nth_zip_with_cons_in_bounds : forall (A : Type) (xs : list A) (yss : list (list A))
    (i : nat) (v : A),
    (i < List.length xs)%nat -> (i < List.length yss)%nat ->
    List.nth i (zip_with cons xs yss) [] =
    List.cons (List.nth i xs v) (List.nth i yss []).
  Proof.
    intros A xs yss i v Hxs Hyss.
    revert xs yss Hxs Hyss.
    induction i as [|i IH]; intros xs yss Hxs Hyss.
    - destruct xs as [|x xs]; [simpl in Hxs; nia |].
      destruct yss as [|ys yss]; [simpl in Hyss; nia |].
      simpl. reflexivity.
    - destruct xs as [|x xs]; [simpl in Hxs; nia |].
      destruct yss as [|ys yss]; [simpl in Hyss; nia |].
      simpl. apply IH; simpl in Hxs, Hyss; nia.
  Qed.


  (** When the index is out of bounds, [nth] of [zip_with cons] returns []. *)
  Lemma nth_zip_with_cons_overflow {A : Type} (xs : list A) (yss : list (list A)) (i : nat) :
    (List.length xs <= i \/ List.length yss <= i)%nat ->
    List.nth i (zip_with cons xs yss) [] = [].
  Proof.
    intros Hle.
    apply List.nth_overflow.  (* use nth_overflow from Rocq stdlib *)
    rewrite zip_with_length.
    destruct Hle as [Hle | Hle].
    - refine (Nat.le_trans _ _ _ (Nat.le_min_l _ _) Hle).
    - refine (Nat.le_trans _ _ _ (Nat.le_min_r _ _) Hle).
  Qed.


  (** [nth] on [map] returns the default when the index is out of bounds. *)
  Lemma nth_map_out_of_bounds : forall (A B : Type) (f : A -> B) (l : list A) (n : nat) (d : B),
    List.length l <= n -> List.nth n (List.map f l) d = d.
  Proof.
    induction l as [|a l' IH]; intros n d Hle; simpl.
    - destruct n; reflexivity.
    - destruct n as [|n']; simpl.
      + simpl in Hle. exfalso. apply (Nat.nle_succ_0 _ Hle).
      + apply IH. apply le_S_n. exact Hle.
  Qed.


  (** [combine l []] is always []. *)
  Lemma combine_nil_r : forall (A B : Type) (l : list A), List.combine l (@nil B) = [].
  Proof.
    induction l; simpl; auto.
  Qed.


  (** Dot product with an empty vector is zero. *)
  Lemma dot_product_nil : forall (v : list R), dot_product v [] = 0.
  Proof.
    intros v. unfold dot_product. rewrite combine_nil_r. simpl. reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Key lemma: transpose_list swaps element access under nth         *)
  (* ----------------------------------------------------------------- *)

  (* The unrestricted statement is false for ragged inputs such as [[]; [a]].
     The intended transpose law is the rectangular, in-bounds form below. *)

  (** Key lemma: transpose swaps indices under [nth] for rectangular matrices. *)
  Lemma nth_transpose_swap : forall (L : list (list R)) (i j : nat),
    L <> [] ->
    (forall xs ys : list R, In xs L -> In ys L -> List.length xs = List.length ys) ->
    (j < List.length L)%nat ->
    (i < List.length (List.hd [] L))%nat ->
    List.nth j (List.nth i (transpose_list L) ([] : list R)) 0 =
    List.nth i (List.nth j L ([] : list R)) 0.
  Proof.
    intros L i j HLne Hrect Hj Hi.
    generalize dependent i. generalize dependent j.
    induction L as [|xsh L' IH]; [congruence | ].
    destruct L' as [|xssth L'']; [|].
    - (* singleton case: L = [xsh] *)
      intros j Hj i Hi. cbn in Hj, Hi. cbn.
      assert (Hj0 : j = 0%nat) by nia.
      subst j; cbn. apply nth_0_map_singleton.
    - (* multi-row case: L = xsh :: xssth :: L'' *)
      intros j Hj i Hi. cbn in Hj, Hi. cbn [hd] in Hi. cbn [hd].
      assert (Hne_tail : xssth :: L'' <> []) by congruence.
      assert (Hrect_tail : forall xs ys : list R,
        In xs (xssth :: L'') -> In ys (xssth :: L'') -> length xs = length ys).
      { intros xs ys Hx Hy. apply Hrect; [right; exact Hx | right; exact Hy]. }
      assert (Hlen_eq : length xsh = length xssth).
      { apply Hrect with (xs := xsh) (ys := xssth);
        [left; reflexivity | right; left; reflexivity]. }
      assert (Hi_xssth : i < length xssth).
      { apply (Nat.lt_le_trans _ _ _ Hi). rewrite Hlen_eq. apply Nat.le_refl. }
      specialize (IH Hne_tail Hrect_tail).
      simpl (transpose_list (xsh :: xssth :: L'')).
      (* shared helper lemmas *)
      assert (Hpos_xsh : 0 < length xsh) by nia.
      assert (Hpos_xssth : 0 < length (xssth :: L'')) by (cbn; nia).
      assert (Hrect_full : forall xs ys : list R,
        In xs (xsh :: xssth :: L'') -> In ys (xsh :: xssth :: L'') ->
        length xs = length ys /\ 0 < length xs).
      { intros xs0 ys0 Hx Hy. split; [apply Hrect; assumption | ].
        assert (Hlen_xs : length xs0 = length xsh).
        { apply Hrect with (ys := xsh); [exact Hx | left; reflexivity]. }
        rewrite Hlen_xs; exact Hpos_xsh. }
      assert (Hi_transpose : i < length (transpose_list (xssth :: L''))).
      { pose proof (transpose_length (A := R) (xssth :: L'') xsh
          Hpos_xssth Hpos_xsh
          (fun xs Hx ys Hy => Hrect_full xs ys Hx Hy)) as Htlen.
        rewrite <- Htlen; exact Hi. }
      erewrite nth_zip_with_cons_in_bounds with (v := 0);
        [| exact Hi | exact Hi_transpose].
      destruct j as [|j'].
      + (* j = 0 *)
        cbn. reflexivity.
      + (* j = S j' *)
        assert (Hj'_bound : j' < length (xssth :: L'')) by (cbn; lia).
        cbn. destruct L'' as [|zssth L''']; cbn.
        * (* inner single row *)
          assert (Hj'0 : j' = 0%nat) by (cbn in Hj'_bound; lia).
          subst j'. cbn. apply nth_0_map_singleton.
        * (* inner multi-row *)
          apply IH. exact Hj'_bound. exact Hi_xssth.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Key lemma: dot_product v1 v2 = sum(λk. v1[k]*v2[k]) when        *)
  (*  |v1| = |v2| = |elements|                                         *)
  (* ----------------------------------------------------------------- *)

  Lemma dot_product_eq_sum : forall (v1 v2 : list R),
    List.length v1 = List.length (elements (s := Node)) ->
    List.length v2 = List.length (elements (s := Node)) ->
    dot_product v1 v2 =
    sum (fun k => list_lookup 0 elements v1 k * list_lookup 0 elements v2 k).
  Proof.
    intros v1 v2 Hlen1 Hlen2.
    pose proof (elements_nodup (s := Node)) as Hnd.
    rewrite <- (@list_lookup_tabulate R 0 v1 Hnd Hlen1) at 1.
    rewrite <- (@list_lookup_tabulate R 0 v2 Hnd Hlen2) at 1.
    apply dot_product_map_eq_sum.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Key lemma: of_list (mul_list L1 L2) r c =                        *)
  (*             dot_product(row_r(L1), col_c(L2))                     *)
  (* ----------------------------------------------------------------- *)

  Lemma of_list_mul_list_as_dot_product : forall (L1 L2 : list (list R)) (r c : Node),
    of_list (mul_list L1 L2) r c =
    dot_product (list_lookup [] elements L1 r)
                (list_lookup [] elements (transpose_list L2) c).
  Proof.
    intros L1 L2 r c.
    unfold of_list, mul_list.
    rewrite list_lookup_nth_R.
    rewrite list_lookup_nth_list.
    rewrite list_lookup_nth_list.
    rewrite list_lookup_nth_list.
    set (i := index_of r).
    set (j := index_of c).
    set (f := fun (row : list R) =>
      List.map (fun col : list R => dot_product row col) (transpose_list L2)).
    destruct (Nat.lt_ge_cases i (List.length L1)) as [Hlt | Hge].
    - (* i in bounds *)
      rewrite (nth_map_inbound (list R) (list R) f L1 i [] [] Hlt).
      unfold f.
      set (row_r := List.nth i L1 []).
      set (g := fun (col : list R) => dot_product row_r col).
      destruct (Nat.lt_ge_cases j (List.length (transpose_list L2))) as [Hlt2 | Hge2].
      + (* j in bounds *)
        rewrite (nth_map_inbound (list R) R g (transpose_list L2) j ([] : list R) 0 Hlt2).
        unfold g, row_r. reflexivity.
      + (* j out of bounds *)
        rewrite (List.nth_overflow (transpose_list L2) (n := j) ([] : list R)) by exact Hge2.
        assert (HL : List.nth j (List.map g (transpose_list L2)) 0 = 0).
        { apply (nth_map_out_of_bounds (list R) R g (transpose_list L2) j 0 Hge2). }
        assert (HR : dot_product row_r [] = 0).
        { apply dot_product_nil. }
        rewrite HL. symmetry. exact HR.
    - (* i out of bounds *)
      rewrite (List.nth_overflow L1 (n := i) ([] : list R)) by exact Hge.
      rewrite (nth_map_out_of_bounds (list R) (list R) f L1 i ([] : list R) Hge).
      unfold dot_product. simpl. destruct j; reflexivity.
  Qed.

  (* Helper: for a list where all rows have equal length, transpose has that many rows *)
  Lemma transpose_list_length_eq_n : forall (L : list (list R)) (m : nat),
    L <> [] ->
    (forall row, In row L -> length row = m) ->
    length (transpose_list L) = m.
  Proof.
    intros L m Hne Hrow.
    destruct L as [|xsh L']; [congruence |]; clear Hne.
    revert xsh Hrow. induction L' as [|xssth L'' IH]; intros xsh Hrow.
    - simpl (transpose_list [xsh]). rewrite List.length_map. apply Hrow. left; reflexivity.
    - change (transpose_list (xsh :: xssth :: L''))
        with (zip_with cons xsh (transpose_list (xssth :: L''))).
      rewrite zip_with_length.
      assert (Hxsh_len : length xsh = m).
      { apply Hrow. left; reflexivity. }
      assert (Hxssth_len : length xssth = m).
      { apply Hrow. right; left; reflexivity. }
      assert (IH_eq := IH xssth (fun row Hin => Hrow row (in_cons xsh row (xssth :: L'') Hin))).
      replace (length (transpose_list (xssth :: L''))) with m by (symmetry; exact IH_eq).
      rewrite Hxsh_len. apply Nat.min_id.
  Qed.

  (* Helper: each row of transpose_list L has length = length L (rectangular, nonempty) *)
  Lemma transpose_row_len_eq : forall (L : list (list R)),
    L <> [] ->
    (forall xs ys : list R, In xs L -> In ys L -> length xs = length ys) ->
    forall row, In row (transpose_list L) -> length row = length L.
  Proof.
    induction L as [|xsh L' IH]; [congruence |]; intros Hne Hrect row Hin.
    destruct L' as [|xssth L''].
    - (* L = [xsh]: transpose = map (fun y => [y]) xsh *)
      cbn in Hin. apply in_map_iff in Hin. destruct Hin as (x & Hx & Hin_xsh).
      subst row. cbn. reflexivity.
    - (* L = xsh :: xssth :: L'': transpose = zip_with cons xsh T *)
      change (transpose_list (xsh :: xssth :: L''))
        with (zip_with cons xsh (transpose_list (xssth :: L''))) in Hin.
      (* Any element of zip_with is at some index k *)
      apply (In_nth (A := list R) _ _ ([] : list R)) in Hin.
      destruct Hin as (k & Hk & Hrow).
      assert (Hk_xsh : (k < length xsh)%nat).
      { rewrite zip_with_length in Hk. apply (Nat.lt_le_trans _ _ _ Hk (Nat.le_min_l _ _)). }
      assert (Hk_T : (k < length (transpose_list (xssth :: L'')))%nat).
      { rewrite zip_with_length in Hk. apply (Nat.lt_le_trans _ _ _ Hk (Nat.le_min_r _ _)). }
      subst row.
      rewrite (nth_zip_with_cons_in_bounds R xsh (transpose_list (xssth :: L'')) k (0 : R) Hk_xsh Hk_T).
      simpl. f_equal.
      (* Need: length (nth k (transpose_list (xssth :: L'')) []) = length (xssth :: L'') *)
      pose proof (nth_In (A := list R) (transpose_list (xssth :: L'')) ([] : list R) Hk_T) as Hin_T.
      apply IH with (row := nth k (transpose_list (xssth :: L'')) []); auto.
      + intro Hc; congruence.
      + intros xs ys Hx Hy. apply Hrect; [right; exact Hx | right; exact Hy].
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  list_lookup_transpose: transpose swaps key lookup                 *)
  (* ----------------------------------------------------------------- *)

  Lemma list_lookup_transpose : forall (L : list (list R)) (c y : Node),
    (forall xs ys : list R, In xs L -> In ys L -> length xs = length ys) ->
    list_lookup 0 elements (list_lookup [] elements (transpose_list L) c) y =
    list_lookup 0 elements (list_lookup [] elements L y) c.
  Proof.
    intros L c y Hrect.
    rewrite !list_lookup_nth_gen.
    set (i := index_of c). set (j := index_of y).
    destruct (Nat.eq_dec (length L) 0) as [Hlen0 | Hlen_pos].
    { (* L is empty *)
      assert (HL : L = []) by (destruct L; cbn in Hlen0; [reflexivity | nia]).
      subst L. cbn. destruct j; destruct i; reflexivity. }
    (* L is nonempty *)
    assert (HLne : L <> []) by (intro H; subst L; cbn in Hlen_pos; nia).
    set (h := List.hd ([] : list R) L).
    set (m := length h).
    assert (Hrow_len : forall row, In row L -> length row = m).
    { intros row Hin. unfold m, h. apply Hrect with (ys := List.hd ([] : list R) L).
      - exact Hin.
      - destruct L; [congruence | left; reflexivity]. }
    assert (HlenT : length (transpose_list L) = m).
    { apply (transpose_list_length_eq_n L m HLne). exact Hrow_len. }
    destruct (Nat.lt_ge_cases i m) as [Hi_lt | Hi_ge].
    { (* i < m: row index in bounds for transpose_list L *)
      destruct (Nat.lt_ge_cases j (length L)) as [Hj_lt | Hj_ge].
      { (* both in bounds: use nth_transpose_swap *)
        apply nth_transpose_swap;
          [exact HLne | exact Hrect | exact Hj_lt | unfold m, h; exact Hi_lt]. }
      { (* j out of bounds: LHS = 0, RHS = 0 *)
        apply eq_trans with (y := 0).
        2: { apply eq_sym. apply List.nth_overflow.
             assert (Hnth_j_L : nth j L ([] : list R) = ([] : list R)).
             { apply List.nth_overflow. exact Hj_ge. }
             rewrite Hnth_j_L. cbn. nia. }
        apply List.nth_overflow.
        assert (Hlen_row : length (nth i (transpose_list L) ([] : list R)) = length L).
        { eapply transpose_row_len_eq; eauto. eapply nth_In; rewrite HlenT; eauto. }
        eapply Nat.le_trans; [| exact Hj_ge].
        rewrite <- Hlen_row. apply Nat.le_refl. } }
    { (* i out of bounds: nth i (transpose_list L) = [] *)
      assert (Hnth_i_T : nth i (transpose_list L) ([] : list R) = ([] : list R)).
      { apply List.nth_overflow. rewrite HlenT. exact Hi_ge. }
      rewrite Hnth_i_T.
      (* Prove nth j [] 0 = 0 by destructing j, then handle RHS *)
      destruct j as [|j'].
      { simpl. apply eq_sym. apply List.nth_overflow.
        assert (Hlen_row_j : length (nth 0 L ([] : list R)) = m).
        { apply Hrow_len. eapply nth_In; eauto; nia. }
        rewrite Hlen_row_j. exact Hi_ge. }
      { simpl.
        destruct (Nat.lt_ge_cases (S j') (length L)) as [Hj_lt' | Hj_ge'].
        { apply eq_sym. apply List.nth_overflow.
          assert (Hlen_row_j : length (nth (S j') L ([] : list R)) = m).
          { apply Hrow_len. eapply nth_In; eauto. }
          rewrite Hlen_row_j. exact Hi_ge. }
        { assert (Hnth_j_L : nth (S j') L ([] : list R) = ([] : list R)).
          { apply List.nth_overflow. exact Hj_ge'. }
          rewrite Hnth_j_L. destruct i; reflexivity. } } }
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Main proof: of_list_mul_list_gen                                  *)
  (* ----------------------------------------------------------------- *)

  Lemma of_list_mul_list_gen : forall (L1 L2 : list (list R)) (r c : Node),
    List.length L1 = List.length (elements (s := Node)) ->
    (forall row : list R, In row L1 ->
      List.length row = List.length (elements (s := Node))) ->
    List.length L2 = List.length (elements (s := Node)) ->
    (forall row : list R, In row L2 ->
      List.length row = List.length (elements (s := Node))) ->
    of_list (mul_list L1 L2) r c = matrix_mul (of_list L1) (of_list L2) r c.
  Proof.
    intros L1 L2 r c HlenL1 HrowL1 HlenL2 HrowL2.
    set (n := List.length (elements (s := Node))).
    assert (HrectL1 : forall xs ys, In xs L1 -> In ys L1 -> length xs = length ys).
    { intros xs ys Hx Hy. rewrite (HrowL1 _ Hx), (HrowL1 _ Hy). reflexivity. }
    assert (HrectL2 : forall xs ys, In xs L2 -> In ys L2 -> length xs = length ys).
    { intros xs ys Hx Hy. rewrite (HrowL2 _ Hx), (HrowL2 _ Hy). reflexivity. }
    rewrite (of_list_mul_list_as_dot_product L1 L2 r c).
    unfold matrix_mul, of_list.
    rewrite (dot_product_eq_sum
               (list_lookup [] elements L1 r)
               (list_lookup [] elements (transpose_list L2) c)).
    - f_equal. apply FunctionalExtensionality.functional_extensionality. intro y.
      rewrite (list_lookup_transpose L2 c y); [reflexivity | exact HrectL2].
    - (* Prove: length (list_lookup [] elements L1 r) = n *)
      rewrite list_lookup_nth_gen.
      set (i := index_of r).
      assert (Hi : (i < List.length L1)%nat).
      { subst i. rewrite HlenL1. apply index_of_bound. }
      apply nth_In with (d := [] : list R) in Hi as Hin.
      apply HrowL1 in Hin. unfold n. exact Hin.
    - (* Prove: length (list_lookup [] elements (transpose_list L2) c) = n *)
      rewrite list_lookup_nth_gen.
      set (i := index_of c).
      (* Need: length (nth i (transpose_list L2) []) = n *)
      (* Lemma: for n×n rectangular L2, each row of transpose has length = length L2 = n *)
      assert (Htranspose_nth_len : length (nth i (transpose_list L2) []) = length L2).
      { (* i is in-bounds for transpose_list L2 since L2 is n×n *)
        assert (L2_nonempty : L2 <> []).
        { intro H; subst L2. cbn in HlenL2.
          pose proof (elements_complete (s := Node) r) as Hin_r.
          destruct (elements (s := Node)); cbn in *; [inversion Hin_r | nia]. }
        assert (Hi_bound : (i < length (transpose_list L2))%nat).
        { rewrite (transpose_list_length_eq_n L2 n L2_nonempty HrowL2). subst i. apply index_of_bound. }
        pose proof (nth_In (A := list R) (transpose_list L2) ([] : list R) Hi_bound) as Hin_row.
        apply transpose_row_len_eq with (row := nth i (transpose_list L2) []).
        - exact L2_nonempty.
        - exact HrectL2.
        - exact Hin_row. }
      rewrite Htranspose_nth_len. rewrite HlenL2. unfold n. reflexivity.
  Qed.

    (** Base case: [pow_list (to_list m) 0 = to_list I]. *)

Lemma pow_list_base : forall (m : Matrix),
    pow_list (to_list m) 0 = to_list I.
  Proof.
    intros m.
    unfold pow_list, to_list, I.
    reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Helper lemmas: to_list and pow_list preserve the square shape     *)
  (* ----------------------------------------------------------------- *)

  Lemma to_list_length : forall (m : Matrix),
    length (to_list m) = length (elements (s := Node)).
  Proof.
    intros m. unfold to_list. rewrite List.length_map. reflexivity.
  Qed.

    (** Every row of [to_list m] has length [|elements|]. *)

Lemma to_list_row_length : forall (m : Matrix) (row : list R),
    In row (to_list m) -> length row = length (elements (s := Node)).
  Proof.
    intros m row Hin.
    unfold to_list in Hin.
    rewrite in_map_iff in Hin. destruct Hin as (r & Hrow & Hin_r).
    subst row. rewrite List.length_map. reflexivity.
  Qed.

    (** [mul_list] preserves the outer length (number of rows). *)

Lemma mul_list_length : forall (la lb : list (list R)),
    length (mul_list la lb) = length la.
  Proof.
    intros la lb. unfold mul_list. rewrite List.length_map. reflexivity.
  Qed.

    (** For a square matrix, the transpose has the same dimension. *)

Lemma transpose_list_length_square : forall (lb : list (list R)),
    length lb = length (elements (s := Node)) ->
    (forall row, In row lb -> length row = length (elements (s := Node))) ->
    length (transpose_list lb) = length (elements (s := Node)).
  Proof.
    intros lb Hlen Hrow.
    destruct lb as [|lbh lbt].
    - (* lb = [] *)
      simpl. rewrite <- Hlen. reflexivity.
    - (* lb is nonempty *)
      apply (transpose_list_length_eq_n (lbh :: lbt) (length (elements (s := Node)))).
      + congruence.
      + exact Hrow.
  Qed.

    (** Rows of [mul_list] have the right length when the second argument is square. *)

Lemma mul_list_row_length : forall (la lb : list (list R)) (row : list R),
    length lb = length (elements (s := Node)) ->
    (forall row', In row' lb -> length row' = length (elements (s := Node))) ->
    In row (mul_list la lb) -> length row = length (elements (s := Node)).
  Proof.
    intros la lb row Hlen_lb Hrow_lb Hin.
    unfold mul_list in Hin.
    rewrite in_map_iff in Hin. destruct Hin as (r & Hrow & Hin_r).
    subst row. rewrite List.length_map.
    apply transpose_list_length_square; auto.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Helper: mul_list preserves square shape                           *)
  (* ----------------------------------------------------------------- *)

  Lemma mul_list_square : forall (la lb : list (list R)),
    length la = length (elements (s := Node)) ->
    (forall row, In row la -> length row = length (elements (s := Node))) ->
    length lb = length (elements (s := Node)) ->
    (forall row, In row lb -> length row = length (elements (s := Node))) ->
    length (mul_list la lb) = length (elements (s := Node))
    /\ (forall row, In row (mul_list la lb) -> length row = length (elements (s := Node))).
  Proof.
    intros la lb Hlena Hrowa Hlenb Hrowb.
    split.
    - rewrite mul_list_length. exact Hlena.
    - intros row Hin. eapply mul_list_row_length; eauto.
  Qed.

    (** [pow_list] of a tabulated matrix stays square for any exponent. *)

Lemma pow_list_square : forall (m : Matrix) (n : nat),
    length (pow_list (to_list m) n) = length (elements (s := Node))
    /\ (forall row, In row (pow_list (to_list m) n) -> length row = length (elements (s := Node))).
  Proof.
    intros m n. revert m. induction n as [|n IH]; intros m.
    - (* n = 0 *)
      split.
      + unfold pow_list. rewrite List.length_map. reflexivity.
      + intros row Hin. unfold pow_list in Hin.
        rewrite in_map_iff in Hin. destruct Hin as (r & Hrow & Hin_r).
        subst row. rewrite List.length_map. reflexivity.
    - (* n = S n *)
      destruct (IH m) as (IHlen & IHrow).
      split.
      + unfold pow_list. fold pow_list. rewrite mul_list_length. apply to_list_length.
      + intros row Hin.
        unfold pow_list in Hin. fold pow_list in Hin.
        eapply mul_list_row_length; eauto.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  pow = pow_fun  (mathematical = efficient, unary case)             *)
  (* ----------------------------------------------------------------- *)

  Lemma pow_pow_fun_eqv : forall (m : Matrix) (n : nat) c d,
    pow m n c d = pow_fun m n c d.
  Proof.
    intros m n c d. revert c d.
    induction n as [|n IH]; intros c d.
    - (* n = 0 *)
      unfold pow, pow_fun.
      rewrite pow_list_base.
      symmetry. apply of_list_to_list.
    - (* n = S n *)
      unfold pow. fold pow.
      unfold pow_fun, pow_list. fold pow_fun. fold pow_list.
      destruct (pow_list_square m n) as (Hpow_len & Hpow_row).
      rewrite (of_list_mul_list_gen (to_list m) (pow_list (to_list m) n) c d
        (to_list_length m) (to_list_row_length m) Hpow_len Hpow_row).
      replace (of_list (to_list m)) with m.
      2: { apply FunctionalExtensionality.functional_extensionality; intro r.
           apply FunctionalExtensionality.functional_extensionality; intro c0.
           symmetry. apply of_list_to_list. }
      replace (of_list (pow_list (to_list m) n)) with (pow m n).
      2: { apply FunctionalExtensionality.functional_extensionality; intro r.
           apply FunctionalExtensionality.functional_extensionality; intro c0.
           rewrite (IH r c0). unfold pow_fun. reflexivity. }
      reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  pow via N.to_nat = powN  (unary = binary exponentiation)          *)
  (* ----------------------------------------------------------------- *)

  (* When NoDup l and d ∉ l, all I y d = 0, so the fold is 0.         *)
  Lemma fold_I_zero : forall (l : list Node) (c d : Node) (m : Matrix),
    (forall y, In y l -> y <> d) ->
    fold_right (fun y acc =>
      m c y * (match fin_eq_dec y d with left _ => 1 | right _ => 0 end) + acc) 0 l = 0.
  Proof.
    induction l as [|h t IH]; intros c d m Hnin; simpl.
    - reflexivity.
    - assert (h <> d) by (apply Hnin; simpl; auto).
      destruct (fin_eq_dec h d) as [Heq | Hneq].
      + exfalso. apply H. exact Heq.
      + simpl. rewrite IH.
        setoid_rewrite mulr0. 
        rewrite add0r. reflexivity. 
        intros y Hy. apply Hnin. simpl. auto.
  Qed.

    (** Right identity: multiplying by the identity matrix on the right. *)

  Lemma matrix_mul_I_r : forall (m : Matrix) (c d : Node),
    matrix_mul m I c d = m c d.
  Proof.
    intros m c d.
    unfold matrix_mul, sum, I.
    pose proof (elements_nodup (s := Node)) as Hnd.
    pose proof (elements_complete (s := Node) d) as Hin_d.
    induction elements as [|k ks IH].
    - (* elements = []: impossible since d ∈ elements *)
      inversion Hin_d.
    - (* elements = k :: ks *)
      simpl. simpl in Hin_d.
      inversion Hnd as [|? ? Hnin Hnd']; subst; clear Hnd.
      destruct Hin_d as [Hkd | Hin_ks].
      + (* k = d *)
        subst k.
        destruct (fin_eq_dec d d) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
        rewrite mulr1.
        assert (Hfold0 : fold_right
          (fun x y => (m c x * (if fin_eq_dec x d then 1 else 0) + y)) 0 ks = 0).
        { apply fold_I_zero with (c := c) (d := d) (m := m).
          intros y Hy. intro Heq. apply Hnin. rewrite <- Heq. exact Hy. }
        transitivity (m c d + 0).
        { f_equal. exact Hfold0. }
        { apply addr0. }
      + (* k ≠ d *)
        destruct (fin_eq_dec k d) as [Heq | Hneq].
        * (* k = d but also k ≠ d from Hin_d, contradiction with NoDup *)
          exfalso. apply Hnin. subst k. exact Hin_ks.
        * (* genuine k ≠ d case *)
          setoid_rewrite mulr0. rewrite add0r.
          apply (IH Hnd' Hin_ks).
  Qed.

    (** Left identity: multiplying by the identity matrix on the left. *)

  Lemma matrix_mul_I_l : forall (m : Matrix) (c d : Node),
    matrix_mul I m c d = m c d.
  Proof.
    intros m c d.
    unfold matrix_mul, sum, I.
    pose proof (elements_nodup (s := Node)) as Hnd.
    pose proof (elements_complete (s := Node) c) as Hin_c.
    induction elements as [|k ks IH].
    - (* elements = []: impossible since c ∈ elements *)
      inversion Hin_c.
    - (* elements = k :: ks *)
      simpl. simpl in Hin_c.
      inversion Hnd as [|? ? Hnin Hnd']; subst; clear Hnd.
      destruct Hin_c as [Hkc | Hin_ks].
      + (* k = c *)
        subst k.
        destruct (fin_eq_dec c c) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
        rewrite mul1r.
        assert (Hfold0 : fold_right
          (fun x y => ((if fin_eq_dec c x then 1 else 0) * m x d + y)) 0 ks = 0).
        { clear IH.
          induction ks as [|h t IHks]; simpl; [reflexivity |].
          inversion Hnd' as [|? ? Hnin' Hnd'']; subst.
          assert (h <> c).
          { intro Heq. apply Hnin. left. rewrite Heq. reflexivity. }
          destruct (fin_eq_dec c h) as [Heq | Hneq]; [exfalso; apply H; rewrite Heq; reflexivity |].
          simpl. setoid_rewrite mul0r. rewrite add0r.
          apply IHks.
          - intro Hin. apply Hnin. right. exact Hin.
          - exact Hnd''. }
        transitivity (m c d + 0).
        { f_equal. exact Hfold0. }
        { apply addr0. }
      + (* k ≠ c *)
        destruct (fin_eq_dec c k) as [Heq | Hneq].
        * (* k = c but c ≠ k from Hin_c, contradiction with NoDup *)
          exfalso. apply Hnin. subst k. exact Hin_ks.
        * (* genuine k ≠ c case *)
          setoid_rewrite mul0r. rewrite add0r.
          apply (IH Hnd' Hin_ks).
  Qed.

    (** [ (a+b)+(c+d) = (a+c)+(b+d) ] — a useful regrouping identity. *)

  Lemma add_swap_mid : forall (a b c d : R),
    (a + b) + (c + d) = (a + c) + (b + d).
  Proof.
    intros a b c d.
    rewrite (addA a b (c + d)).
    rewrite <- (addA b c d) at 1.
    rewrite (addC b c).
    rewrite (addA c b d).
    rewrite <- (addA a c (b + d)).
    reflexivity.
  Qed.

    (** Sum distributes over pointwise addition: [sum (f+g) = sum f + sum g]. *)

  Lemma sum_add : forall (f g : Node -> R),
    sum (fun x => f x + g x) = sum f + sum g.
  Proof.
    intros f g.
    unfold sum.
    induction elements as [|a l IH]; simpl.
    - rewrite addr0. reflexivity.
    - transitivity ((f a + g a) + (fold_right (fun x y => f x + y) 0 l
        + fold_right (fun x y => g x + y) 0 l)).
      + f_equal. exact IH.
      + apply add_swap_mid.
  Qed.

    (** Extensionality of [sum]: equal functions have equal sums. *)

  Lemma sum_ext : forall (f g : Node -> R),
    (forall x, f x = g x) -> sum f = sum g.
  Proof.
    intros f g Heq.
    unfold sum.
    induction elements as [|a l IH]; simpl.
    - reflexivity.
    - rewrite Heq. f_equal. exact IH.
  Qed.

    (** Right-distributivity of sum over multiplication: [(sum f) * k = sum (λx. f x * k)]. *)

  Lemma sum_mul_r : forall (f : Node -> R) (k : R),
    sum f * k = sum (fun x => f x * k).
  Proof.
    intros f k.
    unfold sum.
    induction elements as [|a l IH]; simpl.
    - (* []: 0 * k = 0 *)
      setoid_rewrite mul0r. reflexivity.
    - (* a :: l *)
      setoid_rewrite mulDr.
      f_equal. exact IH.
  Qed.

    (** Left-distributivity of sum over multiplication: [k * (sum f) = sum (λx. k * f x)]. *)

  Lemma sum_mul_l : forall (k : R) (f : Node -> R),
    k * sum f = sum (fun x => k * f x).
  Proof. 
    intros f k.
    unfold sum.
    induction elements as [|a l IH]; simpl.
    - (* []: 0 * k = 0 *)
      setoid_rewrite mulr0. reflexivity.
    - (* a :: l *)
      setoid_rewrite mulDl.
      f_equal. exact IH.
  Qed.
  
  (* Generalized sum_add: works on any list, not just elements *)
  Lemma fold_right_add_gen : forall (g h : Node -> R) (l : list Node),
    fold_right (fun x acc => g x + acc) 0 l + fold_right (fun x acc => h x + acc) 0 l =
    fold_right (fun x acc => (g x + h x) + acc) 0 l.
  Proof.
    intros g h l.
    induction l as [|a l' IH]; simpl.
    - rewrite addr0. reflexivity.
    - transitivity ((g a + h a) + (fold_right (fun x acc => g x + acc) 0 l'
        + fold_right (fun x acc => h x + acc) 0 l')).
      { apply add_swap_mid. }
      f_equal. exact IH.
  Qed.

  (* Interchange of double sums over a semiring.                          *)
  Lemma sum_interchange : forall (f : Node -> Node -> R),
    sum (fun y => sum (fun z => f y z)) = 
    sum (fun z => sum (fun y => f y z)).
  Proof.
    intros f.
    unfold sum.
    assert (forall l1 l2,
      fold_right (fun y acc => fold_right (fun z acc' => f y z + acc') 0 l2 + acc) 0 l1 =
      fold_right (fun z acc => fold_right (fun y acc' => f y z + acc') 0 l1 + acc) 0 l2) as H.
    { induction l1 as [|a l1' IH]; intros l2.
      - simpl.
        induction l2 as [|b l2' IH2]; simpl; [reflexivity |].
        rewrite add0r. apply IH2.
      - simpl. rewrite IH.
        transitivity (fold_right (fun z acc => (f a z
          + fold_right (fun y acc' => f y z + acc') 0 l1') + acc) 0 l2).
        + apply (fold_right_add_gen (fun z => f a z)
            (fun z => fold_right (fun y acc' => f y z + acc') 0 l1') l2).
        + simpl. reflexivity. }
    apply H.
  Qed.

    (** Matrix multiplication is associative. *)

  Lemma matrix_mul_assoc : forall (a b c : Matrix) (r d : Node),
    matrix_mul (matrix_mul a b) c r d = matrix_mul a (matrix_mul b c) r d.
  Proof.
    intros a b c r d.
    unfold matrix_mul.
    transitivity (sum (fun y => sum (fun z => a r z * b z y * c y d))).
    - apply sum_ext. intro y. apply sum_mul_r.
    - rewrite sum_interchange.
      apply sum_ext. intro z.
      setoid_rewrite sum_mul_l.
      apply sum_ext. intro y. apply mulA.
  Qed.

    (** Exponent law: [pow m (a+b) = matrix_mul (pow m a) (pow m b)]. *)

  Lemma pow_add : forall (m : Matrix) (a b : nat) (c d : Node),
    pow m (a + b) c d = matrix_mul (pow m a) (pow m b) c d.
  Proof.
    intros m a b c d. revert c d. revert b.
    induction a as [|a IH]; intros b c d.
    - simpl. unfold pow at 2. symmetry. apply matrix_mul_I_l.
    - simpl plus. unfold pow. fold pow.
      assert (Heq : pow m (a + b) = matrix_mul (pow m a) (pow m b)).
      { apply FunctionalExtensionality.functional_extensionality; intro r.
        apply FunctionalExtensionality.functional_extensionality; intro c0.
        apply IH. }
      rewrite Heq.
      symmetry. apply matrix_mul_assoc.
  Qed.

    (** Binary exponentiation agrees with linear exponentiation for matrices. *)

  Lemma pow_pos_correct : forall (m : Matrix) (p : positive) (c d : Node),
    pow m (Pos.to_nat p) c d = pow_pos m p c d.
  Proof.
    intros m p c d. revert c d.
    induction p as [p IH | p IH |].
    - (* xI p *)
      intros c d.
      rewrite Pos2Nat.inj_xI.
      replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by nia.
      (* Goal: pow m (S (n+n)) c d = pow_pos m p~1 c d *)
      simpl (pow m (S (Pos.to_nat p + Pos.to_nat p))).
      (* Goal: (m * pow m (n+n)) c d = (m * (pow_pos m p * pow_pos m p)) c d *)
      f_equal.
      replace (pow m (Pos.to_nat p + Pos.to_nat p))
        with (matrix_mul (pow m (Pos.to_nat p)) (pow m (Pos.to_nat p))).
      2: { apply FunctionalExtensionality.functional_extensionality; intro r.
           apply FunctionalExtensionality.functional_extensionality; intro s.
           symmetry; apply pow_add. }
      replace (pow m (Pos.to_nat p)) with (pow_pos m p).
      2: { apply FunctionalExtensionality.functional_extensionality; intro r.
           apply FunctionalExtensionality.functional_extensionality; intro s.
           symmetry; apply IH. }
      reflexivity.
    - (* xO p *)
      intros c d.
      rewrite Pos2Nat.inj_xO.
      replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by nia.
      (* Goal: pow m (n+n) c d = pow_pos m p~0 c d *)
      rewrite pow_add.
      (* Goal: (pow m n * pow m n) c d = (pow_pos m p * pow_pos m p) c d *)
      f_equal.
      replace (pow m (Pos.to_nat p)) with (pow_pos m p).
      2: { apply FunctionalExtensionality.functional_extensionality; intro r.
           apply FunctionalExtensionality.functional_extensionality; intro s.
           symmetry; apply IH. }
      reflexivity.
    - (* xH *)
      intros c d.
      simpl. apply matrix_mul_I_r.
  Qed.

    (** [pow m (N.to_nat n) = powN m n] — unary = binary exponentiation. *)

  Lemma pow_powN_eqv : forall (m : Matrix) (n : N) c d,
    pow m (N.to_nat n) c d = powN m n c d.
  Proof.
    intros m n c d.
    destruct n as [|p].
    - (* N0 *) reflexivity.
    - (* Npos p *)
      unfold powN.
      apply pow_pos_correct.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  pow_fun via N.to_nat = powN_fun                                  *)
  (* ----------------------------------------------------------------- *)

  (* Helper: pow_pos_list preserves square shape                        *)
  Lemma pow_pos_list_square : forall (m : Matrix) (p : positive),
    length (pow_pos_list (to_list m) p) = length (elements (s := Node))
    /\ (forall row, In row (pow_pos_list (to_list m) p) -> length row = length (elements (s := Node))).
  Proof.
    induction p as [p IH | p IH |].
    - (* xI p *)
      simpl (pow_pos_list (to_list m) (p~1)).
      destruct IH as (IHlen & IHrow).
      destruct (mul_list_square (pow_pos_list (to_list m) p) (pow_pos_list (to_list m) p)
        IHlen IHrow IHlen IHrow) as (Hlen_PP & Hrow_PP).
      split.
      { rewrite mul_list_length. apply to_list_length. }
      { intros row Hin. eapply mul_list_row_length; eauto. }
    - (* xO p *)
      simpl (pow_pos_list (to_list m) (p~0)).
      destruct IH as (IHlen & IHrow).
      apply (mul_list_square (pow_pos_list (to_list m) p) (pow_pos_list (to_list m) p)
        IHlen IHrow IHlen IHrow).
    - (* xH *)
      split.
      { apply to_list_length. }
      { apply to_list_row_length. }
  Qed.

  (* Helper: of_list is injective on square lists                       *)
  Lemma of_list_inj_square : forall (L1 L2 : list (list R)),
    length L1 = length (elements (s := Node)) ->
    (forall row, In row L1 -> length row = length (elements (s := Node))) ->
    length L2 = length (elements (s := Node)) ->
    (forall row, In row L2 -> length row = length (elements (s := Node))) ->
    (forall r c, of_list L1 r c = of_list L2 r c) ->
    L1 = L2.
  Proof.
    intros L1 L2 Hlen1 Hrow1 Hlen2 Hrow2 Heq.
    pose proof (elements_nodup (s := Node)) as Hnd.
    assert (Hlen_row1 : forall r, length (list_lookup [] elements L1 r) = length (elements (s := Node))).
    { intros r. rewrite list_lookup_nth_gen.
      assert (Hbound : (index_of r < length L1)%nat).
      { rewrite Hlen1. apply index_of_bound. }
      apply nth_In with (d := [] : list R) in Hbound as Hin.
      apply Hrow1. exact Hin. }
    assert (Hlen_row2 : forall r, length (list_lookup [] elements L2 r) = length (elements (s := Node))).
    { intros r. rewrite list_lookup_nth_gen.
      assert (Hbound : (index_of r < length L2)%nat).
      { rewrite Hlen2. apply index_of_bound. }
      apply nth_In with (d := [] : list R) in Hbound as Hin.
      apply Hrow2. exact Hin. }
    assert (Hlookup_eq : forall r, list_lookup [] elements L1 r = list_lookup [] elements L2 r).
    { intro r.
      pose proof (list_lookup_tabulate R 0 (list_lookup [] elements L1 r) Hnd (Hlen_row1 r)) as Htab1.
      pose proof (list_lookup_tabulate R 0 (list_lookup [] elements L2 r) Hnd (Hlen_row2 r)) as Htab2.
      rewrite <- Htab1, <- Htab2.
      f_equal. apply FunctionalExtensionality.functional_extensionality. intro c.
      unfold of_list in Heq. apply Heq. }
    pose proof (list_lookup_tabulate (list R) ([] : list R) L1 Hnd Hlen1) as HtabL1.
    pose proof (list_lookup_tabulate (list R) ([] : list R) L2 Hnd Hlen2) as HtabL2.
    rewrite <- HtabL1, <- HtabL2.
    f_equal. apply FunctionalExtensionality.functional_extensionality. intro r.
    apply Hlookup_eq.
  Qed.

  (* Helper: of_list (pow_pos_list (to_list m) p) = pow_pos m p          *)
  Lemma of_list_pow_pos_list : forall (m : Matrix) (p : positive) (c d : Node),
    of_list (pow_pos_list (to_list m) p) c d = pow_pos m p c d.
  Proof.
    induction p as [p IH | p IH |].
    - (* xI p *)
      intros c d.
      simpl (pow_pos_list (to_list m) (p~1)).
      destruct (pow_pos_list_square m p) as (Hlen_P & Hrow_P).
      destruct (mul_list_square (pow_pos_list (to_list m) p) (pow_pos_list (to_list m) p)
        Hlen_P Hrow_P Hlen_P Hrow_P) as (Hlen_PP & Hrow_PP).
      rewrite (of_list_mul_list_gen (to_list m)
        (mul_list (pow_pos_list (to_list m) p) (pow_pos_list (to_list m) p)) c d
        (to_list_length m) (to_list_row_length m) Hlen_PP Hrow_PP).
      f_equal.
      replace (of_list (to_list m)) with m.
      2: { apply FunctionalExtensionality.functional_extensionality; intro r.
           apply FunctionalExtensionality.functional_extensionality; intro c0.
           symmetry. apply of_list_to_list. }
      f_equal.
      replace (of_list (mul_list (pow_pos_list (to_list m) p) (pow_pos_list (to_list m) p)))
        with (matrix_mul (of_list (pow_pos_list (to_list m) p))
              (of_list (pow_pos_list (to_list m) p))).
      2: { apply FunctionalExtensionality.functional_extensionality; intro r.
           apply FunctionalExtensionality.functional_extensionality; intro c0.
           symmetry. apply (of_list_mul_list_gen
             (pow_pos_list (to_list m) p) (pow_pos_list (to_list m) p) r c0
             Hlen_P Hrow_P Hlen_P Hrow_P). }
      replace (of_list (pow_pos_list (to_list m) p)) with (pow_pos m p).
      2: { apply FunctionalExtensionality.functional_extensionality; intro r.
           apply FunctionalExtensionality.functional_extensionality; intro c0.
           symmetry. apply IH. }
      reflexivity.
    - (* xO p *)
      intros c d.
      simpl (pow_pos_list (to_list m) (p~0)).
      destruct (pow_pos_list_square m p) as (Hlen_P & Hrow_P).
      rewrite (of_list_mul_list_gen (pow_pos_list (to_list m) p) (pow_pos_list (to_list m) p) c d
        Hlen_P Hrow_P Hlen_P Hrow_P).
      f_equal.
      replace (of_list (pow_pos_list (to_list m) p)) with (pow_pos m p).
      2: { apply FunctionalExtensionality.functional_extensionality; intro r.
           apply FunctionalExtensionality.functional_extensionality; intro c0.
           symmetry. apply IH. }
      reflexivity.
    - (* xH *)
      intros c d.
      apply of_list_to_list.
  Qed.

  (* List-level analogue of pow_pos_correct.
     Only holds for square lists (same length and row length as elements). *)

  (* Generalized squareness: pow_list preserves square shape for any square L *)
  Lemma pow_list_square_gen : forall (L : list (list R)) (n : nat),
    length L = length (elements (s := Node)) ->
    (forall row, In row L -> length row = length (elements (s := Node))) ->
    length (pow_list L n) = length (elements (s := Node))
    /\ (forall row, In row (pow_list L n) -> length row = length (elements (s := Node))).
  Proof.
    intros L n HlenL HrowL. revert L HlenL HrowL.
    induction n as [|n IH]; intros L HlenL HrowL; simpl.
    - split.
      { unfold pow_list. rewrite List.length_map. reflexivity. }
      { intros row Hin. unfold pow_list in Hin.
        rewrite in_map_iff in Hin. destruct Hin as (r & Hrow & Hin_r).
        subst row. rewrite List.length_map. reflexivity. }
    - destruct (IH L HlenL HrowL) as (IHlen & IHrow).
      apply (mul_list_square L (pow_list L n) HlenL HrowL IHlen IHrow).
  Qed.

  (* Generalized squareness: pow_pos_list preserves square shape for any square L *)
  Lemma pow_pos_list_square_gen : forall (L : list (list R)) (p : positive),
    length L = length (elements (s := Node)) ->
    (forall row, In row L -> length row = length (elements (s := Node))) ->
    length (pow_pos_list L p) = length (elements (s := Node))
    /\ (forall row, In row (pow_pos_list L p) -> length row = length (elements (s := Node))).
  Proof.
    intros L p HlenL HrowL. revert L HlenL HrowL.
    induction p as [p IH | p IH |]; intros L HlenL HrowL.
    - (* xI p *)
      simpl (pow_pos_list L (p~1)).
      destruct (IH L HlenL HrowL) as (IHlen & IHrow).
      destruct (mul_list_square (pow_pos_list L p) (pow_pos_list L p) IHlen IHrow IHlen IHrow)
        as (Hlen_PP & Hrow_PP).
      split.
      { rewrite mul_list_length. exact HlenL. }
      { intros row Hin. eapply mul_list_row_length; eauto. }
    - (* xO p *)
      simpl (pow_pos_list L (p~0)).
      destruct (IH L HlenL HrowL) as (IHlen & IHrow).
      apply (mul_list_square (pow_pos_list L p) (pow_pos_list L p) IHlen IHrow IHlen IHrow).
    - (* xH *)
      split; [exact HlenL | exact HrowL].
  Qed.

  (* Bridge: of_list (pow_list L n) = pow (of_list L) n for square L *)
  Lemma of_list_pow_list_gen : forall (L : list (list R)) (n : nat) (r c : Node),
    length L = length (elements (s := Node)) ->
    (forall row, In row L -> length row = length (elements (s := Node))) ->
    of_list (pow_list L n) r c = pow (of_list L) n r c.
  Proof.
    intros L n r c HlenL HrowL.
    revert L HlenL HrowL r c.
    induction n as [|n IH]; intros L HlenL HrowL r c; simpl.
    - unfold pow, pow_list.
      change (List.map (fun r : Node => List.map (fun c0 : Node => I r c0) elements) elements)
        with (to_list I).
      apply of_list_to_list.
    - unfold pow. fold pow.
      destruct (pow_list_square_gen L n HlenL HrowL) as (Hsq_len & Hsq_row).
      rewrite (of_list_mul_list_gen L (pow_list L n) r c HlenL HrowL Hsq_len Hsq_row).
      f_equal. f_equal.
      apply FunctionalExtensionality.functional_extensionality; intro x.
      apply FunctionalExtensionality.functional_extensionality; intro y.
      apply (IH L HlenL HrowL x y).
  Qed.

  (* Bridge: of_list (pow_pos_list L p) = pow_pos (of_list L) p for square L *)
  Lemma of_list_pow_pos_list_gen : forall (L : list (list R)) (p : positive) (r c : Node),
    length L = length (elements (s := Node)) ->
    (forall row, In row L -> length row = length (elements (s := Node))) ->
    of_list (pow_pos_list L p) r c = pow_pos (of_list L) p r c.
  Proof.
    intros L p r c HlenL HrowL. revert L HlenL HrowL r c.
    induction p as [p IH | p IH |]; intros L HlenL HrowL r c.
    - (* xI p *)
      simpl (pow_pos_list L (p~1)).
      destruct (pow_pos_list_square_gen L p HlenL HrowL) as (Hlen_P & Hrow_P).
      destruct (mul_list_square (pow_pos_list L p) (pow_pos_list L p) Hlen_P Hrow_P Hlen_P Hrow_P)
        as (Hlen_PP & Hrow_PP).
      rewrite (of_list_mul_list_gen L (mul_list (pow_pos_list L p) (pow_pos_list L p)) r c
        HlenL HrowL Hlen_PP Hrow_PP).
      f_equal.
      replace (of_list (mul_list (pow_pos_list L p) (pow_pos_list L p)))
        with (matrix_mul (of_list (pow_pos_list L p)) (of_list (pow_pos_list L p))).
      2: { apply FunctionalExtensionality.functional_extensionality; intro x.
           apply FunctionalExtensionality.functional_extensionality; intro y.
           symmetry. apply (of_list_mul_list_gen
             (pow_pos_list L p) (pow_pos_list L p) x y Hlen_P Hrow_P Hlen_P Hrow_P). }
      replace (of_list (pow_pos_list L p)) with (pow_pos (of_list L) p).
      2: { apply FunctionalExtensionality.functional_extensionality; intro x.
           apply FunctionalExtensionality.functional_extensionality; intro y.
           symmetry. apply (IH L HlenL HrowL x y). }
      reflexivity.
    - (* xO p *)
      simpl (pow_pos_list L (p~0)).
      destruct (pow_pos_list_square_gen L p HlenL HrowL) as (Hlen_P & Hrow_P).
      rewrite (of_list_mul_list_gen (pow_pos_list L p) (pow_pos_list L p) r c
        Hlen_P Hrow_P Hlen_P Hrow_P).
      f_equal.
      replace (of_list (pow_pos_list L p)) with (pow_pos (of_list L) p).
      2: { apply FunctionalExtensionality.functional_extensionality; intro x.
           apply FunctionalExtensionality.functional_extensionality; intro y.
           symmetry. apply (IH L HlenL HrowL x y). }
      reflexivity.
    - (* xH *)
      reflexivity.
  Qed.

    (** List-level analogue of [pow_pos_correct]: binary = linear list exponentiation (for square lists). *)

  Lemma pow_list_powN_list_eqv : forall (L : list (list R)) (p : positive),
    length L = length (elements (s := Node)) ->
    (forall row, In row L -> length row = length (elements (s := Node))) ->
    pow_list L (Pos.to_nat p) = powN_list L (Npos p).
  Proof.
    intros L p HlenL HrowL.
    unfold powN_list.
    pose proof (pow_list_square_gen L (Pos.to_nat p) HlenL HrowL) as [Hlen1 Hrow1].
    pose proof (pow_pos_list_square_gen L p HlenL HrowL) as [Hlen2 Hrow2].
    apply of_list_inj_square; try assumption.
    intros r c.
    rewrite of_list_pow_list_gen; [| exact HlenL | exact HrowL].
    rewrite pow_pos_correct.
    rewrite of_list_pow_pos_list_gen; [| exact HlenL | exact HrowL].
    reflexivity.
  Qed.

    (** [pow_fun] via [N.to_nat] equals [powN_fun]. *)

  Lemma pow_fun_powN_fun_eqv : forall (m : Matrix) (n : N) c d,
    pow_fun m (N.to_nat n) c d = powN_fun m n c d.
  Proof.
    intros m n c d.
    destruct n as [|p].
    - (* N0 *)
      unfold pow_fun, powN_fun.
      simpl (N.to_nat N0).
      unfold pow_list. unfold powN_list.
      reflexivity.
    - (* Npos p *)
      unfold pow_fun, powN_fun, powN_list.
      simpl (N.to_nat (Npos p)).
      rewrite (of_list_pow_pos_list m p c d).
      rewrite <- (pow_pos_correct m p c d).
      symmetry. apply pow_pow_fun_eqv.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Main theorem: mathematical binary = efficient binary             *)
  (* ----------------------------------------------------------------- *)

  Lemma powN_eqv : forall (n : N) (m : Matrix) c d,
    powN m n c d = powN_fun m n c d.
  Proof.
    intros n m c d.
    rewrite <- pow_powN_eqv.
    rewrite pow_pow_fun_eqv.
    apply pow_fun_powN_fun_eqv.
  Qed.

End Matrix.