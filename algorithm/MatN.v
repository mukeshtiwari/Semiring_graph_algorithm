(* ================================================================= *)
(*  Matrix Operations over a Finite Semiring (list-based)             *)
(*  File: MatN.v                                                     *)
(*  Matrix is `Node -> Node -> R` where `Node` is a finite type      *)
(*  and `R` is a semiring.  This file provides both functional       *)
(*  (high‑level) and list‑based (computationally efficient) matrix   *)
(*  operations together with proofs of their equivalence.            *)
(* ================================================================= *)

From Stdlib Require Import List Utf8
  BinNatDef 
  Lia PeanoNat PArith.
From Semiring Require Import OrelN Structures
  PathN.
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
    {Node : FinType.type}.


  (** A matrix over semiring [R] indexed by finite type [Node]. *)
  Let Matrix {R : Semiring.type} := @OrelN.Matrix Node R.

  (* returns the cth row of m *)
  Definition row {R : Semiring.type} (m : Matrix) (c : Node) : Node -> R := 
    fun d => m c d.

  (* returns the cth column of m *)
  Definition col {R : Semiring.type} (m : Matrix) (c : Node) : Node -> R :=
    fun d => m d c.

  (* zero matrix, additive identity of plus *)
  Definition zeroM {R : Semiring.type} : @Matrix R := 
    fun _ _ => 0.

  (* identity matrix, mulitplicative identity of mul *)
  (* Idenitity Matrix *)
  Definition I {R : Semiring.type} : @Matrix R := 
    fun (c d : Node) =>
    match fin_eq_dec c d with 
    | left _ => 1
    | right _ => 0 
    end.

  
  (* transpose the matrix m *)
  Definition transpose {R : Semiring.type} (m : @Matrix R) : @Matrix R  := 
    fun (c d : Node) => m d c.

  

  (* pointwise addition to two matrices *)
  Definition matrix_add {R : Semiring.type} (m₁ m₂ : @Matrix R) : @Matrix R :=
    fun c d => (m₁ c d + m₂ c d).

 

  (** Finite sum of a [Node]-indexed family over the semiring. *)
  Definition sum {R : Semiring.type} (f : Node -> R) : R :=
    List.fold_right (fun x y => f x + y) 0 elements.

  (** Extensionality of [sum]: equal functions have equal sums. *)
  Lemma sum_ext {R : Semiring.type} : forall (f g : Node -> R),
    (forall x, f x = g x) -> sum f = sum g.
  Proof.
    intros f g Heq.
    unfold sum.
    induction elements as [|a l IH]; simpl.
    - reflexivity.
    - rewrite Heq. f_equal. exact IH.
  Qed.

  (* generalised matrix multiplication *)
  Definition matrix_mul {R : Semiring.type}
    (m₁ m₂ : @Matrix R) : @Matrix R:=
    fun (c d : Node) => 
      sum (fun y => (m₁ c y * m₂ y d)).

  (* ----------------------------------------------------------------- *)
  (*  Matrix exponentiation                                             *)
  (* ----------------------------------------------------------------- *)

  Local Infix "+M" := matrix_add (at level 50, only parsing).


  (** Linear matrix exponentiation: [pow m n = m * m * ... * m] (n times). *)
  Fixpoint pow {R : Semiring.type} (m : @Matrix R) (n : nat) : @Matrix R :=
    match n with 
    | 0%nat => I 
    | S n' => matrix_mul m (pow m n')
    end.


  (** Linear matrix exponentiation: [pow m n = m * m * ... * m] (n times). *)
  Fixpoint pow_pos {R : Semiring.type} (e : @Matrix R) (n : positive) : @Matrix R :=
    match n with
    | xH => e
    | xO p => let ret := pow_pos e p in matrix_mul ret ret
    | xI p => 
      let reta := pow_pos e p in 
      let retb := matrix_mul reta reta in
      matrix_mul e retb
    end.


  (** Matrix exponentiation for [N] (binary for positive, identity for zero). *)
  Definition powN {R : Semiring.type} (e : @Matrix R) (n : N) : @Matrix R :=
    match n with
    | N0 => I
    | Npos p => pow_pos e p 
    end.

  (* ----------------------------------------------------------------- *)
  (*  Scalar exponentiation and partial sums                           *)
  (* ----------------------------------------------------------------- *)

  Fixpoint scalar_pow {R : Semiring.type} (a : R) (n : nat) : R :=
    match n with 
    | O => 1
    | S n' => a * scalar_pow a n'
    end.


  (** Scalar geometric series: [1 + a + a² + ... + aⁿ]. *)
  Fixpoint scalar_geom_sum {R : Semiring.type} (a : R) (n : nat) : R :=
    match n with
    | O => 1
    | S n' => (scalar_geom_sum a n') + scalar_pow a n
    end.


  (** Matrix geometric series: [I + M + M² + ... + Mⁿ]. *)
  Fixpoint geom_sum {R : Semiring.type} (m : @Matrix R) (n : nat) : @Matrix R :=
    match n with
    | O => I 
    | S n' => (geom_sum m n') +M (pow m n)
    end.

  (* ----------------------------------------------------------------- *)
  (*  Efficient list-based matrix operations                           *)
  (* ----------------------------------------------------------------- *)

  (* Dot product of two lists *)
  Definition dot_product {R : Semiring.type} (v1 v2 : list R) : R :=
    fold_left add (map (fun '(x, y) => mul x y) 
    (combine v1 v2)) zero.


  (* Matrix multiplication (list-based) *)
  Definition mul_list {R : Semiring.type} (la lb : list (list R)) : list (list R) :=
    let lbT := transpose_list lb in
    map (fun row =>
      map (fun col => dot_product row col) lbT) la.


  (** Linear matrix exponentiation: [pow m n = m * m * ... * m] (n times). *)
  Fixpoint pow_list {R : Semiring.type} (m : list (list R)) 
    (n : nat) : list (list R) :=
    match n with 
    | 0%nat => List.map (fun r => List.map (fun c => I r c) elements) elements 
    | S n' => mul_list m (pow_list m n')
    end.


  (** Linear matrix exponentiation: [pow m n = m * m * ... * m] (n times). *)
  Fixpoint pow_pos_list {R : Semiring.type} (e : list (list R)) 
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
  Definition powN_list {R : Semiring.type} (e : list (list R)) (n : N) : list (list R) :=
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
  Definition to_list {R : Semiring.type} (m : Node -> Node -> R) : list (list R) :=
    List.map (fun r => List.map (fun c => m r c) elements) elements.


  (** Reconstruct a functional matrix from a list-of-lists representation. *)
  Definition of_list {R : Semiring.type} (me : list (list R)) : @Matrix R :=
    fun r c =>
      let row := list_lookup [] elements me r in
      list_lookup 0 elements row c.


  (** Functional matrix multiplication via the list-based implementation. *)
  Definition mul_fun {R : Semiring.type} (m₁ m₂ : Node -> Node -> R) : Node -> Node -> R :=
    of_list (mul_list (to_list m₁) (to_list m₂)).


  (** Functional matrix exponentiation via the list-based implementation. *)
  Definition pow_fun {R : Semiring.type} (m : Node -> Node -> R) (n : nat)
    : Node -> Node -> R :=
    of_list (pow_list (to_list m) n).


  (** Matrix exponentiation for [N] (binary for positive, identity for zero). *)
  Definition powN_fun {R : Semiring.type} (m : Node -> Node -> R) (n : N)
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
  Lemma of_list_to_list {R : Semiring.type} : forall (m : @Matrix R) (r c : Node),
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
  Lemma list_lookup_nth_list {R : Semiring.type} (l : list (list R)) (k : Node) :
    list_lookup [] elements l k = List.nth (index_of k) l [].
  Proof. apply list_lookup_nth_gen. Qed.


  (** Specialization of [list_lookup_nth_gen] for scalar lists. *)
  Lemma list_lookup_nth_R {R : Semiring.type} (l : list R) (k : Node) :
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

  Lemma fold_left_add_acc {R : Semiring.type} : forall (l : list R) (a : R),
    List.fold_left add l a = a + List.fold_right add 0 l.
  Proof.
    induction l as [|x l' IH]; intros a; simpl.
    - rewrite addr0. reflexivity.
    - rewrite IH.
      (* (a + x) + fold_right add 0 l' = a + (x + fold_right add 0 l') *)
      rewrite addA. reflexivity.
  Qed.


  (** [fold_left add] over a list equals [fold_right add 0]. *)
  Lemma fold_left_add_fold_right_add {R : Semiring.type} : forall (l : list R),
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

  Lemma fold_right_add_map {R : Semiring.type} : forall (h : Node -> R),
    List.fold_right add 0 (List.map h elements) =
    List.fold_right (fun x y => h x + y) 0 elements.
  Proof.
    intro h.
    induction elements as [|e es IH]; simpl; [reflexivity |].
    f_equal. apply IH.
  Qed.


  (** Dot product of tabulated vectors equals the sum of pointwise products. *)
  Lemma dot_product_map_eq_sum {R : Semiring.type} : forall (f g : Node -> R),
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
  Lemma dot_product_nil {R : Semiring.type} : forall (v : list R), dot_product v [] = 0.
  Proof.
    intros v. unfold dot_product. rewrite combine_nil_r. simpl. reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Key lemma: transpose_list swaps element access under nth         *)
  (* ----------------------------------------------------------------- *)

  (* The unrestricted statement is false for ragged inputs such as [[]; [a]].
     The intended transpose law is the rectangular, in-bounds form below. *)

  (** Key lemma: transpose swaps indices under [nth] for rectangular matrices. *)
  Lemma nth_transpose_swap {R : Semiring.type} : forall (L : list (list R)) (i j : nat),
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

  Lemma dot_product_eq_sum {R : Semiring.type} : forall (v1 v2 : list R),
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

  Lemma of_list_mul_list_as_dot_product {R : Semiring.type} : forall (L1 L2 : list (list R)) (r c : Node),
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
  Lemma transpose_list_length_eq_n {R : Semiring.type} : forall (L : list (list R)) (m : nat),
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
  Lemma transpose_row_len_eq {R : Semiring.type} : forall (L : list (list R)),
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

  Lemma list_lookup_transpose {R : Semiring.type} : forall (L : list (list R)) (c y : Node),
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

  Lemma of_list_mul_list_gen {R : Semiring.type} : forall (L1 L2 : list (list R)) (r c : Node),
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
    - apply sum_ext. intro y.
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

  Lemma pow_list_base {R : Semiring.type} : forall (m : @Matrix R),
    pow_list (to_list m) 0 = to_list I.
  Proof.
    intros m.
    unfold pow_list, to_list, I.
    reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Helper lemmas: to_list and pow_list preserve the square shape     *)
  (* ----------------------------------------------------------------- *)

  Lemma to_list_length {R : Semiring.type} : forall (m : @Matrix R),
    length (to_list m) = length (elements (s := Node)).
  Proof.
    intros m. unfold to_list. rewrite List.length_map. reflexivity.
  Qed.

    (** Every row of [to_list m] has length [|elements|]. *)

  Lemma to_list_row_length {R : Semiring.type} : forall (m : @Matrix R) (row : list R),
    In row (to_list m) -> length row = length (elements (s := Node)).
  Proof.
    intros m row Hin.
    unfold to_list in Hin.
    rewrite in_map_iff in Hin. destruct Hin as (r & Hrow & Hin_r).
    subst row. rewrite List.length_map. reflexivity.
  Qed.

    (** [mul_list] preserves the outer length (number of rows). *)

  Lemma mul_list_length {R : Semiring.type} : forall (la lb : list (list R)),
    length (mul_list la lb) = length la.
  Proof.
    intros la lb. unfold mul_list. rewrite List.length_map. reflexivity.
  Qed.

    (** For a square matrix, the transpose has the same dimension. *)

Lemma transpose_list_length_square {R : Semiring.type} : forall (lb : list (list R)),
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

  Lemma mul_list_row_length {R : Semiring.type} : forall (la lb : list (list R)) (row : list R),
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

  Lemma mul_list_square {R : Semiring.type} : forall (la lb : list (list R)),
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

  Lemma pow_list_square {R : Semiring.type} : forall (m : @Matrix R) (n : nat),
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
      + cbn. rewrite mul_list_length. apply to_list_length.
      + intros row Hin.
        cbn in Hin. 
        eapply mul_list_row_length; eauto.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  pow = pow_fun  (mathematical = efficient, unary case)             *)
  (* ----------------------------------------------------------------- *)

  Lemma pow_pow_fun_eqv {R : Semiring.type} : forall (m : @Matrix R) (n : nat) c d,
    pow m n c d = pow_fun m n c d.
  Proof.
    intros m n c d. revert c d.
    induction n as [|n IH]; intros c d.
    - (* n = 0 *)
      unfold pow, pow_fun.
      rewrite pow_list_base.
      symmetry. apply of_list_to_list.
    - (* n = S n *)
      unfold pow. fold (@pow R).
      unfold pow_fun, pow_list. fold (@pow_fun R). fold (@pow_list R).
      destruct (pow_list_square m n) as (Hpow_len & Hpow_row).
      rewrite (of_list_mul_list_gen (to_list m) (pow_list (to_list m) n) c d
        (to_list_length m) (to_list_row_length m) Hpow_len Hpow_row).
      unfold matrix_mul at 1.
      apply sum_ext. intro k.
      rewrite (of_list_to_list m c k).
      rewrite (IH k d).
      unfold pow_fun. reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  pow via N.to_nat = powN  (unary = binary exponentiation)          *)
  (* ----------------------------------------------------------------- *)

  (* When NoDup l and d ∉ l, all I y d = 0, so the fold is 0.         *)
  Lemma fold_I_zero {R : Semiring.type} : forall (l : list Node) (c d : Node) (m : @Matrix R),
    (forall y, In y l -> y <> d) ->
    fold_right (fun y acc =>
      m c y * (match fin_eq_dec y d with 
      | left _ => 1 
      | right _ => 0 end) + acc) 0 l = 0.
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

  Lemma matrix_mul_I_r {R : Semiring.type} : forall (m : @Matrix R) (c d : Node),
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

  Lemma matrix_mul_I_l {R : Semiring.type} : forall (m : @Matrix R) (c d : Node),
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

  Lemma add_swap_mid {R : Semiring.type} : forall (a b c d : R),
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

  Lemma sum_add {R : Semiring.type} : forall (f g : Node -> R),
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

    (** Right-distributivity of sum over multiplication: [(sum f) * k = sum (λx. f x * k)]. *)

  Lemma sum_mul_r {R : Semiring.type} : forall (f : Node -> R) (k : R),
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

  Lemma sum_mul_l {R : Semiring.type} : forall (k : R) (f : Node -> R),
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
  Lemma fold_right_add_gen {R : Semiring.type} : forall (g h : Node -> R) (l : list Node),
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
  Lemma sum_interchange {R : Semiring.type} : forall (f : Node -> Node -> R),
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

  Lemma matrix_mul_assoc {R : Semiring.type} : forall (a b c : @Matrix R) (r d : Node),
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

  Lemma pow_add {R : Semiring.type} : forall (m : @Matrix R) (a b : nat) (c d : Node),
    pow m (a + b) c d = matrix_mul (pow m a) (pow m b) c d.
  Proof.
    intros m a b c d. revert c d. revert b.
    induction a as [|a IH]; intros b c d.
    - simpl. unfold pow at 2. symmetry. apply matrix_mul_I_l.
    - simpl plus. cbn. 
      rewrite (matrix_mul_assoc m (pow m a) (pow m b) c d).
      unfold matrix_mul.
      apply sum_ext. intro k.
      f_equal.
      apply (IH b k d).
  Qed.

    (** Binary exponentiation agrees with linear exponentiation for matrices. *)

  Lemma pow_pos_correct {R : Semiring.type} : forall (m : @Matrix R) (p : positive) (c d : Node),
    pow m (Pos.to_nat p) c d = pow_pos m p c d.
  Proof.
    intros m p c d. revert c d.
    induction p as [p IH | p IH |].
    - (* xI p *)
      intros c d.
      rewrite Pos2Nat.inj_xI.
      replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by nia.
      simpl (pow m (S (Pos.to_nat p + Pos.to_nat p))).
      apply sum_ext. intro k.
      f_equal.
      rewrite (pow_add m (Pos.to_nat p) (Pos.to_nat p) k d).
      unfold matrix_mul.
      apply sum_ext. intro j.
      rewrite (IH k j).
      rewrite (IH j d).
      reflexivity.
    - (* xO p *)
      intros c d.
      rewrite Pos2Nat.inj_xO.
      replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by nia.
      rewrite pow_add.
      unfold matrix_mul.
      apply sum_ext. intro j.
      rewrite (IH c j).
      rewrite (IH j d).
      reflexivity.
    - (* xH *)
      intros c d.
      simpl. apply matrix_mul_I_r.
  Qed.

    (** [pow m (N.to_nat n) = powN m n] — unary = binary exponentiation. *)

  Lemma pow_powN_eqv {R : Semiring.type} : forall (m : @Matrix R) (n : N) c d,
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
  Lemma pow_pos_list_square {R : Semiring.type} : forall (m : @Matrix R) (p : positive),
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
  Lemma of_list_inj_square {R : Semiring.type} : forall (L1 L2 : list (list R)),
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
      apply map_ext. intro c.
      unfold of_list in Heq. apply Heq. }
    pose proof (list_lookup_tabulate (list R) ([] : list R) L1 Hnd Hlen1) as HtabL1.
    pose proof (list_lookup_tabulate (list R) ([] : list R) L2 Hnd Hlen2) as HtabL2.
    rewrite <- HtabL1, <- HtabL2.
    apply map_ext. intro r.
    apply Hlookup_eq.
  Qed.

  (* Helper: of_list (pow_pos_list (to_list m) p) = pow_pos m p          *)
  Lemma of_list_pow_pos_list {R : Semiring.type} : forall (m : @Matrix R) (p : positive) (c d : Node),
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
      unfold matrix_mul at 1.
      apply sum_ext. intro y.
      rewrite (of_list_to_list m c y).
      rewrite (of_list_mul_list_gen (pow_pos_list (to_list m) p)
        (pow_pos_list (to_list m) p) y d Hlen_P Hrow_P Hlen_P Hrow_P).
      f_equal.
      unfold matrix_mul.
      apply sum_ext. intro z.
      rewrite (IH y z).
      rewrite (IH z d).
      reflexivity.
    - (* xO p *)
      intros c d.
      simpl (pow_pos_list (to_list m) (p~0)).
      destruct (pow_pos_list_square m p) as (Hlen_P & Hrow_P).
      rewrite (of_list_mul_list_gen (pow_pos_list (to_list m) p) (pow_pos_list (to_list m) p) c d
        Hlen_P Hrow_P Hlen_P Hrow_P).
      unfold matrix_mul.
      apply sum_ext. intro z.
      rewrite (IH c z).
      rewrite (IH z d).
      reflexivity.
    - (* xH *)
      intros c d.
      apply of_list_to_list.
  Qed.

  (* List-level analogue of pow_pos_correct.
     Only holds for square lists (same length and row length as elements). *)

  (* Generalized squareness: pow_list preserves square shape for any square L *)
  Lemma pow_list_square_gen {R : Semiring.type} : forall (L : list (list R)) (n : nat),
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
  Lemma pow_pos_list_square_gen {R : Semiring.type} : forall (L : list (list R)) (p : positive),
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
  Lemma of_list_pow_list_gen {R : Semiring.type} : forall (L : list (list R)) (n : nat) (r c : Node),
    length L = length (elements (s := Node)) ->
    (forall row, In row L -> length row = length (elements (s := Node))) ->
    of_list (pow_list L n) r c = pow (of_list L) n r c.
  Proof.
    intros L n r c HlenL HrowL.
    revert L HlenL HrowL r c.
    induction n as [|n IH]; intros L HlenL HrowL r c; simpl.
    - unfold pow, pow_list.
      change (List.map (fun r : Node => List.map (fun c0 : Node => I r c0) elements) elements)
        with (to_list (@I R)).
      apply of_list_to_list.
    - unfold pow. fold (@pow R).
      destruct (pow_list_square_gen L n HlenL HrowL) as (Hsq_len & Hsq_row).
      rewrite (of_list_mul_list_gen L (pow_list L n) r c HlenL HrowL Hsq_len Hsq_row).
      unfold matrix_mul at 1.
      apply sum_ext. intro y.
      f_equal.
      apply (IH L HlenL HrowL y c).
  Qed.

  (* Bridge: of_list (pow_pos_list L p) = pow_pos (of_list L) p for square L *)
  Lemma of_list_pow_pos_list_gen {R : Semiring.type} : forall (L : list (list R)) (p : positive) (r c : Node),
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
      unfold matrix_mul at 1.
      apply sum_ext. intro y.
      f_equal.
      rewrite (of_list_mul_list_gen (pow_pos_list L p) (pow_pos_list L p) y c
        Hlen_P Hrow_P Hlen_P Hrow_P).
      unfold matrix_mul.
      apply sum_ext. intro z.
      rewrite (IH L HlenL HrowL y z).
      rewrite (IH L HlenL HrowL z c).
      reflexivity.
    - (* xO p *)
      simpl (pow_pos_list L (p~0)).
      destruct (pow_pos_list_square_gen L p HlenL HrowL) as (Hlen_P & Hrow_P).
      rewrite (of_list_mul_list_gen (pow_pos_list L p) (pow_pos_list L p) r c
        Hlen_P Hrow_P Hlen_P Hrow_P).
      unfold matrix_mul.
      apply sum_ext. intro z.
      rewrite (IH L HlenL HrowL r z).
      rewrite (IH L HlenL HrowL z c).
      reflexivity.
    - (* xH *)
      reflexivity.
  Qed.

    (** List-level analogue of [pow_pos_correct]: binary = linear list exponentiation (for square lists). *)

  Lemma pow_list_powN_list_eqv {R : Semiring.type} : forall (L : list (list R)) (p : positive),
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

  Lemma pow_fun_powN_fun_eqv {R : Semiring.type} : forall (m : @Matrix R) (n : N) c d,
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

  Lemma powN_eqv {R : Semiring.type} : forall (n : N) (m : @Matrix R) c d,
    powN m n c d = powN_fun m n c d.
  Proof.
    intros n m c d.
    rewrite <- pow_powN_eqv.
    rewrite pow_pow_fun_eqv.
    apply pow_fun_powN_fun_eqv.
  Qed.


  (** In a bounded semiring, adding [scalar_pow a n] to the geometric sum
      does not change it — the sum already contains [1] which absorbs everything. *)

  Lemma scalar_geom_sum_add_pow {R : BoundedSemiring.type} : 
    ∀ (n : nat) (a : R), scalar_geom_sum a n = 
    scalar_geom_sum a n + scalar_pow a n.
  Proof.
    intros n a.
    assert (Hgeom : scalar_geom_sum a n = 1).
    { induction n; cbn; [reflexivity | rewrite IHn; apply add_bound]. }
    rewrite Hgeom at 1 2.
    symmetry. apply add_bound.
  Qed.

  (** Recurrence: [scalar_geom_sum a (S n) = 1 + a * scalar_geom_sum a n]. *)

  Lemma scalar_geom_sum_S {R : Semiring.type} :
    forall (n : nat) (a : R), scalar_geom_sum a (S n) = 
      1 + a * scalar_geom_sum a n.
  Proof.
    induction n as [|n IH]; intros a.
    - cbn. rewrite mulr1. reflexivity.
    - cbn.
      rewrite (IH a) at 1.
      setoid_rewrite mulDl.
      rewrite <- addA.
      reflexivity.
  Qed.


  (** ** k-closed semirings                                                   *)

  (**
     Definition 6 (from https://cs.nyu.edu/~mohri/pub/jalc.pdf):  
     Let [k ≥ 0] be an integer. A semiring [(K, ⊕, ⊗, 0̄, 1̄)] is
     [k]-closed if:

       [∀ a ∈ K,   ⊕_{n=0}^{k+1} aⁿ  =  ⊕_{n=0}^{k} aⁿ.]

     In our notation, [scalar_geom_sum a n = ⊕_{p=0}^{n} aᵖ].
     Hence [k]-closedness is simply [scalar_geom_sum a (S k) = scalar_geom_sum a k]
     for every scalar [a].
   *)
  Definition k_closed {R : Semiring.type} (k : nat) : Prop :=
    forall a : R, scalar_geom_sum a k = scalar_geom_sum a (S k).

  (**
     When [k] is 0 the defining identity becomes
     [1 = 1 ⊕ a] for all [a], which is equivalent to
     [1 ⊕ a = 1] (boundedness).  Thus [0]-closed coincides with
     [BoundedSemiring] for commutative semirings.
   *)
  Lemma k_closed_0_equiv_add_one :
    forall {R : Semiring.type},
      k_closed (R := R) 0 <-> (forall a : R, add one a = one).
  Proof.
    split; intros H a.
    - (* k_closed 0 -> add 1 a = 1 *)
      pose proof (H a) as H0.
      cbn in H0.
      rewrite mulr1 in H0.
      rewrite <- H0.
      reflexivity.
    - (* (forall a, add 1 a = 1) -> k_closed 0 *)
      unfold k_closed.
      cbn.
      rewrite mulr1.
      rewrite (H a).
      reflexivity.
  Qed.

  (**
     The stabilization lemma (Lemma 4, ibid.): if the semiring is
     [k]-closed then the geometric sum stays constant beyond [k],
     i.e., [scalar_geom_sum a (n + k) = scalar_geom_sum a k]
     for every [n].
   *)
  Lemma scalar_geom_sum_stable {R : Semiring.type} 
    (q : nat) : 
    (forall w : R, scalar_geom_sum w q =  scalar_geom_sum w (S q)) -> 
    forall (n : nat) (a : R), 
    scalar_geom_sum a (n + q) = scalar_geom_sum a q.
  Proof.
    intros H n a.
    induction n as [|n IH].
    - (* n = 0 *) reflexivity.
    - (* n = S n *)
      assert (Hplus : ((S n) + q = S (n + q))%nat) by nia.
      rewrite Hplus.
      rewrite (scalar_geom_sum_S (n + q) a).
      rewrite IH.
      rewrite <- (scalar_geom_sum_S q a).
      rewrite (H a).
      reflexivity.
  Qed.

  (** In a bounded semiring every geometric sum collapses to [1],
      because [1 + x = 1] for any [x]. *)

  Lemma scalar_geom_sum_bounded {R : BoundedSemiring.type} :
    forall (n : nat) (a : R), scalar_geom_sum a n = 1.
  Proof.
    induction n as [|n IH]; intros a; cbn; [reflexivity |].
    rewrite IH. apply add_bound.
  Qed.

  (** Hence the sum is trivially stable at every index. *)

  Lemma scalar_geom_sum_bounded_stable {R : BoundedSemiring.type} : 
    forall (t q : nat) (a : R), 
    scalar_geom_sum a (t + q) = scalar_geom_sum a q.
  Proof.
    intros t q a.
    rewrite !scalar_geom_sum_bounded.
    reflexivity.
  Qed.

  Local Infix "*M" := matrix_mul (at level 40, only parsing).

  (** Left-distributivity of matrix multiplication over matrix addition:
      [m *M (a +M b) = m *M a +M m *M b]. *)

  (** Pointwise sum distributes: [sum (λy. f y + g y) = sum f + sum g]. *)


  Lemma matrix_mul_add_distr_l {R : Semiring.type} :
    forall (m a b : @Matrix R) (c d : Node),
    (matrix_mul m (matrix_add a b)) c d = 
    matrix_add (matrix_mul m a) (matrix_mul m b) c d.
  Proof.
    intros m a b c d.
    unfold matrix_mul, matrix_add.
    apply eq_trans with (sum (fun y => m c y * a y d + m c y * b y d)).
    - apply sum_ext. intro y. apply mulDl.
    - apply sum_add.
  Qed.

  (** Matrix analog of [scalar_geom_sum_S]:
      [geom_sum m (S t) = I + m * geom_sum m t]. *)

  Lemma matrix_add_unfold {R : Semiring.type} (A B : @Matrix R) 
    (c d : Node) :
    matrix_add A B c d = A c d + B c d.
  Proof. reflexivity. Qed.

  Lemma geom_sum_S {R : Semiring.type} :
    forall (t : nat) (m : @Matrix R) (c d : Node),
    geom_sum m (S t) c d = (I +M 
    (m *M (geom_sum m t))) c d.
  Proof.
    induction t as [|t IH]; intros m c d.
    - cbn. rewrite matrix_add_unfold. rewrite (matrix_mul_I_r m c d). reflexivity.
    - cbn [geom_sum].
      rewrite !matrix_add_unfold.
      rewrite (IH m c d) at 1.
      rewrite !matrix_add_unfold.
      apply (eq_trans (addA (I c d) (matrix_mul m (geom_sum m t) c d)
      (matrix_mul m (pow m (S t)) c d))).
      apply f_equal2 with (f := add); [reflexivity |].
      rewrite (matrix_mul_add_distr_l m (geom_sum m t) (pow m (S t)) c d).
      rewrite matrix_add_unfold.
      reflexivity.
  Qed.


  (* A * A^k = A^k * A : powers of a matrix commute with the matrix     *)
  Lemma geom_sum_stable {R : Semiring.type} (q : nat) : 
    forall (m : @Matrix R),
    (forall (c d : Node), 
      geom_sum m q c d = geom_sum m (S q) c d) -> 
    forall (t : nat)  (u v : Node), 
    geom_sum m (t + q) u v = geom_sum m q u v.
  Proof.
    intros m Hgeom t u v.
    revert u v.
    induction t as [|t IH]; intros u v.
    - (* t = 0 *) reflexivity.
    - (* t = S t *)
      assert (Hplus : ((S t) + q = S (t + q))%nat) by nia.
      rewrite Hplus.
      rewrite (geom_sum_S (t + q) m u v).
      rewrite (matrix_add_unfold I (m *M geom_sum m (t + q)) u v).
      assert (Hinner : (m *M geom_sum m (t + q)) u v = (m *M geom_sum m q) u v).
      { unfold matrix_mul, sum. apply sum_ext. intro y. rewrite (IH y v). reflexivity. }
      rewrite Hinner.
      rewrite <- (matrix_add_unfold I (m *M geom_sum m q) u v).
      rewrite <- (geom_sum_S q m u v).
      rewrite (Hgeom u v).
      reflexivity.
  Qed.

  (** Powers of a matrix commute with the matrix: [m * m^k = m^k * m].
      Proved by induction using associativity of matrix multiplication.
      Compare [matrix_exp_unary_comm_A] in [algorithm/Mat.v]. *)
  Lemma pow_comm {R : Semiring.type} (k : nat) (m : @Matrix R) (c d : Node) :
    (m *M pow m k) c d = (pow m k *M m) c d.
  Proof.
    revert c d.
    induction k as [|k IH]; intros c d.
    - cbn. rewrite (matrix_mul_I_r m c d). rewrite (matrix_mul_I_l m c d). reflexivity.
    - cbn [pow].
      (* Goal: (m *M (m *M pow m k)) c d = ((m *M pow m k) *M m) c d *)
      rewrite (matrix_mul_assoc m (pow m k) m c d).
      (* Goal: (m *M (m *M pow m k)) c d = (m *M (pow m k *M m)) c d *)
      unfold matrix_mul.
      apply sum_ext. intro y.
      apply (f_equal (fun t => m c y * t)). 
      apply IH.
  Qed.

  (** Right-distributivity of matrix multiplication over matrix addition:
      [(A +M B) *M C = (A *M C) +M (B *M C)]. *)
  Lemma matrix_mul_add_distr_r {R : Semiring.type} (A B C : @Matrix R) (c d : Node) :
    ((A +M B) *M C) c d = ((A *M C) +M (B *M C)) c d.
  Proof.
    unfold matrix_mul, matrix_add.
    apply eq_trans with (sum (fun y => A c y * C y d + B c y * C y d)).
    - apply sum_ext. intro y. apply mulDr.
    - apply sum_add.
  Qed.

  (* Right-sided version of [geom_sum_S]:
     [geom_sum m (S t) = I + geom_sum m t *M m]. *)
  Lemma geom_sum_S_right {R : Semiring.type} :
    forall (t : nat) (m : @Matrix R) (c d : Node),
    (geom_sum m (S t) c d) = (I +M (geom_sum m t *M m)) c d.
  Proof.
    induction t as [|t IH]; intros m c d.
    - cbn. rewrite !matrix_add_unfold. 
      rewrite (matrix_mul_I_r m c d). 
      rewrite (matrix_mul_I_l m c d). 
      reflexivity.
    - cbn [geom_sum].
      rewrite !matrix_add_unfold.
      rewrite (IH m c d) at 1.
      rewrite !matrix_add_unfold.
      apply (eq_trans (addA (I c d) (matrix_mul (geom_sum m t) m c d)
        (matrix_mul m (pow m (S t)) c d))).
      apply f_equal2 with (f := add); [reflexivity |].
      rewrite (pow_comm (S t) m c d).
      rewrite (matrix_mul_add_distr_r (geom_sum m t) (pow m (S t)) m c d).
      rewrite matrix_add_unfold.
      reflexivity.
  Qed.


  Lemma geom_sum_idem_recurrence {R : IdempotentSemiring.type} : 
    forall (n : nat) (m : @Matrix R) (c d : Node),  
    (m *M geom_sum m n +M geom_sum m n) c d = geom_sum m (S n) c d.
  Proof.
    (* Helper: in an idempotent semiring, x+y+x = x+y. *)
    assert (add_absorb : forall (x y : R), x + y + x = x + y).
    { intros x y. rewrite (addA x y x). rewrite (addC y x).
      rewrite <- (addA x x y). rewrite (add_idem x) at 1. reflexivity. }
    induction n as [|n IH]; intros m c d.
    - (* n = 0 *)
      cbn. rewrite !matrix_add_unfold. rewrite (matrix_mul_I_r m c d). apply addC.
    - (* n = S n *)
      cbn [geom_sum].
      rewrite !matrix_add_unfold.
      rewrite (matrix_mul_add_distr_l m (geom_sum m n) (pow m (S n)) c d).
      rewrite matrix_add_unfold.
      cbn [pow].
      (* Introduce abbreviations for readability *)
      set (A := matrix_mul m (geom_sum m n) c d).
      set (G := geom_sum m n c d).
      set (P := matrix_mul m (pow m n) c d).
      set (PP := matrix_mul m (matrix_mul m (pow m n)) c d).
      (* Extract the induction hypothesis as a scalar equality *)
      pose proof (IH m c d) as IHscalar.
      unfold matrix_add in IHscalar.
      cbn [geom_sum] in IHscalar.
      rewrite matrix_add_unfold in IHscalar.
      cbn [pow] in IHscalar.
      (* IHscalar : A + G = G + P *)
      (* Goal : A + PP + (G + P) = G + P + PP *)
      rewrite (addA A PP (G + P)).
      rewrite (addC PP (G + P)).
      rewrite <- (addA A (G + P) PP).
      rewrite <- (addA A G P).
      unfold A, G.
      rewrite IHscalar at 1.
      (* Goal now: (G' + P') + P' + PP = G' + P' + PP *)
      unfold P, PP.
      replace ((geom_sum m n c d + matrix_mul m (pow m n) c d)
               + matrix_mul m (pow m n) c d)
        with (geom_sum m n c d + matrix_mul m (pow m n) c d)
        by (rewrite (addA (geom_sum m n c d) (matrix_mul m (pow m n) c d)
                  (matrix_mul m (pow m n) c d));
            rewrite (add_idem (matrix_mul m (pow m n) c d)) at 1;
            reflexivity).
      reflexivity.
  Qed.


  (** In an idempotent semiring, [(m + I)^n = I + m + m² + ... + mⁿ].
      The idempotence collapses all the binomial-coefficient duplicates. 
  *)
  Lemma matrix_pow_idempotence {R : IdempotentSemiring.type} :
    forall (n : nat) (m : @Matrix R) (c d : Node),
    pow (m +M I) n c d = geom_sum m n c d.
  Proof.
    induction n as [|n IH]; intros m c d.
    - cbn. reflexivity.
    - cbn [pow].
      unfold matrix_mul.
      rewrite (sum_ext (fun y => (m +M I) c y * pow (m +M I) n y d)
        (fun y => m c y * geom_sum m n y d + I c y * geom_sum m n y d)).
      + rewrite sum_add.
        change (sum (fun y => m c y * geom_sum m n y d)) with (matrix_mul m (geom_sum m n) c d).
        change (sum (fun y => I c y * geom_sum m n y d)) with (matrix_mul I (geom_sum m n) c d).
        rewrite (matrix_mul_I_l (geom_sum m n) c d).
        rewrite <- matrix_add_unfold.
        apply geom_sum_idem_recurrence.
      + intro y.
        rewrite matrix_add_unfold.
        rewrite (IH m y d).
        apply mulDr.
  Qed.


  (** Bounded-semiring variant of [geom_sum_idem_recurrence]. *)
  Lemma geom_sum_idem_recurrence_bounded {R : BoundedSemiring.type} :
    forall (n : nat) (m : @Matrix R) (c d : Node),
      (m *M geom_sum m n +M geom_sum m n) c d = geom_sum m (S n) c d.
  Proof.
    induction n as [|n IH]; intros m c d.
    - cbn. rewrite !matrix_add_unfold. rewrite (matrix_mul_I_r m c d). apply addC.
    - cbn [geom_sum].
      rewrite !matrix_add_unfold.
      rewrite (matrix_mul_add_distr_l m (geom_sum m n) (pow m (S n)) c d).
      rewrite matrix_add_unfold.
      cbn [pow].
      set (A := matrix_mul m (geom_sum m n) c d).
      set (G := geom_sum m n c d).
      set (P := matrix_mul m (pow m n) c d).
      set (PP := matrix_mul m (matrix_mul m (pow m n)) c d).
      pose proof (IH m c d) as IHscalar.
      unfold matrix_add in IHscalar.
      cbn [geom_sum] in IHscalar.
      rewrite matrix_add_unfold in IHscalar.
      cbn [pow] in IHscalar.
      rewrite (addA A PP (G + P)).
      rewrite (addC PP (G + P)).
      rewrite <- (addA A (G + P) PP).
      rewrite <- (addA A G P).
      unfold A, G.
      rewrite IHscalar at 1.
      unfold P, PP.
      replace ((geom_sum m n c d + matrix_mul m (pow m n) c d)
               + matrix_mul m (pow m n) c d)
        with (geom_sum m n c d + matrix_mul m (pow m n) c d)
        by (rewrite (addA (geom_sum m n c d) (matrix_mul m (pow m n) c d)
                  (matrix_mul m (pow m n) c d));
            rewrite (bounded_add_idem (R := R) (matrix_mul m (pow m n) c d)) at 1;
            reflexivity).
      reflexivity.
  Qed.


  (** Bounded-semiring variant of [matrix_pow_idempotence]. *)
  Lemma matrix_pow_idempotence_bounded {R : BoundedSemiring.type} :
    forall (n : nat) (m : @Matrix R) (c d : Node),
      pow (m +M I) n c d = geom_sum m n c d.
  Proof.
    induction n as [|n IH]; intros m c d.
    - cbn. reflexivity.
    - cbn [pow].
      unfold matrix_mul.
      rewrite (sum_ext (fun y => (m +M I) c y * pow (m +M I) n y d)
        (fun y => m c y * geom_sum m n y d + I c y * geom_sum m n y d)).
      + rewrite sum_add.
        change (sum (fun y => m c y * geom_sum m n y d)) with (matrix_mul m (geom_sum m n) c d).
        change (sum (fun y => I c y * geom_sum m n y d)) with (matrix_mul I (geom_sum m n) c d).
        rewrite (matrix_mul_I_l (geom_sum m n) c d).
        rewrite <- matrix_add_unfold.
        apply geom_sum_idem_recurrence_bounded.
      + intro y.
        rewrite matrix_add_unfold.
        rewrite (IH m y d).
        apply mulDr.
  Qed.


  (** A single power term equals the sum of weights of all length-[n] paths. *)
  Lemma matrix_path_equation {R : Semiring.type} :
    forall n (m : @Matrix R) c d,
    pow m n c d =
    sum_all_rvalues
      (get_all_rvalues
        (construct_all_paths elements m n c d)).
  Proof.
    induction n as [|n IH]; intros m c d.
    - cbn [pow].
      rewrite sum_all_rvalues_get_all_rvalues.
      unfold I.
      pose proof (flat_map_path_partial_sum (R := R) 0 m c d) as H0.
      cbn [partial_sum_paths enum_all_paths_flat] in H0.
      exact H0.
    - cbn [pow all_paths_klength].
      unfold matrix_mul.
      assert (Hflat :
        forall (l : list Node),
        fold_right (fun u v : R => u + v) 0
          (map measure_of_path
            (append_node_in_paths m c
              (flat_map (fun x : Node => all_paths_klength elements m n x d) l))) =
        fold_right
          (fun y acc =>
            m c y * fold_right (fun u v : R => u + v) 0
              (map measure_of_path (all_paths_klength elements m n y d)) + acc)
          0 l).
      {
        intros l.
        induction l as [|a t IHt].
        - cbn. reflexivity.
        - cbn [List.flat_map].
          set (lf := flat_map (fun x : Node => all_paths_klength elements m n x d) t).
          assert (Hacc : forall (xs : list R) (acc : R),
            fold_right (fun u v : R => u + v) acc xs =
            fold_right (fun u v : R => u + v) 0 xs + acc).
          {
            intros xs acc.
            induction xs as [|x xs IHxs].
            - cbn. symmetry. apply add0r.
            - cbn. rewrite IHxs. rewrite addA. reflexivity.
          }
          rewrite (fold_measure_append_node_app
            (all_paths_klength elements m n a d)
            lf
            m c).
          rewrite map_app.
          rewrite fold_right_app.
          rewrite (Hacc
            (map measure_of_path
              (append_node_in_paths m c (all_paths_klength elements m n a d)))
            (fold_right (fun u v : R => u + v) 0
              (map measure_of_path (append_node_in_paths m c lf)))).
          rewrite (fold_measure_append_node_kpaths n m c a d).
          unfold lf.
          rewrite IHt.
          reflexivity.
      }
      rewrite (sum_ext
        (fun y => m c y * pow m n y d)
        (fun y => m c y *
          fold_right (fun u v : R => u + v) 0
            (map measure_of_path (all_paths_klength elements m n y d)))).
      2:{
        intro y.
        rewrite IH.
        unfold sum_all_rvalues, get_all_rvalues, construct_all_paths.
        rewrite map_map.
        cbn [fold_right].
        reflexivity.
      }
      rewrite sum_all_rvalues_get_all_rvalues.
      assert (Hwrap :
        forall c d (lp : list (list (Node * Node * R))),
          @sum_all_flat_paths Node R (map (fun l => (c, d, l)) lp) =
          fold_right (fun u v : R => u + v) 0 (map measure_of_path lp)).
      {
        intros c0 d0 lp.
        induction lp as [|h t IHt].
        - cbn. reflexivity.
        - cbn. rewrite IHt. reflexivity.
      }
      unfold construct_all_paths.
      rewrite Hwrap.
      cbn [all_paths_klength].
      rewrite (Hflat elements).
        unfold sum.
      reflexivity.
  Qed.


  Lemma connect_partial_sum_mat_paths  {R : Semiring.type} : 
    forall n (m : @Matrix R) c d,
    geom_sum m n c d = partial_sum_paths elements m n c d.
  Proof.
    induction n as [|n IH]; intros m c d.
    - cbn [geom_sum partial_sum_paths].
      unfold I.
      destruct (fin_eq_dec c d) as [Hcd | Hcd]; reflexivity.
    - cbn [geom_sum partial_sum_paths].
      rewrite matrix_add_unfold.
      rewrite (IH m c d).
      rewrite (matrix_path_equation (S n) m c d).
      reflexivity.
  Qed.


  Lemma connect_unary_matrix_exp_partial_sum_paths {R : BoundedSemiring.type} : 
    forall n (m : @Matrix R) c d,
    pow (m +M I) n c d = partial_sum_paths elements m n c d.
  Proof. 
    intros n m c d.
    rewrite matrix_pow_idempotence_bounded.
    apply connect_partial_sum_mat_paths.
  Qed.

  (** Matrix geometric sum stabilizes after the finite-node bound. *)
  Lemma geom_sum_stable_after_node_bound {R : BoundedSemiring.type} : 
    forall k (m : @Matrix R), (∀ u v : Node, u = v → m u v = 1) ->
    (forall (c d : Node), 
    geom_sum m (length (@elements Node) - 1)%nat c d = 
    geom_sum m (k + length (@elements Node) - 1)%nat c d).
  Proof.
    intros k m Hdiag c d.
    rewrite !connect_partial_sum_mat_paths.
    apply zero_stable_partial_sum_path.
    exact Hdiag.
  Qed.


  (** The power of the closure matrix stabilizes after the finite-node
      bound: [(m + I)^(|Node|-1) = (m + I)^(n + |Node|-1)]. *)
  Lemma matrix_pow_fixpoint_after_node_bound {R : BoundedSemiring.type} :
    forall (n : nat) (m : @Matrix R) c d,
    (∀ u v : Node, u = v → m u v = 1) ->
    pow (m +M I) (length (@elements Node) - 1) c d =
    pow (m +M I) (n + length (@elements Node) - 1) c d.
  Proof.
    intros n m c d Hdiag.
    rewrite !connect_unary_matrix_exp_partial_sum_paths.
    apply zero_stable_partial_sum_path.
    exact Hdiag.
  Qed.

  (** The partial path sum equals the sum over the flattened enumeration
      of all paths: [Σ_{p ≤ n} paths = Σ (enum_all_paths_flat)]. *)
  Lemma partial_sum_paths_enum_flat {R : Semiring.type} :
    forall n (m : @Matrix R) c d,
    partial_sum_paths elements m n c d =
    sum_all_rvalues (get_all_rvalues (enum_all_paths_flat elements m n c d)).
  Proof.
    intros n m c d.
    rewrite sum_all_rvalues_get_all_rvalues.
    apply flat_map_path_partial_sum.
  Qed.


  (** The matrix geometric sum equals the sum over the flattened
      enumeration of all paths. *)
  Lemma connect_geom_sum_enum_flat {R : Semiring.type} :
    forall n (m : @Matrix R) c d,
    geom_sum m n c d = sum_all_rvalues (get_all_rvalues
      (enum_all_paths_flat elements m n c d)).
  Proof.
    intros n m c d.
    rewrite connect_partial_sum_mat_paths.
    apply partial_sum_paths_enum_flat.
  Qed.


  (** * Monotonicity and structural lemmas for Schulze-method reasoning
      ----------------------------------------------------------------
      The following theorems capture matrix-level properties needed
      for the Schulze beatpath computation.  They are stated as
      [Admitted] placeholders — most are straightforward inductions
      that follow from the path-based characterisations above
      ([matrix_path_equation], [connect_partial_sum_mat_paths]). *)

  (** ** 1.  Monotonicity of [pow] in the matrix argument

      If every entry of [m₁] is below the corresponding entry of [m₂]
      (in the [Orel] preorder), then the same holds for every power.
      This lets us compare beatpath strengths under matrix
      perturbations (e.g., adding a voter). *)
  Lemma pow_monotone {R : BoundedSemiring.type} (m₁ m₂ : @Matrix R) (n : nat) :
    (forall i j, Orel (m₁ i j) (m₂ i j)) ->
    forall c d, Orel (pow m₁ n c d) (pow m₂ n c d).
  Proof.
    intros Hle. induction n as [|n IH]; intros c d.
    - cbn. unfold Orel. apply bounded_add_idem.
    - cbn [pow]. unfold matrix_mul, Orel.
      assert (HR : forall u v w : R, u + v = v -> w * u + w * v = w * v).
      { intros u v w Huv. transitivity (w * (u + v)).
        - apply eq_sym. apply (mulDl (s := R) w u v).
        - rewrite Huv. reflexivity. }
      assert (HL : forall u v w : R, u + v = v -> u * w + v * w = v * w).
      { intros u v w Huv. transitivity ((u + v) * w).
        - apply eq_sym. apply (mulDr (s := R) u v w).
        - rewrite Huv; reflexivity. }
      assert (HS : forall (f g : Node -> R),
        (forall x, f x + g x = g x) -> sum f + sum g = sum g).
      { intros f g Hfg. unfold sum.
        induction (elements (s := Node)) as [|a l IHl]; cbn.
        { apply addr0. }
        { setoid_rewrite (add_swap_mid (f a)
            (fold_right (λ (x : Node) (y : R), f x + y) 0 l)
            (g a)
            (fold_right (λ (x : Node) (y : R), g x + y) 0 l)).
          transitivity (g a + (fold_right (λ (x : Node) (y : R), f x + y) 0 l +
            fold_right (λ (x : Node) (y : R), g x + y) 0 l)).
          - apply (f_equal2 add (Hfg a) eq_refl).
          - apply (f_equal (fun t => g a + t) IHl). } }
      apply HS. intro y.
      apply (orel_trans (R := R) (m₁ c y * pow m₁ n y d)
        (m₂ c y * pow m₁ n y d) (m₂ c y * pow m₂ n y d)).
      { unfold Orel. apply HL. apply Hle. }
      { unfold Orel. apply HR. apply IH. }
  Qed.

  (** ** 2.  Monotonicity of [geom_sum] in the matrix argument

      Pointwise dominance lifts to geometric sums.  This is the key
      lemma for proving monotonicity of the Schulze method: adding
      support to a candidate can only increase their beatpath
      strengths. *)
  Lemma geom_sum_monotone {R : BoundedSemiring.type} (m₁ m₂ : @Matrix R) (n : nat) :
    (forall i j, Orel (m₁ i j) (m₂ i j)) ->
    forall c d, Orel (geom_sum m₁ n c d) (geom_sum m₂ n c d).
  Proof.
    intros Hle. induction n as [|n IH]; intros c d.
    - cbn. unfold Orel. apply bounded_add_idem.
    - cbn [geom_sum]. unfold matrix_add, Orel.
      rewrite (add_swap_mid (geom_sum m₁ n c d) (pow m₁ (S n) c d)
        (geom_sum m₂ n c d) (pow m₂ (S n) c d)).
      unfold Orel in IH. rewrite IH.
      rewrite (pow_monotone m₁ m₂ (S n) Hle c d). reflexivity.
  Qed.

  (** ** 3.  Each power term is below the geometric sum

      [pow m k c d ≤ geom_sum m n c d] whenever [k ≤ n].
      This is the matrix-level analogue of [pow_le_mat_star]
      from [SocialchoiceN.v]. *)
  Lemma pow_le_geom_sum {R : BoundedSemiring.type} (m : @Matrix R) (n k : nat) c d :
    (k <= n)%nat ->
    Orel (pow m k c d) (geom_sum m n c d).
  Proof.
    intros Hle. revert k Hle. induction n as [|n IH]; intros k Hle.
    - destruct k; [| inversion Hle].
      cbn. unfold Orel. apply bounded_add_idem.
    - assert (Hcases : k <= n \/ k = S n) by lia.
      destruct Hcases as [Hk_le_n | Hk_eq_Sn].
      + cbn [geom_sum]. unfold matrix_add, Orel.
        rewrite <- addA.
        unfold Orel in IH. rewrite (IH k Hk_le_n). reflexivity.
      + subst k.
        cbn [geom_sum]. unfold matrix_add, Orel.
        transitivity ((pow m (S n) c d + geom_sum m n c d) + pow m (S n) c d).
        { rewrite addA. reflexivity. }
        rewrite (addC (pow m (S n) c d) (geom_sum m n c d)).
        rewrite addA.
        apply (f_equal (fun t => geom_sum m n c d + t)).
        apply (bounded_add_idem (R := R) (pow m (S n) c d)).
  Qed.

  (** ** 4.  Geometric sum is monotone in [n]

      Adding more terms to the geometric sum can only increase
      (or keep equal) each entry: [geom_sum m n ≤ geom_sum m (S n)]. *)
  Lemma geom_sum_increasing {R : BoundedSemiring.type} (m : @Matrix R) (n : nat) c d :
    Orel (geom_sum m n c d) (geom_sum m (S n) c d).
  Proof.
    cbn [geom_sum]. unfold matrix_add, Orel.
    rewrite <- addA.
    setoid_rewrite (bounded_add_idem (R := R) (geom_sum m n c d)).
    reflexivity.
  Qed.

  (** ** 5.  Closure matrix has [1] on the diagonal

      [(m + I)[c,c] = 1] for every node [c].  This ensures that the
      beatpath from a candidate to itself is always the strongest
      possible (the top element in a bounded semiring). *)
  Lemma closure_diag_one {R : BoundedSemiring.type} (m : @Matrix R) (c : Node) :
    (m +M I) c c = 1.
  Proof. 
    unfold matrix_add, I.
    destruct (fin_eq_dec c c); 
    try congruence.
    rewrite addC. 
    setoid_rewrite add_bound.
    exact eq_refl.
  Qed.

  (** ** 6.  [I] is the top element for the [Orel] preorder on the diagonal

      For every matrix [m], [I[i,i] = 1] is the top element, so in a
      bounded semiring every entry satisfies [m c d ≤ 1 = I c d] when
      [c = d]. *)
  Lemma I_is_top_diag {R : BoundedSemiring.type} (m : @Matrix R) (c : Node) : Orel (m c c) (I c c).
  Proof. 
    intros *.
    unfold Orel, I.
    destruct (fin_eq_dec c c); 
    try congruence.
    rewrite addC. 
    setoid_rewrite add_bound.
    exact eq_refl.
  Qed.

End Matrix.

