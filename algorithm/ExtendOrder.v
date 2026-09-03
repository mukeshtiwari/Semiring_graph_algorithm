(** * Adjoining extremal elements to a total preorder

    [NormalizedOrder.v] needs a least and a greatest element, but none of
    Schulze's link-strength measures has one natively: margins over
    unbounded vote counts run off in both directions.  This file adjoins
    them formally, so a measure only has to supply the ORDER part — the ten
    obligations of [PreSpec] — and gets a full [CanonSpec] back.

    This is the same move as CAPP's AddZero / AddOne combinators, and it
    matters for the same reason it did in WidestShortestPath.v: the
    extremes have to be genuinely new elements rather than repurposed
    existing ones, or they collide with the values already in play. *)

From Stdlib Require Import Utf8 Bool.
From Semiring Require Import Structures NormalizedOrder.

(** ** The order obligations, without bounds *)

Record PreSpec (A : Type) := {
  ps_eq_dec : forall x y : A, {x = y} + {x <> y};
  ps_le     : A -> A -> bool;
  ps_norm   : A -> A;

  ps_refl  : forall a, ps_le a a = true;
  ps_trans : forall a b c,
    ps_le a b = true -> ps_le b c = true -> ps_le a c = true;
  ps_total : forall a b, ps_le a b = true \/ ps_le b a = true;

  ps_norm_idem  : forall a, ps_norm (ps_norm a) = ps_norm a;
  ps_norm_le    : forall a, ps_le a (ps_norm a) = true;
  ps_norm_ge    : forall a, ps_le (ps_norm a) a = true;
  ps_norm_compl : forall a b,
    ps_le a b = true -> ps_le b a = true -> ps_norm a = ps_norm b;
}.

Arguments ps_eq_dec {A}.
Arguments ps_le {A}.
Arguments ps_norm {A}.
Arguments ps_refl {A}.
Arguments ps_trans {A}.
Arguments ps_total {A}.
Arguments ps_norm_idem {A}.
Arguments ps_norm_le {A}.
Arguments ps_norm_ge {A}.
Arguments ps_norm_compl {A}.

(** ** The carrier with two new elements *)

Inductive Ext (A : Type) := EBot | EMid (a : A) | ETop.

Arguments EBot {A}.
Arguments EMid {A}.
Arguments ETop {A}.

Section Extend.

  Context {A : Type} (ps : PreSpec A).

  Definition ext_le (x y : Ext A) : bool :=
    match x, y with
    | EBot, _      => true
    | _, ETop      => true
    | ETop, _      => false
    | _, EBot      => false
    | EMid a, EMid b => ps_le ps a b
    end.

  Definition ext_norm (x : Ext A) : Ext A :=
    match x with
    | EMid a => EMid (ps_norm ps a)
    | _      => x
    end.

  Definition ext_eq_dec : forall x y : Ext A, {x = y} + {x <> y}.
  Proof.
    intros [|a|] [|b|];
      try (left; reflexivity); try (right; discriminate).
    destruct (ps_eq_dec ps a b) as [Heq|Hne].
    - left. rewrite Heq. reflexivity.
    - right. intro Habs. apply Hne. injection Habs. exact (fun h => h).
  Defined.

  (** --- the order laws --- *)

  Lemma ext_le_refl : forall x, ext_le x x = true.
  Proof. intros [|a|]; cbn; [reflexivity | apply (ps_refl ps) | reflexivity]. Qed.

  Lemma ext_le_trans : forall x y z,
    ext_le x y = true -> ext_le y z = true -> ext_le x z = true.
  Proof.
    intros [|a|] [|b|] [|c|] H1 H2; cbn in *;
      try reflexivity; try discriminate.
    exact (ps_trans ps _ _ _ H1 H2).
  Qed.

  Lemma ext_le_total : forall x y, ext_le x y = true \/ ext_le y x = true.
  Proof.
    intros [|a|] [|b|]; cbn; try (left; reflexivity); try (right; reflexivity).
    apply (ps_total ps).
  Qed.

  (** --- the normalisation laws --- *)

  Lemma ext_norm_idem : forall x, ext_norm (ext_norm x) = ext_norm x.
  Proof.
    intros [|a|]; cbn; try reflexivity.
    rewrite (ps_norm_idem ps). reflexivity.
  Qed.

  Lemma ext_norm_le : forall x, ext_le x (ext_norm x) = true.
  Proof.
    intros [|a|]; cbn; [reflexivity | apply (ps_norm_le ps) | reflexivity].
  Qed.

  Lemma ext_norm_ge : forall x, ext_le (ext_norm x) x = true.
  Proof.
    intros [|a|]; cbn; [reflexivity | apply (ps_norm_ge ps) | reflexivity].
  Qed.

  Lemma ext_norm_compl : forall x y,
    ext_le x y = true -> ext_le y x = true -> ext_norm x = ext_norm y.
  Proof.
    intros [|a|] [|b|] H1 H2; cbn in *;
      try reflexivity; try discriminate.
    rewrite (ps_norm_compl ps a b H1 H2). reflexivity.
  Qed.

  (** --- the bounds --- *)

  Lemma ext_bot_canon : ext_norm EBot = EBot.
  Proof. reflexivity. Qed.

  Lemma ext_top_canon : ext_norm ETop = ETop.
  Proof. reflexivity. Qed.

  Lemma ext_bot_least : forall x, ext_le EBot x = true.
  Proof. intros [|a|]; reflexivity. Qed.

  Lemma ext_top_greatest : forall x, ext_le x ETop = true.
  Proof. intros [|a|]; reflexivity. Qed.

  (** A measure supplies the order; the bounds come for free. *)
  Definition ext_spec_def : CanonSpec (Ext A) :=
    {| cs_eq_dec       := ext_eq_dec;
       cs_le           := ext_le;
       cs_norm         := ext_norm;
       cs_bot          := EBot;
       cs_top          := ETop;
       cs_refl         := ext_le_refl;
       cs_trans        := ext_le_trans;
       cs_total        := ext_le_total;
       cs_norm_idem    := ext_norm_idem;
       cs_norm_le      := ext_norm_le;
       cs_norm_ge      := ext_norm_ge;
       cs_norm_compl   := ext_norm_compl;
       cs_bot_canon    := ext_bot_canon;
       cs_top_canon    := ext_top_canon;
       cs_bot_least    := ext_bot_least;
       cs_top_greatest := ext_top_greatest |}.

End Extend.

Definition ext_spec {A : Type} (ps : PreSpec A) : CanonSpec (Ext A) :=
  ext_spec_def ps.

(** * Lexicographic product of two measures

    Combining at the PreSpec level — BEFORE bounds are adjoined — is
    deliberate.  Adding the extremes first and taking the product second is
    precisely the "we have added a zero too soon" error that breaks
    distributivity for the naive widest-shortest-path encoding (CAPP §3.1,
    and the NOTE at the top of examples/WidestShortestPath.v).

    Note also what does NOT need checking here.  Gurney and Griffin's
    side conditions on lexicographic products — cancellativity of the first
    component or constancy of the second — govern products whose
    multiplication acts COMPONENTWISE.  Here multiplication is the meet of
    the combined order, which OrderSemiring proves monotone unconditionally,
    so a lexicographic combination of strength measures is always safe. *)

Section LexProduct.

  Context {A B : Type} (psA : PreSpec A) (psB : PreSpec B).

  Definition lex_le (p q : A * B) : bool :=
    if negb (ps_le psA (fst q) (fst p)) then true
    else if negb (ps_le psA (fst p) (fst q)) then false
    else ps_le psB (snd p) (snd q).

  Definition lex_norm (p : A * B) : A * B :=
    (ps_norm psA (fst p), ps_norm psB (snd p)).

  Definition lex_eq_dec : forall p q : A * B, {p = q} + {p <> q}.
  Proof.
    intros [a1 b1] [a2 b2].
    destruct (ps_eq_dec psA a1 a2) as [Ha|Ha];
      [| right; intro H; apply Ha; injection H; auto].
    destruct (ps_eq_dec psB b1 b2) as [Hb|Hb];
      [| right; intro H; apply Hb; injection H; auto].
    left. rewrite Ha, Hb. reflexivity.
  Defined.

  Lemma lex_le_refl : forall p, lex_le p p = true.
  Proof.
    intros [a b]. unfold lex_le. cbn.
    rewrite (ps_refl psA). cbn. apply (ps_refl psB).
  Qed.

  Lemma lex_le_total : forall p q, lex_le p q = true \/ lex_le q p = true.
  Proof.
    intros [a1 b1] [a2 b2]. unfold lex_le. cbn.
    destruct (ps_le psA a2 a1) eqn:E21; destruct (ps_le psA a1 a2) eqn:E12;
      cbn; try (left; reflexivity); try (right; reflexivity).
    (** only the case where the first components are equivalent survives *)
    apply (ps_total psB).
  Qed.

  Lemma lex_le_trans : forall p q r,
    lex_le p q = true -> lex_le q r = true -> lex_le p r = true.
  Proof.
    intros [a1 b1] [a2 b2] [a3 b3] H1 H2. unfold lex_le in *. cbn in *.
    destruct (ps_le psA a2 a1) eqn:E21; cbn in H1;
    destruct (ps_le psA a3 a2) eqn:E32; cbn in H2;
    destruct (ps_le psA a3 a1) eqn:E31; cbn.
    - (* a1 ≡ a2 ≡ a3: the second components decide, by transitivity there *)
      destruct (ps_le psA a1 a2) eqn:E12; cbn in H1; [| discriminate].
      destruct (ps_le psA a2 a3) eqn:E23; cbn in H2; [| discriminate].
      destruct (ps_le psA a1 a3) eqn:E13; cbn;
        [exact (ps_trans psB _ _ _ H1 H2) |].
      rewrite (ps_trans psA _ _ _ E12 E23) in E13. discriminate.
    - reflexivity.
    - (* a1 ≡ a2 and a2 strictly below a3, so a3 cannot be below a1 *)
      destruct (ps_le psA a1 a2) eqn:E12; cbn in H1; [| discriminate].
      rewrite (ps_trans psA _ _ _ E31 E12) in E32. discriminate.
    - reflexivity.
    - (* a1 strictly below a2 ≡ a3, so a3 cannot be below a1 *)
      destruct (ps_le psA a2 a3) eqn:E23; cbn in H2; [| discriminate].
      rewrite (ps_trans psA _ _ _ E23 E31) in E21. discriminate.
    - reflexivity.
    - (* a1 strictly below a2 strictly below a3 *)
      destruct (ps_total psA a1 a2) as [H12|H12]; [| congruence].
      rewrite (ps_trans psA _ _ _ E31 H12) in E32. discriminate.
    - reflexivity.
  Qed.

  Lemma lex_norm_idem : forall p, lex_norm (lex_norm p) = lex_norm p.
  Proof.
    intros [a b]. unfold lex_norm. cbn.
    rewrite (ps_norm_idem psA), (ps_norm_idem psB). reflexivity.
  Qed.

  Lemma lex_norm_le : forall p, lex_le p (lex_norm p) = true.
  Proof.
    intros [a b]. unfold lex_le, lex_norm. cbn.
    destruct (ps_le psA (ps_norm psA a) a) eqn:E; cbn.
    - rewrite (ps_norm_le psA). cbn. apply (ps_norm_le psB).
    - reflexivity.
  Qed.

  Lemma lex_norm_ge : forall p, lex_le (lex_norm p) p = true.
  Proof.
    intros [a b]. unfold lex_le, lex_norm. cbn.
    destruct (ps_le psA a (ps_norm psA a)) eqn:E; cbn.
    - rewrite (ps_norm_ge psA). cbn. apply (ps_norm_ge psB).
    - reflexivity.
  Qed.

  Lemma lex_norm_compl : forall p q,
    lex_le p q = true -> lex_le q p = true -> lex_norm p = lex_norm q.
  Proof.
    intros [a1 b1] [a2 b2] H1 H2. unfold lex_le, lex_norm in *. cbn in *.
    destruct (ps_le psA a2 a1) eqn:E21; cbn in H1;
      [| destruct (ps_le psA a1 a2) eqn:E12; cbn in H2; [discriminate |];
         destruct (ps_total psA a1 a2) as [H|H]; congruence].
    destruct (ps_le psA a1 a2) eqn:E12; cbn in H1, H2; [| discriminate].
    rewrite (ps_norm_compl psA a1 a2 E12 E21).
    rewrite (ps_norm_compl psB b1 b2 H1 H2). reflexivity.
  Qed.

  Definition lex_pre_def : PreSpec (A * B) :=
    {| ps_eq_dec     := lex_eq_dec;
       ps_le         := lex_le;
       ps_norm       := lex_norm;
       ps_refl       := lex_le_refl;
       ps_trans      := lex_le_trans;
       ps_total      := lex_le_total;
       ps_norm_idem  := lex_norm_idem;
       ps_norm_le    := lex_norm_le;
       ps_norm_ge    := lex_norm_ge;
       ps_norm_compl := lex_norm_compl |}.

End LexProduct.

Definition lex_pre {A B : Type} (psA : PreSpec A) (psB : PreSpec B)
  : PreSpec (A * B) := lex_pre_def psA psB.
