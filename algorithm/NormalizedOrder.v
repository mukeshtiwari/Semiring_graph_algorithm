(* ========================================================================= *)
(*  From a total PREORDER to a bounded commutative semiring                   *)
(*                                                                           *)
(*  [OrderSemiring.v] turns a total ORDER into the algebra: join for +, meet  *)
(*  for *, with distributivity free.  It demands [le_antisym] with respect    *)
(*  to Leibniz equality, and that is exactly the hypothesis a Schulze         *)
(*  link-strength measure cannot satisfy — Schulze's orders on vote-count     *)
(*  pairs are strict WEAK orders, so ties form equivalence classes of         *)
(*  distinct elements.  For margin-then-ratio, for instance, every pairwise   *)
(*  tie (k,k) is equivalent to every other, and commutativity of the join     *)
(*  already fails: add_max (1,1) (2,2) = (1,1) while add_max (2,2) (1,1) =    *)
(*  (2,2).                                                                    *)
(*                                                                           *)
(*  In a setoid development one would change the equality.  With Leibniz      *)
(*  equality the move is to pick canonical representatives: supply an         *)
(*  idempotent [cs_norm] that is sound and complete for the equivalence, and  *)
(*  work in its image                                                        *)
(*                                                                           *)
(*      NT cs = { a : A | is_norm cs a = true }.                              *)
(*                                                                           *)
(*  Equality on [NT cs] is decided by the underlying element alone (via UIP   *)
(*  on bool, so no axiom is used), antisymmetry holds there, and the whole    *)
(*  of OrderSemiring applies.  Note that no operation needs renormalising:    *)
(*  join and meet both RETURN ONE OF THEIR ARGUMENTS, so [NT cs] is closed    *)
(*  under them by construction.                                               *)
(*                                                                           *)
(*  The obligations are bundled in the record [CanonSpec] rather than as an   *)
(*  HB structure, deliberately.  Schulze's four strength measures — margin,   *)
(*  ratio, winning votes, losing votes — are four different orders on the     *)
(*  SAME carrier of vote-count pairs, and HB keys canonical instances on the  *)
(*  type, so structures would force a wrapper type per measure (the problem   *)
(*  mathcomp's Order library carries its [disp] parameter to work around).    *)
(*  As records they are simply four values.  The OUTPUT is still an HB        *)
(*  instance, declared once below, so clients get a bounded commutative       *)
(*  semiring with no per-measure instance blocks.                             *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 Bool Eqdep_dec.
From HB Require Import structures.
From Semiring Require Import Structures OrelN OrderSemiring.

(* ------------------------------------------------------------------ *)
(*  The obligations                                                     *)
(* ------------------------------------------------------------------ *)

Record CanonSpec (A : Type) := {
  cs_eq_dec : forall x y : A, {x = y} + {x <> y};
  cs_le     : A -> A -> bool;
  cs_norm   : A -> A;
  cs_bot    : A;
  cs_top    : A;

  (* [cs_le] is a total preorder — note the absence of antisymmetry *)
  cs_refl  : forall a, cs_le a a = true;
  cs_trans : forall a b c,
    cs_le a b = true -> cs_le b c = true -> cs_le a c = true;
  cs_total : forall a b, cs_le a b = true \/ cs_le b a = true;

  (* [cs_norm] picks a canonical representative of each equivalence class:
     idempotent, sound (it stays inside the class) and complete (equivalent
     elements get the same representative) *)
  cs_norm_idem  : forall a, cs_norm (cs_norm a) = cs_norm a;
  cs_norm_le    : forall a, cs_le a (cs_norm a) = true;
  cs_norm_ge    : forall a, cs_le (cs_norm a) a = true;
  cs_norm_compl : forall a b,
    cs_le a b = true -> cs_le b a = true -> cs_norm a = cs_norm b;

  (* extremal elements, already canonical *)
  cs_bot_canon    : cs_norm cs_bot = cs_bot;
  cs_top_canon    : cs_norm cs_top = cs_top;
  cs_bot_least    : forall a, cs_le cs_bot a = true;
  cs_top_greatest : forall a, cs_le a cs_top = true;
}.

Arguments cs_eq_dec {A}.
Arguments cs_le {A}.
Arguments cs_norm {A}.
Arguments cs_bot {A}.
Arguments cs_top {A}.
Arguments cs_refl {A}.
Arguments cs_trans {A}.
Arguments cs_total {A}.
Arguments cs_norm_idem {A}.
Arguments cs_norm_le {A}.
Arguments cs_norm_ge {A}.
Arguments cs_norm_compl {A}.
Arguments cs_bot_canon {A}.
Arguments cs_top_canon {A}.
Arguments cs_bot_least {A}.
Arguments cs_top_greatest {A}.

Section Normalized.

  Context {A : Type} (cs : CanonSpec A).

  Local Notation sle    := (cs_le cs).
  Local Notation snorm  := (cs_norm cs).
  Local Notation seqd   := (cs_eq_dec cs).

  (* ----------------------------------------------------------------- *)
  (*  The carrier of canonical representatives                          *)
  (* ----------------------------------------------------------------- *)

  Definition is_norm (a : A) : bool :=
    if seqd (snorm a) a then true else false.

  Lemma is_norm_fix : forall a, is_norm a = true -> snorm a = a.
  Proof.
    intros a Ha. unfold is_norm in Ha.
    destruct (seqd (snorm a) a) as [Heq|_]; [exact Heq | discriminate].
  Qed.

  Lemma norm_is_norm : forall a, is_norm (snorm a) = true.
  Proof.
    intro a. unfold is_norm.
    destruct (seqd (snorm (snorm a)) (snorm a)) as [_|Hne];
      [reflexivity | exfalso; exact (Hne (cs_norm_idem cs a))].
  Qed.

  Lemma bot_is_norm : is_norm (cs_bot cs) = true.
  Proof.
    unfold is_norm. destruct (seqd (snorm (cs_bot cs)) (cs_bot cs)) as [_|Hne];
      [reflexivity | exfalso; exact (Hne (cs_bot_canon cs))].
  Qed.

  Lemma top_is_norm : is_norm (cs_top cs) = true.
  Proof.
    unfold is_norm. destruct (seqd (snorm (cs_top cs)) (cs_top cs)) as [_|Hne];
      [reflexivity | exfalso; exact (Hne (cs_top_canon cs))].
  Qed.

  Definition NT : Type := { a : A | is_norm a = true }.
  Definition val (x : NT) : A := proj1_sig x.

  (** Leibniz equality on [NT] is decided by the underlying element.  The
      proof components are equal by UIP on [bool], which is a theorem, so
      nothing is assumed here. *)
  Lemma NT_eq : forall x y : NT, val x = val y -> x = y.
  Proof.
    intros [a Ha] [b Hb] Heq. cbn in Heq. subst b.
    f_equal. apply Eqdep_dec.UIP_dec. exact Bool.bool_dec.
  Qed.

  Definition inj (a : A) : NT := exist _ (snorm a) (norm_is_norm a).
  Definition botN : NT := exist _ (cs_bot cs) bot_is_norm.
  Definition topN : NT := exist _ (cs_top cs) top_is_norm.

  (* ----------------------------------------------------------------- *)
  (*  …carries a total ORDER                                            *)
  (* ----------------------------------------------------------------- *)

  Definition leN (x y : NT) : bool := sle (val x) (val y).

  Lemma leN_refl : forall x, leN x x = true.
  Proof. intro x. apply (cs_refl cs). Qed.

  Lemma leN_trans : forall x y z,
    leN x y = true -> leN y z = true -> leN x z = true.
  Proof. intros x y z. apply (cs_trans cs). Qed.

  Lemma leN_total : forall x y, leN x y = true \/ leN y x = true.
  Proof. intros x y. apply (cs_total cs). Qed.

  (** The point of the whole construction: antisymmetry, which [cs_le] does
      not have, holds on canonical representatives. *)
  Lemma leN_antisym : forall x y, leN x y = true -> leN y x = true -> x = y.
  Proof.
    intros x y Hxy Hyx. apply NT_eq.
    pose proof (is_norm_fix (val x) (proj2_sig x)) as Hx.
    pose proof (is_norm_fix (val y) (proj2_sig y)) as Hy.
    rewrite <- Hx, <- Hy. exact (cs_norm_compl cs _ _ Hxy Hyx).
  Qed.

  Lemma botN_least : forall x, leN botN x = true.
  Proof. intro x. unfold leN. cbn. apply (cs_bot_least cs). Qed.

  Lemma topN_greatest : forall x, leN x topN = true.
  Proof. intro x. unfold leN. cbn. apply (cs_top_greatest cs). Qed.

  (** [inj] transports raw values into [NT], preserving and reflecting the
      order, so a client can build matrices from raw strengths. *)
  Lemma inj_mono : forall a b, sle a b = true -> leN (inj a) (inj b) = true.
  Proof.
    intros a b Hab. unfold leN, inj, val. cbn.
    exact (cs_trans cs _ _ _ (cs_norm_ge cs a)
             (cs_trans cs _ _ _ Hab (cs_norm_le cs b))).
  Qed.

  Lemma inj_reflects : forall a b, leN (inj a) (inj b) = true -> sle a b = true.
  Proof.
    intros a b Hab. unfold leN, inj, val in Hab. cbn in Hab.
    exact (cs_trans cs _ _ _ (cs_norm_le cs a)
             (cs_trans cs _ _ _ Hab (cs_norm_ge cs b))).
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  …and hence a bounded commutative semiring                         *)
  (*                                                                     *)
  (*  Every law comes from OrderSemiring applied to [leN]; nothing is     *)
  (*  proved again here.                                                  *)
  (* ----------------------------------------------------------------- *)

  HB.instance Definition _ := IsCommutativeMonoid.Build NT
    botN (add_max leN)
    (add_max_assoc leN leN_trans leN_antisym leN_total)
    (add_max_comm leN leN_antisym leN_total)
    (add_max_bot_l leN leN_antisym botN botN_least)
    (add_max_bot_r leN botN botN_least).

  HB.instance Definition _ := IsSemiring.Build NT
    topN (meet leN)
    (meet_assoc leN leN_trans leN_antisym leN_total)
    (meet_top_l leN leN_antisym topN topN_greatest)
    (meet_top_r leN topN topN_greatest)
    (meet_add_max_distr_r leN leN_refl leN_trans leN_antisym leN_total)
    (meet_add_max_distr_l leN leN_refl leN_trans leN_antisym leN_total)
    (meet_bot_l leN botN botN_least)
    (meet_bot_r leN leN_antisym botN botN_least).

  HB.instance Definition _ := IsCommutativeSemiring.Build NT
    (meet_comm leN leN_antisym leN_total).

  HB.instance Definition _ := IsBoundedSemiring.Build NT
    (add_max_top_l leN topN topN_greatest).

  (* ----------------------------------------------------------------- *)
  (*  The two orders agree                                              *)
  (*                                                                     *)
  (*  [Orel] is derived from addition as [x + y = y], and is what all of  *)
  (*  SocialchoiceN.v reasons with.  A client who starts from [cs_le]     *)
  (*  needs to know it is the same relation.                              *)
  (* ----------------------------------------------------------------- *)

  (* ----------------------------------------------------------------- *)
  (*  Structural facts, and why they are trivial here                   *)
  (*                                                                     *)
  (*  Several theorems in SocialchoiceN.v carry these as hypotheses on    *)
  (*  the carrier.  On [NT] they are not assumptions at all: both         *)
  (*  operations RETURN ONE OF THEIR ARGUMENTS, so selectivity and the    *)
  (*  meet-lower-bound property hold by case analysis on a boolean.       *)
  (* ----------------------------------------------------------------- *)

  (** Selectivity — [H_total_order] in SocialchoiceN.v. *)
  Lemma NT_selective : forall x y : NT, add x y = x \/ add x y = y.
  Proof.
    intros x y. cbn. unfold add_max.
    destruct (leN y x); [left | right]; reflexivity.
  Qed.

  (** [H_meet_lower_bound]: a lower bound of both factors bounds the meet. *)
  Lemma NT_meet_lower_bound : forall m a b : NT,
    Orel m a -> Orel m b -> Orel m (mul a b).
  Proof.
    intros m a b Hma Hmb. cbn. unfold meet.
    destruct (leN a b); assumption.
  Qed.

  (** Decidable equality, inherited from the underlying elements. *)
  Lemma NT_eq_dec : forall x y : NT, {x = y} + {x <> y}.
  Proof.
    intros x y. destruct (cs_eq_dec cs (val x) (val y)) as [Heq|Hne].
    - left. exact (NT_eq x y Heq).
    - right. intro Habs. apply Hne. rewrite Habs. reflexivity.
  Qed.

  Lemma Orel_iff_leN : forall x y : NT, Orel x y <-> leN x y = true.
  Proof.
    intros x y. unfold Orel. cbn. unfold add_max. split.
    - intro Hadd. destruct (leN y x) eqn:Hyx.
      + subst x. apply leN_refl.
      + destruct (leN_total x y) as [Hxy|Hyx']; [exact Hxy | congruence].
    - intro Hxy. destruct (leN y x) eqn:Hyx.
      + exact (leN_antisym x y Hxy Hyx).
      + reflexivity.
  Qed.

End Normalized.
