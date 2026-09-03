(* ========================================================================= *)
(*  Schulze's conditions on a link-strength measure (Sect. 2.1)              *)
(*                                                                           *)
(*  A strength measure turns the pair of vote counts (N[e,f], N[f,e]) of a    *)
(*  link into an element of a totally preordered carrier.  ExtendOrder and    *)
(*  NormalizedOrder already turn any such preorder, given as a [PreSpec] on   *)
(*  [nat * nat], into a bounded commutative semiring.  What they do not       *)
(*  record is how the order RESPONDS to the counts, and that is exactly what   *)
(*  Schulze's ballot-level arguments use.  He asks for two things:            *)
(*                                                                           *)
(*    (2.1.1)  more support with no more opposition, or less opposition with  *)
(*             no less support, makes a link strictly stronger;               *)
(*    (2.1.2)  every pairwise victory is strictly stronger than every tie,    *)
(*             and every tie strictly stronger than every defeat.             *)
(*                                                                           *)
(*  A [Measure] is a [PreSpec] together with these two conditions.  The       *)
(*  lemmas below lift them from the boolean order on raw count pairs to the   *)
(*  derived order [Orel] on the normalised carrier, which is the order the    *)
(*  Schulze theorems reason with.  In particular the tie [(0,0)] separates    *)
(*  every victory from every defeat, which is the separator that the Smith    *)
(*  and Condorcet theorems take as a hypothesis on the matrix.               *)
(*                                                                           *)
(*  Both conditions are stated as "[x] is not below [y]": on a total preorder  *)
(*  that is the same as "[x] is strictly above [y]", and it is the form that   *)
(*  the concrete measures in examples/ discharge most directly.               *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 Arith Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN OrderSemiring
  NormalizedOrder ExtendOrder.

(* ------------------------------------------------------------------ *)
(*  The record                                                         *)
(* ------------------------------------------------------------------ *)

Record Measure := {
  m_pre : PreSpec (nat * nat);

  (** Schulze (2.1.1): strength responds to support and opposition in the
      right direction. *)
  m_211 : forall x1 x2 y1 y2 : nat,
    (y1 < x1 /\ x2 <= y2) \/ (y1 <= x1 /\ x2 < y2) ->
    ps_le m_pre (x1, x2) (y1, y2) = false;

  (** Schulze (2.1.2): victory above tie above defeat. *)
  m_212 : forall x1 x2 y1 y2 : nat,
    (x2 < x1 /\ y1 <= y2) \/ (x2 <= x1 /\ y1 < y2) ->
    ps_le m_pre (x1, x2) (y1, y2) = false;
}.

(** The bounded, normalised carrier of a measure, and the strength of a
    count pair in it. *)
Definition spec (m : Measure) : CanonSpec (Ext (nat * nat)) :=
  ext_spec (m_pre m).

Definition Strength (m : Measure) : Type := NT (spec m).

Definition strength (m : Measure) (p : nat * nat) : Strength m :=
  inj (spec m) (EMid p).

(* Every Strength is a bounded commutative semiring, by NormalizedOrder. *)
Check (fun m => (Strength m : BoundedCommutativeSemiring.type)).

(* ------------------------------------------------------------------ *)
(*  From the boolean order on counts to [Orel] on the carrier          *)
(* ------------------------------------------------------------------ *)

Section MeasureFacts.

  Context (m : Measure).

  (** [inj] preserves the order of the raw counts. *)
  Lemma strength_le (p q : nat * nat) :
    ps_le (m_pre m) p q = true -> Orel (strength m p) (strength m q).
  Proof.
    intro H. apply (Orel_iff_leN (spec m)). apply inj_mono. cbn. exact H.
  Qed.

  (** …and reflects it: equal strengths come from equivalent counts. *)
  Lemma strength_eq_le (p q : nat * nat) :
    strength m p = strength m q -> ps_le (m_pre m) p q = true.
  Proof.
    intro H.
    change (cs_le (spec m) (EMid p) (EMid q) = true).
    apply inj_reflects. unfold strength in H. rewrite H. apply leN_refl.
  Qed.

  (** A strict comparison of counts is a strict comparison of strengths. *)
  Lemma strength_lt_of_ps (p q : nat * nat) :
    ps_le (m_pre m) q p = false ->
    Orel (strength m p) (strength m q) /\ strength m p <> strength m q.
  Proof.
    intro H. split.
    - destruct (ps_total (m_pre m) p q) as [Hpq | Hqp].
      + apply strength_le. exact Hpq.
      + congruence.
    - intro E. pose proof (strength_eq_le q p (eq_sym E)). congruence.
  Qed.

  (** Real links never reach the adjoined extremes. *)
  Lemma strength_ne_one (p : nat * nat) : strength m p <> one.
  Proof.
    intro H. apply (f_equal (val (spec m))) in H. cbn in H. discriminate.
  Qed.

  Lemma strength_ne_zero (p : nat * nat) : strength m p <> zero.
  Proof.
    intro H. apply (f_equal (val (spec m))) in H. cbn in H. discriminate.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  (2.1.1) on the carrier                                           *)
  (* ---------------------------------------------------------------- *)

  (** Strict form. *)
  Lemma strength_211 (x1 x2 y1 y2 : nat) :
    (y1 < x1 /\ x2 <= y2) \/ (y1 <= x1 /\ x2 < y2) ->
    Orel (strength m (y1, y2)) (strength m (x1, x2)) /\
    strength m (y1, y2) <> strength m (x1, x2).
  Proof.
    intro H. apply strength_lt_of_ps. exact (m_211 m x1 x2 y1 y2 H).
  Qed.

  (** Weak form: no less support and no more opposition is no weaker. *)
  Lemma strength_mono_weak (x1 x2 y1 y2 : nat) :
    y1 <= x1 -> x2 <= y2 ->
    Orel (strength m (y1, y2)) (strength m (x1, x2)).
  Proof.
    intros H1 H2.
    destruct (Nat.eq_dec y1 x1) as [-> | Hne1].
    - destruct (Nat.eq_dec x2 y2) as [-> | Hne2].
      + apply (Orel_iff_leN (spec m)). apply leN_refl.
      + destruct (ps_total (m_pre m) (x1, y2) (x1, x2)) as [H | H].
        * apply strength_le. exact H.
        * exfalso. rewrite (m_211 m x1 x2 x1 y2) in H; [discriminate | lia].
    - destruct (ps_total (m_pre m) (y1, y2) (x1, x2)) as [H | H].
      + apply strength_le. exact H.
      + exfalso. rewrite (m_211 m x1 x2 y1 y2) in H; [discriminate | lia].
  Qed.

  (** Only a full-support, zero-opposition pair has the strength of one.
      This is what lets unanimity be read back from a matrix entry. *)
  Lemma full_strength_inv (n c1 c2 : nat) :
    c1 <= n -> strength m (c1, c2) = strength m (n, 0) -> c1 = n /\ c2 = 0.
  Proof.
    intros Hle Heq.
    pose proof (strength_eq_le (n, 0) (c1, c2) (eq_sym Heq)) as Hback.
    destruct (Nat.eq_dec c1 n) as [-> | Hne1].
    - destruct (Nat.eq_dec c2 0) as [-> | Hne2]; [split; reflexivity |].
      exfalso. rewrite (m_211 m n 0 n c2) in Hback; [discriminate | lia].
    - exfalso. rewrite (m_211 m n 0 c1 c2) in Hback; [discriminate | lia].
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  (2.1.2) on the carrier: the tie separates victories from defeats *)
  (* ---------------------------------------------------------------- *)

  Lemma tie_lt_victory (x1 x2 : nat) :
    x2 < x1 ->
    Orel (strength m (0, 0)) (strength m (x1, x2)) /\
    strength m (0, 0) <> strength m (x1, x2).
  Proof.
    intro H. apply strength_lt_of_ps. apply (m_212 m x1 x2 0 0). left. lia.
  Qed.

  Lemma defeat_lt_tie (y1 y2 : nat) :
    y1 < y2 ->
    Orel (strength m (y1, y2)) (strength m (0, 0)) /\
    strength m (y1, y2) <> strength m (0, 0).
  Proof.
    intro H. apply strength_lt_of_ps. apply (m_212 m 0 0 y1 y2). right. lia.
  Qed.

  (** The general form of (2.1.2)'s second clause: a defeat sits strictly
      below every link that is not a defeat, tie or victory alike. *)
  Lemma defeat_lt_undefeated (x1 x2 y1 y2 : nat) :
    y1 < y2 -> x2 <= x1 ->
    Orel (strength m (y1, y2)) (strength m (x1, x2)) /\
    strength m (y1, y2) <> strength m (x1, x2).
  Proof.
    intros Hy Hx. apply strength_lt_of_ps. apply (m_212 m x1 x2 y1 y2). right. lia.
  Qed.

End MeasureFacts.
