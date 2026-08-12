(* ========================================================================= *)
(*  Schulze's WINNING VOTES measure                                          *)
(*                                                                           *)
(*  Schulze §2.1, Example 3.  The strength of a link is measured primarily   *)
(*  by its support N[e,f].  Unpacking his six clauses, the order is:          *)
(*                                                                           *)
(*    - every pairwise victory beats every tie, every tie beats every         *)
(*      defeat  (clauses 1-2, which is condition (2.1.2));                    *)
(*    - within the victories and within the defeats, more support is          *)
(*      stronger, and among equal support less opposition is stronger         *)
(*      (clauses 3-4 and 5-6 respectively);                                   *)
(*    - all ties are equivalent, no clause separating two of them.            *)
(*                                                                           *)
(*  So the only non-trivial equivalence class is the ties — which is exactly  *)
(*  what [wnorm] collapses, and what makes Leibniz antisymmetry fail before   *)
(*  normalisation.                                                            *)
(*                                                                           *)
(*  The order is defined by nested comparisons and then characterised once,   *)
(*  in [wle_spec], as a purely arithmetic condition.  Every preorder law is   *)
(*  then a consequence of that characterisation, so the case analysis is      *)
(*  paid for once rather than in each proof.                                  *)
(* ========================================================================= *)

From Stdlib Require Import Utf8 Arith Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN OrderSemiring
  NormalizedOrder ExtendOrder SocialchoiceN SchulzeOnNT.

(* ------------------------------------------------------------------ *)
(*  Victory / tie / defeat                                             *)
(* ------------------------------------------------------------------ *)

(** [0] = defeat, [1] = tie, [2] = victory. *)
Definition vclass (p : nat * nat) : nat :=
  if Nat.ltb (fst p) (snd p) then 0
  else if Nat.eqb (fst p) (snd p) then 1
  else 2.

Lemma vclass_spec : forall p,
  (vclass p = 0 /\ fst p < snd p)
  \/ (vclass p = 1 /\ fst p = snd p)
  \/ (vclass p = 2 /\ snd p < fst p).
Proof.
  intros [x y]. unfold vclass. cbn [fst snd].
  destruct (Nat.ltb x y) eqn:E1.
  - apply Nat.ltb_lt in E1. left. split; [reflexivity | exact E1].
  - apply Nat.ltb_nlt in E1.
    destruct (Nat.eqb x y) eqn:E2.
    + apply Nat.eqb_eq in E2. right; left. split; [reflexivity | exact E2].
    + apply Nat.eqb_neq in E2. right; right. split; [reflexivity | lia].
Qed.

(* ------------------------------------------------------------------ *)
(*  The order                                                          *)
(* ------------------------------------------------------------------ *)

Definition wle (p q : nat * nat) : bool :=
  if Nat.ltb (vclass p) (vclass q) then true
  else if Nat.ltb (vclass q) (vclass p) then false
  else if Nat.eqb (vclass p) 1 then true
  else if Nat.ltb (fst p) (fst q) then true
  else if Nat.ltb (fst q) (fst p) then false
  else Nat.leb (snd q) (snd p).

(** The arithmetic content of [wle], proved once. *)
Lemma wle_spec : forall p q,
  wle p q = true <->
  (vclass p < vclass q
   \/ (vclass p = vclass q
       /\ (vclass p = 1
           \/ fst p < fst q
           \/ (fst p = fst q /\ snd q <= snd p)))).
Proof.
  intros p q. unfold wle.
  destruct (Nat.ltb (vclass p) (vclass q)) eqn:E1.
  { apply Nat.ltb_lt in E1. split; [intros _; left; exact E1 | reflexivity]. }
  apply Nat.ltb_nlt in E1.
  destruct (Nat.ltb (vclass q) (vclass p)) eqn:E2.
  { apply Nat.ltb_lt in E2. split; [discriminate |].
    intros [H|[H _]]; lia. }
  apply Nat.ltb_nlt in E2.
  assert (Hcl : vclass p = vclass q) by lia.
  destruct (Nat.eqb (vclass p) 1) eqn:E3.
  { apply Nat.eqb_eq in E3. split.
    - intros _. right. split; [exact Hcl | left; exact E3].
    - reflexivity. }
  apply Nat.eqb_neq in E3.
  destruct (Nat.ltb (fst p) (fst q)) eqn:E4.
  { apply Nat.ltb_lt in E4. split.
    - intros _. right. split; [exact Hcl | right; left; exact E4].
    - reflexivity. }
  apply Nat.ltb_nlt in E4.
  destruct (Nat.ltb (fst q) (fst p)) eqn:E5.
  { apply Nat.ltb_lt in E5. split; [discriminate |].
    intros [H|[_ [H|[H|[H _]]]]]; lia. }
  apply Nat.ltb_nlt in E5.
  assert (Hfst : fst p = fst q) by lia.
  split.
  - intro H. apply Nat.leb_le in H. right. split; [exact Hcl |].
    right; right. split; [exact Hfst | exact H].
  - intros [H|[_ [H|[H|[_ H]]]]]; try lia.
    apply Nat.leb_le. exact H.
Qed.

Lemma wle_refl : forall p, wle p p = true.
Proof. intro p. apply wle_spec. right. split; [reflexivity |]. right; right. lia. Qed.

Lemma wle_trans : forall p q r, wle p q = true -> wle q r = true -> wle p r = true.
Proof.
  intros p q r H1 H2. apply wle_spec in H1, H2. apply wle_spec.
  destruct H1 as [H1|[H1a H1b]]; destruct H2 as [H2|[H2a H2b]]; lia.
Qed.

Lemma wle_total : forall p q, wle p q = true \/ wle q p = true.
Proof.
  intros p q.
  destruct (Nat.lt_trichotomy (vclass p) (vclass q)) as [H|[H|H]].
  - left. apply wle_spec. left. exact H.
  - destruct (Nat.eq_dec (vclass p) 1) as [Hc|Hc].
    { left. apply wle_spec. right. split; [exact H | left; exact Hc]. }
    destruct (Nat.lt_trichotomy (fst p) (fst q)) as [H2|[H2|H2]].
    + left. apply wle_spec. right. split; [exact H | right; left; exact H2].
    + destruct (Nat.le_ge_cases (snd q) (snd p)) as [H3|H3].
      * left. apply wle_spec. right. split; [exact H |].
        right; right. split; [exact H2 | exact H3].
      * right. apply wle_spec. right. split; [lia |].
        right; right. split; [lia | lia].
    + right. apply wle_spec. right. split; [lia | right; left; lia].
  - right. apply wle_spec. left. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(*  Normalisation: only the ties collapse                              *)
(* ------------------------------------------------------------------ *)

Definition wnorm (p : nat * nat) : nat * nat :=
  if Nat.eqb (fst p) (snd p) then (0, 0) else p.

Lemma wnorm_tie : forall p, fst p = snd p -> wnorm p = (0, 0).
Proof.
  intros [x y] H. unfold wnorm. cbn [fst snd] in *.
  destruct (Nat.eqb x y) eqn:E; [reflexivity |].
  apply Nat.eqb_neq in E. lia.
Qed.

Lemma wnorm_nontie : forall p, fst p <> snd p -> wnorm p = p.
Proof.
  intros [x y] H. unfold wnorm. cbn [fst snd] in *.
  destruct (Nat.eqb x y) eqn:E; [| reflexivity].
  apply Nat.eqb_eq in E. lia.
Qed.

Lemma wnorm_idem : forall p, wnorm (wnorm p) = wnorm p.
Proof.
  intro p. destruct (Nat.eq_dec (fst p) (snd p)) as [H|H].
  - rewrite (wnorm_tie p H). reflexivity.
  - rewrite (wnorm_nontie p H). exact (wnorm_nontie p H).
Qed.

Lemma vclass_tie : forall p, fst p = snd p -> vclass p = 1.
Proof.
  intros [x y] H. unfold vclass. cbn [fst snd] in *.
  destruct (Nat.ltb x y) eqn:E1; [apply Nat.ltb_lt in E1; lia |].
  destruct (Nat.eqb x y) eqn:E2; [reflexivity | apply Nat.eqb_neq in E2; lia].
Qed.

Lemma wnorm_le : forall p, wle p (wnorm p) = true.
Proof.
  intro p. destruct (Nat.eq_dec (fst p) (snd p)) as [H|H].
  - rewrite (wnorm_tie p H). apply wle_spec. right.
    rewrite (vclass_tie p H), (vclass_tie (0,0) eq_refl).
    split; [reflexivity | left; reflexivity].
  - rewrite (wnorm_nontie p H). apply wle_refl.
Qed.

Lemma wnorm_ge : forall p, wle (wnorm p) p = true.
Proof.
  intro p. destruct (Nat.eq_dec (fst p) (snd p)) as [H|H].
  - rewrite (wnorm_tie p H). apply wle_spec. right.
    rewrite (vclass_tie p H), (vclass_tie (0,0) eq_refl).
    split; [reflexivity | left; reflexivity].
  - rewrite (wnorm_nontie p H). apply wle_refl.
Qed.

Lemma wnorm_compl : forall p q,
  wle p q = true -> wle q p = true -> wnorm p = wnorm q.
Proof.
  intros p q H1 H2.
  apply wle_spec in H1. apply wle_spec in H2.
  pose proof (vclass_spec p) as Sp. pose proof (vclass_spec q) as Sq.
  destruct (Nat.eq_dec (fst p) (snd p)) as [Hp|Hp].
  - (* p is a tie, hence so is q, and both normalise to (0,0) *)
    assert (Hq : fst q = snd q) by lia.
    rewrite (wnorm_tie p Hp), (wnorm_tie q Hq). reflexivity.
  - (* neither is a tie, and the sub-order is antisymmetric, so p = q *)
    assert (Hq : fst q <> snd q) by lia.
    rewrite (wnorm_nontie p Hp), (wnorm_nontie q Hq).
    destruct p as [x1 y1]; destruct q as [x2 y2]. cbn [fst snd] in *.
    assert (Hx : x1 = x2) by lia.
    assert (Hy : y1 = y2) by lia.
    rewrite Hx, Hy. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  …packaged                                                          *)
(* ------------------------------------------------------------------ *)

Definition wv_eq_dec (p q : nat * nat) : {p = q} + {p <> q}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition wv_pre : PreSpec (nat * nat) :=
  {| ps_eq_dec     := wv_eq_dec;
     ps_le         := wle;
     ps_norm       := wnorm;
     ps_refl       := wle_refl;
     ps_trans      := wle_trans;
     ps_total      := wle_total;
     ps_norm_idem  := wnorm_idem;
     ps_norm_le    := wnorm_le;
     ps_norm_ge    := wnorm_ge;
     ps_norm_compl := wnorm_compl |}.

Definition wv_spec : CanonSpec (Ext (nat * nat)) := ext_spec wv_pre.

Definition WinningVotes : Type := NT wv_spec.

Check (WinningVotes : BoundedCommutativeSemiring.type).

Section WinningVotesSchulze.

  Context {Node : FinType.type}.

  Theorem wv_schulze_trans (M : @Matrix Node WinningVotes) :
    forall a b c : Node,
      schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c.
  Proof. exact (schulze_trans_normalized wv_spec M). Qed.

  Theorem wv_winner_exists (M : @Matrix Node WinningVotes) :
    exists a : Node, schulze_winner M a.
  Proof. exact (winner_exists_normalized wv_spec M). Qed.

End WinningVotesSchulze.

(* ------------------------------------------------------------------ *)
(*  Sanity checks against Schulze's clauses                            *)
(* ------------------------------------------------------------------ *)

(* Clause 1: a victory beats a tie, and a tie beats a defeat. *)
Example wv_victory_beats_tie : wle (3, 5) (5, 5) = true /\ wle (5, 5) (7, 5) = true.
Proof. split; reflexivity. Qed.

(* Clause 3: among victories, more support wins. *)
Example wv_more_support : wle (7, 2) (9, 2) = true /\ wle (9, 2) (7, 2) = false.
Proof. split; reflexivity. Qed.

(* Clause 4: with equal support, less opposition wins. *)
Example wv_less_opposition : wle (9, 4) (9, 2) = true /\ wle (9, 2) (9, 4) = false.
Proof. split; reflexivity. Qed.

(* All ties are equivalent, and share a normal form. *)
Example wv_ties_equivalent : wle (4, 4) (9, 9) = true /\ wle (9, 9) (4, 4) = true.
Proof. split; reflexivity. Qed.

Example wv_ties_share_normal_form : wnorm (4, 4) = wnorm (9, 9).
Proof. reflexivity. Qed.
