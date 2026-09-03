(** * Schulze's LOSING VOTES measure

    Schulze §2.1, Example 4.  The mirror image of winning votes: strength is
    measured primarily by the OPPOSITION N[f,e], smaller being stronger, and
    among equal opposition more support is stronger.  The stratification into
    victory / tie / defeat is unchanged, as are the collapsed ties.

    The development follows WinningVotes.v exactly, with the roles of the two
    components exchanged, so [vclass] is reused from there.  As before the
    order is characterised once in [lle_spec] and every law then follows by
    arithmetic. *)

From Stdlib Require Import Utf8 Arith Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN MatN SemimoduleN OrderSemiring
  NormalizedOrder ExtendOrder SocialchoiceN SchulzeOnNT.
From Examples Require Import WinningVotes.

(** ** The order: less opposition first, then more support *)

Definition lle (p q : nat * nat) : bool :=
  if Nat.ltb (vclass p) (vclass q) then true
  else if Nat.ltb (vclass q) (vclass p) then false
  else if Nat.eqb (vclass p) 1 then true
  else if Nat.ltb (snd q) (snd p) then true
  else if Nat.ltb (snd p) (snd q) then false
  else Nat.leb (fst p) (fst q).

(** The arithmetic content of [lle], proved once. *)
Lemma lle_spec : forall p q,
  lle p q = true <->
  (vclass p < vclass q
   \/ (vclass p = vclass q
       /\ (vclass p = 1
           \/ snd q < snd p
           \/ (snd q = snd p /\ fst p <= fst q)))).
Proof.
  intros p q. unfold lle.
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
  destruct (Nat.ltb (snd q) (snd p)) eqn:E4.
  { apply Nat.ltb_lt in E4. split.
    - intros _. right. split; [exact Hcl | right; left; exact E4].
    - reflexivity. }
  apply Nat.ltb_nlt in E4.
  destruct (Nat.ltb (snd p) (snd q)) eqn:E5.
  { apply Nat.ltb_lt in E5. split; [discriminate |].
    intros [H|[_ [H|[H|[H _]]]]]; lia. }
  apply Nat.ltb_nlt in E5.
  assert (Hsnd : snd q = snd p) by lia.
  split.
  - intro H. apply Nat.leb_le in H. right. split; [exact Hcl |].
    right; right. split; [exact Hsnd | exact H].
  - intros [H|[_ [H|[H|[_ H]]]]]; try lia.
    apply Nat.leb_le. exact H.
Qed.

Lemma lle_refl : forall p, lle p p = true.
Proof. intro p. apply lle_spec. right. split; [reflexivity |]. right; right. lia. Qed.

Lemma lle_trans : forall p q r, lle p q = true -> lle q r = true -> lle p r = true.
Proof.
  intros p q r H1 H2. apply lle_spec in H1, H2. apply lle_spec.
  destruct H1 as [H1|[H1a H1b]]; destruct H2 as [H2|[H2a H2b]]; lia.
Qed.

Lemma lle_total : forall p q, lle p q = true \/ lle q p = true.
Proof.
  intros p q.
  destruct (Nat.lt_trichotomy (vclass p) (vclass q)) as [H|[H|H]].
  - left. apply lle_spec. left. exact H.
  - destruct (Nat.eq_dec (vclass p) 1) as [Hc|Hc].
    { left. apply lle_spec. right. split; [exact H | left; exact Hc]. }
    destruct (Nat.lt_trichotomy (snd q) (snd p)) as [H2|[H2|H2]].
    + left. apply lle_spec. right. split; [exact H | right; left; exact H2].
    + destruct (Nat.le_ge_cases (fst p) (fst q)) as [H3|H3].
      * left. apply lle_spec. right. split; [exact H |].
        right; right. split; [exact H2 | exact H3].
      * right. apply lle_spec. right. split; [lia |].
        right; right. split; [lia | lia].
    + right. apply lle_spec. right. split; [lia | right; left; lia].
  - right. apply lle_spec. left. exact H.
Qed.

(** ** Normalisation: only the ties collapse, exactly as before *)

Lemma lnorm_le : forall p, lle p (wnorm p) = true.
Proof.
  intro p. destruct (Nat.eq_dec (fst p) (snd p)) as [H|H].
  - rewrite (wnorm_tie p H). apply lle_spec. right.
    rewrite (vclass_tie p H), (vclass_tie (0,0) eq_refl).
    split; [reflexivity | left; reflexivity].
  - rewrite (wnorm_nontie p H). apply lle_refl.
Qed.

Lemma lnorm_ge : forall p, lle (wnorm p) p = true.
Proof.
  intro p. destruct (Nat.eq_dec (fst p) (snd p)) as [H|H].
  - rewrite (wnorm_tie p H). apply lle_spec. right.
    rewrite (vclass_tie p H), (vclass_tie (0,0) eq_refl).
    split; [reflexivity | left; reflexivity].
  - rewrite (wnorm_nontie p H). apply lle_refl.
Qed.

Lemma lnorm_compl : forall p q,
  lle p q = true -> lle q p = true -> wnorm p = wnorm q.
Proof.
  intros p q H1 H2.
  apply lle_spec in H1. apply lle_spec in H2.
  pose proof (vclass_spec p) as Sp. pose proof (vclass_spec q) as Sq.
  destruct (Nat.eq_dec (fst p) (snd p)) as [Hp|Hp].
  - assert (Hq : fst q = snd q) by lia.
    rewrite (wnorm_tie p Hp), (wnorm_tie q Hq). reflexivity.
  - assert (Hq : fst q <> snd q) by lia.
    rewrite (wnorm_nontie p Hp), (wnorm_nontie q Hq).
    destruct p as [x1 y1]; destruct q as [x2 y2]. cbn [fst snd] in *.
    assert (Hx : x1 = x2) by lia.
    assert (Hy : y1 = y2) by lia.
    rewrite Hx, Hy. reflexivity.
Qed.

(** ** …packaged *)

Definition lv_pre : PreSpec (nat * nat) :=
  {| ps_eq_dec     := wv_eq_dec;
     ps_le         := lle;
     ps_norm       := wnorm;
     ps_refl       := lle_refl;
     ps_trans      := lle_trans;
     ps_total      := lle_total;
     ps_norm_idem  := wnorm_idem;
     ps_norm_le    := lnorm_le;
     ps_norm_ge    := lnorm_ge;
     ps_norm_compl := lnorm_compl |}.

Definition lv_spec : CanonSpec (Ext (nat * nat)) := ext_spec lv_pre.

Definition LosingVotes : Type := NT lv_spec.

Check (LosingVotes : BoundedCommutativeSemiring.type).

Section LosingVotesSchulze.

  Context {Node : FinType.type}.

  Theorem lv_schulze_trans (M : @Matrix Node LosingVotes) :
    forall a b c : Node,
      schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c.
  Proof. exact (schulze_trans_normalized lv_spec M). Qed.

  Theorem lv_winner_exists (M : @Matrix Node LosingVotes) :
    exists a : Node, schulze_winner M a.
  Proof. exact (winner_exists_normalized lv_spec M). Qed.

End LosingVotesSchulze.

(** ** Sanity checks, and the contrast with winning votes *)

(** Clause 3: among victories, less opposition wins. *)
Example lv_less_opposition : lle (9, 4) (7, 2) = true /\ lle (7, 2) (9, 4) = false.
Proof. split; reflexivity. Qed.

(** Clause 4: with equal opposition, more support wins. *)
Example lv_more_support : lle (7, 2) (9, 2) = true /\ lle (9, 2) (7, 2) = false.
Proof. split; reflexivity. Qed.

(** The two measures genuinely disagree.  Winning votes prefers (9,4) — more
    support — while losing votes prefers (7,2) — less opposition.  So they
    are different voting rules, not the same rule in different clothes. *)
Example winning_and_losing_disagree :
  wle (7, 2) (9, 4) = true /\ lle (9, 4) (7, 2) = true.
Proof. split; reflexivity. Qed.
