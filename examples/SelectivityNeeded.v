(* ========================================================================= *)
(*  Selectivity is not removable from the transitivity theorem                *)
(*                                                                           *)
(*  [schulze_trans_weaker] assumes two things about the carrier:              *)
(*                                                                           *)
(*    H_total_order      : forall x y, x + y = x \/ x + y = y   (selectivity) *)
(*    H_meet_lower_bound : m <= a -> m <= b -> m <= a * b                     *)
(*                                                                           *)
(*  This file shows the first cannot be dropped, even keeping the second.     *)
(*                                                                           *)
(*  The witness is the four-element Boolean algebra B = {Bot, Ba, Bb, Top}    *)
(*  with Ba, Bb incomparable, + = join and * = meet.  It is a bounded         *)
(*  commutative semiring — indeed a distributive path algebra — and the meet  *)
(*  is the greatest lower bound, so H_meet_lower_bound holds.  It is not      *)
(*  selective: Ba + Bb = Top is neither Ba nor Bb.                            *)
(*                                                                           *)
(*  On three nodes with                                                       *)
(*                                                                           *)
(*      M X Y = Ba      M Y Z = Bb      every other off-diagonal = Bot        *)
(*                                                                           *)
(*  we get X beats Y and Y beats Z, but X does NOT beat Z: the two victories  *)
(*  have incomparable strengths, so the route through Y carries              *)
(*  Ba * Bb = Bot and nothing composes.  The Schulze relation is therefore    *)
(*  not transitive, and with it the winner set can be empty.                  *)
(*                                                                           *)
(*  Note what this does and does not show.  It shows selectivity is not       *)
(*  removable.  It does NOT show every non-selective algebra fails: the       *)
(*  construction turns on Ba * Bb = Bot, and incomparable elements whose      *)
(*  meet is above Bot would defeat this particular matrix.                    *)
(* ========================================================================= *)

From Stdlib Require Import List Utf8 Psatz.
From HB Require Import structures.
From Semiring Require Import MatN SemimoduleN Structures OrelN SocialchoiceN.
Import ListNotations SemiringNotations.

Section Carrier.

  (* Three alternatives *)
  Inductive Node := X | Y | Z.

  (* The four-element Boolean algebra: Ba and Bb are incomparable *)
  Inductive B := Bot | Ba | Bb | Top.

  (* join *)
  Definition addB (u v : B) : B :=
    match u, v with
    | Bot, w => w
    | w, Bot => w
    | Top, _ => Top
    | _, Top => Top
    | Ba, Ba => Ba
    | Bb, Bb => Bb
    | Ba, Bb => Top
    | Bb, Ba => Top
    end.

  (* meet *)
  Definition mulB (u v : B) : B :=
    match u, v with
    | Bot, _ => Bot
    | _, Bot => Bot
    | Top, w => w
    | w, Top => w
    | Ba, Ba => Ba
    | Bb, Bb => Bb
    | Ba, Bb => Bot
    | Bb, Ba => Bot
    end.

End Carrier.

Section Instances.

  Definition fin_eq_dec (x y : Node) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition elements_list : list Node := [X; Y; Z].

  Lemma elements_nodup_proof : NoDup elements_list.
  Proof.
    unfold elements_list.
    apply NoDup_cons; [intro H; cbn in H; intuition discriminate |].
    apply NoDup_cons; [intro H; cbn in H; intuition discriminate |].
    apply NoDup_cons; [intro H; cbn in H; intuition |].
    apply NoDup_nil.
  Qed.

  Lemma elements_complete_proof : forall x : Node, In x elements_list.
  Proof. intros [ | | ]; cbn; auto. Qed.

  Lemma elements_two_or_more_proof : (2 <= List.length elements_list)%nat.
  Proof. cbn. lia. Qed.

  HB.instance Definition _ := IsFinType.Build Node
    elements_list elements_nodup_proof elements_complete_proof
    elements_two_or_more_proof fin_eq_dec.

  (* --- B is a bounded commutative semiring, all laws by exhaustion --- *)

  Lemma addB_assoc : forall x y z, addB (addB x y) z = addB x (addB y z).
  Proof. intros [| | |] [| | |] [| | |]; reflexivity. Qed.

  Lemma addB_comm : forall x y, addB x y = addB y x.
  Proof. intros [| | |] [| | |]; reflexivity. Qed.

  Lemma addB_0l : forall x, addB Bot x = x.
  Proof. intros [| | |]; reflexivity. Qed.

  Lemma addB_0r : forall x, addB x Bot = x.
  Proof. intros [| | |]; reflexivity. Qed.

  HB.instance Definition _ := IsCommutativeMonoid.Build B
    Bot addB addB_assoc addB_comm addB_0l addB_0r.

  Lemma mulB_assoc : forall x y z, mulB (mulB x y) z = mulB x (mulB y z).
  Proof. intros [| | |] [| | |] [| | |]; reflexivity. Qed.

  Lemma mulB_1l : forall x, mulB Top x = x.
  Proof. intros [| | |]; reflexivity. Qed.

  Lemma mulB_1r : forall x, mulB x Top = x.
  Proof. intros [| | |]; reflexivity. Qed.

  Lemma mulB_distr_r : forall x y z, mulB (addB x y) z = addB (mulB x z) (mulB y z).
  Proof. intros [| | |] [| | |] [| | |]; reflexivity. Qed.

  Lemma mulB_distr_l : forall x y z, mulB x (addB y z) = addB (mulB x y) (mulB x z).
  Proof. intros [| | |] [| | |] [| | |]; reflexivity. Qed.

  Lemma mulB_0l : forall x, mulB Bot x = Bot.
  Proof. intros [| | |]; reflexivity. Qed.

  Lemma mulB_0r : forall x, mulB x Bot = Bot.
  Proof. intros [| | |]; reflexivity. Qed.

  HB.instance Definition _ := IsSemiring.Build B
    Top mulB mulB_assoc mulB_1l mulB_1r
    mulB_distr_r mulB_distr_l mulB_0l mulB_0r.

  Lemma mulB_comm : forall x y, mulB x y = mulB y x.
  Proof. intros [| | |] [| | |]; reflexivity. Qed.

  HB.instance Definition _ := IsCommutativeSemiring.Build B mulB_comm.

  Lemma addB_bound : forall x, addB Top x = Top.
  Proof. intros [| | |]; reflexivity. Qed.

  HB.instance Definition _ := IsBoundedSemiring.Build B addB_bound.

End Instances.

Section Counterexample.

  (* B is NOT selective: the join of the two incomparable elements is Top. *)
  Lemma B_not_selective :
    ~ (forall x y : B, addB x y = x \/ addB x y = y).
  Proof.
    intro Hsel. destruct (Hsel Ba Bb) as [Habs|Habs]; discriminate.
  Qed.

  (* …but the meet IS the greatest lower bound, so the other hypothesis of
     [schulze_trans_weaker] holds. *)
  Lemma B_meet_lower_bound : forall m a b : B,
    Orel m a -> Orel m b -> Orel m (mulB a b).
  Proof.
    intros [| | |] [| | |] [| | |] Hma Hmb;
      cbn in *; try reflexivity; try discriminate.
  Qed.

  (* X --Ba--> Y --Bb--> Z, and nothing else. *)
  Definition M (i j : Node) : B :=
    match i, j with
    | X, X => Top | Y, Y => Top | Z, Z => Top
    | X, Y => Ba
    | Y, Z => Bb
    | _, _ => Bot
    end.

  Theorem X_beats_Y : schulze_beats M X Y.
  Proof. split; vm_compute; [reflexivity | discriminate]. Qed.

  Theorem Y_beats_Z : schulze_beats M Y Z.
  Proof. split; vm_compute; [reflexivity | discriminate]. Qed.

  (** The route X ⇝ Z through Y carries [Ba * Bb = Bot], and there is no
      other route, so both closure entries collapse to the bottom and the
      strictness clause fails. *)
  Theorem X_does_not_beat_Z : ~ schulze_beats M X Z.
  Proof.
    assert (Hxz : mat_star M X Z = Bot) by (vm_compute; reflexivity).
    assert (Hzx : mat_star M Z X = Bot) by (vm_compute; reflexivity).
    intros [_ Hne]. apply Hne. rewrite Hzx, Hxz. reflexivity.
  Qed.

  (** The Schulze relation is not transitive without selectivity. *)
  Theorem schulze_beats_not_transitive :
    ~ (forall a b c : Node,
         schulze_beats M a b -> schulze_beats M b c -> schulze_beats M a c).
  Proof.
    intro Htrans.
    exact (X_does_not_beat_Z (Htrans X Y Z X_beats_Y Y_beats_Z)).
  Qed.

End Counterexample.
