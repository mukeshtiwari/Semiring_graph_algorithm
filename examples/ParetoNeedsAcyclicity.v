(* ========================================================================= *)
(*  The strict Pareto criterion needs more than the algebra                  *)
(*                                                                           *)
(*  [pareto_stronger] in SocialchoiceN.v carries a hypothesis                 *)
(*                                                                           *)
(*    Htop_trans : M X Y = M A B -> M Y Z = M A B -> M X Z = M A B            *)
(*                                                                           *)
(*  saying that links of maximal strength compose.  Schulze establishes the   *)
(*  corresponding fact in §4.3.1 by an argument OUTSIDE the algebra: under    *)
(*  unanimity the maximal links are exactly the unanimous ones, and unanimous *)
(*  preference cannot cycle because individual ballots are transitive.        *)
(*                                                                           *)
(*  This file shows the hypothesis cannot simply be dropped.  In the max-min  *)
(*  semiring — the one the Schulze method actually uses — every other         *)
(*  hypothesis of [pareto_stronger] can hold while its conclusion fails.      *)
(*                                                                           *)
(*  Three alternatives, strengths drawn from the chain T0 < T1 < T2 with      *)
(*  + = max and * = min:                                                      *)
(*                                                                           *)
(*    M A B = T1     M B C = T1     M C A = T1                                *)
(*                                                                           *)
(*  and every other off-diagonal entry T0.  So A beats B by the strongest     *)
(*  link available, nobody prefers B to A, and no link exceeds A -> B.  But   *)
(*  the route B -> C -> A is built from links just as strong, so it carries   *)
(*  strength T1 back to A, matching the forward strength exactly, and A does  *)
(*  NOT beat B in the closure.                                                *)
(*                                                                           *)
(*  Note what has gone wrong: B -> C -> A -> B is a CYCLE of maximal links.   *)
(*  That is precisely the configuration [Htop_trans] forbids, and precisely   *)
(*  the one transitive ballots cannot produce — so no real profile realises   *)
(*  this matrix.  The counterexample is a statement about the algebra's       *)
(*  blindness, not about voting.                                              *)
(* ========================================================================= *)

From Stdlib Require Import List Utf8 Psatz.
From HB Require Import structures.
From Semiring Require Import MatN SemimoduleN Structures OrelN SocialchoiceN.
Import ListNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y /\ x <> y) (at level 70).

Section Carrier.

  Inductive Node := NA | NB | NC.

  (** A three element chain, T0 < T1 < T2, with + = max and * = min:
      the max-min semiring in miniature. *)
  Inductive Tri := T0 | T1 | T2.

  Definition addT (u v : Tri) : Tri :=
    match u, v with
    | T2, _ | _, T2 => T2
    | T1, _ | _, T1 => T1
    | _, _ => T0
    end.

  Definition mulT (u v : Tri) : Tri :=
    match u, v with
    | T0, _ | _, T0 => T0
    | T1, _ | _, T1 => T1
    | _, _ => T2
    end.

End Carrier.

Section Instances.

  Definition fin_eq_dec (x y : Node) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition elements_list : list Node := [NA; NB; NC].

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
  Proof. cbn. nia. Qed.

  HB.instance Definition _ := IsFinType.Build Node
    elements_list elements_nodup_proof elements_complete_proof
    elements_two_or_more_proof fin_eq_dec.

  (* All laws by exhaustion over three elements. *)
  Lemma addT_assoc : forall x y z, addT (addT x y) z = addT x (addT y z).
  Proof. intros [| |] [| |] [| |]; reflexivity. Qed.
  Lemma addT_comm : forall x y, addT x y = addT y x.
  Proof. intros [| |] [| |]; reflexivity. Qed.
  Lemma addT_0l : forall x, addT T0 x = x.
  Proof. intros [| |]; reflexivity. Qed.
  Lemma addT_0r : forall x, addT x T0 = x.
  Proof. intros [| |]; reflexivity. Qed.

  HB.instance Definition _ := IsCommutativeMonoid.Build Tri
    T0 addT addT_assoc addT_comm addT_0l addT_0r.

  Lemma mulT_assoc : forall x y z, mulT (mulT x y) z = mulT x (mulT y z).
  Proof. intros [| |] [| |] [| |]; reflexivity. Qed.
  Lemma mulT_1l : forall x, mulT T2 x = x.
  Proof. intros [| |]; reflexivity. Qed.
  Lemma mulT_1r : forall x, mulT x T2 = x.
  Proof. intros [| |]; reflexivity. Qed.
  Lemma mulT_distr_r : forall x y z, mulT (addT x y) z = addT (mulT x z) (mulT y z).
  Proof. intros [| |] [| |] [| |]; reflexivity. Qed.
  Lemma mulT_distr_l : forall x y z, mulT x (addT y z) = addT (mulT x y) (mulT x z).
  Proof. intros [| |] [| |] [| |]; reflexivity. Qed.
  Lemma mulT_0l : forall x, mulT T0 x = T0.
  Proof. intros [| |]; reflexivity. Qed.
  Lemma mulT_0r : forall x, mulT x T0 = T0.
  Proof. intros [| |]; reflexivity. Qed.

  HB.instance Definition _ := IsSemiring.Build Tri
    T2 mulT mulT_assoc mulT_1l mulT_1r
    mulT_distr_r mulT_distr_l mulT_0l mulT_0r.

  Lemma mulT_comm : forall x y, mulT x y = mulT y x.
  Proof. intros [| |] [| |]; reflexivity. Qed.

  HB.instance Definition _ := IsCommutativeSemiring.Build Tri mulT_comm.

  Lemma addT_bound : forall x, addT T2 x = T2.
  Proof. intros [| |]; reflexivity. Qed.

  HB.instance Definition _ := IsBoundedSemiring.Build Tri addT_bound.

End Instances.

Section Counterexample.

  (** A -> B, B -> C and C -> A all at the maximal strength T1. *)
  Definition M (i j : Node) : Tri :=
    match i, j with
    | NA, NA => T2 | NB, NB => T2 | NC, NC => T2
    | NA, NB => T1
    | NB, NC => T1
    | NC, NA => T1
    | _, _ => T0
    end.

  (* --- every hypothesis of pareto_stronger except Htop_trans --- *)

  Lemma hyp_distinct : NA <> NB.
  Proof. discriminate. Qed.

  Lemma hyp_zero : M NB NA = T0.
  Proof. reflexivity. Qed.

  Lemma hyp_pos : T0 < M NA NB.
  Proof. split; [reflexivity | discriminate]. Qed.

  Lemma hyp_max : forall X Y : Node, X <> Y -> M X Y ≤ M NA NB.
  Proof. intros [| |] [| |] H; try reflexivity; congruence. Qed.

  Lemma hyp_diag : forall i j : Node, i = j -> M i j = T2.
  Proof. intros [| |] [| |] H; try reflexivity; discriminate. Qed.

  (* --- but the acyclicity hypothesis fails --- *)

  (** [B -> C] and [C -> A] are both maximal, yet [B -> A] is not: the three
      maximal links form a cycle. *)
  Theorem htop_trans_fails :
    ~ (forall X Y Z : Node,
         M X Y = M NA NB -> M Y Z = M NA NB -> M X Z = M NA NB).
  Proof.
    intro H. specialize (H NB NC NA eq_refl eq_refl). discriminate.
  Qed.

  (* --- and so does the conclusion --- *)

  (** Both closures are T1: the return route B -> C -> A is exactly as strong
      as the direct link A -> B. *)
  Lemma star_AB : mat_star M NA NB = T1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma star_BA : mat_star M NB NA = T1.
  Proof. vm_compute. reflexivity. Qed.

  Theorem pareto_conclusion_fails : ~ schulze_beats M NA NB.
  Proof.
    intros [_ Hne]. apply Hne. rewrite star_AB, star_BA. reflexivity.
  Qed.

  (** So [Htop_trans] is not removable: dropping it leaves a statement with
      a counterexample in the method's own semiring. *)
  Theorem pareto_stronger_needs_acyclicity :
    ~ (forall (R : BoundedSemiring.type) (N : @Matrix Node R) (A B : Node),
         A <> B -> N B A = zero -> zero < N A B ->
         (forall X Y, X <> Y -> N X Y ≤ N A B) ->
         (forall i j, i = j -> N i j = one) ->
         schulze_beats N A B).
  Proof.
    intro H.
    exact (pareto_conclusion_fails
             (H Tri M NA NB hyp_distinct hyp_zero hyp_pos hyp_max hyp_diag)).
  Qed.

End Counterexample.
