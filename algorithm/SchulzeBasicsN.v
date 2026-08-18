From Stdlib Require Import List Utf8 Lia Wf_nat Sorting.Permutation.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures
  SchulzeDefsN SchulzeOrderN SchulzeClosureN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).
Local Infix "<" := (fun x y => x ≤ y ∧ x ≠ y) (at level 70).

(* ===================================================================================== *)
(*  Schulze over a semiring: order facts about the beat relation and the winner notions *)
(*  Split out of the former monolithic SocialchoiceN.v.                                 *)
(* ===================================================================================== *)

Section SchulzeBasicsN.

  Context {Node : FinType.type}.



  
  (* ==================================================================== *)
  (*  Order-theoretic facts about O and the two notions of winner          *)
  (* ==================================================================== *)

  (** With at least two alternatives, every alternative has a rival. *)
  Lemma exists_other (x : Node) : exists y : Node, y ≠ x.
  Proof.
    pose proof (elements_two_or_more (s := Node)) as Hlen.
    pose proof (elements_nodup (s := Node)) as Hnd.
    destruct (elements (s := Node)) as [|z1 [|z2 l]] eqn:He;
      cbn in Hlen; try lia.
    inversion Hnd as [|u0 l0 Hnin Hnd'].
    assert (Hz12 : z1 ≠ z2).
    { intro Habs. apply Hnin. rewrite Habs. left. reflexivity. }
    destruct (fin_eq_dec z1 x) as [Heq|Hne].
    - exists z2. intro Habs. apply Hz12. rewrite Habs. exact Heq.
    - exists z1. exact Hne.
  Qed.

  (** Asymmetry of O (§2.2): it follows from the asymmetry of the strict
      order on path strengths, exactly as in the paper. *)
  Lemma schulze_beats_asym {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) :
    schulze_beats M a b -> ~ schulze_beats M b a.
  Proof.
    unfold schulze_beats, beats.
    intros [Hab_le Hab_ne] [Hba_le _].
    apply Hab_ne, orel_antisym; assumption.
  Qed.



  (** Beating everybody implies being unbeaten: [strict_winner ⊆ schulze_winner]. *)
  Lemma strict_winner_is_schulze_winner {R : Semiring.type}
    (M : @Matrix Node R) (a : Node) :
    strict_winner M a -> schulze_winner M a.
  Proof.
    intros Hstrict b Hb_ne_a.
    exact (schulze_beats_asym M a b (Hstrict b Hb_ne_a)).
  Qed.

  (** A strict winner leaves no other winner. *)
  Lemma strict_winner_excludes_others {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) :
    strict_winner M a -> b ≠ a -> ~ schulze_winner M b.
  Proof.
    intros Ha Hb Hwin.
    exact (Hwin a (fun h => Hb (eq_sym h)) (Ha b Hb)).
  Qed.

  (** Hence there is at most one strict winner. *)
  Lemma strict_winner_unique {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) :
    strict_winner M a -> strict_winner M b -> a = b.
  Proof.
    intros Ha Hb.
    destruct (fin_eq_dec a b) as [Heq|Hne]; [exact Heq | exfalso].
    exact (schulze_beats_asym M a b
      (Ha b (fun h => Hne (eq_sym h))) (Hb a Hne)).
  Qed.

  (** The same argument one level down, on [M] itself. *)
  Lemma condorcet_winner_unique {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node) :
    condorcet_winner M a -> condorcet_winner M b -> a = b.
  Proof.
    intros Ha Hb.
    destruct (fin_eq_dec a b) as [Heq|Hne]; [exact Heq | exfalso].
    destruct (Ha b (fun h => Hne (eq_sym h))) as [Hab_le Hab_ne].
    destruct (Hb a Hne) as [Hba_le _].
    apply Hab_ne, orel_antisym; assumption.
  Qed.


  Lemma schulze_beats_irrefl {R : Semiring.type} (M : @Matrix Node R) (a : Node) :
    ~ schulze_beats M a a.
  Proof.
    unfold schulze_beats, beats.
    intros [Hle Hneq]. apply Hneq. reflexivity.
  Qed.


  (* schulze_beats is decidable when R has decidable equality.               *)
  (* This holds in concrete semirings like max-min (Nat) or min-plus.        *)
  Lemma schulze_beats_dec {R : Semiring.type}
    (M : @Matrix Node R) (a b : Node)
    (Hdec : forall x y : R, {x = y} + {x ≠ y}) :
    {schulze_beats M a b} + {~ schulze_beats M a b}.
  Proof.
    unfold schulze_beats, beats, Orel.
    destruct (Hdec (mat_star M b a + mat_star M a b) (mat_star M a b)) as [Hle | Hnle].
    - destruct (Hdec (mat_star M b a) (mat_star M a b)) as [Heq | Hneq].
      + right. intros [H H']. apply H'. exact Heq.
      + left. split; assumption.
    - right. intros [H H']. apply Hnle. exact H.
  Qed.


  (** Either something beats [a] in the closure, or [a] is a winner.  A finite
      search, so no classical reasoning is needed to invert [schulze_winner]. *)
  Lemma beater_or_winner {R : Semiring.type}
    (Hdec : forall x y : R, {x = y} + {x ≠ y})
    (M : @Matrix Node R) (a : Node) :
    (exists x, schulze_beats M x a) \/ schulze_winner M a.
  Proof.
    set (test := fun x : Node =>
      if schulze_beats_dec M x a Hdec then true else false).
    destruct (List.filter test (@elements Node)) as [|w ws] eqn:E.
    - right. intros b Hb Hbeats.
      assert (Hin : List.In b (List.filter test (@elements Node))).
      { apply filter_In. split; [apply elements_complete |].
        unfold test. destruct (schulze_beats_dec M b a Hdec);
          [reflexivity | contradiction]. }
      rewrite E in Hin. inversion Hin.
    - left. exists w.
      assert (Hin : List.In w (List.filter test (@elements Node)))
        by (rewrite E; left; reflexivity).
      apply filter_In in Hin as [_ Ht]. unfold test in Ht.
      destruct (schulze_beats_dec M w a Hdec); [assumption | discriminate].
  Qed.

  (** Winner status is decidable when equality on the carrier is. *)
  Lemma schulze_winner_dec {R : Semiring.type} (M : @Matrix Node R) (a : Node)
    (Hdec : forall x y : R, {x = y} + {x <> y}) :
    {schulze_winner M a} + {~ schulze_winner M a}.
  Proof.
    assert (Hd : forall b : Node,
      {b <> a /\ schulze_beats M b a} + {~ (b <> a /\ schulze_beats M b a)}).
    { intro b. destruct (fin_eq_dec b a) as [E|E].
      - right. intros (Hb & _). exact (Hb E).
      - destruct (schulze_beats_dec M b a Hdec) as [Hb|Hb].
        + left. exact (conj E Hb).
        + right. intros (_ & H'). exact (Hb H'). }
    destruct (Exists_dec _ (@elements Node) Hd) as [He|Hne].
    - right. intro Hw.
      destruct (proj1 (Exists_exists _ _) He) as (b & _ & Hb & Hbeat).
      exact (Hw b Hb Hbeat).
    - left. intros b Hb Hbeat. apply Hne.
      apply (proj2 (Exists_exists _ _)).
      exists b. split; [apply elements_complete | exact (conj Hb Hbeat)].
  Qed.


  (* ------------------------------------------------------------------ *)
  (*  Version 2 — pareto_stronger (strict form):  a ≻ᵥ b ∀v  →  a ≻ b   *)
  (*                                                                      *)
  (*  The semiring alone does not decide this: with [M A B] the strongest *)
  (*  link, a route B → C → A built from equally strong links can match   *)
  (*  it, and in the max-min semiring of the Schulze example the two      *)
  (*  closures then coincide.  Schulze rules such a route out in §4.3.1   *)
  (*  by an argument outside the algebra: the links of maximal strength   *)
  (*  are exactly the unanimous ones, and unanimous preference cannot     *)
  (*  cycle because individual ballots are transitive.  That is the       *)
  (*  content of [Htop_trans] below — maximal links compose — and it is   *)
  (*  a constraint on the ballot matrix [M], not on the semiring, so the  *)
  (*  max-min instance is still covered.  [Htotal] says the natural       *)
  (*  order is total, as in [condorcet_implies_strict_winner].            *)
  (* ------------------------------------------------------------------ *)

  (** Schulze (2.2.4): a link stronger than the return closure is respected by
      the relation O.  As in the paper this is immediate from (2.2.1) and
      (2.2.3) — the link [a → b] is itself a path, so [M a b ≤ mat_star M a b],
      and the strict comparison carries across. *)
  Lemma link_beats {R : BoundedSemiring.type} (M : @Matrix Node R) (a b : Node) :
    mat_star M b a < M a b -> schulze_beats M a b.
  Proof.
    intro H. exact (orel_lt_le_trans _ _ _ H (link_le_mat_star M a b)).
  Qed.

End SchulzeBasicsN.
