From Stdlib Require Import List Utf8 Lia.
From Semiring Require Import PathN MatN OrelN
  SemimoduleN Structures SocialchoiceN
  ClosureTransportN BeatsOnN.
Import ListNotations SemiringNotations.

Local Infix "≤" := Orel (at level 70).

(* ====================================================================== *)
(*  Independence of clones (Schulze, Section 4.6).                       *)
(*                                                                       *)
(*  One alternative [d] is replaced by a set of clones [K].  Both        *)
(*  elections run over a single ambient [Node] type and differ only in   *)
(*  which candidate list the closure folds over, which is what makes the *)
(*  comparison statable at all.  Both matrices carry [1] on the          *)
(*  diagonal, the standing hypothesis used throughout SemimoduleN.       *)
(* ====================================================================== *)

Section CloneReplacement.

  Context {Node : FinType.type}.
  Context {R : BoundedSemiring.type}.

  (** [A_old] is the original list of alternatives, [d] one of them, and [K]
      a nonempty set of fresh alternatives that replaces it. *)
  Context (A_old K : list Node) (d : Node)
          (M_old M_new : @OrelN.Matrix Node R).

  Hypothesis Hd_old : List.In d A_old.
  Hypothesis HK_nonempty : K <> [].
  Hypothesis HK_fresh : forall x, List.In x K -> ~ List.In x A_old.

  Hypothesis Hdiag_old : forall u v : Node, u = v -> M_old u v = 1.
  Hypothesis Hdiag_new : forall u v : Node, u = v -> M_new u v = 1.

  (** Schulze's (4.6.13): every clone inherits the outgoing edges of [d]. *)
  Hypothesis Hclone_out : forall a g, List.In a A_old -> a <> d ->
    List.In g K -> M_new g a = M_old d a.
  (** Schulze's (4.6.12): every clone inherits the incoming edges of [d]. *)
  Hypothesis Hclone_in : forall a g, List.In a A_old -> a <> d ->
    List.In g K -> M_new a g = M_old a d.
  (** Schulze's (4.6.14): edges between surviving alternatives are untouched.
      Nothing at all is assumed about edges *between* clones. *)
  Hypothesis Hclone_ext : forall a b, List.In a A_old -> a <> d ->
    List.In b A_old -> b <> d -> M_new a b = M_old a b.

  (** [A_new = (A_old ∪ K) \ {d}]. *)
  Definition A_new : list Node := List.remove fin_eq_dec d A_old ++ K.

  (** Sending [d] to a chosen clone [g] carries an old path to a new one. *)
  Definition expand (g : Node) : Node -> Node :=
    fun x => if fin_eq_dec x d then g else x.

  (** Sending every clone back to [d] carries a new path to an old one. *)
  Definition collapse : Node -> Node :=
    fun x => if List.in_dec fin_eq_dec x K then d else x.

  (* ------------------------------------------------------------------ *)
  (*  Membership bookkeeping                                             *)
  (* ------------------------------------------------------------------ *)

  Lemma A_new_nonempty : A_new <> [].
  Proof.
    unfold A_new. intro Hnil.
    apply app_eq_nil in Hnil. destruct Hnil as [_ HK].
    exact (HK_nonempty HK).
  Qed.

  Lemma A_old_nonempty : A_old <> [].
  Proof.
    intro Hnil. rewrite Hnil in Hd_old. inversion Hd_old.
  Qed.

  Lemma in_A_new_intro_old (x : Node) :
    List.In x A_old -> x <> d -> List.In x A_new.
  Proof.
    intros Hx Hne. unfold A_new. apply in_or_app. left.
    apply in_in_remove; assumption.
  Qed.

  Lemma in_A_new_intro_clone (g : Node) :
    List.In g K -> List.In g A_new.
  Proof.
    intros Hg. unfold A_new. apply in_or_app. right. exact Hg.
  Qed.

  Lemma in_A_new_inv (x : Node) :
    List.In x A_new ->
    (List.In x A_old /\ x <> d /\ ~ List.In x K) \/ List.In x K.
  Proof.
    intros Hx. unfold A_new in Hx. apply in_app_or in Hx.
    destruct Hx as [Hx | Hx].
    - apply in_remove in Hx. destruct Hx as [Hx_old Hx_ne].
      left. split; [exact Hx_old | split; [exact Hx_ne |]].
      intro Hx_K. exact (HK_fresh x Hx_K Hx_old).
    - right. exact Hx.
  Qed.

  (** An original alternative is never a clone. *)
  Lemma old_not_clone (x : Node) : List.In x A_old -> ~ List.In x K.
  Proof.
    intros Hx Hx_K. exact (HK_fresh x Hx_K Hx).
  Qed.

  Lemma collapse_old (x : Node) : List.In x A_old -> collapse x = x.
  Proof.
    intros Hx. unfold collapse.
    destruct (List.in_dec fin_eq_dec x K) as [Hin | Hnin];
      [exfalso; exact (old_not_clone x Hx Hin) | reflexivity].
  Qed.

  Lemma collapse_clone (g : Node) : List.In g K -> collapse g = d.
  Proof.
    intros Hg. unfold collapse.
    destruct (List.in_dec fin_eq_dec g K) as [Hin | Hnin];
      [reflexivity | contradiction].
  Qed.

  Lemma expand_other (g x : Node) : x <> d -> expand g x = x.
  Proof.
    intros Hne. unfold expand.
    destruct (fin_eq_dec x d) as [Heq | _]; [contradiction | reflexivity].
  Qed.

  Lemma expand_d (g : Node) : expand g d = g.
  Proof.
    unfold expand.
    destruct (fin_eq_dec d d) as [_ | Hc];
      [reflexivity | exfalso; apply Hc; reflexivity].
  Qed.

  Lemma in_cons2 (c e x : Node) (l : list Node) :
    List.In c l -> List.In e l -> List.In x (c :: e :: l) -> List.In x l.
  Proof.
    intros Hc He Hx.
    destruct Hx as [Hx | [Hx | Hx]]; [subst x; exact Hc | subst x; exact He | exact Hx].
  Qed.

  Lemma nonempty_has_member {A : Type} (l : list A) :
    l <> [] -> exists x, List.In x l.
  Proof.
    destruct l as [|x t]; intros Hne.
    - exfalso. apply Hne. reflexivity.
    - exists x. left. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The two transports                                                 *)
  (* ------------------------------------------------------------------ *)

  (** Expansion: replacing [d] by a chosen clone [g] carries the old closure
      below the new one.  Every edge of the image has exactly the weight the
      original edge had, by the three clone hypotheses. *)
  Lemma expand_transport (g c e : Node) :
    List.In g K -> List.In c A_old -> List.In e A_old ->
    path_star A_old M_old c e ≤ path_star A_new M_new (expand g c) (expand g e).
  Proof.
    intros Hg Hc He.
    apply path_star_transport.
    - exact A_new_nonempty.
    - exact Hdiag_old.
    - exact Hdiag_new.
    - intros x Hx.
      pose proof (in_cons2 c e x A_old Hc He Hx) as Hx_old.
      destruct (fin_eq_dec x d) as [Heq | Hne].
      + subst x. rewrite expand_d. exact (in_A_new_intro_clone g Hg).
      + rewrite (expand_other g x Hne). exact (in_A_new_intro_old x Hx_old Hne).
    - intros a b Ha Hb.
      pose proof (in_cons2 c e a A_old Hc He Ha) as Ha_old.
      pose proof (in_cons2 c e b A_old Hc He Hb) as Hb_old.
      destruct (fin_eq_dec a d) as [Had | Han];
        destruct (fin_eq_dec b d) as [Hbd | Hbn].
      + subst a b. rewrite !expand_d.
        rewrite (Hdiag_old d d eq_refl), (Hdiag_new g g eq_refl).
        apply bounded_orel_refl.
      + subst a. rewrite expand_d, (expand_other g b Hbn).
        rewrite (Hclone_out b g Hb_old Hbn Hg).
        apply bounded_orel_refl.
      + subst b. rewrite (expand_other g a Han), expand_d.
        rewrite (Hclone_in a g Ha_old Han Hg).
        apply bounded_orel_refl.
      + rewrite (expand_other g a Han), (expand_other g b Hbn).
        rewrite (Hclone_ext a b Ha_old Han Hb_old Hbn).
        apply bounded_orel_refl.
  Qed.

  (** Collapse: sending every clone back to [d] carries the new closure below
      the old one.  The three boundary cases are equalities again; only the
      clone-to-clone edges lose information, and there the bound is [1].  This
      is the one step where boundedness of the semiring is genuinely used, and
      it is why independence of clones sits with transitivity and winner
      existence rather than with neutrality and monotonicity. *)
  Lemma collapse_transport (c e : Node) :
    List.In c A_new -> List.In e A_new ->
    path_star A_new M_new c e ≤ path_star A_old M_old (collapse c) (collapse e).
  Proof.
    intros Hc He.
    apply path_star_transport.
    - exact A_old_nonempty.
    - exact Hdiag_new.
    - exact Hdiag_old.
    - intros x Hx.
      pose proof (in_cons2 c e x A_new Hc He Hx) as Hx_new.
      destruct (in_A_new_inv x Hx_new) as [[Hx_old [Hx_ne _]] | Hx_K].
      + rewrite (collapse_old x Hx_old). exact Hx_old.
      + rewrite (collapse_clone x Hx_K). exact Hd_old.
    - intros a b Ha Hb.
      pose proof (in_cons2 c e a A_new Hc He Ha) as Ha_new.
      pose proof (in_cons2 c e b A_new Hc He Hb) as Hb_new.
      destruct (in_A_new_inv a Ha_new) as [[Ha_old [Ha_ne _]] | Ha_K];
        destruct (in_A_new_inv b Hb_new) as [[Hb_old [Hb_ne _]] | Hb_K].
      + rewrite (collapse_old a Ha_old), (collapse_old b Hb_old).
        rewrite (Hclone_ext a b Ha_old Ha_ne Hb_old Hb_ne).
        apply bounded_orel_refl.
      + rewrite (collapse_old a Ha_old), (collapse_clone b Hb_K).
        rewrite (Hclone_in a b Ha_old Ha_ne Hb_K).
        apply bounded_orel_refl.
      + rewrite (collapse_clone a Ha_K), (collapse_old b Hb_old).
        rewrite (Hclone_out b a Hb_old Hb_ne Ha_K).
        apply bounded_orel_refl.
      + rewrite (collapse_clone a Ha_K), (collapse_clone b Hb_K).
        rewrite (Hdiag_old d d eq_refl).
        apply le_one.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Path strengths are preserved (Schulze 4.6.21 to 4.6.23)           *)
  (* ------------------------------------------------------------------ *)

  (** (4.6.23) Strengths between surviving alternatives are unchanged. *)
  Theorem clone_strength_survivors (a b : Node) :
    List.In a A_old -> a <> d -> List.In b A_old -> b <> d ->
    path_star A_new M_new a b = path_star A_old M_old a b.
  Proof.
    intros Ha Ha_ne Hb Hb_ne.
    destruct (nonempty_has_member K HK_nonempty) as [g Hg].
    apply orel_antisym.
    - pose proof (collapse_transport a b
        (in_A_new_intro_old a Ha Ha_ne) (in_A_new_intro_old b Hb Hb_ne)) as H.
      rewrite (collapse_old a Ha), (collapse_old b Hb) in H. exact H.
    - pose proof (expand_transport g a b Hg Ha Hb) as H.
      rewrite (expand_other g a Ha_ne), (expand_other g b Hb_ne) in H. exact H.
  Qed.

  (** (4.6.21) The strength into any clone equals the old strength into [d]. *)
  Theorem clone_strength_to_clone (a g : Node) :
    List.In a A_old -> a <> d -> List.In g K ->
    path_star A_new M_new a g = path_star A_old M_old a d.
  Proof.
    intros Ha Ha_ne Hg.
    apply orel_antisym.
    - pose proof (collapse_transport a g
        (in_A_new_intro_old a Ha Ha_ne) (in_A_new_intro_clone g Hg)) as H.
      rewrite (collapse_old a Ha), (collapse_clone g Hg) in H. exact H.
    - pose proof (expand_transport g a d Hg Ha Hd_old) as H.
      rewrite (expand_other g a Ha_ne), expand_d in H. exact H.
  Qed.

  (** (4.6.22) The strength out of any clone equals the old strength out of
      [d].  In particular all clones are pairwise indistinguishable from the
      outside, however they compare among themselves. *)
  Theorem clone_strength_from_clone (a g : Node) :
    List.In a A_old -> a <> d -> List.In g K ->
    path_star A_new M_new g a = path_star A_old M_old d a.
  Proof.
    intros Ha Ha_ne Hg.
    apply orel_antisym.
    - pose proof (collapse_transport g a
        (in_A_new_intro_clone g Hg) (in_A_new_intro_old a Ha Ha_ne)) as H.
      rewrite (collapse_clone g Hg), (collapse_old a Ha) in H. exact H.
    - pose proof (expand_transport g d a Hg Hd_old Ha) as H.
      rewrite expand_d, (expand_other g a Ha_ne) in H. exact H.
  Qed.
  (** A clone beats a survivor exactly when [d] used to — the two directions
      of Schulze's (4.6.5): [db ∈ O_old ⇔ gb ∈ O_new]. *)
  Lemma clone_beats_survivor (g a : Node) :
    List.In g K -> List.In a A_old -> a <> d ->
    beats_on A_new M_new g a -> beats_on A_old M_old d a.
  Proof.
    intros Hg Ha Ha_ne Hbeats.
    apply (beats_on_congr A_new M_new A_old M_old g a d a);
      [ exact (clone_strength_from_clone a g Ha Ha_ne Hg)
      | exact (clone_strength_to_clone a g Ha Ha_ne Hg)
      | exact Hbeats ].
  Qed.

  Lemma d_beats_survivor (g a : Node) :
    List.In g K -> List.In a A_old -> a <> d ->
    beats_on A_old M_old d a -> beats_on A_new M_new g a.
  Proof.
    intros Hg Ha Ha_ne Hbeats.
    apply (beats_on_congr A_old M_old A_new M_new d a g a);
      [ exact (eq_sym (clone_strength_from_clone a g Ha Ha_ne Hg))
      | exact (eq_sym (clone_strength_to_clone a g Ha Ha_ne Hg))
      | exact Hbeats ].
  Qed.

  (** A survivor beats a clone exactly when it used to beat [d] — the two
      directions of Schulze's (4.6.4): [ad ∈ O_old ⇔ ag ∈ O_new]. *)
  Lemma survivor_beats_clone (b g : Node) :
    List.In g K -> List.In b A_old -> b <> d ->
    beats_on A_new M_new b g -> beats_on A_old M_old b d.
  Proof.
    intros Hg Hb Hb_ne Hbeats.
    apply (beats_on_congr A_new M_new A_old M_old b g b d);
      [ exact (clone_strength_to_clone b g Hb Hb_ne Hg)
      | exact (clone_strength_from_clone b g Hb Hb_ne Hg)
      | exact Hbeats ].
  Qed.

  Lemma survivor_beats_d (b g : Node) :
    List.In g K -> List.In b A_old -> b <> d ->
    beats_on A_old M_old b d -> beats_on A_new M_new b g.
  Proof.
    intros Hg Hb Hb_ne Hbeats.
    apply (beats_on_congr A_old M_old A_new M_new b d b g);
      [ exact (eq_sym (clone_strength_to_clone b g Hb Hb_ne Hg))
      | exact (eq_sym (clone_strength_from_clone b g Hb Hb_ne Hg))
      | exact Hbeats ].
  Qed.

  (** Survivors beat each other exactly as before — the two directions of
      Schulze's (4.6.6): [ab ∈ O_old ⇔ ab ∈ O_new]. *)
  Lemma survivors_beat_new_old (a b : Node) :
    List.In a A_old -> a <> d -> List.In b A_old -> b <> d ->
    beats_on A_new M_new a b -> beats_on A_old M_old a b.
  Proof.
    intros Ha Ha_ne Hb Hb_ne Hbeats.
    apply (beats_on_congr A_new M_new A_old M_old a b a b);
      [ exact (clone_strength_survivors a b Ha Ha_ne Hb Hb_ne)
      | exact (clone_strength_survivors b a Hb Hb_ne Ha Ha_ne)
      | exact Hbeats ].
  Qed.

  Lemma survivors_beat_old_new (a b : Node) :
    List.In a A_old -> a <> d -> List.In b A_old -> b <> d ->
    beats_on A_old M_old a b -> beats_on A_new M_new a b.
  Proof.
    intros Ha Ha_ne Hb Hb_ne Hbeats.
    apply (beats_on_congr A_old M_old A_new M_new a b a b);
      [ exact (eq_sym (clone_strength_survivors a b Ha Ha_ne Hb Hb_ne))
      | exact (eq_sym (clone_strength_survivors b a Hb Hb_ne Ha Ha_ne))
      | exact Hbeats ].
  Qed.
  (** (4.6.8) A surviving alternative wins the new election exactly when it
      won the old one.  This needs nothing beyond the three strength
      equalities, so no selectivity assumption on the semiring appears. *)
  Theorem clone_winner_survivors (a : Node) :
    List.In a A_old -> a <> d ->
    (winner_on A_old M_old a <-> winner_on A_new M_new a).
  Proof.
    intros Ha Ha_ne. split.
    - intros Hwin b Hb_new Hb_ne Hbeats.
      destruct (in_A_new_inv b Hb_new) as [[Hb_old [Hb_d _]] | Hb_K].
      + exact (Hwin b Hb_old Hb_ne
                 (survivors_beat_new_old b a Hb_old Hb_d Ha Ha_ne Hbeats)).
      + apply (Hwin d Hd_old (fun h => Ha_ne (eq_sym h))).
        exact (clone_beats_survivor b a Hb_K Ha Ha_ne Hbeats).
    - intros Hwin b Hb_old Hb_ne Hbeats.
      destruct (fin_eq_dec b d) as [Hbd | Hbn].
      + subst b.
        destruct (nonempty_has_member K HK_nonempty) as [g Hg].
        assert (Hg_ne : g <> a).
        { intro Heq. subst g. exact (old_not_clone a Ha Hg). }
        exact (Hwin g (in_A_new_intro_clone g Hg) Hg_ne
                 (d_beats_survivor g a Hg Ha Ha_ne Hbeats)).
      + exact (Hwin b (in_A_new_intro_old b Hb_old Hbn) Hb_ne
                 (survivors_beat_old_new b a Hb_old Hbn Ha Ha_ne Hbeats)).
  Qed.

  (** Half of (4.6.7): if any clone wins the new election then [d] won the old
      one.  Contrapositively, a beaten [d] leaves every clone beaten. *)
  Theorem clone_winner_implies_d_winner (g : Node) :
    List.In g K -> winner_on A_new M_new g -> winner_on A_old M_old d.
  Proof.
    intros Hg Hwin b Hb_old Hb_ne Hbeats.
    assert (Hb_ne_g : b <> g).
    { intro Heq. subst b. exact (HK_fresh g Hg Hb_old). }
    exact (Hwin b (in_A_new_intro_old b Hb_old Hb_ne) Hb_ne_g
             (survivor_beats_d b g Hg Hb_old Hb_ne Hbeats)).
  Qed.

  (** The other half.  No survivor can beat a clone, so the only obstacle is
      the clones beating one another, and a maximal clone under the new beat
      relation is therefore a winner.  This is the one step that needs the
      beat relation to be transitive and decidable, exactly as Schulze's own
      proof invokes asymmetry and transitivity of [O_new].  Both are supplied
      by [beats_on_trans] and [beats_on_dec] below; they are left as
      hypotheses here so that the statement stays independent of which
      selectivity assumptions one is willing to make. *)
  Theorem d_winner_implies_clone_winner
    (Htrans : forall x y z, List.In x A_new -> List.In y A_new -> List.In z A_new ->
                beats_on A_new M_new x y -> beats_on A_new M_new y z ->
                beats_on A_new M_new x z)
    (Hdecb : forall x y, {beats_on A_new M_new x y} + {~ beats_on A_new M_new x y}) :
    winner_on A_old M_old d ->
    exists g, List.In g K /\ winner_on A_new M_new g.
  Proof.
    intros Hwin_d.
    destruct (exists_maximal_in (beats_on A_new M_new) K
                (fun x y z Hx Hy Hz => Htrans x y z
                   (in_A_new_intro_clone x Hx) (in_A_new_intro_clone y Hy)
                   (in_A_new_intro_clone z Hz))
                (fun x _ => beats_on_irrefl A_new M_new x)
                Hdecb HK_nonempty) as [w [Hw Hwmax]].
    exists w. split; [exact Hw |].
    intros b Hb_new Hb_ne Hbeats.
    destruct (in_A_new_inv b Hb_new) as [[Hb_old [Hb_d _]] | Hb_K].
    - exact (Hwin_d b Hb_old Hb_d
               (survivor_beats_clone b w Hw Hb_old Hb_d Hbeats)).
    - exact (Hwmax b Hb_K Hbeats).
  Qed.

  (** Independence of clones (4.6.7 and 4.6.8 together): replacing an
      alternative by a set of clones leaves the winner status of every other
      alternative untouched, and puts a clone in the winner set exactly when
      the replaced alternative was in it. *)
  Theorem independence_of_clones
    (Htrans : forall x y z, List.In x A_new -> List.In y A_new -> List.In z A_new ->
                beats_on A_new M_new x y -> beats_on A_new M_new y z ->
                beats_on A_new M_new x z)
    (Hdecb : forall x y, {beats_on A_new M_new x y} + {~ beats_on A_new M_new x y}) :
    (forall a, List.In a A_old -> a <> d ->
       (winner_on A_old M_old a <-> winner_on A_new M_new a))
    /\ (winner_on A_old M_old d <-> exists g, List.In g K /\ winner_on A_new M_new g).
  Proof.
    split.
    - exact clone_winner_survivors.
    - split.
      + exact (d_winner_implies_clone_winner Htrans Hdecb).
      + intros [g [Hg Hwin]]. exact (clone_winner_implies_d_winner g Hg Hwin).
  Qed.

  (** Independence of clones with the two order hypotheses discharged.  The
      three assumptions are exactly the ones SocialchoiceN carries for the
      corresponding results about [mat_star]: the order on path strengths is
      total, equality on strengths is decidable, and multiplication is a
      greatest lower bound.  Nothing about clones is assumed beyond the three
      hypotheses of this section. *)
  Theorem independence_of_clones_selective
    (H_total_order : forall x y : R, x + y = x \/ x + y = y)
    (HdecR : forall x y : R, {x = y} + {x <> y})
    (H_meet_lower_bound : forall u v w : R, u ≤ v -> u ≤ w -> u ≤ v * w) :
    (forall a, List.In a A_old -> a <> d ->
       (winner_on A_old M_old a <-> winner_on A_new M_new a))
    /\ (winner_on A_old M_old d <-> exists g, List.In g K /\ winner_on A_new M_new g).
  Proof.
    apply independence_of_clones.
    - exact (beats_on_trans A_new M_new A_new_nonempty Hdiag_new
               H_total_order H_meet_lower_bound).
    - exact (beats_on_dec HdecR A_new M_new).
  Qed.
End CloneReplacement.
