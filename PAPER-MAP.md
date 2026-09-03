# Map between Schulze's paper and the Rocq development

This file maps the definitions, equations, and claims of

> Markus Schulze, *A new monotonic, clone-independent, reversal symmetric,
> and condorcet-consistent single-winner election method*,
> Social Choice and Welfare (2011) 36:267–303
> (the file `algorithm/schulze-paper.pdf`)

to the Rocq formalisation in `algorithm/`. Equation numbers such as
(4.3.2.10) are the paper's own display numbers.

## How to read the correspondence

The formalisation has two layers.

The **matrix layer**, where the algebra lives, works at the pairwise level
over an abstract (bounded) semiring: a profile is a matrix
`M : Node -> Node -> R` whose entry `M a b` is the *strength* of the link
`ab`, playing the role of the paper's pair `(N[a,b], N[b,a])` under the
order `≻_D`. Every criterion is stated and proved here, so it holds of any
matrix over any carrier satisfying the relevant axioms.

The **ballot layer** (`BallotN.v`, `ResolvabilityBallotN.v`) sits on top and
supplies what a matrix throws away: a ballot is a ranking
`Node -> nat` (lower is better), a profile is a list of ballots, `count P i j`
is the number of voters strictly preferring `i` to `j`, and `matrix_of P`
sends each off-diagonal pair of counts through a `Measure` (`MeasureN.v`),
any of Schulze's strength measures satisfying (2.1.1) and (2.1.2). See
[the ballot layer](#the-ballot-layer) below.

Consequently:

- The paper's closure `P_D[a,b]` is `mat_star M a b`, the Kleene star
  `geom_sum M (|A| - 1)` of `SchulzeDefsN.v`.
- The paper's `min_D` over the links of a path is the semiring product `*`;
  the paper's `max_D` over paths is the semiring sum `+`; the derived order
  `x ≤ y := x + y = y` (`Orel`) plays the role of `≾_D`.
- Criteria that the paper states by quantifying over profiles and voters
  enter the matrix layer as hypotheses on the matrix. For example the
  unanimity premise (4.3.1.1) becomes `M B A = 0` together with dominance
  hypotheses on rows and columns, and the ballot modifications of
  (4.5.1)–(4.5.3) and (4.6.1)–(4.6.3) become the matrix comparisons
  (4.5.10)–(4.5.12) and (4.6.12)–(4.6.14). These are assumptions *at that
  layer only*: the ballot layer derives each of them from Schulze's own
  ballot-level premise, so none is left standing as an axiom.
- Several theorems carry algebraic hypotheses (`Htotal` for selectivity of
  `+`, `Hmeet` or `H_meet_lower_bound` for the meet property of `*`,
  `Hdec` for decidable equality). These hold in the max-min semiring of the
  Schulze instance, and `SchulzeOnNT.v` discharges them once and for all on
  a normalised carrier. The characterisation theorems show that selectivity
  and the meet property are not merely sufficient but necessary; these
  converses have no counterpart in the paper.

## Section 2 — definition of the Schulze method

| Paper | Statement | Rocq | File |
|---|---|---|---|
| §2.1 | strict partial order (transitive and asymmetric) | `strict_partial_order` | `SchulzeDefsN.v` |
| (2.1.1)–(2.1.3) | axioms on `≻_D` | not axiomatised as such; their roles are played by the semiring order (see notes below) | — |
| §2.1 remark | anonymity and neutrality follow from strength depending only on `N[e,f]`, `N[f,e]` | `NeutralityN.v` (neutrality proved, which the paper only asserts) | `NeutralityN.v` |
| §2.2 | strength of the strongest path `P_D[a,b]` | `mat_star M a b` | `SchulzeDefsN.v` |
| (2.2.1) | `ab ∈ O :⇔ P_D[a,b] ≻_D P_D[b,a]` | `schulze_beats` | `SchulzeDefsN.v` |
| (2.2.2) | `S := {a ∈ A | ∀b ∈ A\{a} : ba ∉ O}` | `schulze_winner` | `SchulzeDefsN.v` |
| (2.2.3) | `P_D[a,b] ≿_D (N[a,b], N[b,a])` | `link_le_mat_star` | `SchulzeClosureN.v` |
| (2.2.4) | `(N[a,b], N[b,a]) ≻_D P_D[b,a] ⇒ ab ∈ O` | `link_beats` | `SchulzeBasicsN.v` |
| (2.2.5) | `min_D{P_D[a,b], P_D[b,c]} ≾_D P_D[a,c]` | `star_path_compose` | `SchulzeClosureN.v` |
| §2.2 | asymmetry of `O` | `schulze_beats_asym` | `SchulzeBasicsN.v` |
| §2.2 | output is a strict partial order `O` and a non-empty `S ⊆ A` | `schulze_output_well_formed` | `WinnerexistenceN.v` |

Notes on (2.1.1)–(2.1.3). At the matrix layer links are abstract semiring
values, so (2.1.1), monotonicity of `≻_D` in support and opposition, has no
direct analogue there and the resulting matrix comparison is assumed
instead; likewise (2.1.2), victories beat ties beat defeats, is what the
separation hypothesis `Hsep` in `IsolateN.v` and `SmithiiaN.v` extracts.
Both become real conditions in the ballot layer: they are the two fields
`m_211` and `m_212` of the `Measure` record in `MeasureN.v`, and the
concrete measures in `examples/` discharge them. (2.1.3), homogeneity, is
not formalised.

## Section 4.1 — transitivity and winner existence

| Paper | Statement | Rocq | File |
|---|---|---|---|
| §4.1 Claim, (4.1.1)+(4.1.2) ⇒ (4.1.3) | `O` is transitive | `schulze_trans_weaker_necessary` | `TransitivityN.v` |
| — | converse: transitivity forces selectivity and the meet property | `schulze_trans_weaker_sufficient`, `transitivity_characterisation` | `TransitivityN.v` |
| §4.1 Corollary, headline | `S` is non-empty | `winner_exists_weaker_necessary` | `WinnerexistenceN.v` |
| (4.1.14) | `∀b ∉ S ∃a ∈ S : ab ∈ O` | `winner_beats_nonwinner` | `WinnerexistenceN.v` |
| — | converses and joint characterisations | `winner_exists_characterisation`; `output_well_formed_characterisation`, `strict_partial_order_characterisation`, `winner_beats_nonwinner_characterisation` | `WinnerexistenceN.v`; `CharacterisationsN.v` |

## Section 4.2 — resolvability

Both of the paper's formulations are formalised. They quantify over
profiles and voters, so they live in the ballot layer; the matrix-level
resolution step and the critical-link machinery they rest on are in
`ResolvabilityN.v` and `CriticalLinkN.v`.

| Paper | Statement | Rocq | File |
|---|---|---|---|
| §4.2.1, from (4.2.1.3) | a winner untied in the closure beats everyone | `untied_winner_is_strict` | `ResolvabilityN.v` |
| §4.2.1, resolution step | an untied winner is the unique winner | `untied_winner_unique` | `ResolvabilityN.v` |
| §4.2.1, second half | distinct link strengths force an untied closure | `distinct_links_unique_winner` | `CriticalLinkN.v` |
| §4.2.1, full statement | if no two links of the profile share a strength there is at most one winner | `distinct_links_unique_winner_from_profile` | `ResolvabilityBallotN.v` |
| §4.2.2 | for every winner `a` some added ballot makes `a` the unique winner | `resolvability_from_profile` (via `add_ballot_strict_winner`, `add_ballot_unique_winner`) | `ResolvabilityBallotN.v` |

The added ballot differs from Schulze's. His `w` ranks `a` first and orders
the rest by closure strength into `a`, breaking ties along the predecessor
tree of the strongest paths. The ballot used here ranks `a` first and orders
the rest by `P[.,a]` descending, leaving ties as ties; the tree is not
needed, because the claim it serves — that the strongest paths out of `a`
are not weakened — is obtained instead by a threshold argument
(`reach_level`), inducting on the number of levels above the threshold.

## Section 4.3 — Pareto

| Paper | Statement | Rocq | File |
|---|---|---|---|
| (4.3.1.2) | unanimous strict preference gives `ab ∈ O` | `pareto_stronger` (also `pareto_stronger_iff` for the converse) | `ParetoN.v` |
| (4.3.1.3) | the dominated alternative is no winner, `b ∉ S` | `pareto_stronger_loser` | `ParetoN.v` |
| (4.3.2.10) | weak unanimity gives `P_D[a,b] ≿_D P_D[b,a]` | `pareto_weaker` | `ParetoN.v` |
| (4.3.2.2) | `ba ∉ O` | immediate from `pareto_weaker` (see the `f = B` case of `pareto_weaker_winner_transfer`) | `ParetoN.v` |
| (4.3.2.11) | `∀f : P_D[a,f] ≿_D P_D[b,f]` | `pareto_star_source_swap` | `ParetoN.v` |
| (4.3.2.12) | `∀f : P_D[f,b] ≿_D P_D[f,a]` | `pareto_star_target_swap` | `ParetoN.v` |
| (4.3.2.3) | `bf ∈ O ⇒ af ∈ O` | `pareto_weaker_beats_transfer` | `ParetoN.v` |
| (4.3.2.4) | `fa ∈ O ⇒ fb ∈ O` | `pareto_weaker_loses_transfer` | `ParetoN.v` |
| (4.3.2.5) | `b ∈ S ⇒ a ∈ S` | `pareto_weaker_winner_transfer` | `ParetoN.v` |

The premise (4.3.2.1), `∀v : a ≿_v b`, appears as the hypotheses
`M B A ≤ M A B`, `Hrow`, and `Hcol` (ballot transitivity), and the
premise (4.3.1.1), `∀v : a ≻_v b`, as `M B A = 0` with `0 < M A B`
plus the maximality hypothesis `Hmax` and the composition hypothesis
`Htop_trans` (unanimous links compose, the algebraic residue of ballot
transitivity).

## Section 4.4 — reversal symmetry

Ballot reversal (4.4.1) is matrix transposition: the reversed profile is
`fun i j => M j i`.

| Paper | Statement | Rocq | File |
|---|---|---|---|
| (4.4.2) | `ab ∈ O_old ⇔ ba ∈ O_new` | `reversal_symmetry_O` (commutative semiring), `reversal_symmetry_O_level2` (meet property instead) | `ReversalsymmetryN.v` |
| (4.4.3) | reversal displaces a winner iff it promotes a non-winner | `reversal_symmetry_S`, `reversal_symmetry_S_level2` | `ReversalsymmetryN.v` |
| (4.4.4) | `S_old = S_new ⇔ S_old = A` | `reversal_symmetry_all_tied`, `reversal_symmetry_all_tied_level2` | `ReversalsymmetryN.v` |
| — | winner-level corollary: a strict winner cannot survive reversal | `reversal_symmetry` | `ReversalsymmetryN.v` |

## Section 4.5 — monotonicity

The ballot modification (4.5.1)–(4.5.3) enters through its link-strength
consequences (4.5.10)–(4.5.12), taken as the hypotheses `Hrow`, `Hcol`,
and `Heq`.

| Paper | Statement | Rocq | File |
|---|---|---|---|
| (4.5.13) | `P_new[a,b] ≿_D P_old[a,b]` | `monotonicity` | `MonotonicityN.v` |
| (4.5.14) | `P_old[b,a] ≿_D P_new[b,a]` | `monotonicity_rev` | `MonotonicityN.v` |
| (4.5.4) | `ab ∈ O_old ⇒ ab ∈ O_new` | `monotonicity_beats` | `MonotonicityN.v` |
| (4.5.5) | `ba ∉ O_old ⇒ ba ∉ O_new` | `monotonicity_unbeaten` | `MonotonicityN.v` |
| (4.5.6), first half | `a ∈ S_old ⇒ a ∈ S_new` | `winner_monotonicity` | `MonotonicityN.v` |
| (4.5.6), second half | `S_new ⊆ S_old` | `winner_monotonicity_subset`, under an extra no-ties hypothesis the paper does not need; the paper's own argument uses critical-link machinery that is out of reach here | `MonotonicityN.v` |

## Section 4.6 — independence of clones

Both elections live over one ambient `Node` type; the two alternative sets
are the candidate lists `A_old` and `A_new = (A_old \ {d}) ++ K`, and the
closure over a list is `path_star` (`PathN.v`), which agrees with
`mat_star` at the full list `elements`
(`path_star_elements_is_mat_star`, `SchulzeDefsN.v`). The clone premises
(4.6.1)–(4.6.3) enter through their strength consequences, taken as
hypotheses.

| Paper | Statement | Rocq | File |
|---|---|---|---|
| (4.6.12) | clones inherit the incoming edges of `d` | hypothesis `Hclone_in` | `CloneN.v` |
| (4.6.13) | clones inherit the outgoing edges of `d` | hypothesis `Hclone_out` | `CloneN.v` |
| (4.6.14) | edges between survivors are untouched | hypothesis `Hclone_ext` | `CloneN.v` |
| (4.6.21) | `P_new[a,g] ≈_D P_old[a,d]` | `clone_strength_to_clone` | `CloneN.v` |
| (4.6.22) | `P_new[g,a] ≈_D P_old[d,a]` | `clone_strength_from_clone` | `CloneN.v` |
| (4.6.23) | `P_new[a,b] ≈_D P_old[a,b]` for survivors | `clone_strength_survivors` | `CloneN.v` |
| (4.6.4) | `ad ∈ O_old ⇔ ag ∈ O_new` | `survivor_beats_clone`, `survivor_beats_d` | `CloneN.v` |
| (4.6.5) | `db ∈ O_old ⇔ gb ∈ O_new` | `clone_beats_survivor`, `d_beats_survivor` | `CloneN.v` |
| (4.6.6) | `ab ∈ O_old ⇔ ab ∈ O_new` | `survivors_beat_new_old`, `survivors_beat_old_new` | `CloneN.v` |
| (4.6.7) | `d ∈ S_old ⇔ S_new ∩ K ≠ ∅` | `clone_winner_implies_d_winner`, `d_winner_implies_clone_winner` | `CloneN.v` |
| (4.6.8) | `a ∈ S_old ⇔ a ∈ S_new` for survivors | `clone_winner_survivors` | `CloneN.v` |
| (4.6.7) and (4.6.8) together | independence of clones | `independence_of_clones`, `independence_of_clones_selective` | `CloneN.v` |
| — | converse: clone independence is equivalent to winner existence and characterises the bottleneck semirings | `clone_characterisation`, `clone_iff_winner_exists` | `CloneCharacterisationN.v` |

## Section 4.7 — Smith, Condorcet, and Smith-IIA

The cut premise (4.7.2) enters as a shared threshold `c` separating the
two blocks: every `B2 → B1` link lies strictly below `c` and every
`B1 → B2` link at or above it, which subsumes the per-pair form.

| Paper | Statement | Rocq | File |
|---|---|---|---|
| (4.7.3) | `∀a ∈ B1 ∀b ∈ B2 : ab ∈ O` | `smith_beats` | `SmithN.v` |
| (4.7.4) | `S ⊆ B1` | `smith_criterion_weaker` | `SmithN.v` |
| §4.7 Remark | Condorcet criterion (`B1 = {a}`), proved directly and in the stronger strict-winner form | `condorcet_implies_strict_winner_weaker` | `CondorcetN.v` |
| (4.7.5)(a), isolation form | zeroing the links of a weak `d` leaves `O` on `B1` unchanged | `smith_iia_isolate`, `smith_iia_isolate_out` | `IsolateN.v` |
| (4.7.5)(a), removal form | deleting a weak `d` from the ballot leaves the beat relation on `B1` unchanged | `smith_iia_removal_beats`, `smith_iia_removal_all_beats` | `SmithiiaN.v` |
| (4.7.5)(a) at winner level | winner status of every strong alternative is untouched | `smith_iia_removal`, `smith_iia_removal_all` | `SmithiiaN.v` |
| (4.7.5)(b) | `S_old = S_new` | `smith_iia_winner_set`, `smith_iia_winner_set_all` | `SmithiiaN.v` |
| (4.7.6), isolation form | isolating a strong `d ∈ B1` leaves the beat relation on `B2` unchanged | `smith_iia_isolate_strong` (with `pow_isolate_strong_dichotomy` and `mat_star_isolate_strong_preserved`) | `IsolateN.v` |
| (4.7.6), removal form | deleting a strong `d ∈ B1` from the ballot leaves the beat relation on `B2` unchanged | `smith_iia_removal_strong_beats` | `SmithiiaN.v` |

The majority criterion for solid coalitions and participation
((4.7.14)–(4.7.15)) are only discussed, not proved, in the paper, and are
not formalised.

## Section 4.8 — the MinMax set

Subsets are boolean predicates `B : Node -> bool`; `β_D` is a parameter
`beta` constrained by hypotheses rather than a computed minimum, since the
semiring has joins but no meet over the powerset. `Hmin` says `beta` is a
lower bound of every cut, `Ba` with `cut_in M Ba = beta` witnesses
`a ∈ 𝔅_D`, and `Hb_out` says `b ∉ 𝔅_D`.

| Paper | Statement | Rocq | File |
|---|---|---|---|
| §4.8 definition | `Γ_D(B)`, the strongest link entering `B` (also (6.3)) | `cut_in` | `MinMaxN.v` |
| Claim #1, (4.8.7) | `P_D[b,a] ≾_D β_D` | `path_into_B_le_cut`, `mat_star_into_B_le_cut` | `MinMaxN.v` |
| Claim #2, (4.8.11) | `P_D[a,b] ≿_D γ_D ≻_D β_D` | `minmax_reach` | `MinMaxN.v` |
| (4.8.1) | `∀a ∈ 𝔅_D ∀b ∉ 𝔅_D : ab ∈ O` | `minmax_beats` | `MinMaxN.v` |
| (4.8.2) | `S ⊆ 𝔅_D` | `minmax_winner` | `MinMaxN.v` |

## Section 4.9 — prudence

| Paper | Statement | Rocq | File |
|---|---|---|---|
| (4.9.2) | `λ_D`, the strength of the strongest directed cycle | `cycle_strength` | `PrudenceN.v` |
| (4.9.3) | `(N[a,b], N[b,a]) ≻_D λ_D ⇒ ab ∈ O` | `prudence` (global), `prudence_local` (per-link form of the paper's proof) | `PrudenceN.v` |
| (4.9.4) | `(N[a,b], N[b,a]) ≻_D λ_D ⇒ b ∉ S` | `prudence_not_winner` | `PrudenceN.v` |

## The ballot layer

`BallotN.v` supplies the layer the matrix throws away and discharges the
hypotheses the criterion files carry. A ballot is a ranking
`Node -> nat` (lower is better), which makes each ballot transitive by
construction and represents every strict weak order on a finite set; a
profile is a list of ballots; `count P i j` counts the voters who strictly
prefer `i` to `j`; and `matrix_of P` sends each off-diagonal pair of counts
through a `Measure`. Changes to a profile (raising, cloning, reversing) are
relations between profiles, stated as `Forall2` of a relation between
ballots, so "some voters do X" is expressed without choosing which voters.

Nothing here changes a matrix-level theorem. Each section states Schulze's
ballot-level premise, derives the matrix hypotheses of the corresponding
theorem from it, and applies that theorem to `matrix_of P`.

| Paper | Ballot-level premise | Rocq | File |
|---|---|---|---|
| §2.1 | anonymity: permuting the ballots | `anonymity_from_profile` | `BallotN.v` |
| (4.3.1.1) | every voter strictly prefers `A` to `B` (`unanimous`) | `pareto_from_profile`, `pareto_loser_from_profile` | `BallotN.v` |
| (4.3.2.1) | every voter ranks `A` at least as high as `B` | `pareto_weak_from_profile`, `pareto_weak_winner_from_profile`, `pareto_weak_beats_from_profile`, `pareto_weak_loses_from_profile` | `BallotN.v` |
| §4.4 | every ballot is reversed (`reverse`) | `reversal_from_profile`, `reversal_S_from_profile` | `BallotN.v` |
| (4.5.1)–(4.5.3) | `A` is raised, voter by voter (`raise`) | `monotonicity_from_profile`, `monotonicity_unbeaten_from_profile` | `BallotN.v` |
| (4.6.1)–(4.6.3) | `d` is replaced by clones, voter by voter (`cloned`) | `clones_from_profile` | `BallotN.v` |
| §4.7 Remark | `A` wins every pairwise comparison | `condorcet_from_profile`, `condorcet_unique_from_profile` | `BallotN.v` |
| (4.7.3), (4.7.4) | every member of `B1` pairwise beats every member of `B2` | `smith_beats_from_profile`, `smith_from_profile` | `BallotN.v` |
| §4.2.1, §4.2.2 | resolvability (see above) | `distinct_links_unique_winner_from_profile`, `resolvability_from_profile` | `ResolvabilityBallotN.v` |

Two of these bridges are worth singling out. Pareto is the only one that
needs the individual ballots rather than the counts alone: `Htop_trans`
holds because a link as strong as the unanimous one *is* unanimous, and
unanimity composes because each ballot is transitive. And the separator that
Smith and Condorcet take as a hypothesis on the matrix is the tie strength,
by (2.1.2); `SchulzeOnNT.v` notes that no carrier construction can supply
it, whereas the count layer can, because `M a b` and `M b a` come from one
pair of counts.

The measure itself is a parameter. `MeasureN.v` records Schulze's (2.1.1)
and (2.1.2) as a record, and `examples/` discharges it for winning votes
(`WinningVotes.v`), margins (`MarginMeasure.v`), and losing votes
(`LosingVotes.v`), so every result above holds for each of them.

## The normalised instance

`SchulzeOnNT.v` restates the main results over a carrier built by
`NormalizedOrder.v`, where selectivity, the meet property, and decidable
equality hold by construction: `schulze_trans_normalized` (§4.1),
`winner_exists_normalized` and `winner_beats_nonwinner_normalized`
((4.1.14)), `smith_beats_normalized` and `smith_criterion_normalized`
((4.7.3), (4.7.4)), `schulze_output_well_formed_normalized` (§2.2),
`untied_winner_unique_normalized` (§4.2.1),
`reversal_symmetry_S_normalized` ((4.4.3)), and
`reversal_symmetry_all_tied_normalized` ((4.4.4)).

## Not formalised

- The majority criterion for solid coalitions and participation
  ((4.7.14), (4.7.15)), which the paper also does not prove.
- The paper's §2.3 Floyd–Warshall implementation as such; the extraction
  targets under `extraction/` compute the closure via the matrix semiring
  instead.
- §3 Example 1 is formalised separately in `examples/Schulze.v`.
