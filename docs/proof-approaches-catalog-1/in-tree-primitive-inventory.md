# §C — In-tree primitive inventory

**EXPLORATORY ONLY — NOT a live program.**  Sub-deliverable §C of
`mg-e112`. Doc-only. No Lean source changes; no signature changes;
no new axioms.  Catalogs Lean primitives currently in tree relevant
to balanced-pair construction on the K=2 obstruction family of §A.

---

## §0 — Reading guide

Each entry records:

* **Symbol** — fully qualified Lean name.
* **File:line** — primary declaration site.
* **Kind** — `def` / `theorem` / `lemma` / `structure` / `axiom`.
* **Hypotheses (typed, English gloss)** — what callers must supply.
* **Conclusion (typed, English gloss)** — what the primitive proves.
* **Scope** — the regime where the primitive applies (e.g.,
  "`K = 2` only", "`w = 0` only", "any layered width-3").
* **Origin ticket** — work item that introduced the primitive.
* **Currently used for** — the operative consumer in the dispatch
  chain.
* **Adaptability** — what's coupled vs decoupled, what would need
  to change to use the primitive in a new setting.

§7 carries the **"primitives that COULD exist but DON'T"** list —
the gaps Daniel's saturation lemma would need filled.

All file paths are relative to the repository root (containing
the worktree at `/Users/daniel/.pogo/polecats/pe112` for this
catalog; the source repo `/Users/daniel/research/one_third_width_three`
holds the same tree).

---

## §1 — Step-3 ordinal closure primitives

### `OrdinalDecomp` (the structure)

* **Symbol.** `OneThird.OrdinalDecomp`
* **File:line.** `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:140`
* **Kind.** `structure`
* **Fields.**
  - `Lower Mid Upper : Finset α` — the three pieces.
  - `hCover : Lower ∪ Mid ∪ Upper = Finset.univ`.
  - `hDisj{LM,LU,MU}` — pairwise disjointness.
  - `hLM_lt`, `hLU_lt`, `hMU_lt` — element-wise comparability
    `Lower < Mid < Upper`.
* **Scope.** Any finite poset.
* **Origin ticket.** Step 3 / `lem:ordinal-factorisation`
  (`step8.tex:2404-2418`).
* **Currently used for.** The fundamental ordinal-decomposition
  carrier; consumed by `linExtEquivOfReducible`,
  `tripleEquiv`, `numLinExt_eq`, `probLT_restrict_eq`,
  `hasBalancedPair_lift`.
* **Adaptability.** Decoupled from K and band structure — pure
  poset-level decomposition.  Adapts to any reducible (in the
  ordinal-sum sense) poset.

### `OrdinalDecomp.probLT_restrict_eq`

* **Symbol.** `OneThird.OrdinalDecomp.probLT_restrict_eq`
* **File:line.** `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1065`
* **Kind.** `theorem`
* **Hypotheses.** `D : OrdinalDecomp α`, `u v : α` with
  `u, v ∈ same piece` (`Lower`, `Mid`, or `Upper`).
* **Conclusion.** `probLT u v = probLT u' v'` where `u', v'` are
  the restrictions of `u, v` to the corresponding sub-poset's
  `LinearExt`.
* **Scope.** Any `OrdinalDecomp α`.  This is the **marginal-
  invariance identity** — the foundational fact that ordinal-sum
  cuts preserve within-piece probabilities.
* **Origin ticket.** Step-3 closure (mg-9568 / mg-7f06).
* **Currently used for.** Consumed by
  `OrdinalDecomp.hasBalancedPair_lift{,_lower,_upper}`.
* **Adaptability.** Foundational; decoupled from K, w, band
  structure.  Cannot be tightened (it is an exact equality).

### `OrdinalDecomp.hasBalancedPair_lift_lower` /
### `OrdinalDecomp.hasBalancedPair_lift_upper`

* **Symbols.** `OneThird.OrdinalDecomp.hasBalancedPair_lift_lower`,
  `OneThird.OrdinalDecomp.hasBalancedPair_lift_upper`
* **File:line.** `Mathlib/LinearExtension/Subtype.lean:1227, 1268`
* **Kind.** `theorem`
* **Hypotheses.** `D : OrdinalDecomp α`,
  `HasBalancedPair (D.Lower : Finset α)` (or `Upper`).
* **Conclusion.** `HasBalancedPair α`.
* **Scope.** Any ordinal-decomposable poset.
* **Origin ticket.** mg-7f06.
* **Currently used for.** The reducible-branch lift; consumed by
  the trichotomy's R branch in any saturation-lemma rewrite.
* **Adaptability.** Lifts from sub-poset to ambient — exactly
  what the saturation lemma's R branch needs.  Decoupled from K.

### `OrdinalDecomp.numLinExt_eq` and `tripleEquiv`

* **Symbols.** `OneThird.OrdinalDecomp.numLinExt_eq` (line 1036),
  `OneThird.OrdinalDecomp.tripleEquiv` (line 1020).
* **Kind.** `theorem` / `noncomputable def`.
* **Conclusion.** `|L(α)| = |L(Lower)| · |L(Mid)| · |L(Upper)|`
  and the underlying triple bijection.
* **Adaptability.** Useful for closed-form `|L|` computation in
  the saturation lemma's per-class enumeration when classes
  reduce.

---

## §2 — Step-7 layered primitives

### `LayeredDecomposition` (the structure)

* **Symbol.** `OneThird.Step8.LayeredDecomposition`
* **File:line.** `lean/OneThird/Step8/LayeredReduction.lean:115`
* **Kind.** `structure`
* **Fields.**
  - `K : ℕ` — depth.
  - `w : ℕ` — interaction width.
  - `band : α → ℕ` — band-index map.
  - `band_pos : ∀ x, 1 ≤ band x`.
  - `band_le : ∀ x, band x ≤ K`.
  - `band_size : ∀ k, |{x : band x = k}| ≤ 3` — (L1).
  - `band_antichain : ∀ k, IsAntichain (≤) (band-k slice)` — (L1b).
  - `forced_lt : ∀ x y, band x + w < band y → x < y` — (L2-forced).
  - `cross_band_lt_upward : ∀ x y, x < y → band x ≤ band y` —
    (L2-upward, mg-53ce).
* **Scope.** Layered width-3 posets at depth `K` with interaction
  width `w`.
* **Origin ticket.** mg-53ce (added (L2-upward) field;
  `docs/a5-g2-status.md`).
* **Currently used for.** The root structure on which all of Step
  8's machinery hangs.

### `LayerOrdinalReducible`

* **Symbol.** `OneThird.Step8.LayerOrdinalReducible`
* **File:line.** `lean/OneThird/Step8/LayerOrdinal.lean:88`
* **Kind.** `def`
* **Definition.** `LayerOrdinalReducible L k := ∀ u v : α,
  L.band u ≤ k → k < L.band v → u < v`.
* **Scope.** Any `LayeredDecomposition L`, any `k : ℕ`.
* **Origin ticket.** Step-7 / `lem:reducible-witness`.
* **Currently used for.** Witnesses ordinal-sum reducibility at
  cut `k`.  Consumed by `OrdinalDecompOfReducible` to build
  the corresponding `OrdinalDecomp`.
* **Adaptability.** The trichotomy's R branch is exactly
  "∃ k. LayerOrdinalReducible L k".

### `LayerOrdinalIrreducible`

* **Symbol.** `OneThird.Step8.LayerOrdinalIrreducible`
* **File:line.** `lean/OneThird/Step8/LayerOrdinal.lean:240`
* **Kind.** `def`
* **Definition.** `LayerOrdinalIrreducible L := ∀ k, ¬ LayerOrdinalReducible L k`
  (no reducibility witness at any `k`).
* **Currently used for.** The defining hypothesis of every
  Case-3 / N-poset / strict-residual primitive in tree.  The
  saturation lemma's input scope.

### `cross_band_lt_upward`

* **Symbol.** `OneThird.Step8.LayeredDecomposition.cross_band_lt_upward`
  (a field of the structure, `LayeredReduction.lean:149`).
* **Origin.** mg-53ce.
* **Currently used for.** Rules out `b < a` for `a ∈ L_1, b ∈ L_2`
  in K=2; foundational for the bipartite framing of the
  obstruction family.
* **Adaptability.** Already required by every K=2 consumer.

### `OrdinalDecompOfReducible` and `numLinExt_factorOfReducible`

* **Symbols.** `OneThird.Step8.OrdinalDecompOfReducible`
  (`LayerOrdinal.lean:108`),
  `numLinExt_factorOfReducible` (line 222).
* **Currently used for.** The R-branch lift in the layered
  setting: from `LayerOrdinalReducible L k` to a balanced-pair
  conclusion via `OrdinalDecomp.hasBalancedPair_lift_{lower,upper}`.
* **Adaptability.** Couples `LayerOrdinalReducible` to
  `OrdinalDecomp`; the bridge.

### `lem_layered_reduction` and `K₀`

* **Symbols.** `OneThird.Step8.lem_layered_reduction`
  (`LayeredReduction.lean:491`), `K₀` (line 514).
* **Origin.** mg-805c (B1 size-minimality form).
* **Scope.** `K ≥ K₀(γ, w) := max(2w + 2, ⌈2/γ⌉ + 6w + 4)`.
  **Vacuous at K=2** (requires K ≥ 2w+2 ≥ 4 for w ≥ 1).
* **Adaptability.** **Not applicable** to the K=2 obstruction
  family (per F2).

### `bandSizes` / `bandSize` / `bandSize_le_three`

* **Symbols.** `OneThird.Step8.bandSizes` (`BoundedIrreducibleBalanced.lean:350`),
  `bandSize` (line 344), `bandSize_le_three` (line 360).
* **Currently used for.** Recovers the band-size list for use
  with `case3_certificate`'s Bool enumeration.

---

## §3 — Compound automorphism kit (mg-84f2)

### `SameBandPair`

* **Symbol.** `OneThird.Step8.CompoundSwap.SameBandPair`
* **File:line.** `lean/OneThird/Step8/CompoundSwap.lean:89`
* **Kind.** `structure`
* **Fields.** `a₁ a₂ : α`, `hne : a₁ ≠ a₂`,
  `hband : L.band a₁ = L.band a₂`.
* **Scope.** Any `LayeredDecomposition L`.
* **Origin ticket.** mg-84f2.
* **Currently used for.** Carries a within-band incomparable
  pair (incomparability follows from `band_antichain`).
* **Adaptability.** General; instantiable at any band.

### `compoundSwap`

* **Symbol.** `OneThird.Step8.CompoundSwap.compoundSwap`
* **File:line.** `lean/OneThird/Step8/CompoundSwap.lean:139`
* **Kind.** `def` (returns `α ≃ α`).
* **Hypotheses.** `L : LayeredDecomposition α`,
  `P₁ P₂ : SameBandPair L`.
* **Conclusion.** A bijection `α ≃ α` swapping
  `(a₁ ↔ a₂)` of `P₁` and `(b₁ ↔ b₂)` of `P₂`, identity elsewhere.
* **Scope.** Any layered poset; matching-compatibility required
  for **order preservation** (next entry).
* **Origin ticket.** mg-84f2.
* **Currently used for.** The operative ambient swap for the
  N-poset class.
* **Adaptability.** Requires `MatchingCompatible` to be order-
  preserving; this is the bottleneck for the F1-active regime.

### `MatchingCompatible`

* **Symbol.** `OneThird.Step8.CompoundSwap.MatchingCompatible`
* **File:line.** `lean/OneThird/Step8/CompoundSwap.lean:169`
* **Kind.** `structure`
* **Fields (selected).** `compatibility : ∀ z, P₁.a₁ < z ↔ P₁.a₂ < z`
  (and similarly for the second pair, plus cross-constraints).
* **Scope.** Pairs in different bands.
* **Origin ticket.** mg-84f2.
* **Currently used for.** The hypothesis on which `compoundSwap`
  is order-preserving (`compoundSwap_preserves_le`,
  `CompoundSwap.lean:278`).
* **Adaptability.** **F1 obstruction** lives here: when one of
  the same-band pairs has strict ⪯-containment of nbhds, the
  compatibility predicate fails (per `path-c-track-1-status-1.md`
  §2's cardinality lemma).

### `compoundSwap_preserves_le` / `compoundSwap_le_iff`

* **Symbols.** `OneThird.Step8.CompoundSwap.compoundSwap_preserves_le`,
  `compoundSwap_le_iff` (`CompoundSwap.lean:278, 288`).
* **Currently used for.** The order-preservation derivation; the
  basis of `probLT_eq_half_of_swap_aut`.

### `matching_exists_of_K2_irreducible_noWithinBand`

* **Symbol.** `OneThird.Step8.CompoundMatching.matching_exists_of_K2_irreducible_noWithinBand`
* **File:line.** `lean/OneThird/Step8/CompoundMatching.lean:663`
* **Kind.** `theorem`
* **Hypotheses.** `L : LayeredDecomposition α`, `HasWidthAtMost α 3`,
  `L.K = 2`, `LayerOrdinalIrreducible L`, `1 ≤ L.w`,
  `3 ≤ Fintype.card α`, `NoWithinBandPreceq L`.
* **Conclusion.** `∃ P₁ P₂ : SameBandPair L, hBandNe ∧
  MatchingCompatible L P₁ P₂` (a matched same-band pair pair).
* **Scope.** **K=2** with no within-band ⪯-pair (the F1-inactive
  case-3 / N-poset regime).
* **Origin ticket.** mg-c0c7.
* **Currently used for.** Closes the F1-inactive K=2 regime in
  `bipartite_balanced_enum_general` (case 3).
* **Adaptability.** Hypotheses are tight: K=2 is hard-wired (the
  band partition is binary).  An analogous theorem for K ≥ 3
  would need new infrastructure.

### `NConfig` (the witness configuration structure)

* **Symbol.** `OneThird.Step8.CompoundMatching.NConfig`
* **File:line.** `lean/OneThird/Step8/CompoundMatching.lean:326`
* **Kind.** `structure`
* **Fields.** Carries 4 elements `a, a', b, b'` with
  `a, a' ∈ L_1` (same band 1), `b, b' ∈ L_2` (same band 2),
  appropriate distinctness hypotheses.
* **Origin ticket.** mg-c0c7.
* **Currently used for.** The N-poset configuration witness.
  Consumed by `matchingCompatible_of_NConfig`
  (`CompoundMatching.lean:580`).
* **Adaptability.** Specific to K=2; requires bands of size ≥ 2
  in both `L_1` and `L_2`.  For (1,2) / (2,1) / (1,3) / (3,1)
  partitions, the structure is vacuous.

### `NoWithinBandPreceq`

* **Symbol.** `OneThird.Step8.CompoundMatching.NoWithinBandPreceq`
* **File:line.** `lean/OneThird/Step8/CompoundMatching.lean:89`
* **Kind.** `def`
* **Definition.** Negation of `Case2Witness L` — no within-band
  ⪯-comparable pair exists.
* **Equivalence.** `noWithinBandPreceq_iff_not_case2Witness`
  (line 94).
* **Scope.** Any `LayeredDecomposition L`.

---

## §4 — Case dispatch (mg-48db / mg-02c2)

### `bipartite_balanced_enum_general`

* **Symbol.** `OneThird.Step8.InSitu.bipartite_balanced_enum_general`
* **File:line.** `lean/OneThird/Step8/BipartiteEnumGeneral.lean:210`
* **Kind.** `theorem`
* **Hypotheses.** `L : LayeredDecomposition α`,
  `HasWidthAtMost α 3`, `LayerOrdinalIrreducible L`, `L.K = 2`,
  `1 ≤ L.w`, `3 ≤ Fintype.card α`, `Case2FKGSubClaim L`.
* **Conclusion.** `HasBalancedPair α`.
* **Scope.** **K=2, w ≥ 1, |α| ≥ 3, irreducible, width ≤ 3.**
  Operative on the entire 40-class catalog of §A *modulo*
  consumption of `Case2FKGSubClaim`.
* **Origin ticket.** mg-02c2.
* **Currently used for.** The K=2 closure for the case-3 / N-poset
  regime; the F1-inactive subset.
* **Adaptability.** **Bottleneck:** `Case2FKGSubClaim` is
  *provably false* at K=2 strict (mg-a79e / mg-b666).  So this
  theorem closes only when the call-site can supply the FKG
  hypothesis — which works for the F1-inactive regime (the FKG
  sub-claim holds vacuously when no within-band ⪯-pair exists)
  but fails on the F1-active regime.
* **Three-case dispatch.** Internally:
  - Case 1: ambient profile-match pair (`hasBalancedPair_of_case1`).
  - Case 2: within-band ⪯-pair (`case2Witness_balanced_under_FKG`).
  - Case 3: neither — invoke `matching_exists_of_K2_irreducible_
    noWithinBand` + `hasBalancedPair_of_matchingCompatible`.

### `Case2FKGSubClaim`

* **Symbol.** `OneThird.Step8.InSitu.Case2FKGSubClaim`
* **File:line.** `lean/OneThird/Step8/Case2Rotation.lean:772`
* **Kind.** `structure (Prop)` with two fields:
  - `pair : ∀ (a a'), within-band ⪯-pair → Pr ≥ 1/2`.
  - `chain : ∀ (a₁, a₂, a₃), within-band ⪯-chain → triple Pr ≥ 1/2`.
* **Scope.** Hypothesis-shaped Prop; consumed by case-2 dispatch.
* **Origin ticket.** mg-27c2.
* **Currently used for.** Bundled hypothesis for
  `bipartite_balanced_enum_general` and
  `case2Witness_balanced_under_FKG`.
* **Adaptability / status.** **Provably false** at K=2 strict
  (3-element witness `K2-N3-MIN`, where `Pr_Q[a < a'] = 1/3`,
  not ≥ 1/2).  Per mg-a79e, mg-b0de, mg-b666.

### `hasBalancedPair_of_matchingCompatible`

* **Symbol.** `OneThird.Step8.hasBalancedPair_of_matchingCompatible`
* **File:line.** `lean/OneThird/Step8/BipartiteEnumGeneral.lean:153`
* **Kind.** `theorem`
* **Conclusion.** From a `MatchingCompatible L P₁ P₂` pair pair,
  produces `HasBalancedPair α`.
* **Scope.** Layered, K=2-style (specifically, the matched-pair
  setting).
* **Origin ticket.** mg-02c2.
* **Currently used for.** The closure step in the case-3 dispatch
  of `bipartite_balanced_enum_general`.

### `Case3Witness` (the universal hypothesis on the headline)

* **Symbol.** `OneThird.Step8.Case3Witness`
* **File:line.** `lean/OneThird/Step8/LayeredBalanced.lean:438`
* **Kind.** `def : Prop`
* **Definition.** `∀ β [Fintype β] [PartialOrder β] [DecidableEq β]
  (LB : LayeredDecomposition β), HasWidthAtMost β 3 →
  ¬ IsChainPoset β → 2 ≤ Fintype.card β → HasBalancedPair β`.
* **Scope.** **Universally quantified** over every layered
  width-3 non-chain β with `|β| ≥ 2`.  No K-restriction.
* **Origin ticket.** Step-8 headline structure
  (`docs/why-hC3-is-structural.md`).
* **Currently used for.** Threaded as `hC3` through the headline
  `width3_one_third_two_thirds`.  Sole operational consumer:
  `LayeredBalanced.lean:548`.
* **Adaptability.** A K=2-restricted variant (`K2RestrictedCase3Witness`,
  sketched in `case3witness-operational-audit.md` §4a) is
  mathematically possible but does not by itself discharge `hC3`
  (per mg-e0b8 §5).

### `Case2Witness` (the predicate dispatched on)

* **Symbol.** `OneThird.Step8.InSitu.Case2Witness`
* **File:line.** `lean/OneThird/Step8/Case3Dispatch.lean:156`
* **Kind.** `def : Prop`
* **Currently used for.** The within-band ⪯-pair predicate;
  branches the case dispatch in `bipartite_balanced_enum_general`.

---

## §5 — Chain swap (mg-ba0c / mg-b846)

### `chainSwap_LE`

* **Symbol.** `OneThird.Step8.InSitu.chainSwap_LE`
* **File:line.** `lean/OneThird/Step8/Case2Rotation.lean:553`
* **Kind.** `def` (LE → LE involution).
* **Hypotheses.** `a a' : α`, `a ≠ a'`, `a ∥ a'`,
  `(∀ z, a < z → a' < z)` (upper closure), `(∀ z, z < a' → z < a)`
  (lower closure), `L : LinearExt α`, `L.lt a a'`.
* **Conclusion.** `LinearExt α` with `a' <_{L'} a`.
* **Scope.** Any one-sided ⪯-chain pair (a, a').
* **Origin ticket.** Pre-mg-ba0c.
* **Currently used for.** The involution underlying
  `probLT_le_half_of_chain`.

### `probLT_le_half_of_chain`

* **Symbol.** `OneThird.Step8.InSitu.probLT_le_half_of_chain`
* **File:line.** `lean/OneThird/Step8/Case2Rotation.lean:629`
* **Kind.** `theorem`
* **Hypotheses.** As `chainSwap_LE` (one-sided ⪯-chain).
* **Conclusion.** `probLT a a' ≤ 1/2`.
* **Scope.** One-sided ⪯-chain; available in tree for case-2
  symm closures.
* **Origin ticket.** Pre-mg-ba0c (consumed by mg-8801 for
  case-2-symm closure).
* **Currently used for.** Combined with `Case2FKGSubClaim.pair`
  (in tree) gives `probLT a a' = 1/2` for symm pairs.
* **Adaptability.** **F1 obstruction:** for *strict* ⪯-pairs
  with `upper(a) ⊊ upper(a')` strictly, the `(∀ z, z < a' → z < a)`
  hypothesis fails (the "lower closure" half is a one-direction
  closure that does not hold on strict pairs).

---

## §6 — Bipartite enumeration (K=2 / w=0 closures)

### `bipartite_balanced_enum`

* **Symbol.** `OneThird.Step8.bipartite_balanced_enum` (or
  `Step8.InSitu`-namespaced).
* **File:line.** `lean/OneThird/Step8/BipartiteEnum.lean:288`
  (and `BipartiteEnumGeneral.lean:39` for the general entry-point).
* **Kind.** `theorem`
* **Scope.** Closes the **fully bipartite** K=2 case (every
  cross-pair comparable, `α = A ⊔ B` with `A < B`).  Used as a
  sub-step / Case 1 dispatch.
* **Origin ticket.** Closes the original `fkg_case_output` axiom.

### `hasBalancedPair_of_K2_w0_incomp`

* **Symbol.** `OneThird.Step8.hasBalancedPair_of_K2_w0_incomp`
* **File:line.** `lean/OneThird/Step8/Case2BipartiteBound.lean:197`
* **Kind.** `theorem`
* **Hypotheses.** `L.K = 2`, `L.w = 0`, plus a within-band
  incomparable witness.
* **Conclusion.** `HasBalancedPair α`.
* **Scope.** **K=2, w=0 only** — `bandSet_one_le_bandSet_two_of_w0`
  ensures `∀ a ∈ A, ∀ b ∈ B, a ≤ b` at w=0, which makes the
  bipartite framing complete.
* **Origin ticket.** mg-ed4d.
* **Currently used for.** The K=2/w=0 base case of the dispatch
  chain.
* **Adaptability.** **Not applicable to w ≥ 1** — the (L2-forced)
  axiom no longer forces all cross-pairs comparable.

### `probLT_eq_half_of_within_band_K2_w0` /
### `probLT_le_two_thirds_of_within_band_K2_w0` /
### `probLT_ge_one_third_of_within_band_K2_w0`

* **File:line.** `Case2BipartiteBound.lean:242, 260, 269`.
* **Scope.** K=2, w=0.
* **Currently used for.** The detailed within-band probability
  bounds that close `hasBalancedPair_of_within_band_K2_w0`
  (line 322).

---

## §7 — F3 strong-induction framework (mg-a735, present but unused)

### `hasBalancedPair_of_layered_strongInduction_width3`

* **Symbol.** `OneThird.Step8.hasBalancedPair_of_layered_strongInduction_width3`
* **File:line.** `lean/OneThird/Step8/Step8/LayerOrdinal.lean:472`
  (note: the actual path is `lean/OneThird/Step8/LayerOrdinal.lean:472`).
* **Kind.** `theorem`
* **Hypotheses.** A general layered induction frame plus
  an `hStep` argument supplying the per-step closure.
* **Conclusion.** `HasBalancedPair α` for any layered width-3
  poset (under hypotheses).
* **Scope.** Generic strong-induction on `|α|`; descent on
  reducibility cuts.
* **Origin ticket.** mg-a735.
* **Currently used for.** **Not used** in the headline
  `lem_layered_balanced` — the K ≥ 2 branch jumps directly to
  `hC3` (per `case3witness-operational-audit.md` §3a).
* **Adaptability.** This is the **foundational frame for the
  saturation lemma**.  The saturation lemma's body would build
  the `hStep` argument by case-by-case discharge across §A's 40
  classes (R / N / B branches).  Currently no `hStep` exists;
  building it is the mg-344a follow-up commission.

### `hasBalancedPair_of_layered_strongInduction` /
### `_le` variants

* **File:line.** `LayerOrdinal.lean:370, 416, 521`.
* **Currently used for.** The general (non-width-3-specific)
  framework versions.  Not consumed in tree.

---

## §8 — Brightwell axiom

### `brightwell_sharp_centred`

* **Symbol.** `OneThird.LinearExt.brightwell_sharp_centred`
* **File:line.** `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159`
* **Kind.** `axiom`
* **Statement.** Per-element perturbation bound `|Σ_{L' ∈ A} (f(L') − f̄)| ≤ 2N/m`,
  where `m = |Q| = |α| + 1`.
* **Scope.** Any finite poset α; faithful transcription of
  `step8.tex:1048, eq:sharp-centred`.
* **Origin ticket.** mg-134c.
* **QA-audited by.** mg-a6a1.
* **Status.** Retained as named axiom (decision
  `mg-b699`).
* **Currently used for.** Single-element perturbation bound used
  in higher-K balanced-pair derivations (Step 7-8 boundary).
* **Adaptability.** **F2 vacuous at K=2 / |α| ≤ 6** — the
  required `|Q| ≥ 12` is unreachable
  (`why-hC3-is-structural.md` §F2).
* **Cross-reference.** `lean/AXIOMS.md` (full disclosure).

---

## §9 — Case3Enum certificate (mg-fd88 + bridges)

### `case3_certificate`

* **Symbol.** `OneThird.Step8.Case3Enum.case3_certificate`
* **File:line.** `lean/OneThird/Step8/Case3Enum/Certificate.lean:57`
* **Kind.** `theorem`
* **Statement.** Bool-level certificate that every irreducible
  width-3 layered poset within `InCase3Scope` admits a balanced
  pair, proved by `native_decide`.
* **Scope.** `InCase3Scope w card K := K = 3 ∧ 1 ≤ w ≤ 4 ∧
  size cap` (per `BoundedIrreducibleBalanced.lean:1484`).
  **K=3 only**; does not cover K=2.
* **Origin ticket.** mg-fd88, A5-G2, A5-G3 line.
* **Currently used for.** Discharges the Case-3 certified scope
  in the F5a enumeration.  Consumes `Lean.ofReduceBool` axiom.
* **Adaptability.** A K=2 analog would be a similar Bool
  certificate over the 40-class enumeration of §A (~300-500 LoC
  per `path-c-cleanup-roadmap.md` §6b).  Not in tree.

### Case3Enum bridge family

* **Symbols.** `predMaskOf` (`BoundedIrreducibleBalanced.lean:872`),
  `enumPosetsFor`, `irreducible`, `hasAdjacentIncomp`,
  `findSymmetricPair`, `closureCanonical`, `successorMasks`,
  `bitsOf`, `cleStep`, `countLinearExtensions`, `addEdgeClose`
  (all in `Case3Enum.lean` modulo final landing locations).
* **Scope.** Bool-level routines for poset enumeration,
  irreducibility test, adjacency check, symmetric-pair detection.
* **Origin ticket.** mg-46d7, mg-a08f, mg-e9d6, mg-0f0e
  (B1-B4 bridge), mg-580e / mg-b487 (G1).
* **Currently used for.** Underlying machinery for
  `case3_certificate`.
* **Adaptability.** Available off-the-shelf for any K-restricted
  Bool certificate.  The polecat could build a K=2 certificate
  in ~300-500 LoC by reusing this kit.

### Bool↔Prop bridges

* **Files.** `Case3Enum/AdjIncompBridge.lean`,
  `Case3Enum/IrreducibleBridge.lean`,
  `Case3Enum/BalancedLift.lean`,
  `Case3Enum/EnumPosetsForBridge.lean`,
  `Case3Enum/AllBalancedBridge.lean`,
  `Case3Enum/Correctness.lean`.
* **Currently used for.** Lifting the Bool certificate to
  Prop-level conclusions on abstract finite types.

---

## §10 — Out-of-scope axiom

### `case3Witness_hasBalancedPair_outOfScope`

* **Symbol.** `OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`
* **File:line.** `lean/OneThird/Step8/Case3Residual.lean:208`
* **Kind.** `axiom`
* **Statement.** Under hybrid hypotheses (width 3, irreducible,
  K ≥ 3, w ≥ 1, size cap, depth cap, `¬ InCase3Scope`,
  `Case3Witness L`), `HasBalancedPair α`.
* **Scope.** **K ≥ 3 outside `InCase3Scope`** (the F5 C2 leaf
  beyond the enumeration's certified range).
* **Origin ticket.** mg-b846.
* **QA-audited by.** mg-7377.
* **Status.** Retained as named axiom (paper sketch
  `step8.tex:3157-3173 rem:enumeration`).
* **Currently used for.** Closes the K ≥ 3 leaves outside the
  Bool certificate's range in `bounded_irreducible_balanced_hybrid`.
* **Adaptability.** Specific to K ≥ 3.  K=2 leaves do not
  consume this axiom; they consume `Case3Witness.{u}` instead.
* **Cross-reference.** `lean/AXIOMS.md`; `case3witness-operational-audit.md`.

### `bounded_irreducible_balanced_hybrid`

* **Symbol.** `OneThird.Step8.bounded_irreducible_balanced_hybrid`
* **File:line.** `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1660`
* **Kind.** `theorem`
* **Scope.** `K ≥ 3`, `w ≥ 1`, size cap `|α| ≤ 6w + 6`,
  depth cap `K ≤ 2w + 2`.
* **Currently used for.** The F5 C2 leaf-closer; consumes
  the out-of-scope axiom on `¬ InCase3Scope`.

---

## §11 — Ancillary utility primitives

### `HasBalancedPair`

* **Symbol.** `OneThird.HasBalancedPair`
* **File:line.** `lean/OneThird/RichPair.lean` (referenced;
  see file for exact line).
* **Kind.** `def : Prop`
* **Scope.** Any finite poset.
* **Currently used for.** The conclusion type of every
  balanced-pair theorem.

### `HasWidthAtMost`

* **Scope.** Any finite poset.
* **Currently used for.** The width-3 hypothesis throughout.

### `IsChainPoset`

* **Currently used for.** The `¬ IsChainPoset β` hypothesis on
  `Case3Witness.{u}`.

### `numLinExt` / `probLT`

* **Symbols.** `OneThird.numLinExt α`, `OneThird.probLT a b`.
* **Currently used for.** The `|L(α)|` and `Pr_α[a<b]` quantities
  catalogued in §A.

### `hasBalancedPair_of_orderIso`

* **Symbol.** `OneThird.Step8.hasBalancedPair_of_orderIso`
* **File:line.** `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:251`
* **Kind.** `theorem`
* **Scope.** Any pair of order-isomorphic finite posets.
* **Currently used for.** Transports a Fin-encoded Bool-level
  balanced pair to an abstract `α` via `bandMajorOrderIso`.

### `LinearExt.transport` / `numLinExt_of_orderIso` /
### `probLT_of_orderIso`

* **File:line.** `BoundedIrreducibleBalanced.lean:131, 189, 210`.
* **Currently used for.** Fin↔α transport for the F5a route.

### `bandMajorOrderIso` / `predMaskOf` / `maskOf`

* **File:line.** `BoundedIrreducibleBalanced.lean:941, 872, 1004`.
* **Currently used for.** Encoding a `LayeredDecomposition L`
  into the Bool-certificate's predecessor-mask format.

---

## §12 — Primitives that COULD exist but DON'T

The following primitives do **not** exist in tree but would be
required by the saturation lemma for one or more branches of
its trichotomy.  Each is a **gap** that the catalog identifies.

### Gap 12.1 — `nposet_core_implies_balanced`

* **Wanted statement.** "Any width-3 K=2 layered poset α with
  an N-poset core (4-element induced N-poset) admits a balanced
  pair."
* **Why needed.** The saturation lemma's **N branch** would
  consume this to discharge classes with N-poset cores.
  Currently `bipartite_balanced_enum_general` does this only
  via the case-3 dispatch under `Case2FKGSubClaim` (which is
  provably false for the strict residual).  A direct N-core
  primitive would close the F1-inactive classes uniformly.
* **Estimated cost.** ~150-300 LoC, building on the existing
  `compoundSwap` + `MatchingCompatible` kit.
* **Trichotomy branch.** N.

### Gap 12.2 — Cyclic compound automorphism (3-cycle)

* **Wanted statement.** "On `K=2` configurations with a 3-cycle
  symmetry (specifically `K2-N6-{222}-(2,2,2)` of §A — the
  K_{3,3} \ matching 6-cycle), a cyclic compound permutation of
  order 3 is order-preserving, giving `Pr_α[a < a'] = 1/3`
  exactly for any `a, a'` in the same band."
* **Why needed.** The 6-cycle class has neither a within-band
  ⪯-pair nor a `MatchingCompatible` matching.  Existing
  `compoundSwap` is order-2; a 3-fold compound is required.
* **Estimated cost.** ~150-300 LoC, generalizing
  `compoundSwap` from `Equiv.swap` to `Equiv.cycle`.
* **Trichotomy branch.** N (cyclic).

### Gap 12.3 — F1-active uniform discharge

* **Wanted statement.** "For F1-active K=2 configurations
  (32 of 40 classes in §A), a uniform balanced-pair witness
  parameterized by the strict ⪯-pair structure."
* **Why needed.** The saturation lemma's **B branch** for the
  case-2-strict regime; this is the operative open piece of
  `hC3` (`docs/why-hC3-is-structural.md`, the F1 + F2 + F3 stack).
* **Estimated cost.** Per `case3witness-operational-audit.md` §5a:
  either ~2000-3500 LoC (A8-S2-cont's cross-poset
  probability-normalised FKG; multi-polecat) or ~300-500 LoC
  (K=2 finite-enumeration certificate; adds `Lean.ofReduceBool`
  axiom).
* **Trichotomy branch.** B.
* **Status.** Active open problem; this catalog is part of its
  scoping, not a closure.

### Gap 12.4 — Sign-imbalance / saturation primitive

* **Wanted statement.** "For any width-3 K=2 layered poset α,
  if `|sign-imbalance| < 1/3`, then α has an N-poset core or is
  ordinal-reducible."
* **Why needed.** The saturation lemma's hypothesis (mg-344a §2).
* **Status.** **No in-tree primitive related to sign-imbalance
  exists.** The quantity `Σ(α) / |L(α)|` is mentioned in §A
  but is not formalized.  Building this primitive is *part of
  the saturation-lemma construction itself*, not a missing
  utility.
* **Estimated cost.** Unknown; depends on the saturation
  lemma's exact statement.
* **Trichotomy branch.** Pre-trichotomy (the dispatch
  predicate).

### Gap 12.5 — Multi-element Brightwell

* **Wanted statement.** "Multi-element / chain-form covariance
  bound generalizing `brightwell_sharp_centred` to k-element
  perturbations."
* **Why needed.** Closes the F2 vacuity at K=2 / `|α| ≤ 6`
  (per `why-hC3-is-structural.md` §F2).
* **Estimated cost.** ~500-800 LoC of mathlib-tier covariance
  / set-system work, **if the math existed**.  Per the audit-bar
  test (mg-80ab framing 1), introducing this as a project
  axiom is RED-fallback (mathematically equivalent to the
  existing Steps 5–7 rigidity content).
* **Trichotomy branch.** B (alternative to Gap 12.3).
* **Status.** Not in scope; out-of-tree research.

### Gap 12.6 — Trichotomy dispatch predicate

* **Wanted statement.** A decidable predicate on
  `LayeredDecomposition α` that branches into
  `{N-core, reducible, balanced-pair-witness}` per-class for
  the saturation lemma's case analysis.
* **Why needed.** Discriminator for the trichotomy.
* **Status.** Not in tree.  Currently the trichotomy is a
  *structural* decomposition, not a predicate in code.
  Building a Lean dispatch predicate is part of the
  saturation-lemma construction.

---

## §13 — Summary by trichotomy branch

| branch | in-tree primitives | gaps | overall status |
|--------|---------------------|------|----------------|
| **N** (F1-inactive) | `compoundSwap`, `MatchingCompatible`, `matching_exists_of_K2_irreducible_noWithinBand`, `bipartite_balanced_enum_general` (case 3) | Gap 12.1 (uniform N-core), Gap 12.2 (cyclic compound) | mostly closed; cyclic case (`K2-N6-{222}-(2,2,2)`) is the only open piece |
| **R** (reducible) | `OrdinalDecomp` family, `OrdinalDecompOfReducible`, `hasBalancedPair_lift_{lower,upper}`, `numLinExt_factorOfReducible` | none | closed |
| **B** (F1-active residual) | `chainSwap_LE`, `probLT_le_half_of_chain` (symm pairs only), `Case2FKGSubClaim` (provably false at strict), `case3_certificate` (K=3 only), `case3Witness_hasBalancedPair_outOfScope` (K≥3 only) | Gap 12.3 (uniform F1-active), Gap 12.5 (multi-Brightwell) | open; matches the operative residual of `hC3` |

---

## §14 — Audit-bar discipline

Same as §A and §B: `feedback_audit_bar_for_axioms`,
`feedback_signature_regressions`,
`feedback_n_poset_is_not_ordinal_sum`,
`feedback_audit_as_deliverable`,
`feedback_distinguish_arc_chunk_outcomes`.

This inventory is **doc-only**.  No primitives proposed,
modified, or removed.  The "primitives that COULD exist but
DON'T" sub-section in §12 is identification, not commission;
each gap carries a cost estimate and a trichotomy-branch tag,
and is left for follow-up planning under `mg-344a`.

---

## §15 — Cross-references

* §A (`obstruction-enumeration.md`) — the 40-class catalog this
  inventory is keyed against.
* §B (`proof-techniques-taxonomy.md`) — technique categories;
  every technique has a primitive in this inventory or a gap
  in §12.
* `lean/AXIOMS.md` — full disclosure of named axioms
  (`brightwell_sharp_centred`, `case3Witness_hasBalancedPair_outOfScope`).
* `docs/case3witness-operational-audit.md` (mg-e0b8) — the
  prior pass's primitive-discovery work this inventory builds on.
* `docs/path-c-cleanup-roadmap.md` — option-(δ) park decision;
  §6 routes that this inventory's gaps map to.
* `docs/why-hC3-is-structural.md` — F1/F2/F3 framing the
  inventory is constructed against.

---

## §16 — Provenance

Sub-deliverable §C of `mg-e112`. Filed 2026-05-05 by polecat.
Origin: Daniel directive 2026-05-05T~11:30Z.  Direction context:
mg-344a (active).  Doc-only; no Lean source changes; no signature
changes; no axiom proposals.  Catalog focused exclusively on
balanced-pair construction primitives in tree as of 2026-05-05.
