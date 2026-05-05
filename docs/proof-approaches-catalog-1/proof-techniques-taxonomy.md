# §B — Proof-techniques taxonomy

**EXPLORATORY ONLY — NOT a live program.**  Sub-deliverable §B of
`mg-e112`. Doc-only. No Lean source changes; no signature changes;
no new axioms; no fresh paper-level math.

---

## §0 — Purpose and scope

### Goal

Classify the proof techniques the polecat / Daniel would use
**directly** in working out the saturation lemma's trichotomy
discharge (mg-344a §2) on the K=2 obstruction family.  For each
technique, assess strengths, weaknesses, the in-tree primitive that
instantiates it (cross-referenced to §C), and applicability to each
of the three trichotomy branches.

### Distinct from mg-8baf

`mg-8baf` (`docs/conceptual-arc-1/lit-audit.md`, archived
2026-05-05) surveyed **adjacent fields** (expander obstructions,
1D Gibbs, low-treewidth, constrained Markov chains, FKG, order
polytope, promotion, S_n random walks) for off-the-shelf imports.
Verdict: NO USABLE; SUGGESTIVE cluster around Caputo / DSC /
Bubley-Dyer addresses F5 prerequisite only.

This document is about **techniques the polecat / Daniel would
apply directly**, not external lemmas to invoke.  The categories
overlap mg-8baf's — but the framing is "what tools can we use to
discharge each branch of the trichotomy?", not "what published
result subsumes our problem?".

Where mg-8baf's SUGGESTIVE cluster appears as a relevant technique,
we cross-reference rather than re-derive.

### Stop-loss adherence

The taxonomy below uses the in-tree primitive list of §C as
ground truth.  Where a technique's in-tree primitive matches an
entry in §C, the cross-reference is explicit and we do not
re-state the primitive's statement here.  Where a technique
requires a primitive that **does not** exist in tree (e.g.,
multi-element Brightwell), we mark it "**not in tree**" and
defer to §C's "primitives that COULD exist but DON'T" sub-section.

---

## §1 — Technique categories

### §1.1 — Counting / generating functions

**Approach.** Direct enumeration of `L(α)` (linear extensions) plus
direct counting of `{L : L.lt x y}` for each incomp pair `(x, y)`,
then `Pr_α[x < y] = |{L : L.lt x y}| / |L(α)|`.  Bijective proofs
identifying `|{L : x < y}|` with `|{L : y < x}|` are a sub-technique.

**Strengths.**
* Closes any class on `|α| ≤ 6` mechanically — direct LE
  enumeration is `O(|α|! × |E|)` and runs `< 1ms` on any class
  in §A's catalog.
* Witnesses are constructive — produces the actual balanced pair
  with the actual `Pr` value.
* Compatible with Lean's `native_decide` route
  (`case3_certificate` style) — the in-tree primitive
  `Step8.Case3Enum.countLinearExtensions`
  (`lean/OneThird/Step8/Case3Enum.lean:202`) implements it
  directly.

**Weaknesses.**
* Does not generalize beyond a finite enumeration scope.  For a
  saturation-lemma proof that ranges over **all** `(K=2, w ≥ 1, |α|
  ∈ {3..6})` configurations, the route is "enumerate all 40 classes
  and certify each" — workable in tree (the Bool-certificate
  precedent of `case3_certificate` covers `K = 3, w ∈ {1..4}`),
  but the certificate adds a `Lean.ofReduceBool` axiom
  (`docs/case3witness-operational-audit.md` §5a).
* Does not produce *insight* into why a balanced pair exists —
  the "pigeonhole pattern" Daniel's mg-344a §2 sketch refers to
  is invisible from the count.

**In-tree primitive.** `countLinearExtensions`
(`lean/OneThird/Step8/Case3Enum.lean:202`); `Case3Enum.case3_certificate`
(`Case3Enum/Certificate.lean:57`); the `case3Witness_hasBalancedPair_outOfScope`
axiom for the `¬ InCase3Scope` residual
(`Case3Residual.lean:208`).  See §C for full hypotheses and scope.

**Applicability to trichotomy branches.**
* **N branch (F1-inactive):** ✓ Closes mechanically on every class
  in §A's F1-inactive list (6 classes). |α| ≤ 6 is well within
  enumeration budget.
* **R branch (reducible):** N/A — reducible classes discharge
  via `OrdinalDecomp.hasBalancedPair_lift` *before* enumeration
  is needed. The K=2/w=1/|α|=2 base case bottoms via
  `bipartite_balanced_enum_general` after one ordinal cut.
* **B branch (balanced-pair):** ✓ Closes every class — the
  balanced pair is *defined* by the count.  The witness extraction
  is the contribution.

### §1.2 — Coupling

**Approach.** Construct an injection / bijection between the
"witness" set (`{L : a <_L b}`) and a target set with a known
size relationship.  Examples: chain swap (involution on LEs swapping
`a` and `a'`), Bubley-Dyer-style path coupling, Brightwell single-
element coupling, Caputo-style comparison coupling.

**Strengths.**
* Bypasses explicit enumeration; produces a structural reason for
  the bound.
* Compatible with the in-tree `chainSwap_LE` primitive
  (`lean/OneThird/Step8/Case2Rotation.lean:553`) and
  `compoundSwap` (`CompoundSwap.lean:139`).
* For one-sided ⪯-chains, gives `Pr_α[a < a'] ≤ 1/2` with no
  enumeration (`probLT_le_half_of_chain`,
  `Case2Rotation.lean:629`).

**Weaknesses.**
* **F1 obstruction.** For strict ⪯-pairs `(a, a')` with
  `upper(a) ⊊ upper(a')` strictly, *no* order-preserving permutation
  σ has `σ a = a'` (`docs/why-hC3-is-structural.md` §F1, lemma
  proven in `path-c-track-1-status-1.md` §2).  This rules out
  compound-automorphism / triple-orbit / partial-injection variants
  for the case-2-strict residual.
* **Cardinality obstruction generalizes.** Daniel's hypothesis
  ("compound-automorphism extension would close case-2-strict")
  is provably false in tree (mg-b666, 2026-05-04) for the K=2
  case-2-strict regime (32 of 40 classes in §A are F1-active).
* Brightwell single-element coupling has a `2/|Q|` per-step
  perturbation bound; for K=2 with `|α| ≤ 6` this gives `≤ 1/6`,
  which does not close `≤ 2/3` (F2 vacuity, `why-hC3-is-structural.md`
  §F2).

**In-tree primitive.**
* `chainSwap_LE` (`Case2Rotation.lean:553`) — operative on
  one-sided ⪯-chains.
* `compoundSwap` (`CompoundSwap.lean:139`) — symmetry on
  matched pairs; consumed by `BipartiteEnumGeneral.lean:210`.
* `MatchingCompatible` structure (`CompoundSwap.lean:169`) —
  the matched-pair compatibility predicate.
* **Not in tree:** multi-element Brightwell (chain-form
  covariance); cross-poset probability-normalised FKG (the
  open A8-S2-cont infrastructure, `docs/a8-s2-status.md`).

**Applicability to trichotomy branches.**
* **N branch:** ✓ The N-poset-core (`K2-N4-22-N`) closes via
  `compoundSwap` on the diagonal pair (mg-84f2 / mg-c0c7) — one
  of the cleanest discharges in tree.  All F1-inactive classes
  in §A admit a similar treatment via `matching_exists_of_K2_
  irreducible_noWithinBand`.
* **R branch:** N/A.
* **B branch (F1-active subset):** ✗ FAIL. F1 rules out
  symmetry-based reduction to `Pr = 1/2`; chainSwap gives only
  `≤ 1/2` not `= 1/2`, but on a *strict* ⪯-pair the chain
  hypothesis does not hold (the within-band case-2-strict regime
  has `upper(a) ⊊ upper(a')` strictly, but `chain` requires the
  relation between `a` and `a'` to be known *outside* of `(a, a')`
  — which the strict containment does not give symmetrically).

### §1.3 — Structural reduction

**Approach.** Decompose `α` into smaller pieces (`OrdinalDecomp`,
B1's size-minimality, layered-reduction in tree, ⪯-pair reduction,
Dilworth chain refinement), recurse into each, lift the conclusion.

**Strengths.**
* The natural fit for a saturation lemma — the saturation lemma
  *is* a structural reduction (saturated → trichotomy → branches).
* `OrdinalDecomp.hasBalancedPair_lift_lower / _upper` (mg-7f06)
  cleanly handles the **R branch** of the trichotomy.
* B1's size-minimality reduction (`mg-805c`,
  `LayeredReduction.lean:491`) is the operative reduction at the
  Step 7 → Step 8 boundary; the polecat-instructional precedent
  is fresh and trustworthy.

**Weaknesses.**
* The **R branch** trivializes by `OrdinalDecomp` lift, but the
  **N** and **B** branches do not admit a direct structural
  reduction (the N-poset and the case-2-strict residuals are the
  *terminal* structures — they don't decompose further).
* Layered reduction (`lem_layered_reduction`,
  `LayeredReduction.lean:491`) requires `K ≥ K_0(γ, w)` with
  `K_0 ≥ 2w + 2` — vacuous for `K = 2`.  Not applicable to the
  K=2 obstruction family.
* `LayerOrdinalReducible L k` requires a band-cut `k` exists.  For
  the K=2 irreducible classes in §A's catalog, *no* such `k`
  exists by hypothesis.

**In-tree primitive.**
* `OrdinalDecomp.hasBalancedPair_lift_lower` /
  `hasBalancedPair_lift_upper`
  (`Mathlib/LinearExtension/Subtype.lean:1227, 1268`).
* `LayerOrdinalReducible` /
  `OrdinalDecompOfReducible`
  (`Step8/LayerOrdinal.lean:88, 108`).
* `lem_layered_reduction` (`LayeredReduction.lean:491`).
* `OrdinalDecomp.probLT_restrict_eq`
  (`Mathlib/LinearExtension/Subtype.lean:1065`) — marginal
  invariance, transports `Pr_α` through ordinal cuts.
* B1 size-minimality: `LayeredReduction.lean:491` and the
  `ReductionWitness` structure.

**Applicability to trichotomy branches.**
* **N branch:** ✗ The N-poset is irreducible; structural
  reduction does not apply to the terminal N case.
* **R branch:** ✓ The defining route.  `OrdinalDecomp` lift
  handles every reducible class.
* **B branch:** ✗ for the K=2/w≥1/irreducible/strict regime
  (the operative residual); the structure does not decompose
  further by hypothesis.

### §1.4 — Symmetry / group action

**Approach.** Use `Aut(α, ≤)` (or `Equiv.swap`-style ambient
permutations that preserve `≤`) to reduce LE counts on incomp
pairs.  Compound-automorphism kit (mg-84f2: `compoundSwap`,
`SameBandPair`, `MatchingCompatible`); profile-matching ambient
swaps; `Aut(α, ≤)`-orbit counting.

**Strengths.**
* Closes the N-poset class (`K2-N4-22-N`) via `compoundSwap` on
  the diagonal — the canonical clean discharge.
* For F1-inactive classes (the matching `K2-N6-M`, the 6-cycle
  `K2-N6-{222}-(2,2,2)`, etc.), the available |Aut(α, ≤)| ≥ 2
  gives an immediate route via `probLT_eq_half_of_swap_aut`
  (`BipartiteEnum.lean:95`).

**Weaknesses.**
* **F1 obstruction.** Strict ⪯-pairs with strict containment of
  upper/lower nbhds rule out any non-trivial automorphism between
  them.  For the 32 F1-active classes in §A, this branch is
  closed off entirely.
* For the 8 F1-inactive classes, |Aut(α, ≤)| is small (1, 2, 6) —
  the route is local, not a uniform argument.
* The `compoundSwap` route requires the matching-compatibility
  predicate (`MatchingCompatible L P_1 P_2`,
  `CompoundSwap.lean:169`) which is not always derivable from
  the structure; the case-3 / N-poset closure
  `matching_exists_of_K2_irreducible_noWithinBand`
  (`CompoundMatching.lean:663`) is precisely the existence proof
  for matched-pair compatibility in the F1-inactive K=2 regime.

**In-tree primitive.**
* `compoundSwap` (`CompoundSwap.lean:139`).
* `SameBandPair` (`CompoundSwap.lean:89`).
* `MatchingCompatible` (`CompoundSwap.lean:169`).
* `matching_exists_of_K2_irreducible_noWithinBand`
  (`CompoundMatching.lean:663`).
* `probLT_eq_half_of_swap_aut` (`BipartiteEnumGeneral.lean:95`).
* `bipartite_balanced_enum_general` (`BipartiteEnumGeneral.lean:210`)
  — the dispatch theorem consuming the matching primitive.

**Applicability to trichotomy branches.**
* **N branch:** ✓ Operative for all F1-inactive classes.  The
  in-tree `bipartite_balanced_enum_general` already closes this
  for `K = 2, w ≥ 1, |β| ≥ 3, NoWithinBandPreceq`.
* **R branch:** N/A.
* **B branch (F1-active):** ✗ FAIL by F1 obstruction.  The
  case-2-strict residual is precisely the regime where this
  branch fails; mg-b666 documents the obstruction.

### §1.5 — Direct enumeration

**Approach.** Enumerate the entire scope (all (K, w, bandsizes))
within a Bool certificate, run `native_decide`, and lift the
Bool-level result to Prop via the `case3_certificate` pattern.

**Strengths.**
* Mechanically closes any finite scope; the operational route for
  the K=3, w ∈ {1..4}, size-cap-7-or-9 sub-regime
  (`docs/case3witness-operational-audit.md` §3c).
* Available infrastructure: `Case3Enum.case3_certificate`
  (`Case3Enum/Certificate.lean:57`), `IsValidPredMask`
  (`BoundedIrreducibleBalanced.lean:688`), `posetFromPredMask`
  (`BoundedIrreducibleBalanced.lean:701`), Bool↔Prop bridges
  (`Case3Enum/AdjIncompBridge.lean`,
  `Case3Enum/IrreducibleBridge.lean`,
  `Case3Enum/BalancedLift.lean`).

**Weaknesses.**
* **Adds an axiom.** Closing via `case3_certificate` adds
  `Lean.ofReduceBool` to the headline `#print axioms` set
  (`docs/a5-g3e-path-c-wiring-v6-status.md` §5).  This was the
  v6 conclusion — closing K=2 by enumeration alone trades `hC3`
  for `Lean.ofReduceBool` on the K=2 piece (plus retains the
  `case3Witness_hasBalancedPair_outOfScope` axiom for K ≥ 3).
* `InCase3Scope` (`BoundedIrreducibleBalanced.lean:1484`) is the
  hard-wired scope: `K = 3 ∧ 1 ≤ w ≤ 4 ∧ size cap`.  Extending
  to K = 2 is a new Bool certificate (the
  `path-c-cleanup-roadmap.md` §6b option (α) at ~300-500 LoC).
* For the 40-class catalog of §A, direct enumeration is
  *trivial* (≪ 1s of `native_decide`); but the wiring back to a
  Prop-level discharge of the saturation lemma's trichotomy is
  not trivial — the Bool enumeration produces a `HasBalancedPair`
  per-class, and the saturation lemma's universal statement
  requires aggregation across 40 classes.

**In-tree primitive.**
* `case3_certificate` (`Case3Enum/Certificate.lean:57`).
* `case3Witness_hasBalancedPair_outOfScope` axiom
  (`Case3Residual.lean:208`).
* `InCase3Scope` (`BoundedIrreducibleBalanced.lean:1484`).
* The Case3Enum bridge family: `predMaskOf` (`:872`),
  `enumPosetsFor`, `irreducible`, `hasAdjacentIncomp`,
  `findSymmetricPair` (`Case3Enum.lean`).

**Applicability to trichotomy branches.**
* **N branch:** ✓ Mechanically.
* **R branch:** ✓ But unnecessary — `OrdinalDecomp` lift is
  cleaner.
* **B branch:** ✓ Mechanically.

### §1.6 — Order polytope / volume

**Approach.** Use `O(P)` (order polytope) or `C(P)` (chain polytope)
to recast LE counts as volumes; the marginal-volume-as-probability
framing relates `Pr_α[x < y]` to a polytope volume ratio.  Stanley-
Edelman-Hibi technology.

**Strengths.**
* Powerful framework for analytic bounds (FKG, AD-inequality,
  log-concavity).
* Connects to the Brightwell line via the FKG/AD step in
  `step8.tex:1046-1276`.

**Weaknesses.**
* Not directly useful for the specific 40-class catalog —
  polytope volumes for `|α| ≤ 6` are computed by enumeration
  anyway (the polytope is a discrete simplex / order polytope of
  a small poset).
* In tree, the polytope framing is not formalized; the FKG
  building block is in `Mathlib/RelationPoset/FKG.lean`
  (`fkg_uniform_initialLowerSet'`, lines 325, etc.) but the
  polytope itself is not.
* Reaching the saturation lemma's trichotomy via polytope volumes
  is a substantial new infrastructure layer (~1000-2000 LoC),
  not in the polecat scope.

**In-tree primitive.**
* `Mathlib/RelationPoset/FKG.lean`:
  `fkg_uniform_initialLowerSet'` (line 325).
* `Mathlib/LinearExtension/FKG.lean` (the underlying FKG / AD
  formalization of mg-391c).
* **Not in tree:** order polytope `O(P)`, chain polytope `C(P)`,
  Stanley's transfer map.

**Applicability to trichotomy branches.**
* **N / R / B:** all in principle ✓, all in practice ✗ for
  budget reasons. (mg-8baf §3.6 already classifies order polytope
  as SUGGESTIVE-not-USABLE.)

### §1.7 — Spectral / character

**Approach.** S_n character theory for the LE distribution; BK
walk eigenvalues; Cheeger inequality on the BK graph; representation-
theoretic decomposition of `L(α)`.

**Strengths.**
* The published paper's headline argument (Cheeger / BK / fiber-
  coherence / globalization / layered) — this is the **first known
  path to `δ_3* = 1/3`** via spectral methods (`why-hC3-is-structural.md`
  §F3).
* Working note `notes-bk-walk-eigenvalues-by-irrep.md` (mg-7e24)
  is current Daniel-side material.

**Weaknesses.**
* Arc 4.0 (mg-0bc8) closed RED at Step 2 specifically on the K=2
  N-poset: the spectral argument requires `K ≥ 2w + 2` for
  Cheeger to fire, vacuous at K=2.
* For the K=2 obstruction family (where the saturation lemma
  ranges), spectral / character methods do not give a uniform
  bound — they give a "Cheeger inequality" that the K=2 regime
  fails to satisfy structurally (the BK-graph mixing time at
  K=2 is small but the conductance bound is too loose).
* In tree: not formalized.  The paper's Cheeger argument is
  manual at the LaTeX level; the `BrightwellAxiom.lean` axiom
  imports the per-element perturbation bound, which is the FKG/AD
  consequence of the spectral content, not the spectral content
  itself.

**In-tree primitive.**
* `brightwell_sharp_centred` axiom
  (`BrightwellAxiom.lean:159`) — the FKG/AD-derived per-element
  bound.  Vacuous at K=2 / |α| ≤ 6 per F2.
* **Not in tree:** S_n character theory; BK walk eigenvalues;
  Cheeger inequality; the spectral content of the published proof.

**Applicability to trichotomy branches.**
* **N branch:** ✗ vacuous at K=2.
* **R branch:** N/A.
* **B branch (K=2):** ✗ — F3 obstruction documents 30+ years of
  unsuccessful "correlation-inequality + width-3" attacks.

### §1.8 — Probability moment / FKG / log-concavity

**Approach.** Chan-Pak, Kahn-Linial, Brightwell-Felsner-Trotter
correlation inequalities; FKG sub-claims; log-concavity of LE
counts under one-element perturbations.

**Strengths.**
* The standard "Kahn-Saks line" (`why-hC3-is-structural.md` §F3
  table).
* `fkg_uniform_initialLowerSet'`
  (`Mathlib/RelationPoset/FKG.lean:325`) is in tree as the
  building block for the `brightwell_sharp_centred` axiom.

**Weaknesses.**
* F2 numerical instantiation: at K=2, `|α| ≤ 6` makes the
  single-element Brightwell bound `2 / |Q| ≥ 2/6 = 1/3`, which
  cannot close the `≤ 2/3` target.  Iterated Brightwell is
  *worse* (harmonic-sum bound).
* F3 literature obstruction: the unconditional
  correlation-inequality bounds have been stuck below `1/3` for
  30+ years.
* The cross-poset probability-normalized FKG (the open
  A8-S2-cont infrastructure) is the proposed extension; **not
  in tree** (`docs/a8-s2-status.md` §5: ~2000-3500 LoC,
  multi-polecat).

**In-tree primitive.**
* `brightwell_sharp_centred` (axiom).
* `Mathlib/RelationPoset/FKG.lean` and `Mathlib/LinearExtension/FKG.lean`.
* **Not in tree:** cross-poset probability-normalized FKG;
  multi-element / chain-form Brightwell; log-concavity of LE
  counts.

**Applicability to trichotomy branches.**
* **N / R:** N/A.
* **B branch (K=2 case-2-strict):** ✗ by F2; the regime where
  the saturation lemma ranges is precisely the regime where this
  technique fails.

---

## §2 — Per-branch applicability summary

| technique          | N branch | R branch | B branch (F1-active) |
|--------------------|---------|---------|----------------------|
| Counting / GFs     | ✓ mechanical | N/A | ✓ mechanical |
| Coupling           | ✓ via compoundSwap | N/A | ✗ F1 |
| Structural reduction | ✗ | ✓ | ✗ |
| Symmetry / group   | ✓ N-poset, matching | N/A | ✗ F1 |
| Direct enumeration | ✓ (+ axiom) | ✓ unnec. | ✓ (+ axiom) |
| Order polytope     | ✓ infra missing | N/A | ✓ infra missing |
| Spectral           | ✗ K=2 vacuous | N/A | ✗ F3 |
| FKG / log-concav   | N/A | N/A | ✗ F2 / F3 |

**Reading.** The trichotomy's three branches admit **disjoint**
discharge routes in tree:

* **R branch:** structural reduction (`OrdinalDecomp` lift) —
  cleanest, no axioms beyond what's already in tree.
* **N branch:** symmetry/coupling (`compoundSwap` + matching) —
  for F1-inactive classes only; existing infra
  (`bipartite_balanced_enum_general`) closes them.
* **B branch (F1-active residual):** **only** counting / direct
  enumeration produces a discharge in tree; both add an axiom
  (`Lean.ofReduceBool` and/or `case3Witness_hasBalancedPair_
  outOfScope`).

This is consistent with the v6 / mg-5f0c conclusion (5-axiom target
inflates to 7 axioms) and with the audit's mg-e0b8 finding (no
single-trick discharge of `Case3Witness.{u}`).

---

## §3 — Per-class applicability (cross-reference to §A)

For each F1-classification group of §A, which technique is the
intended discharge?

### F1-inactive classes (6 total in §A)

| class | trichotomy | technique | in-tree primitive |
|-------|-----------|-----------|-------------------|
| `K2-N3-AC` | B | counting (3-elt antichain) | `bipartite_balanced_enum` |
| `K2-N3-AC'` | B | counting | same (dual) |
| `K2-N4-22-N` | N | symmetry: `compoundSwap` on diag | `bipartite_balanced_enum_general` (mg-02c2) |
| `K2-N6-M` | N | symmetry: `compoundSwap` on the 3 matching pairs | (same family; matching compatibility holds by no-within-band) |
| `K2-N6-{122}-(1,2,2)a` | B | symmetry: symm-pair `compoundSwap` | (same family) |
| `K2-N6-{222}-(2,2,2)` | N (cyclic) | symmetry: `Equiv.swap` along cycle | needs **6-cycle-aware** lemma — **not in tree** |

The 6-cycle class (`K2-N6-{222}-(2,2,2)`) has no within-band ⪯-pair
*and* no matching-compatible pair pair (the cyclic structure
prevents `MatchingCompatible` from holding).  This is a **gap**
in the in-tree compound-automorphism kit — see §C "primitives
that COULD exist but DON'T".

### F1-active classes (32 total in §A)

For these, the intended discharge in the saturation lemma is
**not** symmetry-based.  Per-class options:

* **Strict ⪯-pair present (the case-2-strict regime):**
  `chainSwap_LE` gives `Pr ≤ 1/2` only when the chain hypothesis
  `(∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)` holds — which
  fails when `(a, a')` is *strictly* ⪯-related (one direction).
  See mg-b0de / mg-a79e for the specific failure on the K=2 strict
  3-element witness `K2-N3-MIN`.
* **Symm ⪯-pair only (no strict):** `chainSwap_LE` applies (the
  chain hypothesis holds at equality of nbhds).  Closes `Pr ≤ 1/2`,
  combined with `Pr ≥ 1/2` from the dual chain → `Pr = 1/2` and
  balanced.
* **Both bands have nontrivial structure but no chain:** direct
  enumeration via `case3_certificate`-style Bool certificate is
  the only in-tree route.

---

## §4 — Gap analysis: techniques the saturation lemma needs but lacks

The saturation lemma's trichotomy commits to discharging every
class via one of {N, R, B}.  Per §2 and §3, the following are
**unsupported** by current in-tree machinery:

### Gap 1 — 6-cycle / cyclic-N case in F1-inactive

**Class.** `K2-N6-{222}-(2,2,2)` (the 6-cycle `K_{3,3} \ matching`).

**Issue.** No within-band ⪯-pair (incl. symm) and no
`MatchingCompatible` matching exists (the cyclic structure prevents
the predicate from holding).  Existing
`matching_exists_of_K2_irreducible_noWithinBand`
(`CompoundMatching.lean:663`) discharges the *non-cyclic*
F1-inactive subset; the cyclic case is **not closed**.

**Closure path.** A 3-cycle compound-automorphism on
`(a_1, a_2, a_3) → (b_1, b_2, b_3)` (a 6-element rotation) — the
generalization of `compoundSwap` to a 3-fold orbit.  Estimated:
~150-300 LoC of new infrastructure on top of the existing
compound-automorphism kit.  Not in scope for this catalog.

(It is *possible* this class admits a separate balanced-pair
witness by counting — `Pr` for any incomp pair is `1/2` by the
6-cycle symmetry, all pairs balanced — but the *uniform structural*
discharge requires the cyclic compound-automorphism.)

### Gap 2 — case-2-strict residual

**Classes.** Every F1-active class with a strict ⪯-pair (most of
the 32 F1-active classes — see §A for per-class detail).

**Issue.** F1 + F2 + F3 obstruction stack
(`why-hC3-is-structural.md` §§F1-F3).  No in-tree-derivable
technique closes this regime as of 2026-05-04 (mg-b666).

**Closure path (NOT for this catalog).** Either (a) cross-poset
probability-normalised FKG (A8-S2-cont; ~2000-3500 LoC), (b) K=2
finite-enumeration certificate (path-c-cleanup-roadmap.md §6b;
~300-500 LoC + `Lean.ofReduceBool` axiom), or (c) a math-simp arc
reframing (Track 2; multi-week external research).

### Gap 3 — saturation-lemma framework itself

**Issue.** The saturation lemma's *body* (the proof of the
trichotomy) is not constructed in tree.  The F3 strong-induction
framework `hasBalancedPair_of_layered_strongInduction_width3`
(`LayerOrdinal.lean:472`) is in tree but unused
(`docs/case3witness-operational-audit.md` §3a) — it requires an
`hStep` argument that supplies the per-step closure.  This `hStep`
is the saturation lemma's *content*; building it is the
mg-344a follow-up commission.

The catalog above is the structural prerequisite for that
construction, not the construction itself.

---

## §5 — Anti-techniques (excluded by F1/F2/F3)

For audit-bar discipline, we record the techniques that are *not*
applicable to the K=2 obstruction family, with the specific
obstruction:

| anti-technique | obstruction | source |
|----------------|-------------|--------|
| Compound-automorphism on case-2-strict | F1 (cardinality) | `why-hC3-is-structural.md` §F1 |
| Triple-orbit / partial-injection variants | F1 | same |
| Iterated Brightwell at K=2 / |Q| ≤ 6 | F2 (numerical vacuity) | `why-hC3-is-structural.md` §F2 |
| Direct correlation-inequality + width-3 | F3 (30-year literature gap) | `why-hC3-is-structural.md` §F3 |
| `Case2BipartiteBound` extended to w ≥ 1 | structural (`hAB` fails) | `Case2BipartiteBound.lean:182` (mg-ed4d) |
| Cross-poset count-form FKG | wrong normalisation | `why-hC3-is-structural.md` §F2 |
| Chain swap on `(a, z)` for K=2 / w ≥ 1 | chain hypothesis fails | `a8-s2-restate-block-and-report-status.md` §3.4 |

These anti-techniques are explicitly *not* candidate discharges
for the saturation lemma's B branch.  Polecat / Daniel commissioning
a follow-up that re-attempts any of them must do so with explicit
override (audit-bar: external + difficult + labeled + low-risk —
F1/F2/F3 fail at least one each).

---

## §6 — Audit-bar discipline

Same as §A: `feedback_audit_bar_for_axioms`,
`feedback_signature_regressions`,
`feedback_n_poset_is_not_ordinal_sum`,
`feedback_audit_as_deliverable`,
`feedback_distinguish_arc_chunk_outcomes`.

This taxonomy is **doc-only** — no Lean source changes proposed
or implemented.  The cross-references to §A's per-class data and
§C's in-tree primitive list are the load-bearing structure;
deviations from those (e.g., proposing a new in-tree primitive)
are flagged as "**not in tree**" with an estimated cost in §C.

---

## §7 — Cross-references

* §A (`obstruction-enumeration.md`) — the 40-class enumeration
  that this taxonomy is applied to.
* §C (`in-tree-primitive-inventory.md`) — full Lean primitive
  cross-reference.
* `docs/why-hC3-is-structural.md` — the F1/F2/F3 framing this
  taxonomy applies to anti-techniques.
* `docs/conceptual-arc-1/lit-audit.md` (mg-8baf) — adjacent-field
  literature audit; this taxonomy's category structure echoes
  §1.3 / §3.3 of that audit.
* `docs/case3witness-operational-audit.md` (mg-e0b8) — operational
  consumption analysis; this taxonomy's gap analysis (§4) is the
  forward-direction complement to that audit's residual-gap
  analysis.
* `docs/path-c-track-1-status-1.md` (mg-b666) — Track 1 cardinality
  obstruction; provides the F1 specific lemma cited here.

---

## §8 — Provenance

Sub-deliverable §B of `mg-e112`. Filed 2026-05-05 by polecat.
Origin: Daniel directive 2026-05-05T~11:30Z.  Direction context:
mg-344a (active).  Doc-only; rigor-first; no fresh paper-level math.
