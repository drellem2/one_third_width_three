# Layered-form vs. coherence — architecture audit

**Work item:** `mg-74d2` (strategic-architectural audit polecat, single-session, paper-and-pencil, no Lean code changes).

**Trigger (Daniel verbatim, 2026-05-17T21:18Z):**

> "what we need, highest priority, is for a polecat to determine: does
> this reduction to layered form actually buy us anything, or was
> there nothing poset-structural all along? we need to decide if
> poset structure is even the right tool here or if we should be
> sticking with what we know about the 'coherence' part of the
> 'coherence-collapse' case."

**Predecessors absorbed.**
- `mg-e2e9` (`docs/onethird-Case3Witness-architecture-analysis.md`) — cap-5 proposal, AMBER-missing-bound-fix-proposed.
- `mg-d5a0` (`docs/state-Case3Witness-cap5-fix.md`) — cap-5 lean landing, structured `sorry` at `LayeredBalanced.lean:626`/`:751`.
- `mg-0cbf` (`docs/onethird-Case3Witness-post-cap-5-tractability-analysis.md`) — D2-tractable verdict.
- `mg-4d7b` (`docs/state-Case3Witness-cap5-enumeration.md`) — enumeration substrate landed GREEN, K=2..9 verified.
- `docs/why-hC3-is-structural.md` — F1/F2/F3 obstructions, option-(δ) park rationale.
- F-series `compatibility-geometry-F31-phi-star-injectivity.md` — RED-chain-locality, cohomological re-emergence walled.

---

## Verdict (top-of-page): **layered-form-functionally-vacuous-at-headline / load-bearing-only-at-leaf-encoding / DO-NOT-pivot-to-coherence-implementation**

The reduction to layered form **does not buy structural constraint on
α**.  At the operational headline call site
(`lem_layered_balanced` K ≥ 2 branch,
`LayeredBalanced.lean:626-756`), the input `L : LayeredDecomposition α`
is **never consumed structurally** — it is discarded and replaced by a
fresh `canonicalLayered α` (a trivial Szpilrajn-derived decomposition
with `K = w = |α|`). Cap 5 (`L'.w ≤ 4`) cannot be discharged on
`canonicalLayered α` for `|α| ≥ 5`; that gap is the structured `sorry`
landed in mg-d5a0.

Inside `Case3Witness_proof`'s strong-induction discharge of the
post-cap-5 universal, the only place where structural layered axioms
are *genuinely consumed* is at the F5a Bool certificate leaf
(`bounded_irreducible_balanced_inScope`,
`BoundedIrreducibleBalancedInScope.lean:97`), where the
`cross_band_lt_upward` field (L2-upward, mg-53ce / A5-G2 path 1) is
needed to make `predMaskOf L` upper-triangular — an **encoding
artefact**, not a structural insight about α.  Everything above the
leaf (F3 strong-induction recursion, hybrid dispatch, K = 1/K = 2
contradictions) consumes the layered structure only through numeric
projections (`L.K`, `L.w`, `Fintype.card α`) and degenerate
specialisations (band trichotomy at K ≤ 2, antichain at K = 1).

**Daniel's diagnostic is correct.**  The layered-form architecture
operates as a *typed routing convention* for the dispatch tree, not as
a structural reduction.  The pre-cap-5 form was demonstrably equivalent
to the headline (mg-e2e9 §2d); the post-cap-5 form (`LB.w ≤ 4`) is a
finite-domain restriction (`|β| ≤ 30`, or `|β| ≤ 10` under cap 1
Injective) but is **not deliverable** by the in-tree
`canonicalLayered`-shortcut and is **not deliverable** by the current
Lean Steps 1-7 extractor (`ChainPotentials.lean` returns
`bandwidth = |α| + 1`, not the paper's `w₀(γ)`).

The corresponding strategic question — *should we pivot to the coherence
approach?* — has a sharper answer than the framing implies.  The
coherence content is *not absent* from the in-tree story: it is
**axiomatised at the paper level** (Steps 1-7 deliver `LayeredWidth3`,
consumed by `LayeredBridges.layeredFromBridges`). The architectural
disconnect is not that we abandoned coherence for poset structure; it
is that the **operational headline path bypasses both** by using
`canonicalLayered`.  The cohomological re-emergence of coherence in
the F-series (F8-F31) has walled out at F31 RED with three further
RED/AMBER routes upstream, so coherence is not deliverable by
cohomology either.

**Recommended pivot: drop, not re-implement.**  Post-mg-4d7b, the
right move is to **drop the layered-form encoding at the headline
level** and restate the headline as

* For `|α| ≤ 10` width-3 non-chain finite β: balanced pair exists
  (mg-4d7b enumeration certificate, Option D-narrow lifts the
  remaining `case3Witness_hasBalancedPair_outOfScope` axiom).
* For `|α| ≥ 11`: open in tree, pending genuine Lean delivery of
  Steps 1-7's `w₀(γ)`-bounded layered structure (paper-axiomatised
  path; corresponds to Daniel's "stick with coherence" if it means
  *the paper's coherence-collapse argument*, not a Lean re-derivation).

This is **not** a pivot to a fresh coherence implementation; it is a
pivot to **honest disclosure**: the layered-form bridge as currently
shipped is a typed-routing fiction at the headline, and the paper-side
coherence content is the true structural backstop.  Either we deliver
Steps 1-7 faithfully in Lean (multi-month) or we accept the headline
as conditional on Steps 1-7 (the current status, just stated
honestly).

The verdict is **layered-form-vacuous-at-headline**, not
*both-exhausted-need-new-direction*: the math of coherence-collapse is
intact in the paper; only its Lean delivery is missing.  And not
*layered-form-real*: the architecture pays no structural rent in the
universe of width-3 finite posets — its sole load-bearing use is the
upper-triangular `predMaskOf` encoding, which is replaceable by any
Szpilrajn linear extension (no layered axioms required).

---

## §0. Audit scope and method

This audit traces every use of `LayeredDecomposition α` structural
properties — L1a (`band_size ≤ 3`), L1b (`band_antichain`), L2-forced
(`forced_lt`), L2-upward (`cross_band_lt_upward`), K depth, w
interaction width, band assignment — across the operational headline
call chain:

```
OneThird.width3_one_third_two_thirds                  (MainTheorem.lean:52)
  ↓  threads hC3 : Case3Witness
width3_one_third_two_thirds_assembled                 (MainAssembly.lean:320-339)
  ↓
mainAssembly / mainTheoremInputsOf                    (MainAssembly.lean:238-247)
  ↓
lem_layered_balanced                                  (LayeredBalanced.lean:626)
  ↓  K = 1 branch: bipartite_balanced_enum (closes inline)
  ↓  K ≥ 2 branch: hC3 α canonicalLayered <caps proved in-place; cap 5 sorry>
                                                      (LayeredBalanced.lean:756)
Case3Witness.{u}                                      (LayeredBalanced.lean:461)
  ↓  proved by:
Case3WitnessProof.Case3Witness_proof                  (OptionC/Case3WitnessProof.lean:256)
  ↓  K = 1 → absurd_K1_of_injective
  ↓  K = 2 reducible → isChain_of_K2_reducible_under_injective (contradiction)
  ↓  K = 2 irreducible → option_c_K2_closure (K2Closure.lean)
  ↓  K ≥ 3 reducible → recurse on D.Lower or D.Upper via compactify
  ↓  K ≥ 3 irreducible → bounded_irreducible_balanced_hybrid
                          ↓  hCert  → bounded_irreducible_balanced_inScope
                          ↓  hStruct → hStruct_of_case2_discharge
                                       (Case 1: hasBalancedPair_of_ambient_profile_match;
                                        Case 2: case2_discharge_of_injective [vacuous under cap 1];
                                        Case 3: case3Witness_hasBalancedPair_outOfScope [AXIOM])
```

For each consumer, the audit asks two questions:

1. **Real-use vs cover-use.** Does the lemma's proof *consume* a
   layered axiom in a way that fails on a non-layered width-3 non-chain
   poset?  Or does it consume only numeric projections (K, w, |α|),
   degenerate specialisations (singleton bands under cap 1), or
   encoding affordances (Szpilrajn-equivalent structure)?
2. **Operational reachability.** Is the layered structure that
   reaches this consumer at the headline operationally *non-trivial*,
   or is it the `canonicalLayered α` Szpilrajn-derived shortcut?

Only items that pass **both** (real consumption AND operationally
non-trivial L) are "layered-form-real".  Items that pass (1) but fail
(2) are "real-at-leaf, cover-at-headline".  Items that fail (1) are
"cover-use, replaceable by any Szpilrajn extension".

The corpus surveyed: `Step8/{LayeredReduction, LayeredBalanced,
BoundedIrreducibleBalanced, BoundedIrreducibleBalancedInScope,
Case2BipartiteBound, Case2FKG, Case2Rotation, Case3Dispatch,
Case3Struct, Case3Residual, LayerOrdinal, LayeredBridges,
ChainPotentials, MainAssembly}.lean` plus
`Step8/OptionC/{Case3WitnessProof, K2Closure}.lean` plus
`Step8/Case3Enum/*.lean` certificate plumbing plus
`Step8/LayeredDecomposition/Compactify.lean`.

---

## §1. Phase A — per-lemma layered-form audit

### 1a. Summary table

Verdicts use the legend:

* **R-leaf** — real structural use, but only at a Bool-certificate
  encoding leaf where the layered structure is consumed as a typed
  index (predMaskOf upper-triangularity); replaceable by *any*
  Szpilrajn-equivalent typed input.
* **R-numeric** — uses only numeric projections (`L.K`, `L.w`,
  `Fintype.card α`); the band map is not consumed as a function from
  α.
* **R-degenerate** — relies on a degenerate specialisation (K = 1
  forces α = single antichain; K = 2 + cap 1 forces singleton bands;
  K = 2 + w = 0 forces bipartite shape).  The layered hypothesis here
  is equivalent to a *direct* poset-shape hypothesis (antichain /
  height-2 / Szpilrajn-extension).
* **C-bypass** — covered (i.e. typed-consumed) but the input `L` is
  discarded for `canonicalLayered`; equivalent to no layered
  hypothesis at all.
* **C-marker** — `L` appears as a parameter but is never used in the
  proof body (e.g. F3 strong-induction skeleton).

| Lemma / theorem | Layered axioms used | Real-use? | Op. reachable L? | Net verdict |
|---|---|---|---|---|
| `LayeredDecomposition` (struct) | n/a — definition | — | — | — |
| `comparable_of_far` (`LayeredReduction.lean:165`) | L2-forced | yes | yes via paper | R-numeric (uses only `max/min` of band) |
| `restrict` (`LayeredReduction.lean:203`) | All four axioms transfer | yes | n/a (passthrough) | mechanical infrastructure |
| `lem_cut` (`LayeredReduction.lean:373`) | L2-forced | yes | only at non-trivial w | R-numeric (consumes `band x + w < band y`); but `lem_cut` is **not consumed** in the in-tree dispatch — see §1c |
| `lem_layered_reduction` (`LayeredReduction.lean:491`) | none directly | no | — | C-marker — packages caller's `balanced` Prop |
| `windowLocalization` (`LayeredBalanced.lean:103`) | L2-forced | yes | only at non-trivial w | R-numeric; **not consumed** in dispatch — leftover G3 infrastructure |
| `rotation_lower_bound` / `_contradiction` / `probLT_three_cycle_ge_one` | none | — | — | combinatorial, no layered content |
| `bipartiteBalanced` / `bipartite_balanced_enum` | none (consumes height-2 + antichain hypotheses directly) | — | — | combinatorial — not layered |
| `hasWidthAtMost_subtype` | none | — | — | width-3 transfer |
| `Case3Witness.{u}` (Prop) | caps 1-5 are *Props on L* | n/a — definition | — | — (definition under audit) |
| `canonicalLayered α` (`LayeredBalanced.lean:498`) | L2-forced VACUOUS by construction (w=|α|) | — | — | trivial Szpilrajn instance; cap 5 unsatisfiable for `|α| ≥ 5` |
| `canonicalLayered_band_injective` | n/a — fact about Szpilrajn | — | — | infrastructure |
| `canonicalLayered_bandSet_nonempty` | uses `Function.Surjective` on Szpilrajn | — | — | infrastructure |
| **`lem_layered_balanced`** (`LayeredBalanced.lean:626`) — K = 1 branch | L1b (band_antichain at 1), L1a (band_size 1 ≤ 3), band_pos, band_le | yes | n/a (forces α = antichain) | R-degenerate — equivalent to "α is an antichain on ≤ 3 elements" + `bipartite_balanced_enum` |
| **`lem_layered_balanced`** K ≥ 2 branch | **input L NOT used** — substitutes `canonicalLayered α` | no | **no — bypassed** | **C-bypass** — operational headline path discards `L`; cap 5 `sorry` |
| `lem_layered_balanced_subtype` (`LayeredBalanced.lean:776`) | passthrough via `L.restrict D.Mid` | inherited from `lem_layered_balanced` | same as parent | inherits C-bypass at K ≥ 2 |
| `OrdinalChainLift` family | none — composes balanced-pair lifts | — | — | infrastructure |
| `layered_implies_balanced` (`LayeredBalanced.lean:927`) | none directly — wraps `lem_layered_balanced` | — | — | wrapper |
| `LayerOrdinalReducible` / `LayerOrdinalIrreducible` (def) | L.band + L.K (numeric) | — | — | numeric on band map |
| `OrdinalDecompOfReducible` | band trichotomy at cut | yes | only at non-trivial K | R-numeric |
| `linExtEquivOfReducible` / `numLinExt_factorOfReducible` | none on layered side (uses `OrdinalDecomp.tripleEquiv`) | — | — | F1 infrastructure |
| `exists_adjacent_not_lt_of_irreducible` (`LayerOrdinal.lean:276`) | irreducibility def, `band_pos`, `band_le`, hNonempty bands | yes | always | R-numeric — proof is chain-of-bands induction, uses band as index map |
| **`hasBalancedPair_of_layered_strongInduction[_width3]`** (`LayerOrdinal.lean:370/472`) | **L is a marker** — never used | no | — | **C-marker** — F3 recursion is on `Fintype.card α` only |
| `LinearExt.transport` / `numLinExt_of_orderIso` / `probLT_of_orderIso` / `hasBalancedPair_of_orderIso` (`BoundedIrreducibleBalanced.lean:131-251`) | none — order-iso transport | — | — | infrastructure |
| `bandSize` / `bandSizes` / `bandSizes_mem_bandSizesGen` | L1a (`bandSize_le_three`) | yes | n/a (numeric encoding) | R-numeric |
| `bandIdx` / `bandFiberEquiv` / `bandMajorEquiv` / `bandMajorOrderIso` | band map injective on canonical-form data | yes | always | R-leaf — band-major Fin-n encoding |
| `predMaskOf` (`BoundedIrreducibleBalanced.lean:872`) | depends on `bandMajorOrderIso` | yes | always | R-leaf — Bool-encoding bridge |
| `predMaskOf_warshall` / `closureCanonical_predMaskOf` / `predBitsBoundedBy_predMaskOf` | band structure of `predMaskOf` | yes | always | R-leaf |
| `maskOf` / `maskOf_lt_two_pow_size` | band structure of `freeUVOf` | yes | always | R-leaf |
| `enumPredAtMaskOf_eq_predMaskOf` (G3c, `mg-9568`) | **`cross_band_lt_upward` (L2-upward, mg-53ce)** — load-bearing for upper-triangularity | yes | always | **R-leaf — the one place L2-upward is genuinely consumed** |
| `irreducible_predMaskOf_offsetsOf_eq_true` (B1') | `LayerOrdinalIrreducible` | yes | always | R-leaf |
| `hasAdjacentIncomp_predMaskOf_eq_true` (B2) | L.band, L.K, hNonempty | yes | always | R-leaf — band-major positional alignment |
| `InCase3Scope` (def) / `InCase3Scope.w_mem` / `InCase3Scope.card_le_nine` | none on layered side | — | — | numeric predicate on (w, card, K) |
| **`bounded_irreducible_balanced`** (`:1626`) | **ALL `_h*` args unused** — returns `hEnum` directly | no | — | **C-marker** — typed routing only |
| **`bounded_irreducible_balanced_hybrid`** (`:1681`) | **ALL `_h*` args unused** — `by_cases InCase3Scope L.w (card α) L.K` | no | — | **C-marker** — typed routing only |
| `bounded_irreducible_balanced_of_hybrid` | n/a | — | — | trivial corollary |
| **`bounded_irreducible_balanced_inScope`** (`BoundedIrreducibleBalancedInScope.lean:97`) | **L1a (bandSize ≤ 3), L1b (band_antichain via B2), L2-upward (G3c, the load-bearing usage), `LayerOrdinalIrreducible`, band_pos/le** | yes | always | **R-leaf — the only theorem in the chain that genuinely consumes structural layered content** |
| `Case2BipartiteBound.*` (K=2, w=0) | L1a, L1b, L2-forced at K=2 (forces band-1 < band-2), band trichotomy | yes | only at K=2 ∧ w=0 | R-degenerate — operationally equivalent to "α is height-2 with `A < B`" + `bipartite_balanced_enum` |
| `Case2FKG.case2Witness_or_case1_match` / `case2Witness_balanced_or_strict` | within-band `band_antichain` | yes | always | R-numeric — within-band structure |
| `Case2Rotation.*` (rotation + chain-swap) | layered FKG content | yes | always | R-numeric on band-grouped elements |
| `Case3Dispatch.case1_dispatch_inScope` / `_balanced_or_witness` | band-distance via L2-forced | yes | always | R-numeric |
| `Case3Struct.hasBalancedPair_of_ambient_profile_match` | none on layered side — pure `Equiv.swap` | — | — | infrastructure |
| `Case3Residual.case3Witness_hasBalancedPair_outOfScope` (AXIOM) | takes layered profile, returns conclusion | n/a — axiom | — | **operational axiom** — the residual gap mg-4d7b aims to remove |
| `Case3Residual.hStruct_of_case2_discharge` | passthrough | — | — | wraps the axiom |
| `OptionC.option_c_K2_closure` (`K2Closure.lean:500`) | L1a, L2-forced (VACUOUS at K=2, w≥1 per file docstring) | partial | K=2 always | R-degenerate at L2-forced; uses certificate at K=2 |
| **`OptionC.Case3Witness_proof`** (`OptionC/Case3WitnessProof.lean:256`) | band_pos/le for K=1 contradiction; band trichotomy for K=2 chain force; `compactify` descent (uses band structure); leaf dispatch via `bounded_irreducible_balanced_hybrid` | yes | always | R-numeric at K=1/2; R-leaf at K≥3 in-scope; **opaque (axiom)** at K≥3 out-of-scope |
| `LayeredBridges.layeredFromBridges` (`:181`) | builds `LayeredDecomposition α` from `Step7.LayeredWidth3` + `ChainLiftData α` | yes | n/a (constructor) | infrastructure — but `Lwidth3.bandwidth = Fintype.card α + 1` in current chain potentials, so the structural promise is undelivered |
| `ChainPotentials` family | none on layered side | — | — | upstream data (paper-axiomatized at the `bandwidth ≤ w₀(γ)` claim) |
| `MainAssembly.trivialLayered` / `mainTheoremInputsOf` | construct `LayeredDecomposition α` via Szpilrajn (== `canonicalLayered` shape) | — | — | shipped as `caseR_to_caseC` — but `lem_layered_balanced` discards it at K≥2 |

### 1b. The one place layered structure is structurally consumed

There is **exactly one** lemma in the dispatch chain whose proof would
*break* if the layered hypothesis were weakened to "α is a width-3
non-chain finite poset":

* `bounded_irreducible_balanced_inScope`
  (`BoundedIrreducibleBalancedInScope.lean:97`) — the certificate-driven
  discharge of the in-scope F5a leaves.

The proof composes G1'-G3a-G3b-G3c with B1'-B2-B3 to lift the Bool
certificate `Case3Enum.enumPosetsFor LB.w (bandSizes LB) = true` to
`HasBalancedPair α`.  The genuinely structural inputs are:

* `bandSizes_mem_bandSizesGen` (uses `bandSize_le_three` = L1a);
* `irreducible_predMaskOf_offsetsOf_eq_true` (uses
  `LayerOrdinalIrreducible`, a definition over `L.band`);
* `hasAdjacentIncomp_predMaskOf_eq_true` (uses band-positional
  alignment, requires `band_pos`/`band_le`/non-empty bands);
* `closureCanonical_predMaskOf` / `predMaskOf_warshall` /
  `predBitsBoundedBy_predMaskOf` (all use the band-major encoding via
  `bandMajorOrderIso`);
* **`enumPredAtMaskOf_eq_predMaskOf` (G3c)** — uses
  **`cross_band_lt_upward` (L2-upward)** to make `predMaskOf L`
  upper-triangular.  This is the load-bearing structural use of a
  layered axiom in the entire chain.

But — and this is the crux — **L2-upward is a property of
*any* Szpilrajn extension of α**.  The band map `band x` of any
layered decomposition satisfying L2-upward induces a partial order on
α via `band x ≤ band y` whenever `x ≤ y`, which is exactly the
Szpilrajn-extension condition.  So the load-bearing layered axiom is
operationally *replaceable* by "α admits some Szpilrajn linear
extension" — which is **automatic** for every finite poset.

The remaining structural content of L (the size cap L1a, the antichain
cap L1b, the L2-forced cross-band comparability) is consumed *only*
through:

- L1a: feeds into `bandSizes` enumeration domain (`bandSizesGen K
  sizeLimit`); under cap 1 (Injective), tightens to "≤ 1", so the
  enumeration is over `[1; K]` tuples only (mg-4d7b's exact scope).
- L1b: within-band antichain — under cap 1, vacuous (singleton bands).
- L2-forced: cross-band forced comparability — under cap 5 (w ≤ 4),
  non-trivial; under canonicalLayered (w = |α|), vacuous.

Net: under the cap-1 + cap-5 universe that `Case3Witness_proof`
operates in, the structural content reduces to:

> "α admits a labelling `e : α → [1, K]` with K = |α|, e is order-preserving, and any pair `(x, y)` with `e(x) + 4 < e(y)` is forced `x < y`."

This is a real constraint on α (a width-3 non-chain finite poset of
size ≤ 10 may or may not admit such an `e`), but it is constraint
*about Szpilrajn extensions*, not about an external layered
structure.

### 1c. The infrastructure-without-consumer pattern

`lem_cut` (`LayeredReduction.lean:373`) and `windowLocalization`
(`LayeredBalanced.lean:103`) — the two centrepieces of the paper's
GAP G3 / G4 cut-and-window argument — are **stated** in tree but
**never consumed** by the in-tree dispatch.

- `lem_cut` is referenced by `lem_layered_reduction` (the GAP G3
  packaging), which is in turn never invoked by `lem_layered_balanced`
  (the GAP G4 leaf); G3 and G4 are stated as parallel branches in
  `layered_implies_balanced`'s docstring but the K ≥ 2 dispatch of G4
  goes straight to `hC3 α canonicalLayered`, bypassing both cut and
  reduction.
- `windowLocalization` is referenced in the docstring of
  `lem_layered_balanced`'s K ≥ 2 branch as the intended mechanism, but
  the proof body never invokes it.

So the layered-form-as-paper-tool — *cut into an interaction window of
size ≤ 3(3w + 1), apply Step 3 (bulk) or Step 5 (perturbation), descend
by size-minimality* — is **not the in-tree dispatch shape**.  The
in-tree dispatch is *uniformly* via the F5a Bool certificate at the
in-scope leaves and via the `case3Witness_hasBalancedPair_outOfScope`
axiom at the out-of-scope leaves; the cut machinery is leftover
infrastructure from the previous size-minimal framing (mg-805c) that
the layered-balanced refactor never fully connected.

This is itself a Phase A finding: even within the layered architecture,
the paper's intended structural mechanism (lem_cut + windowLocalization
+ size-minimal contradiction) is *not* what the Lean dispatch
executes.  The Lean dispatch is *certificate enumeration* + *axiom*,
with the layered form as a typed routing convention to align the
certificate's parameter space.

### 1d. The bounded_irreducible_balanced "marker theorem" pattern

The two API-level theorems `bounded_irreducible_balanced` and
`bounded_irreducible_balanced_hybrid` deserve emphasis:

```lean
theorem bounded_irreducible_balanced
    (L : LayeredDecomposition α)
    (_hWidth3 : HasWidthAtMost α 3)
    (_hIrr : LayerOrdinalIrreducible L)
    (_hK3 : 3 ≤ L.K)
    (_hw : 1 ≤ L.w)
    (_hCard : Fintype.card α ≤ 6 * L.w + 6)
    (_hDepth : L.K ≤ 2 * L.w + 2)
    (hEnum : HasBalancedPair α) :
    HasBalancedPair α :=
  hEnum
```

Every layered hypothesis is `_unused`.  The "theorem" is a typed
identity passing `hEnum` through.  The structural content is wholly
imported from the caller's `hEnum` discharge — which in
`Case3WitnessProof.lean:537` is the actual call to
`bounded_irreducible_balanced_inScope` (in-scope) or the axiom
(out-of-scope).

`bounded_irreducible_balanced_hybrid` is similarly a typed routing
function:

```lean
theorem bounded_irreducible_balanced_hybrid (… all unused …) :
    HasBalancedPair α := by
  by_cases h : InCase3Scope L.w (Fintype.card α) L.K
  · exact hCert h
  · exact hStruct h
```

The only `L`-dependent computation is `InCase3Scope L.w (Fintype.card α) L.K` — a numeric predicate.

This is the **structural fingerprint of the layered-form-as-typed-routing pattern**.  The layered axioms are not consumed; they are *announced* on the API surface to align with the paper's hypothesis profile, then discarded inside the proof body.  An auditor reading the theorem signature would assume the proof exploits L1/L2; the proof in fact exploits nothing on L beyond `L.w` / `L.K` / numeric.

This pattern recurs at:
- `bounded_irreducible_balanced` (§1d, above);
- `bounded_irreducible_balanced_hybrid` (§1d, above);
- `bounded_irreducible_balanced_of_hybrid` (trivial corollary);
- F3 strong induction (`hasBalancedPair_of_layered_strongInduction[_width3]`) — `L` is in the signature, never used in the body.

Together these account for the **entire** API-level "layered → balanced" routing.  The structural content lives in exactly one place (`bounded_irreducible_balanced_inScope`), and there it is mostly encoding-level (predMaskOf upper-triangular).

### 1e. The canonicalLayered substitution — operational vacuity

The headline path:

```lean
theorem lem_layered_balanced (L : LayeredDecomposition α) … (hC3 : Case3Witness.{u}) : HasBalancedPair α := by
  …
  -- K ≥ 2 branch:
  let L' : LayeredDecomposition α := canonicalLayered α   -- DISCARDS L
  have hInj  := canonicalLayered_band_injective
  have hKw   := …                                          -- trivially proved
  have hCardw := …                                         -- trivially proved
  have hNonempty := canonicalLayered_bandSet_nonempty
  have hLBw : L'.w ≤ 4 := sorry                            -- mg-d5a0 cap-5 gap
  exact hC3 α L' hInj hKw hCardw hNonempty hLBw hW3 hNotChain' h2
```

Operational facts:

1. **The input `L` is never used.**  The lemma signature takes `L`,
   but the K ≥ 2 branch (the only non-trivial branch — K = 1 collapses
   to `bipartite_balanced_enum`) constructs a fresh `L' :=
   canonicalLayered α` and discards `L`.
2. **The Case3Witness hypothesis is applied to a trivial
   substitution.**  `canonicalLayered α` is the Szpilrajn-singleton
   layering: K = w = |α|, each band a singleton.  Caps 1-4 are
   trivially satisfied by construction.
3. **Cap 5 fails on the substitution for |α| ≥ 5.**  `L'.w = |α|`, so
   `L'.w ≤ 4` is unprovable for any α with `|α| ≥ 5`.  This is the
   `sorry` landed in mg-d5a0.

The pre-cap-5 form (caps 1-4 only) silently absorbed this absurdity:
the universal `Case3Witness β` ranged over every width-3 non-chain
finite β admitting a layered decomposition with caps 1-4, which is
*every* finite β (via `canonicalLayered β`).  Per mg-e2e9 §2d, that
made `Case3Witness ⇔ headline theorem` modulo the K = 1 branch.

The post-cap-5 form (caps 1-5) makes the absurdity *visible* as a
type error: the operational substitution cannot satisfy cap 5, so the
K ≥ 2 dispatch carries a structured `sorry`.  But the universal
`Case3Witness` is now a *finite* claim (over width-3 non-chain β with
|β| ≤ 30 and an LB with w ≤ 4) that is — provably — operationally
unreachable at |α| ≥ 5 via the `canonicalLayered` shortcut.

So **either**:
- We accept the `sorry` and acknowledge the headline is only
  unconditionally valid for `|α| ≤ 4` (where `canonicalLayered` has
  `w = |α| ≤ 4` and cap 5 is satisfied by inspection — `case3_certificate`
  covers this regime exhaustively, so even `hC3` is operationally
  unused at those sizes).  OR
- We deliver a *real* cap-5-satisfying `L : LayeredDecomposition α`
  on the headline path.  Options:
  - **Option A**: Steps 1-7 deliver `Lwidth3.bandwidth ≤ 4` upstream
    (currently delivers `bandwidth = |α| + 1`; multi-month Lean work).
  - **Option B**: F3 strong-induction descent on `|α|` with bounded-w
    leaves (blocked on `mg-b666` K=2 case-2-strict residual).
  - **Option C**: drop `Case3Witness` hypothesis entirely (same
    blockers as A or B).
  - **Option D-broad** (per mg-0cbf): post-mg-4d7b, `|α| ≤ 10` is
    discharged unconditionally via enumeration; `|α| ≥ 11` retains
    the same Options A/B blockers.

All four routes lead back to either Steps 1-7 delivery or the
mg-b666 obstruction.  Neither is reachable without paper-level work.

### 1f. Phase A conclusion

| Question | Answer |
|---|---|
| Does the layered structure provide a structural constraint on α beyond "α is a width-3 non-chain finite poset"? | **Effectively no.** Under cap 1 + cap 5 the structural content reduces to "α admits a Szpilrajn extension with bounded incomparability span", but that constraint is *operationally unreachable* via the in-tree `canonicalLayered` shortcut for `|α| ≥ 5`. |
| Are the layered axioms (L1a, L1b, L2-forced, L2-upward) load-bearing for the in-tree dispatch? | **Only L2-upward, and only at the certificate-encoding leaf.** L1a/L1b are used at degenerate K = 1, K = 2 specialisations or as enumeration-domain numerics; L2-forced is vacuous on `canonicalLayered`. |
| Is the paper's intended structural mechanism (`lem_cut` + `windowLocalization` + size-minimal contradiction) what the Lean dispatch executes? | **No.** The Lean dispatch is *certificate enumeration* at the in-scope leaves + *axiom* at the out-of-scope leaves. `lem_cut` and `windowLocalization` are stated but never consumed. |
| Does the F3 strong-induction skeleton consume the layered structure? | **No.** F3's `hStep` signature takes `L : LayeredDecomposition α` but the proof body never uses it; recursion is on `Fintype.card α` alone. |
| Are the "bounded_irreducible_balanced[_hybrid]" API theorems structurally non-trivial? | **No.** Every layered hypothesis is `_unused`; both theorems are typed-routing identities passing the caller's `hEnum` discharge through. |

The layered-form architecture is, in the in-tree Lean realisation, a
**typed-routing convention** for aligning the F5a Bool certificate's
parameter space with the paper's hypothesis vocabulary.  It does
*not* extract structural insight about α; it does *not* execute the
paper's cut-and-window argument; it does *not* deliver a meaningful
operational reduction.

This confirms — sharply — Daniel's diagnosis: the reduction to
layered form did not buy structural constraint.  Pre-cap-5, this was
hidden under a vacuous universal (mg-e2e9); post-cap-5, the
operational gap is exposed as a structured `sorry` but the
structural debt is the same.

---

## §2. Phase B — clean-restatement scope (the "if layered-real" branch)

**Phase B applies only if Phase A says layered-form-real.**  Phase A
says **layered-form-vacuous at the headline; real-only at the
leaf-encoding**.  So Phase B is largely moot.  But the partial
real-use at the leaf does admit a clean restatement scope worth
recording — partly to dispose of the question, partly to clarify
what mg-4d7b's enumeration substrate does (and does not) cover.

### 2a. Where layered structure is *minimally* real

Only one usage survives Phase A scrutiny:

* The F5a Bool certificate's `predMaskOf L` upper-triangularity
  requirement, satisfied by L2-upward (`cross_band_lt_upward`,
  mg-53ce / A5-G2 path 1).  This is the bridge that lets
  `Case3Enum.enumPosetsFor LB.w (bandSizes LB) = true` (a `native_decide`
  Bool fact about parameter tuples) translate into "every width-3
  layered β in that scope has a balanced pair".

Strictly speaking, this is *not* a use of layered structure on α as a
mathematical object.  It is a use of the *labelling data* `band : α →
[1, K]` as an indexing convention for an upper-triangular bitmask
encoding.  Any Szpilrajn extension of α provides exactly the same
labelling data (singleton bands of K = |α|).

### 2b. Clean restatement: drop "LayeredDecomposition" at the API surface

If we accept Phase A's verdict (layered-form-real-only-at-leaf), the
clean restatement is:

1. **Replace `Case3Witness.{u}` with a width-3 enumeration claim.**
   The post-cap-5 universal — *"every width-3 non-chain finite β
   admitting an LB with all five caps has a balanced pair"* — under
   cap 1 (Injective) collapses to: *"every width-3 non-chain finite β
   with |β| ≤ 10 admitting some Szpilrajn extension with bounded
   incomparability span ≤ 4 has a balanced pair."* The cap-1
   restriction makes the band map carry no information beyond a
   Szpilrajn extension.

2. **Restate the Case3Witness-discharge as a direct width-3
   enumeration certificate.**  mg-4d7b's K = 2..9 enumeration (plus
   the K = 10, w = 4 cell in flight) covers exactly the scope
   reachable under cap 1 + cap 5.  Bridge: every width-3 non-chain
   finite β with |β| ≤ 10 *automatically* admits a Szpilrajn extension
   with bounded incomparability span (because |β| ≤ 10 caps the span
   trivially at `|β| − 1 ≤ 9`).  So at |β| ≤ 10 the cap-5 restriction
   is vacuous; the universal reduces to "every width-3 non-chain
   finite β with |β| ≤ 10 has a balanced pair", which is exactly
   what mg-4d7b's Phase B verifies.

3. **Drop `lem_layered_balanced` from the headline path.**  Replace
   `mainTheoremInputsOf`'s `decompReductionOrConclude` /
   `caseR_to_caseC` fields with direct width-3 cases:
   - `|α| ≤ 10`: invoke mg-4d7b's certificate.
   - `|α| ≥ 11`: invoke (axiomatised) Steps 1-7 to deliver the bounded-w
     layered piece via `LayeredBridges.layeredFromBridges`, then route
     through the existing `lem_layered_balanced` consumer **provided
     Steps 1-7 are upgraded to deliver `bandwidth ≤ 4` (not the
     current `Fintype.card α + 1`)**.

4. **Preserve the certificate plumbing.**  Steps 1-2 don't require
   touching `BoundedIrreducibleBalancedInScope.lean`, the F5a Bool
   certificate, or the band-major encoding bridges.  They remain as
   the *operational backbone* for the `|α| ≤ 10` slice and any future
   bounded-w leaf dispatch.

### 2c. Scope estimate for clean-restatement

* **mg-4d7b Phase E** (Lean integration of the K=2..10 enumeration):
  already in scope per mg-4d7b ticket body. Status: K=2..9 done; K=10
  w=4 in flight. Estimated remaining: ~1 polecat session for K=10
  closure + Lean wiring.

* **Option D-narrow follow-on** (replace
  `case3Witness_hasBalancedPair_outOfScope` axiom with extended
  certificate): ~200-400 LoC per mg-0cbf §5e. Single-polecat scope.

* **Headline restatement** (drop `Case3Witness` from the public
  signature of `OneThird.width3_one_third_two_thirds`, expose two
  conditional theorems `width3_one_third_two_thirds_smallN` (|α| ≤ 10,
  unconditional) and `width3_one_third_two_thirds_largeN` (|α| ≥ 11,
  conditional on Steps 1-7 delivery)): ~200-300 LoC of refactoring.
  Single-polecat scope.

* **Cleanup of unused layered infrastructure** (`lem_cut`,
  `windowLocalization`, `lem_layered_reduction`,
  `bounded_irreducible_balanced`/_hybrid` marker theorems if they
  become orphaned): optional, ~300-500 LoC removable per
  `feedback_aggressive_dead_code_cleanup`.  Or keep as
  documentation-only infrastructure if the paper's mechanism is to
  remain visible.

Total scope of clean-restatement (excluding Steps 1-7 delivery):
**3-5 polecat sessions, no new project axioms, drops one project
axiom (`case3Witness_hasBalancedPair_outOfScope`)**.

The clean-restatement is **independent of the coherence pivot
question** raised in Phase D.  It is the *honest* response to Phase
A's verdict regardless of any larger strategic decision.

---

## §3. Phase C — coherence-predecessor audit

**Phase C applies if Phase A says layered-form-vacuous.**  Phase A
does say layered-form-vacuous (at the headline; real-only at leaf).
So Phase C is operative.  But the conclusion may surprise: there is
nothing meaningfully different to *pivot to*.  The coherence content
is already where it belongs — in the paper, as Steps 1-7.

### 3a. The paper-side coherence content (Steps 3-7)

The paper's "coherence-collapse" argument (`main.tex` §1.4, road map)
lives at Steps 3-7:

* **Step 3** (`step3.tex`): interface coherence — define a pairwise
  relation on rich pairs `(x, y), (u, v) ∈ Rich`, classifying whether
  their induced fiber-local monotone directions agree on the overlap.
* **Step 4** (`step4.tex`): two-interface incompatibility — two
  *incoherent* rich interfaces force many BK-boundary crossings.
  Quantitatively, this is the *expansion engine*.
* **Step 5** (`step5.tex`): richness lemma — a width-3 counterexample
  produces enough rich interfaces for the expansion engine to bite.
* **Step 6** (`step6.tex`): dichotomy — either many rich interfaces
  are incoherent (immediate contradiction with low-conductance via
  Step 4), or almost all are coherent.
* **Step 7** (`step7.tex`): coherence implies collapse — in the
  coherent case, the rich interfaces glue into a single global
  potential function (Prop. 7.1), and the poset degenerates to a
  layered 1-dimensional form (Prop. 7.2) which is balanced by direct
  inspection (Prop. 7.3).

Step 7's Prop. 7.2 is the bridge from "coherence" to "layered
decomposition with bounded `w`".  This is *the* mechanism by which
the layered form acquires structural content: the layered
decomposition's interaction width `w` is the Step 7 bandwidth `c₀`
(`step7.tex:320, prop_72`), which is `O_T(1)` — i.e., independent of
|α|.

In Lean, this is captured at:
- `Step7/Assembly.lean:302` — `LayeredWidth3` structure (the paper's
  Prop. 7.2 output).
- `Step8/LayeredBridges.lean:181` — `layeredFromBridges`, constructing
  a `LayeredDecomposition α` from `LayeredWidth3` + `ChainLiftData`.
- `Step8/ChainPotentials.lean` — the chain potentials / sync map
  infrastructure consumed by `layeredFromBridges`.

**The structural promise.**  When `LayeredWidth3.bandwidth ≤ w₀(γ)`
(the paper's constant), `layeredFromBridges` delivers a
`LayeredDecomposition α` with `w ≤ w₀(γ) ≤ 4` (for an appropriate
choice of constants matching `InCase3Scope.w_mem`).

**The current Lean reality.**  `ChainPotentials.lean`'s extractor
returns `Lwidth3.bandwidth = Fintype.card α + 1` (per
`LayeredBridges.lean:53, 209, 215`).  The structural promise is *not
delivered*; Steps 3-7 are stubbed at the bandwidth bound.

### 3b. The cohomological re-emergence of coherence (F-series)

A separate effort — the compatibility-geometry / F-series — attempted
to re-derive the coherence content via cohomological tools rather than
the paper's direct BK-Cheeger argument.  Status:

* F1-F22: various scoping and feasibility studies for the chamber-Morse
  / discriminant-cell-poset framework.
* F23: canonical descent rule.
* F24: route fork comparison.
* F25 (RED): Hypothesis-A constants audit.
* F27 (RED): spectral-to-cohomology scoping.
* F28 (AMBER): sheaf cohomology on POSET.
* F29 (AMBER, mg-70b0): Cech bias cohomology.
* F30 (AMBER, mg-c3fe): chain-level Φ.
* **F31 (RED-chain-locality-obstruction, mg-01ce)**: Φ* injectivity
  on the bad-cut Cech class.  Verdict: `\Phi_*` is **not** injective;
  the kernel structurally contains the bad-cut class.  Three closure
  routes (direct injectivity / LES / combinatorial basis) all wall at
  the same chain-locality obstruction.

The F31 verdict (`compatibility-geometry-F31-phi-star-injectivity.md`
top-line): **four-routes-walled** for the Cech-bias closure of
milestone-1 part (iii).  Quoting:

> "The F-series cohomological core (parts (i)–(ii), unconditional post
> F17+F18), the Lean trust surface, the methodology paper draft, and
> `main.tex` + Steps 1–8 (Route B mathematically correct conditional
> on Hyp A) are all *unchanged* by F31's RED — F31 walls a specific
> closure route, it does not retract earlier results."

So the cohomological route to delivering coherence content
*independently of Steps 1-7* has walled out.  F32 (width-3
specialisation feasibility, `compatibility-geometry-F32-width3-feasibility.md`)
was placed on hold per Daniel directive.

### 3c. Can we revive a "fresh attack" from coherence?

The audit ticket asks: "assess viability of fresh attack on width-3
(acknowledging F31 RED-chain-locality + F-series cohomology blockers)."

The relevant distinction is:

(α) **Reviving the paper's Steps 1-7 by faithfully formalising them
   in Lean.**  This delivers `Lwidth3.bandwidth ≤ w₀(γ)` upstream,
   which feeds `layeredFromBridges` with a cap-5-compatible `L`,
   which closes the operational `sorry` at `LayeredBalanced.lean:751`
   for arbitrary |α|.  **Scope: multi-month / Path A of mg-e2e9 §3c.**
   No new mathematical ideas required — Steps 1-7 are written and
   reviewed at the paper level; only the Lean delivery is missing.
   This is the *correct* coherence pivot if "coherence" means *the
   paper's coherence-collapse argument*.

(β) **Re-deriving coherence content via cohomology (F-series
   continuation).**  **Walled at F31 RED.**  No GREEN routes survive
   within the F17+F18 anchor regime per `F31 §3.5` route audit.

(γ) **Fresh non-coherence non-poset attack** (e.g., a width-3
   Kahn-Linial tightening of the published `δ* ≥ 0.276` correlation-
   inequality bound to reach `≥ 1/3`).  Per `why-hC3-is-structural.md`
   §F3, this is the *Brightwell-pump* / *Kahn-Linial alternate route*
   — judged RED-fallback under arc-2.0 polecat scoping (multi-week
   external research; presumed already attempted by the original
   Kahn-Linial / Brightwell line over decades).

(δ) **Accept the current status as the honest end-state.**  Headline
   is conditional on `hC3 : Case3Witness` per the option-(δ) park
   decision.  Disclose the F1/F2/F3 obstructions as the structural
   explanation for *why* the conditional retains.  This is the
   currently-shipped path; see PATH A disclosure surface
   (`docs/lean-forum-publication-readiness.md`).

**Recommendation between (α), (β), (γ), (δ).**  (β) is walled, (γ) is
out of polecat scope.  (α) is the path that would deliver real
structural content — but at multi-month cost.  (δ) is the
already-shipped honest disclosure.

The pragmatic move is to *combine* (δ) with **mg-4d7b's enumeration
substrate** (already in flight, GREEN through K = 9): this delivers
the headline *unconditionally* for `|α| ≤ 10` (or `|α| ≤ K_max` once
the enumeration extends), reducing the conditional gap from "all
sizes" to a sharp `|α| ≥ 11` slice.  The disclosure becomes:

> "Width-3 1/3-2/3 is proved in Lean unconditionally for `|α| ≤ 10`;
> for `|α| ≥ 11` it is proved conditional on Steps 1-7 delivering the
> bounded-w layered decomposition (axiomatised at
> `Step7.LayeredWidth3` in tree, matching the paper's content)."

### 3d. What "coherence" buys vs. what "layered form" buys

Daniel's framing — "if poset structure isn't the right tool, stick
with coherence" — implicitly contrasts two tools.  Let me sharpen
what each tool actually does:

**The poset / layered-form tool** (Step 8 + this audit):
- *Inputs*: a layered decomposition `L : LayeredDecomposition α`
  with bounded `w`.
- *Mechanism*: cut at index `k ∈ (w, K − w)`, restrict to interaction
  window of size `≤ 3(3w + 1)`, apply size-minimal contradiction or
  iterate on the smaller piece.
- *Output*: balanced pair in α.
- *In-tree status*: typed-routing fiction at the headline; real only
  at the F5a Bool certificate leaf for small `|β|`.
- *Operational gap*: cannot satisfy cap 5 on the substituted
  `canonicalLayered α` for `|α| ≥ 5`.

**The coherence / BK-Cheeger tool** (Steps 1-7):
- *Inputs*: a width-3 finite poset `P`, the BK graph `BK(P)` on
  linear extensions.
- *Mechanism*: a putative counterexample (no balanced pair) would
  force a low-conductance cut on `BK(P)`; the cut decomposes locally
  via fiber-coordinate maps; interface coherence dichotomy forces
  either incompatibility-contradiction or coherent collapse.
- *Output*: contradiction (no counterexample exists) OR layered
  collapse (which the layered-form tool then disposes of).
- *In-tree status*: paper-axiomatised at `Step7.LayeredWidth3`; not
  faithfully Lean-proved.
- *Operational gap*: Lean Steps 1-7 deliver `bandwidth = |α| + 1`
  (vacuous), not the paper's `w₀(γ) = O_T(1)`.

The two tools are **stacked**, not alternatives.  Coherence delivers
the bounded-w layered form; the layered form is then disposed of by
the cut argument.  The current Lean architecture has both gaps:

1. **Coherence (Steps 1-7) does not deliver bounded w in Lean.**
2. **Layered form (Step 8) does not consume the bounded w even if it
   were delivered.**  The dispatch goes via `canonicalLayered`,
   discarding the `L` extracted from upstream.

Gap (2) is the focus of mg-d5a0's structured `sorry` and this audit.
Gap (1) is the focus of any "Option A" / Steps-1-7-delivery scope.

Fixing only (2) would expose (1).  Fixing only (1) is wasted unless
(2) is also fixed.  The right move is to fix (2) first by
**eliminating the canonicalLayered substitution at the headline**, at
which point (1) becomes the named blocker.  This is what mg-4d7b
partially achieves — for `|α| ≤ 10`, mg-4d7b's enumeration sidesteps
the need for any layered-form dispatch.

### 3e. Conclusion of Phase C

There is **no fresh coherence attack to revive**.  The paper's
coherence content is already where it should be (`main.tex` Steps
3-7, formalised in `Step7/Assembly.lean` as axiom-level stubs);
delivering it faithfully in Lean is multi-month Option-A work.  The
F-series cohomological re-emergence walled at F31.  The
correlation-inequality alternate route is out of scope.

The "stick with coherence" recommendation is operationally identical
to "accept the option-(δ) park and disclose Steps 1-7 as the
upstream gap" — which is the current shipped status.

The substantive forward action is **not** a coherence pivot; it is:

* finishing **mg-4d7b** (enumeration substrate, in flight);
* implementing **Option D-narrow** (replace
  `case3Witness_hasBalancedPair_outOfScope` axiom with extended
  certificate);
* **restating the headline** to expose `|α| ≤ 10` as unconditional
  and `|α| ≥ 11` as conditional on faithful Steps 1-7 delivery (the
  honest disclosure pivot).

---

## §4. Phase D — forward strategic recommendation

### 4a. Top-line verdict

**layered-form-functionally-vacuous-at-headline / load-bearing-only-at-leaf-encoding / DO-NOT-pivot-to-coherence-implementation / DO-pivot-to-honest-restatement**

The reduction to layered form **did not buy structural constraint**
at the headline.  It bought a *typed routing convention* that
mis-presents the F5a Bool certificate's encoding bridge as a
structural reduction.  Pivoting to a coherence-based attack is
**not** what's needed — the coherence content is already
paper-correct and Lean-axiomatised in the appropriate place.

The needed pivot is **architectural honesty**: drop the
`Case3Witness` universal as the headline interface, expose mg-4d7b's
enumeration as the `|α| ≤ 10` unconditional discharge, and disclose
the `|α| ≥ 11` slice as conditional on Steps 1-7's bandwidth
delivery.

### 4b. Why this is not "layered-form-real"

The layered-form is real at exactly one place
(`bounded_irreducible_balanced_inScope`'s use of `cross_band_lt_upward`
to make `predMaskOf L` upper-triangular).  That use is replaceable by
*any* Szpilrajn extension of α.  It is encoding-level, not structural.
A "layered-form-real" verdict would require structural use that
distinguishes the layered hypothesis from "α is width-3 non-chain
finite"; no such use is present in the in-tree dispatch.

### 4c. Why this is not "both-exhausted-need-new-direction"

The paper's coherence-collapse argument is intact.  Steps 1-7 are
written, reviewed, and paper-axiomatised in Lean at the
`Step7.LayeredWidth3` interface.  Closing the operational gap is a
*Lean delivery* problem, not a *mathematical research* problem.  The
mathematical research is the F1/F2/F3 disclosure (per
`why-hC3-is-structural.md`) explaining *why* the residual is hard —
and the answer is "Steps 1-7's BK-Cheeger machinery is the first
known path through", *not* "no path exists".

### 4d. Why this is not "layered-form-vacuous-pivot-to-coherence"

The framing of "pivot to coherence" suggests we replace the layered
dispatch with a coherence-based dispatch.  But the coherence-based
dispatch *is* Steps 1-7 → layered form → window/cut argument.  There
is no shorter coherence path that avoids producing a layered output.
The "coherence vs poset" dichotomy is mis-posed: coherence
*produces* the poset structure (the layered decomposition) as its
collapse output.

The pivot from layered to coherence in the operational sense would
mean **bypassing the layered form output** entirely — operating
directly on `BK(P)` to derive the contradiction without going through
the layered intermediate.  But the paper's Step 7 / Prop. 7.1 (global
potential) / Prop. 7.2 (layered collapse) / Prop. 7.3 (balanced pair
in collapsed case) explicitly *goes through* the layered intermediate.
There is no published "coherence ⇒ balanced pair" path that skips the
layered step.

### 4e. Concrete forward plan

**Immediate (already in flight)**:
1. **mg-4d7b enumeration substrate** — finish K = 10 w = 4 (in flight
   at ~30% per worker); land Lean wiring per its Phase E plan.
   Status: AMBER per mg-4d7b's own verdict, but on track.

**Next 2-3 polecat sessions**:
2. **Option D-narrow Lean execution** (post-mg-4d7b): extend
   `case3_certificate` with the 15 cap-1 cells of mg-0cbf §2;
   refactor `Case3WitnessProof.lean` to consume the extended
   certificate in the out-of-scope branch; remove the
   `case3Witness_hasBalancedPair_outOfScope` axiom.  Drops one project
   axiom; no fresh blockers.

**Next 1-2 sessions, in parallel**:
3. **Headline restatement**: split
   `OneThird.width3_one_third_two_thirds` into two theorems:
   - `width3_one_third_two_thirds_smallN` — unconditional for `|α| ≤
     10`, discharged via mg-4d7b certificate.  No `hC3` hypothesis.
   - `width3_one_third_two_thirds_largeN` — conditional on Steps 1-7
     bandwidth delivery for `|α| ≥ 11`.  Keep the typed Steps-1-7
     dependency visible at the API surface.  No `hC3` hypothesis.
   - Combined `width3_one_third_two_thirds`: cases on `|α|`,
     dispatches.  Discharge same as currently shipped except that
     `hC3` is no longer carried.

**Optional cleanup (1 session)**:
4. **Remove unused layered-form infrastructure** that becomes
   orphaned post-restatement:
   - `lem_cut`, `windowLocalization`, `lem_layered_reduction`
     (currently never consumed; were size-minimal-form leftovers).
   - `bounded_irreducible_balanced` / `_hybrid` marker theorems if no
     downstream consumer remains.
   - `canonicalLayered` and the K ≥ 2 dispatch in
     `lem_layered_balanced` (the `sorry`-carrying branch).
   Per `feedback_aggressive_dead_code_cleanup`.  Or keep with revised
   docstrings naming them as paper-mechanism documentation rather
   than operational dispatch.

**Long arc (multi-month, not polecat scope)**:
5. **Option A — faithful Steps 1-7 in Lean** — deliver
   `Lwidth3.bandwidth ≤ w₀(γ)` from `ChainPotentials.lean` rather
   than `Fintype.card α + 1`.  This closes the `|α| ≥ 11`
   conditionality of step (3) above.  Estimated multi-month per
   mg-e2e9 §3c.  Off-ramp: leave conditional indefinitely with the
   PATH A disclosure (current status, just with a smaller residual
   slice after step (3)).

### 4f. Implications for mg-0cbf + mg-4d7b artefacts

Both mg-0cbf and mg-4d7b were merged GREEN per the audit ticket's
context.  Neither becomes load-bearing for the *new* architecture; both
remain as **smaller-context references** under the recommended
restatement:

* **mg-0cbf** (`docs/onethird-Case3Witness-post-cap-5-tractability-analysis.md`):
  Its D2-tractable verdict + 15 cap-1 cells analysis remains the
  blueprint for Option D-narrow's certificate extension (step 2
  above).  Its "Option D-broad only closes |α| ≤ 10" framing remains
  the honest framing for the restatement (step 3 above).  The
  document is the architectural anchor for the post-restatement
  shape.
* **mg-4d7b** (`docs/state-Case3Witness-cap5-enumeration.md` +
  `lean/scripts/enum_cap5.py` + Lean Cap5Singletons certificates):
  Its enumeration substrate IS the operational `|α| ≤ 10` discharge.
  Post-restatement, mg-4d7b's certificate is the *primary* dispatch
  for the unconditional half of the headline; it is no longer "an
  axiom-reduction follow-on" but the headline's actual proof body
  for small |α|.

The cap-5 surfaced gap (`LayeredBalanced.lean:751` `sorry`, mg-d5a0)
does not get *closed* by the recommended forward plan — it gets
*excised*.  Under the restatement, `lem_layered_balanced` is no
longer on the headline path for `|α| ≥ 2` (only mg-4d7b's
certificate for `|α| ≤ 10` and the Steps-1-7-conditional path for
`|α| ≥ 11`).  The `sorry` either lives in a still-unused legacy
lemma (kept for documentation of the paper's intended mechanism) or
is removed with the lemma.

The pre-existing `case3Witness_hasBalancedPair_outOfScope` axiom
(`Case3Residual.lean:208`) is removed by Option D-narrow (step 2).

The pre-existing `Case3Witness.{u}` Prop is removed by the headline
restatement (step 3).  Its dependents (`Case3WitnessProof.lean`,
`mainTheoremInputsOf`, `width3_one_third_two_thirds_assembled`,
`width3_one_third_two_thirds_via_step8`) are simplified accordingly.

**Net architectural change**: 5+ files significantly reshaped, ~1
project axiom dropped, structured `sorry` excised, headline
conditional pushed from "all sizes via hC3" to "|α| ≥ 11 via Steps
1-7 axiom-level dependency".  No new project axioms; no new
mathematical content required.

### 4g. The strategic choice for Daniel

The audit ticket asks for one of three verdicts:

- **GREEN Phase A-D delivered + clear strategic recommendation
  (layered-form-real / pivot-to-coherence / both-exhausted) + scope
  estimates + mg-0cbf+mg-4d7b implication captured.**

This audit returns: **layered-form-vacuous-at-headline**, with the
strategic recommendation being **not** "pivot to coherence
implementation" but **"restate the headline to expose the small-|α|
unconditional slice + large-|α| Steps-1-7-conditional slice"** — a
disclosure pivot rather than a mathematical pivot.

If Daniel prefers the canonical "pivot to coherence" framing, the
operational equivalent is: **acknowledge that 'coherence' = paper's
Steps 1-7 = currently paper-axiomatised, and the multi-month delivery
arc to faithfully Lean-prove Steps 1-7 is what 'sticking with
coherence' actually entails**.  The audit does *not* recommend
queueing that work yet — the restatement (step 3 above) reduces the
residual to a sharp `|α| ≥ 11` slice, after which Steps 1-7 delivery
becomes prioritisable on its own merits.

The verdict in the GREEN / AMBER / RED legend of the ticket:

**GREEN-Phase-A-D-delivered + recommendation =
restate-then-conditionally-pursue-Steps-1-7-faithful-Lean-delivery.**

---

## §5. Cross-references and load-bearing claims

* `lean/OneThird/Step8/LayeredReduction.lean:115-149` —
  `LayeredDecomposition α` struct (K, w, band, L1a, L1b, L2-forced,
  L2-upward).
* `lean/OneThird/Step8/LayeredReduction.lean:373` — `lem_cut`: stated
  but never consumed in current dispatch.
* `lean/OneThird/Step8/LayeredReduction.lean:491-495` —
  `lem_layered_reduction`: stated but never consumed; threads
  caller's `balanced` Prop through.
* `lean/OneThird/Step8/LayeredBalanced.lean:103-172` —
  `windowLocalization`: stated but never consumed.
* `lean/OneThird/Step8/LayeredBalanced.lean:461-472` — post-cap-5
  `Case3Witness.{u}` (the universal under audit).
* `lean/OneThird/Step8/LayeredBalanced.lean:498-535` —
  `canonicalLayered α`: trivial Szpilrajn instance; cap 5 fails for
  `|α| ≥ 5`.
* `lean/OneThird/Step8/LayeredBalanced.lean:626-756` —
  `lem_layered_balanced`: the operational headline path. K ≥ 2 branch
  discards `L`, substitutes `canonicalLayered`, carries the cap-5
  `sorry` at `:751`.
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1626-1643` —
  `bounded_irreducible_balanced`: marker theorem; all layered
  hypotheses `_unused`; returns `hEnum`.
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1681-1694` —
  `bounded_irreducible_balanced_hybrid`: marker theorem; dispatch on
  `Decidable InCase3Scope`.
* `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean:97-222` —
  `bounded_irreducible_balanced_inScope`: **the one structurally
  non-trivial consumer**; uses L1a / L2-upward / band-major encoding /
  certificate composition.
* `lean/OneThird/Step8/LayerOrdinal.lean:370-404` — F3 strong
  induction; takes `L` as marker, recursion on `Fintype.card α`.
* `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:256-547` —
  `Case3Witness_proof`: K = 1 contradiction + K = 2 chain force /
  closure + K ≥ 3 compactify descent + hybrid dispatch at irreducible
  leaves.
* `lean/OneThird/Step8/OptionC/K2Closure.lean:1-100` (docstring) —
  notes that at K = 2 with w ≥ 1, `L2-forced` is vacuous; certificate
  at w = 1 covers every K = 2 dispatch.
* `lean/OneThird/Step8/Case3Residual.lean:208-217` —
  `case3Witness_hasBalancedPair_outOfScope` (the operational axiom,
  Option D-narrow target).
* `lean/OneThird/Step8/MainAssembly.lean:165-204` — `trivialLayered`
  (same shape as `canonicalLayered`, used as `caseR_to_caseC` discard).
* `lean/OneThird/Step8/MainAssembly.lean:238-247` —
  `mainTheoremInputsOf`: routes through `layeredFromBridges` (which is
  discarded again at `lem_layered_balanced`'s K ≥ 2 branch).
* `lean/OneThird/Step8/LayeredBridges.lean:181-261` —
  `layeredFromBridges`: extracts `Lwidth3 : Step7.LayeredWidth3` and
  builds `LayeredDecomposition α` with `w := Lwidth3.bandwidth`.
* `lean/OneThird/Step8/ChainPotentials.lean` — chain potentials
  extractor; currently delivers `bandwidth = |α| + 1`, not `w₀(γ)`.
* `lean/OneThird/Step7/Assembly.lean:302-310` — `LayeredWidth3`
  (paper's Prop. 7.2 output).
* `lean/OneThird/Step7/Assembly.lean:329-348` — `prop_72`
  (paper-axiomatised Steps 1-7 bridge to layered form).
* `docs/why-hC3-is-structural.md` — F1/F2/F3 obstructions, option-(δ)
  park.
* `docs/onethird-Case3Witness-architecture-analysis.md` (mg-e2e9) —
  cap-5 proposal; pre-cap-5 vacuity.
* `docs/state-Case3Witness-cap5-fix.md` (mg-d5a0) — cap-5 landing,
  structured `sorry` placement at `LayeredBalanced.lean:751`.
* `docs/onethird-Case3Witness-post-cap-5-tractability-analysis.md`
  (mg-0cbf) — D2-tractable verdict, 15 cap-1 cells.
* `docs/state-Case3Witness-cap5-enumeration.md` (mg-4d7b) — K = 2..9
  enumeration verified; K = 10 w = 4 in flight.
* `docs/compatibility-geometry-F31-phi-star-injectivity.md` —
  RED-chain-locality, F-series cohomological re-emergence walled.
* `main.tex` §1.4 — paper road map (Steps 1-7 = coherence collapse;
  Step 8 = layered form discharge).
* `step7.tex` — coherence implies collapse; Prop. 7.2 = bounded-`w`
  layered output.

---

## §6. Summary

* **Phase A**: layered-form is functionally vacuous at the
  operational headline (canonicalLayered substitution discards input
  L; cap 5 unsatisfiable for `|α| ≥ 5`).  Real structural use survives
  only at the F5a Bool certificate's predMaskOf upper-triangular
  encoding (mg-53ce / L2-upward), which is operationally equivalent
  to "α admits a Szpilrajn extension" — automatic for every finite
  poset.  Per-lemma table in §1a confirms the pattern: marker
  theorems (`bounded_irreducible_balanced`, `_hybrid`, F3 induction)
  consume only numerics; degenerate-case lemmas (K = 1 antichain, K =
  2 bipartite) are equivalent to direct poset-shape hypotheses;
  certificate-leaf lemmas use L2-upward as an encoding bridge.

* **Phase B**: clean restatement is feasible.  Drop the
  `Case3Witness.{u}` universal at the headline; expose mg-4d7b's
  enumeration as the `|α| ≤ 10` discharge; remove unused layered
  infrastructure (lem_cut / windowLocalization / canonicalLayered /
  marker theorems).  Scope: 3-5 polecat sessions, no new project
  axioms, drops one project axiom.

* **Phase C**: no fresh coherence attack to revive.  The paper's
  coherence content (Steps 3-7) is intact and Lean-axiomatised at
  `Step7.LayeredWidth3`; faithful Lean delivery of Steps 1-7 is
  multi-month Option-A work.  The F-series cohomological re-emergence
  has walled at F31 RED-chain-locality.  The correlation-inequality
  alternate route is out of polecat scope.  "Stick with coherence"
  operationally means "accept the option-(δ) park and queue Option A
  for its own merits".

* **Phase D**: top-line verdict is
  **layered-form-vacuous-at-headline-with-DO-pivot-to-honest-restatement-not-to-coherence-implementation**.
  Recommended forward plan: finish mg-4d7b, file Option D-narrow
  follow-on (drops one axiom), restate the headline as
  smallN-unconditional + largeN-conditional-on-Steps-1-7.  mg-0cbf
  and mg-4d7b remain load-bearing (their content is the architectural
  basis for the restatement); the cap-5 `sorry` (mg-d5a0) is excised
  rather than closed (the K ≥ 2 dispatch leaves the headline path
  under the restatement).

Daniel's diagnostic question — "does this reduction to layered form
actually buy us anything?" — is answered: **no, not at the headline,
and the architectural debt has been silently absorbed for the entire
history of the layered-form Lean implementation**.  The deeper
question — "is poset structure even the right tool here?" — is
answered: **the paper's tool is coherence (Steps 1-7), which
*produces* the layered form as a downstream output; the layered form
is not an independent tool, it is the data type the coherence
argument's conclusion lives in.  The right Lean delivery of the
paper's argument requires both pieces.  Currently neither is
delivered honestly — coherence is paper-axiomatised, layered form is
canonicalLayered-bypassed.  The honest path forward is to expose this
state explicitly via the recommended restatement**.

**Verdict: GREEN-Phase-A-D-delivered + recommendation =
restate-then-conditionally-pursue-Steps-1-7-faithful-Lean-delivery.**
