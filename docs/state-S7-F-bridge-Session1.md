# S7-F-bridge — Session 1 audit + RED 7th vacuity discovery (mg-5fbd)

**Ticket:** mg-5fbd (OneThird-S7-F-lem-layered-from-step7-bridge,
sixth and final S7 pilot sub-ticket).
**Predecessor:** mg-516f (S7-E, GREEN, commit 15a5308 —
`lem_bandwidth_le_four_bundled` shipped).
**Verdict:** **RED — 7th vacuity discovery on the bridge call-site
architecture.** Escalation to pm-onethird required; the
`MainAssembly.lean:265` sorry **cannot be closed honestly** by a
bridge of the shape S7-F's spec calls for, irrespective of how
much Lean bandwidth is poured at the construction.

This session produced **no Lean changes**. The deliverable is this
audit document plus an updated entry in `PROOF-STRUCTURE-ONBOARDING.md`
(maintenance contract §5: "Discharges Steps 1–7's `w₀(γ)`
faithfully"). The mg-6ab8 Phase D Checkpoint 3 hold-the-line audit,
mandatory per §4.3, fires here.

---

## §1. mg-6ab8 Phase D Checkpoint 3 audit

The mandatory hold-the-line question per the scoping doc §4.3:

> Does the `prop:72` output actually deliver `LayeredDecomposition α`
> with `L.w ≤ 4`, or does it deliver a packaging-with-bandwidth-field?
> If the latter, the S7-F bridge is the heart of the work and the
> budget multiplier on S7-F is higher (~2M alone). This is the
> highest-risk checkpoint.

**Audit answer:** `prop:72` (in both abstract `Assembly.lean`
form and S7-E grounded `Prop71_Prop72_LemBandwidth.lean` form)
delivers a **`Step7.LayeredWidth3 richPairs` packaging on a
`Pair` space**, **not** a `LayeredDecomposition α` on the ground
set α.

Concretely, `lem_bandwidth_le_four_bundled` (the S7-E
load-bearing deliverable, mg-516f) has signature:

```lean
theorem lem_bandwidth_le_four_bundled
    (src tgt : Edge → Vertex) (signedWeight : Edge → ℤ)
    (edgeWeight : Edge → ℕ) (path : Vertex → List Edge)
    (psrc ptgt : Pair → Vertex) (posMass : Pair → ℕ)
    (pairs richPairs : Finset Pair) (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs) (hBud : …) (hRich : …) :
    ∃ (L : LayeredWidth3 richPairs),
      L.bandwidth ≤ 4 ∧ … ∧ … :=
```

`Step7.LayeredWidth3 richPairs` has fields `bandwidth : ℕ`,
`richPairsIn : Finset Pair`, `richPairsOut : Finset Pair`,
`partition`, `disjoint`. It is **not** a `Step8.LayeredDecomposition α`
(which has fields `K, w, band : α → ℕ, band_pos, band_le,
band_size, band_antichain, forced_lt, cross_band_lt_upward`).

The two structures are **disjoint in type**: the former lives on
an abstract `Pair` space and bundles a partition of a richPairs
finset; the latter lives on `α` and bundles an indexed antichain
partition of the ground set. Translating between them requires
the paper's `lem:layered-from-step7` (`step8.tex:1913-2106`) —
ground-set lift via Dilworth chains, potential, synchronization
maps, and the exceptional set `X^exc`.

**Checkpoint 3 verdict:** The S7-F bridge construction is
substantial (gap is real), matching scoping doc §4.3's "highest-risk
checkpoint" worst-case. This alone is **AMBER**, not RED — sub-split
contingency was pre-authorised in the ticket body and the bridge
construction would be a multi-polecat sub-arc per the proper §7.1
spec budget (~600M-1M / 2-4 sessions).

---

## §2. Beyond Checkpoint 3 — the structural pitfall

The unexpected finding (not anticipated by mg-6ab8 §4.3) is a
**call-site architectural issue** that makes the S7-F bridge's
intended consumer (`MainAssembly.lean:265`'s `caseC_canonicalLayered`)
**not honestly closable by any bridge of the spec'd shape**,
irrespective of how much Lean construction work goes into the
bridge itself. This is the **7th vacuity discovery** in the
cumulative pattern (after mg-e2e9, mg-74d2, mg-5c32, mg-82fc,
mg-2970, mg-ac13).

### §2.1. The closure target

```lean
-- MainAssembly.lean:236
noncomputable def caseC_canonicalLayered.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (h2 : 2 ≤ Fintype.card α)
    (hNotChain : ¬ OneThird.IsChainPoset α)
    (hW3 : HasWidthAtMost α 3)
    (hC3 : Step8.Case3Witness.{u}) : HasBalancedPair α := by
  let L : LayeredDecomposition α := canonicalLayered α
  have hInj : Function.Injective L.band := …      -- ✓
  have hKw : L.K ≤ 2 * L.w + 2 := …               -- ✓
  have hCardw : Fintype.card α ≤ 6 * L.w + 6 := …  -- ✓
  have hNonempty : … := …                         -- ✓
  have hLw : L.w ≤ 4 := by sorry                  -- ✗ THE SORRY
  exact lem_layered_balanced L h2 hNotChain hW3 hInj hKw hCardw
    hNonempty hLw hC3
```

The five caps are needed to apply `lem_layered_balanced`. With
`L := canonicalLayered α` (singleton bands via Szpilrajn,
`K = w = |α|`), caps 1–4 hold trivially; cap 5 (`L.w = |α| ≤ 4`)
holds **only for `|α| ≤ 4`** and fails as soon as `|α| ≥ 5`.

To close the sorry honestly, the goal must become "replace `L`
with a *different* layered decomposition for which all five caps
hold including `L'.w ≤ 4`". That is the S7-F bridge's intended
output.

### §2.2. The five-cap unsatisfiability proof

The five caps together force, for *any* layered decomposition `L`
on `α`:

* cap 1 (`Function.Injective L.band`) + cap 4 (nonempty bands
  on `[1, L.K]`) ⇒ each band has exactly one element ⇒
  `L.K = Fintype.card α`.
* cap 2 (`L.K ≤ 2 * L.w + 2`) + cap 5 (`L.w ≤ 4`) ⇒
  `L.K ≤ 2 · 4 + 2 = 10`.
* combined ⇒ `Fintype.card α = L.K ≤ 10`.

So the five caps are **structurally unsatisfiable** for `|α| ≥ 11`,
**irrespective of how `L` is constructed**. Mirror of
`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2.1 — but applied at
the `caseC_canonicalLayered` integration point rather than at the
original mg-5c32 residual-extraction site.

### §2.3. Even within `|α| ≤ 10`, the caps are not always satisfiable

Take `α = 3 disjoint chains of length 3` (`|α| = 9`, width 3,
non-chain — the canonical structural witness analogue of
PROOF-STRUCTURE-ONBOARDING §3 pitfall #2.3's 3-disjoint-chains-of-10):

* `A = (a_1 < a_2 < a_3)`, `B = (b_1 < b_2 < b_3)`,
  `C = (c_1 < c_2 < c_3)`, all cross-chain pairs incomparable.

Try to find `L` with all five caps:

* cap 1 forces singleton bands ⇒ `L.K = 9`.
* cap 2 + cap 5 force `L.K ≤ 10` (OK, 9 ≤ 10) but `L.w ≥ ⌈(L.K − 2)/2⌉ = 4`
  is forced just by cap 2 — so `L.w ∈ {4}` exactly under cap 5.
* (L2-forced) `band x + L.w < band y ⇒ x < y`:
  with singleton bands `1, …, 9` in some order, pairs at band-distance
  `≥ L.w + 1 = 5` must satisfy `x <_P y`. There are
  `4 + 3 + 2 + 1 = 10` such pairs at distance ≥ 5. But `P` has
  only `3 × 3 = 9` comparable pairs total (all within-chain).
  So **at least one forced pair is cross-chain** — but cross-chain
  pairs are incomparable in `P` — contradiction.

So `α = 3 disjoint chains of 3` is a **width-3 non-chain finite
poset with `2 ≤ |α| ≤ 10` for which no `L : LayeredDecomposition α`
satisfies all five `Case3Witness` caps**, *not even with* `|α| ≤ 10`.

(Notice: α *does* have a balanced pair, e.g. `(a_1, b_1)` are
symmetric under `Equiv.swap` so `Pr[a_1 < b_1] = 1/2`. The
existence of the balanced pair is not in question; what fails is
the *route* `caseC_canonicalLayered` tries to use to construct
the discharge.)

### §2.4. Consequence: the closure target is not the right target

The `caseC_canonicalLayered` shape attempts to discharge
`HasBalancedPair α` for **every** width-3 non-chain `α` with
`|α| ≥ 2` by:

1. Building an `L : LayeredDecomposition α` with all five caps.
2. Applying `lem_layered_balanced`.

By §2.2 + §2.3, **no construction of L** can satisfy all five
caps for arbitrary width-3 non-chain α — neither at `|α| ≥ 11`
(where caps 1+2+5 force `|α| ≤ 10`, contradiction) nor for
specific `|α| ≤ 10` configurations like `3 disjoint chains of 3`
(where forced cross-chain comparability under (L2) contradicts
P's structure).

**Therefore the S7-F bridge cannot honestly close the sorry by
producing a "better L" alone.** The closure target itself is
ill-posed.

---

## §3. What the paper actually says

The paper's `lem:layered-from-step7` (`step8.tex:2009-2089`) does
**not** claim "for every width-3 non-chain `α` with `|α| ≥ 2`,
there exists `L : LayeredDecomposition α` with `L.w ≤ 4`". It
claims (paraphrased, see `step8.tex:2009-2027`):

> Let `P = (X, ≤_P)` be a width-3 poset **with Dilworth
> decomposition X = A ⊔ B ⊔ C into three chains**. Assume *either*
> (a) Step 5(C) collapse conclusion holds, *or* (b) Step 7(ii)
> globalization conclusion holds, with bandwidth constant
> `K_bw = K(T) = O_T(1)`. Then `P|_{X∖X^exc}` admits an exact
> layered decomposition with interaction width
> `w = K_bw + 2 = O_T(1)`.

Three things the paper assumes that the call site doesn't supply:

1. **Dilworth decomposition of α into 3 chains** (paper input;
   not derivable in the current call-site signature). Mathlib
   does have a Dilworth theorem but the *concrete* `A, B, C`
   chain data is not in tree on the call-site path.
2. **Step 5(C) collapse data or Step 7(ii) globalization data**
   (paper input; these are *cascade outputs*, not free hypotheses
   on arbitrary width-3 non-chain α). Their existence is gated on
   `α` being a **minimal γ-counterexample** in the (R)+(coherent)
   regime — paper's proof-by-contradiction setup.
3. **The conclusion is on `P|_{X∖X^exc}`, not on `P`** —
   `|X^exc| = O_T(1)` exceptional elements are removed, and the
   resulting layered decomposition lives on the sub-poset.
   Transferring `HasBalancedPair (X∖X^exc)` back to
   `HasBalancedPair X` uses the perturbation bound
   (`step8.tex:2080-2088`, F6b `exc_perturb`).

So even at the paper level, the bridge is *partial*: it applies to
α satisfying the Steps 1-7 cascade hypotheses, **not** to all
width-3 non-chain α. The 3-disjoint-chains-of-3 counterexample
above is NOT in the bridge's domain (it has a balanced pair by
symmetry, so it's not a γ-counterexample).

**The paper handles the disjoint-chains case implicitly via the
proof-by-contradiction setup: such α already has a balanced pair,
so it's never a γ-counterexample, so the bridge is never invoked
on it.**

---

## §4. Why current Lean architecture cannot host the paper bridge

The Lean architecture in `MainAssembly.lean` is **direct
construction**, not proof-by-contradiction:

```lean
-- MainAssembly.lean:353
theorem width3_one_third_two_thirds_assembled.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hC3 : Step8.Case3Witness.{u}) :
    HasBalancedPair α := by
  by_cases hcard : Fintype.card α ≤ 1
  · …  -- chain contradiction
  have h2 : 2 ≤ Fintype.card α := by omega
  exact mainAssembly 1 3 h2 hP hNonChain
    (mainTheoremInputsOf 1 3 h2 hNonChain hP hC3)
```

`mainTheoremInputsOf` packages `caseC_canonicalLayered h2 hNotChain
hW3 hC3` as `caseC`. `mainAssembly` then collapses both Step 5
branches to `I.caseC`. The entire control flow is "build the
balanced pair directly from `(α, hP, hNonChain, hC3)`".

There is **no contradiction hypothesis** in scope at the call
site. There is **no Dilworth chain data, no chain potential,
no Steps 1-7 cascade output**. These cannot be invented; the paper
bridge fundamentally requires them.

To host the paper bridge faithfully, the Lean architecture would
need to be refactored as follows:

1. `width3_one_third_two_thirds_assembled` becomes a proof by
   classical contradiction: `by_contra hNoBP; …; exact absurd …`.
2. The contradiction hypothesis `hNoBP : ¬ HasBalancedPair α`
   is threaded through `mainAssembly` and through to the case
   dispatch.
3. The Step 5 dichotomy becomes a real dichotomy (not a Bool
   collapse) — case (R) and case (C) genuinely differ, and the
   case (R) branch derives the Steps 1-7 cascade.
4. From the cascade outputs (Steps 5(C) or Step 7(ii) inputs),
   apply the S7-F bridge to derive an `L : LayeredDecomposition
   (X ∖ X^exc)` with `L.w ≤ 4`, lift `HasBalancedPair (X ∖ X^exc)`
   back to `HasBalancedPair X` via `exc_perturb`, contradict
   `hNoBP`.

This is a **substantial architectural refactor of `MainAssembly.lean`**
that touches: `mainAssembly` (dispatch), `mainTheoremInputsOf`
(input bundle), `caseC_canonicalLayered` (entire helper),
`width3_one_third_two_thirds_assembled` (top-level). It is **out
of scope for any single S7-F polecat session**, and the work also
requires the Lean port of the **upstream Steps 1-6 cascade**
(currently paper-axiomatised at parametric scaffolding interfaces)
to provide the concrete cascade-output hypotheses the bridge
needs as inputs.

---

## §5. What S7-A through S7-E actually achieved

The S7-A through S7-E sub-tickets (mg-4584, mg-9331, mg-1069,
mg-d135, mg-516f) are not negated by this finding. They produced
**grounded forms** of paper Steps 7's individual lemmas:

* `signed_threshold_grounded` (S7-A) — wired to Step 2 staircase.
* `triple_visibility_grounded` (S7-B) — wired to Step 5 second-moment.
* `cocycle_grounded` / `potential_grounded` (S7-C) — concrete
  BFS-tree potential via `bfsSumPot`.
* `lem_giant_component_grounded` (S7-D) — bipartite-richness +
  diameter-3 walk witness.
* `lem_bandwidth_le_four_bundled` (S7-E) — `LayeredWidth3 richPairs`
  packaging with `L.bandwidth = 4` from upstream Step 5 var-budget +
  richness hypotheses.

Each of these is a *real* Lean theorem with parametric upstream
hypotheses. They build a credible Step 7 *internal* scaffolding.
What S7-A–E **do not do** (and were never going to do per the
mg-6ab8 §7.1 spec) is produce a *call-site-consumable*
`LayeredDecomposition α` with `L.w ≤ 4`. That output requires the
**ground-set lift** + the **proof-by-contradiction architectural
setup**, neither of which is in the S7-F sub-arc as scoped.

The S7-E `lem_bandwidth_le_four_bundled` is honest scaffolding
for a *future* bridge that would invoke it; but invoking it
requires concrete `Edge`/`Vertex`/`Pair`/`src`/`tgt`/`path`/
`signedWeight`/`edgeWeight`/`posMass` data on the BK-graph of `α`,
and concrete `b_n, b_d, c_n, c_d, M₀` constants + concrete
var-budget / richness witnesses — all of which are Step 1-6
cascade outputs, none of which are in tree.

---

## §6. Verdict and recommendations

**Verdict:** RED — 7th vacuity discovery on the *call-site
architecture*, not on the bridge construction per se. The cap-5
sorry at `MainAssembly.lean:265` **cannot be closed honestly** by
any bridge of the shape scoped in mg-6ab8 §7.1; the architectural
refactor required is well beyond a polecat-session scope and also
requires upstream Steps 1-6 grounded ports (paper-axiomatised
in tree).

### §6.1. Three forward options for Daniel

Adapting mg-6ab8 §6's three options to the post-S7-pilot state:

**Option (C'): RED-STAY-PUT (status-quo, recommended default).**
Retain the `MainAssembly.lean:265` sorry as a documented
architectural-debt marker. Document the situation honestly in
`AXIOMS.md` (analog of `case3Witness_hasBalancedPair_outOfScope`
entry) and in the Zulip post:

> The headline `width3_one_third_two_thirds` carries one
> structured `sorry` at `MainAssembly.lean:265`
> (`caseC_canonicalLayered`), which represents the call-site of
> paper's `lem:layered-from-step7` (`step8.tex:1913-2106`) ground-
> set lift bridge. Closing this sorry honestly requires (i) the
> bridge construction itself (multi-polecat), (ii) ground porting
> of Steps 1-6 cascade outputs (multi-month), and (iii) an
> architectural refactor of `MainAssembly.lean` to proof-by-
> contradiction (the paper's argument shape). The paper proof is
> unconditional on the BK-expansion cascade (modulo Hypothesis A);
> the gap is Lean-side engineering, not paper-side math.

Cost: 0 polecat work. Honest disclosure restores ground truth.

**Option (B'): NARROW-LOCALLY-CLOSE (intermediate).**
Decouple the S7-F bridge from the architectural refactor:

1. **Add a smallN branch** to `width3_one_third_two_thirds_assembled`
   for `|α| ≤ N₀` (some explicit threshold ≤ 10) routing
   through `lem_small_n` or direct `bipartite_balanced_enum`.
2. **Refactor `caseC_canonicalLayered` to take an explicit `L`
   parameter** (replace `let L := canonicalLayered α` with a
   parameter `L : LayeredDecomposition α` plus the five caps as
   hypotheses). This relocates the cap-5 gap one level up.
3. **Build an axiomatic stub** `Step7.layeredFromStep7 :
   ∀ (α width-3 non-chain |α| ≥ N₀ minimal-γ-counterexample),
   ∃ L : LayeredDecomposition α, all-five-caps` — declare as
   project axiom in `AXIOMS.md` with full disclosure.

This *closes the sorry* (via the new axiom) but doesn't actually
discharge it via Lean math. The honest framing is "we lifted the
gap from a `sorry` to a named project axiom of the same shape",
which is arguably an improvement in trust surface (the axiom is
discoverable via `#print axioms` whereas the `sorry` is not). Per
mg-ac13 §5.3 Daniel "shouldn't even go there yet", but if a
clean `#print axioms` output is the gate, this option achieves
it.

Cost: ~250-400k polecat tokens, 1-2 sessions. Risk: Daniel
correctly identifies this as moving the deck chairs without
sinking the ship.

**Option (A'): FULL REFACTOR (out of scope but enumerated).**
The honest-close path:

1. Port Steps 1-6 grounded forms (~5 sub-arcs each, mg-6ab8
   Option A worst case 6-9M tokens / 4-6 months calendar).
2. Build the S7-F bridge as the genuine ground-set lift
   per `step8.tex:1913-2106` (~600k-1M tokens / 2-4 sessions).
3. Refactor `MainAssembly.lean` to proof-by-contradiction with
   the cascade chain threaded through (~500k-1M tokens / 2-4
   sessions).

Total cost: 7M-12M tokens / 5-7 months calendar. Out of any
single polecat scope. Per mg-6ab8 §6.2.

### §6.2. Recommendation

**Option (C'): RED-STAY-PUT.** Per mg-6ab8 §6.3 Status-quo
rationale + the strengthened mg-ac13 §5.3 Daniel "shouldn't even
go there yet" stance + this Session 1's confirmation that the
gap is architectural (not just construction).

The S7-A–E pilot remains a valid landed contribution: the Step 7
internal scaffolding is now grounded, and the paper's Step 7 is
the most-confidence-improved part of the cascade. The remaining
gap is correctly localised at the architectural call-site —
not hidden inside an inscrutable `canonicalLayered α` shortcut.

---

## §7. Forward-action mail to Daniel (drafted)

Polecat self-mails mayor with verdict; mayor forwards to Daniel
per the post-GREEN protocol (here adapted for RED). Draft body:

```
Subject: mg-5fbd S7-F bridge — RED 7th vacuity discovery
From: mg-5fbd

Verdict: RED.

Phase D Checkpoint 3 audit (per mg-6ab8 §4.3) found the expected
gap: prop:72's output is LayeredWidth3 richPairs (Pair-space
bundle), not LayeredDecomposition α — substantial bridge
construction work, sub-split contingency was authorized.

UNEXPECTED beyond Checkpoint 3: the bridge's intended consumer
(MainAssembly.lean:265 caseC_canonicalLayered) cannot be honestly
closed by ANY bridge of the spec'd shape. Concretely:

1. Case3Witness's five caps force |α| ≤ 10 (caps 1+4+2+5
   structurally; mirror of PROOF-STRUCTURE-ONBOARDING.md pitfall
   #2.1 at the integration-point site).
2. Even within |α| ≤ 10, no L satisfies all 5 caps for α = 3
   disjoint chains of length 3 (|α|=9, width 3, non-chain) —
   forced cross-chain comparability under (L2) contradicts P's
   structure with singleton bands at L.w = 4.
3. Paper's lem:layered-from-step7 doesn't claim coverage of
   arbitrary width-3 non-chain α — it requires Steps 1-7 cascade
   inputs, which only hold for minimal γ-counterexamples (the
   proof-by-contradiction setup not present at the call site).

Resolution requires architectural refactor of MainAssembly.lean
to proof-by-contradiction + Lean port of Steps 1-6 cascade
(months of work). Three forward options enumerated in
docs/state-S7-F-bridge-Session1.md §6.

Recommendation: Option (C') RED-STAY-PUT — retain the
MainAssembly.lean:265 sorry as documented architectural-debt
marker, file AXIOMS.md disclosure analog of
case3Witness_hasBalancedPair_outOfScope. The S7-A-E pilot
remains a valid landed contribution (Step 7 internal scaffolding
is grounded); the closure of the sorry requires multi-month
upstream work that is unchanged in scope by this session's
findings.

Status of the S7-pilot arc: CLOSED with documented architectural
gap. Six sub-tickets executed; mg-5fbd surfaces the call-site
limitation honestly rather than declaring closure prematurely.
```

---

## §8. Maintenance contract notes

Per `PROOF-STRUCTURE-ONBOARDING.md` §5, the following maintenance
actions are warranted in the same patch as this doc:

* Add **Pitfall #5** to `PROOF-STRUCTURE-ONBOARDING.md` §3
  documenting the cap-5 unsatisfiability at the
  `caseC_canonicalLayered` integration point + the 3-disjoint-
  chains-of-3 counterexample for `|α| ≤ 10`.
* Update §1 onboarding TL;DR to reflect that S7-F closure was
  found to require an architectural refactor beyond bridge
  construction.
* No `AXIOMS.md` changes (no axioms added or removed in this
  session); however, if Option (C') is adopted, a future ticket
  may add an analog disclosure for the documented `MainAssembly.lean:265`
  sorry.
* Cross-reference list: this doc is added to the predecessor
  audits / state docs index.

---

## §9. Cross-references

* `lean/OneThird/Step8/MainAssembly.lean:236-267` —
  `caseC_canonicalLayered` (the unfixable call site).
* `lean/OneThird/Step8/LayeredBalanced.lean:461-472` —
  `Case3Witness.{u}` definition (the 5-cap unsatisfiability
  source).
* `lean/OneThird/Step8/LayeredBalanced.lean:498-535` —
  `canonicalLayered α` (the current K=w=|α| placeholder).
* `lean/OneThird/Step7/Prop71_Prop72_LemBandwidth.lean:380-414` —
  S7-E's `lem_bandwidth_le_four_bundled` (the load-bearing
  S7-E deliverable, structurally typed on `Pair` not `α`).
* `paper/step8.tex:1983-2089` — `def:layered` +
  `lem:layered-from-step7` definitions.
* `paper/step8.tex:2009-2027` — `lem:layered-from-step7`
  input hypotheses (the cascade-output gating).
* `docs/PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2 + #3 —
  related historical vacuity-discoveries.
* `docs/OneThird-Steps-1-7-Lean-port-scoping.md` §4.3
  Checkpoint 3 + §6.1-3 three forward options + §8 risk
  watchlist row 4.
* `docs/coherence-collapse-case-extraction.md` (mg-ac13) —
  the 3-disjoint-chains-of-10 counterexample that the
  3-disjoint-chains-of-3 of §2.3 specialises.
* Predecessor S7 state docs: `state-S7-A-G1-G2-Session1.md`
  (mg-4584), `state-S7-B-G3-Session1.md` (mg-9331),
  `state-S7-C-G4-G5-Session1.md` (mg-1069),
  `state-S7-D-G6-G9-Session1.md` (mg-d135),
  `state-S7-E-prop71-prop72-Session1.md` (mg-516f).
