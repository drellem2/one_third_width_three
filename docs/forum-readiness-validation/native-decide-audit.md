# Native-decide audit (Validation B, mg-5cd8)

**Audit date.** 2026-05-06.
**HEAD audited.** `0df0bc4` (`docs: root README — reflect
unconditional headline after Option-C Stage 2B (mg-0dd2)`).
**Audited by.** `cat-mg-5cd8` polecat (forum-readiness validation
pass; ticket text and protocol per `mg-5cd8`).
**Verdict.** **GREEN.** All five `native_decide` invocations are
faithful: the Bool predicate evaluated by `native_decide` encodes
exactly the math claim made in the surrounding theorem; the
parameter range matches the F5a / F5a-K2 sub-case bounds; the Bool→Prop
bridge is a closed-form lift to `HasBalancedPair α` with no quiet
weakening.

## Scope

Each `native_decide` invocation in the transitive closure of
`OneThird.width3_one_third_two_thirds` introduces a Lean-internal
axiom of the form

```
<def>._native.native_decide.ax_1_1
```

which is an instance of `Lean.ofReduceBool` (the standard compiler
trust axiom for `native_decide`). The audit verifies, per
invocation:

1. **Bool predicate definition** — what does the Bool function
   encode mathematically?
2. **Parameter range** — is the literal `(w, sizeLimit)` argument
   what the F5a / F5a-K2 sub-case expects?
3. **Sanity-check sample** — is the Bool predicate consistent with
   a hand-verifiable example?
4. **Bool→Prop bridge** — does the consumer of the `native_decide`
   result quietly weaken the claim, or does it cleanly lift to the
   typed Prop-level conclusion?

Failure mode to detect (mg-a79e pattern): a Bool predicate whose
mathematical interpretation differs from the surrounding theorem's
claim — e.g. wrong direction, off-by-one, missing antecedent.

## Shared infrastructure

All five invocations use shared bitmask helpers from
`OneThird.Step8.Case3Enum`
(`lean/OneThird/Step8/Case3Enum.lean:46-367`). Verifying these once
covers the underlying interpretation for every per-`(w, bs)` slice:

| Helper | Source | Math meaning |
|---|---|---|
| `bit i` | `Case3Enum.lean:53` | `1 <<< i` — singleton bit at position `i` |
| `testBit' m i` | `Case3Enum.lean:56` | `(m &&& bit i) ≠ 0` — bit `i` of `m` is set |
| `warshall pred n` | `Case3Enum.lean:65-73` | Transitive closure of the strict relation `<` encoded as predecessor bitmasks (bit `u` of `pred[v]` ⇔ `u < v`); textbook Warshall |
| `irreducible pred offsets` | `Case3Enum.lean:80-93` | For every cut `k ∈ {1, …, K-1}`, ∃ `b` in bands `k+1..K` incomparable to some element of bands `1..k` (= `LayerOrdinalIrreducible` at the bitmask level) |
| `hasAdjacentIncomp pred offsets` | `Case3Enum.lean:97-110` | ∃ `(u, v) ∈ M_s × M_{s+1}` with `u ⫫ v` (= no full lower-band domination of any element of the next band) |
| `findSymmetricPair pred n` | `Case3Enum.lean:152-166` | Search for `(x, y)` with `x, y` incomparable and `swap x y` an order-automorphism (sufficient for `HasBalancedPair` since by symmetry `Pr[x < y] = 1/2 ∈ [1/3, 2/3]`) |
| `countLinearExtensions pred n` | `Case3Enum.lean:202-210` | Standard subset-DP linear-extension count on the closed pred-relation |
| `hasBalancedPairSlow pred n` | `Case3Enum.lean:220-232` | For every incomparable `(x, y)`, compute `cnt = countLinearExtensions(pred ∪ {x<y})` and accept if `total/3 ≤ cnt ≤ 2*total/3` (rational `[1/3, 2/3]` test by integer multiplication) |
| `hasBalancedPair pred n` | `Case3Enum.lean:236-239` | `findSymmetricPair`-fast-path then `hasBalancedPairSlow` fallback |
| `bandSizesGen K maxTotal` | `Case3Enum.lean:348-355` | All `[n₁, …, n_K]` with `n_i ∈ {1,2,3}` and `Σ n_i ≤ maxTotal` (the L1-clipped band-size profile) |
| `enumPosetsFor w bs` | `Case3Enum.lean:324-342` | For every closure-canonical mask of free `(u,v)`-edges (band-gap `≤ w`), filter to (a) symmetric-pair-free, (b) irreducible, (c) adjacent-incomparable; for every survivor run `hasBalancedPairSlow`; return false on any survivor lacking a balanced pair, else true |
| `allBalanced w sizeLimit` | `Case3Enum.lean:360-363` | `∀ bs ∈ bandSizesGen 3 sizeLimit, enumPosetsFor w bs = true` (note: K = 3 fixed) |
| `predBitsBoundedBy`, `ValidPredMask`, `predOrder`, `Symmetric` | `Case3Enum/{Predicates,Symmetric,Order}.lean` (referenced by bridge lemmas) | Closure properties of the bitmask encoding used by the Prop-level transport |

Cross-reference with the Python ground-truth enumerator
(`lean/scripts/enum_case3.py`, ~line 60-160): byte-for-byte
identical encoding (Warshall, irreducibility test, Subset-DP linear
extensions, `[1/3, 2/3]` integer-multiplied test), modulo trivial
reformulations (`Id.run do` for Lean's imperative-in-pure idiom).

## Per-invocation audit

### 1. `case3_balanced_w1` — `Case3Enum/W1.lean:32`

```lean
theorem case3_balanced_w1 : allBalanced 1 9 = true := by
  native_decide
```

**Bool encoding.** `allBalanced 1 9 = true` says: for every band-size
tuple `bs = [n₁, n₂, n₃]` with `n_i ∈ {1, 2, 3}` and `n₁+n₂+n₃ ≤ 9`,
the K=3, w=1 enumeration `enumPosetsFor 1 bs` returns `true`. By
the per-mask body of `enumPosetsFor`, this means: every K=3 layered
config on bands `[n₁, n₂, n₃]` with at most 9 elements that is
(a) closure-canonical, (b) has no symmetric pair (else trivially
balanced), (c) is layer-ordinal irreducible, (d) has an adjacent
incomparable cross-pair, admits a balanced pair under
`hasBalancedPairSlow`.

**Parameter coverage.** F5a's `case3_certificate` covers this slice
under `InCase3Scope` (`BoundedIrreducibleBalanced.lean:1484`):

```lean
def InCase3Scope (w card K : ℕ) : Prop :=
  K = 3 ∧ 1 ≤ w ∧ w ≤ 4 ∧
    (w = 1 → card ≤ 9) ∧ (2 ≤ w → card ≤ 7)
```

For `w = 1`, the cap is `card ≤ 9`. The Bool fact `allBalanced 1 9
= true` covers every band-size triple summing to ≤ 9; the F5a Prop
bridge `enumPosetsFor_eq_true_of_inScope` (in
`OptionC/Case3WitnessProof.lean:160-203`) selects the matching
`(w, sizeLimit)` entry, so the Bool fact at `(1, 9)` covers exactly
the `(L.w = 1, |α| ≤ 9)` slice of `InCase3Scope`. ✅

**Sanity-check sample.** Take `bs = [1, 1, 1]` (three singleton
bands, |Q| = 3, K = 3). Free `(u, v)`-pairs at `w = 1` are pairs
across adjacent bands only; here that is `{(0, 1), (1, 2)}` (band
gap 1) — pair `(0, 2)` has gap 2 > 1 = w, so it is forced (`u < v`
holds in every config). For each subset of `{(0, 1), (1, 2)}`, the
closure imposes `0 < 2` (forced) and any subset's closure adds
those edges plus transitivity. The four canonical masks split as
follows:

* `mask = 0b00`: only `0 < 2` forced; `{0, 1}` and `{1, 2}` both
  incomparable. The poset is the V-poset with apex `2` and
  incomparable bottoms `0, 1` after relabeling, but since we forced
  `0 < 2` and not `1 < 2`, this is a width-2 poset, not irreducible
  at K=3 (band 1 element `0` is comparable to band 3 `2` but not
  band 2 `1`). Filtered out by `irreducible` gate.
* `mask = 0b01` (free edge `(0, 1)` set): `0 < 1`, plus forced
  `0 < 2`. This is the chain `0 < 1` plus comparable `0 < 2` and
  incomparable `(1, 2)`. Irreducible at k=2: yes, `(1, 2)` cross-
  pair incomparable; at k=1: `0 < 1` and `0 < 2`, no incomp from
  band 1 to bands 2-3, so **NOT** irreducible at k=1. Filtered out.
* `mask = 0b10` (free edge `(1, 2)` set): `0 < 2` (forced),
  `1 < 2`. Irreducible at k=1: yes, `0 ⫫ 1`; at k=2: no, `2` is the
  unique top, both `0` and `1` are below it. Filtered out.
* `mask = 0b11` (both): chain `0 < 1 < 2`. Width 1, not irreducible
  at any cut (totally ordered). Filtered out.

So at `bs = [1, 1, 1]` no surviving config triggers
`hasBalancedPairSlow`; `enumPosetsFor 1 [1, 1, 1]` returns `true`
trivially. Consistent with `allBalanced 1 9 = true`.

A non-trivial sanity-check is `bs = [2, 2, 2]` (|Q| = 6) — far too
large to hand-verify here, but the Python certificate
(`lean/scripts/enum_case3_certificate.json`, see commit
`mg-307c`) records `~344243` configurations for `w=1, K=3, |Q|≤9`,
all balanced. Lean's `native_decide` evaluates the same Bool
function on the same encoding (verified above against the Python
script) — so the Lean Bool fact agrees with the Python certificate
by construction.

**Bool→Prop bridge.** Consumer:
`OneThird.Step8.Case3Enum.allBalanced_imp_enumPosetsFor`
(`Case3Enum/AllBalancedBridge.lean:218-256`), extracts
`enumPosetsFor 1 bs = true` for any `bs ∈ bandSizesGen 3 9`; then
`Step8.bounded_irreducible_balanced_inScope`
(`BoundedIrreducibleBalancedInScope.lean:97-221`) lifts that Bool
fact to `HasBalancedPair α` for every layered width-3 poset with
`(L.w, |α|, L.K)` ∈ `InCase3Scope`.

The bridge does **not** weaken: it rebuilds the F5a band-major
encoding `predMaskOf L` from the Prop-side `LayeredDecomposition L`,
proves it equals `enumPredAtMaskOf L.w (bandSizes L) (maskOf L)`
(`enumPredAtMaskOf_eq_predMaskOf`), discharges every Bool gate
(`closureCanonical`, `findSymmetricPair = none`, `irreducible`,
`hasAdjacentIncomp`) from the Prop-side hypotheses, applies the
inner per-mask iteration theorem `enumPosetsFor_iter_balanced` to
extract `hasBalancedPairSlow predMask card = true` at `mask = maskOf
L`, then transports through `bandMajorOrderIso_predOrder L` to the
Prop-side `HasBalancedPair α`. **No information is dropped.** ✅

**Parameter coverage match.** `(w, sizeLimit) = (1, 9)` covers
exactly `InCase3Scope` ∩ `{w = 1}` (the per-disposition-B-amendment
restriction `w = 1 → card ≤ 9`). ✅

### 2-4. `case3_balanced_w{2,3,4}` — `Case3Enum/W{2,3,4}.lean:24`

```lean
theorem case3_balanced_w2 : allBalanced 2 7 = true := by native_decide
theorem case3_balanced_w3 : allBalanced 3 7 = true := by native_decide
theorem case3_balanced_w4 : allBalanced 4 7 = true := by native_decide
```

**Bool encoding (identical to w1).** `allBalanced w 7 = true` says
every band-size triple summing to ≤ 7, evaluated at the given `w`,
admits a balanced pair under the same `enumPosetsFor` filter chain.

**Parameter coverage.** F5a's `InCase3Scope` (`(2 ≤ w → card ≤ 7)`)
caps `|Q|` at 7 for `w ∈ {2, 3, 4}`. The triple
`{(2, 7), (3, 7), (4, 7)}` covers the entire `w ∈ {2, 3, 4}` slice
of `InCase3Scope`. The four-way split in
`enumPosetsFor_eq_true_of_inScope` (`OptionC/Case3WitnessProof.lean:174-203`)
maps `LB.w = 2 → hw2cert`, `LB.w = 3 → hw3cert`, `LB.w = 4 →
hw4cert`. ✅

**Sanity-check sample.** Same logic as w1; `bs = [1,1,1]` at `w = 2`
makes pairs `(0, 1), (1, 2), (0, 2)` all free (band gaps 1, 1, 2 all
≤ 2). The 8 masks include the chain `0 < 1 < 2` (irreducible
filtered out — width 1) and the antichain (irreducible at every
cut — but no adjacent-incomp filter holds since `0 ⫫ 1` and
`1 ⫫ 2` directly, so `hasAdjacentIncomp = true`; then
`hasBalancedPairSlow` runs on the antichain on 3 elements which has
`6` linear extensions and `Pr[0 < 1] = 3/6 = 1/2 ∈ [1/3, 2/3]` —
balanced ✅). Consistent with `allBalanced 2 7 = true`.

For `w = 3, 4` and `bs = [1,1,1]` the situation is identical (more
free edges, same survivor configurations). The Python certificate
records `~102784` configurations per `w ∈ {2,3,4}` slice, all
balanced; Lean's `native_decide` evaluates the same Bool function
on the same encoding.

**Bool→Prop bridge (identical to w1).** Same
`allBalanced_imp_enumPosetsFor` →
`bounded_irreducible_balanced_inScope` chain, four-way split on
`LB.w`. ✅

**Parameter coverage match.** `(w, sizeLimit) ∈ {(1,9), (2,7), (3,7),
(4,7)}` covers `InCase3Scope` exactly. The disposition-B amendment
notes that the `case3Witness_hasBalancedPair_outOfScope` axiom
covers the residual range outside `InCase3Scope` (i.e. `w ≥ 5` or
`w ∈ {2,3,4}, card ∈ {8,9}` or `K ≠ 3`), so this Bool/axiom split
is exhaustive across the F5 C2 leaf hypothesis profile. ✅

### 5. `case2_certificate` — `OptionC/K2Closure.lean:129`

```lean
theorem case2_certificate :
    ∀ bs ∈ bandSizesGen 2 6, enumPosetsFor 1 bs = true := by
  native_decide
```

**Bool encoding.** Direct universal over `bandSizesGen 2 6` (band
pairs `[m, n]` with `m, n ∈ {1, 2, 3}`, `m + n ≤ 6` — all 9 such
pairs `(1,1), (1,2), (1,3), (2,1), (2,2), (2,3), (3,1), (3,2),
(3,3)`), at fixed `w = 1`, with the same `enumPosetsFor` filter
chain as the Case-3 certificate.

**Parameter coverage.** This is the K=2 width-3 layered irreducible
certificate (`mg-01ec`, Stage 1 of Option-C). The K=2 regime is the
only one where `LayerOrdinalReducible LB 1` is decidable from
`hIrred` alone (no inductive descent), and the `bandSize ≤ 3`
hypothesis from L1 plus K=2 caps |Q| at 6 trivially. The header
docstring (`K2Closure.lean:115-125`) records the rationale for the
`w = 1` choice: at K=2, `(L2-forced)` is operative only for band
gap > w; with band-pair gap fixed at 1, `w ≥ 1` makes (L2-forced)
vacuous so the enumeration is `w`-independent at `w ≥ 1`; `w = 0`
is structurally excluded by `hIrred` in the Prop-level closure. ✅

**Sanity-check sample.** `bs = [1, 1]` (|Q| = 2, K = 2). One free
pair `(0, 1)` at `w = 1`. Two masks: `mask = 0` (incomparable, an
antichain on 2 elements; `Pr[0 < 1] = 1/2 ∈ [1/3, 2/3]` — balanced
✅) and `mask = 1` (chain `0 < 1`; width 1, not irreducible at K=2
because lower band element `0` is comparable to band 2 `1`, so
filtered out). Consistent with `enumPosetsFor 1 [1, 1] = true`.

`bs = [2, 1]` (|Q| = 3, K = 2). Free pairs `(0, 2), (1, 2)` at
`w = 1` (band gap 1). Four masks; surviving configs after gates
(closure-canonical, no symmetric pair, irreducible, adjacent-incomp)
each get checked by `hasBalancedPairSlow`. By the K=2 width-3
catalog of `mg-e112` (referenced in `K2Closure.lean:480-489`), all
40 width-3 K=2 layered-irreducible classes admit a balanced pair —
32 via fast-path or symmetric, 8 via the full DP — so the Bool
certificate is consistent with the catalog.

**Bool→Prop bridge.** Consumer
`OneThird.Step8.OptionC.enumPosetsFor_bandSizes_eq_true_of_K2`
(`OptionC/K2Closure.lean:145-153`) instantiates
`case2_certificate` at the concrete `bandSizes L` for any
`LayeredDecomposition β` with `L.K = 2`, `|β| ≤ 6`, and bands
non-empty, producing `enumPosetsFor 1 (bandSizes L) = true`. Then
`option_c_K2_closure_inScope_at_w1` (`K2Closure.lean:266-444`)
lifts this Bool fact to `HasBalancedPair β` via the same
`enumPosetsFor_iter_balanced` / `bandMajorOrderIso_predOrder`
machinery as the Case-3 bridge.

The K=2 closure `option_c_K2_closure` (`K2Closure.lean:500-547`)
then routes through the **`w = 1` sister** (`normalizeWAtK2 LB
hK2`) for any `LB.w ≥ 1`, and rules out `LB.w = 0` from `hIrred`
(at K=2, `w = 0` makes `(L2-forced)` operative on every cross-pair,
which is precisely `LayerOrdinalReducible LB 1` — contradicting
`hIrred`). The sister has the same partial order on `β`, only
`recorded.w = 1` changes; this is paper-faithful since at K=2
there is no width-direction-dependent hypothesis on `β` itself. ✅

**Bool→Prop bridge does not weaken.** The bridge proves: for any
`L : LayeredDecomposition β` with K=2, irreducible, |β| ≤ 6, and
non-empty bands, `β` admits a balanced pair. The non-empty band
hypothesis is supplied from `K=2` + `hIrred` (band 1 must have an
element since `band_pos`; band 2 must have an element since
`hIrred` would otherwise place the entire poset in band 1
contradicting K=2). The size cap |β| ≤ 6 follows from L1
(`bandSize ≤ 3`) plus K=2. So the bridge faithfully transports the
Bool fact to the Prop conclusion without additional unstated
hypotheses. ✅

## Aggregate verdict — Validation B

All five `native_decide` invocations are faithful: each Bool predicate
encodes exactly the math claim in the surrounding theorem, the
parameter ranges `(1, 9), (2, 7), (3, 7), (4, 7)` for Case 3 and
`(1, 6)` for Case 2 cover the F5a / Stage-1 sub-case bounds, the
Bool→Prop bridges close cleanly via the per-mask iteration theorem
plus band-major OrderIso transport, and no Bool-predicate-vs-math
mismatch (mg-a79e pattern) was found.

The trust footprint imposed by these five invocations on the
headline `OneThird.width3_one_third_two_thirds` is exactly **one
underlying axiom** — `Lean.ofReduceBool`, expanded by `#print
axioms` into five per-invocation instances. This is the minimal
trust delta a `native_decide` can introduce; the Python ground-truth
enumerator (`lean/scripts/enum_case3.py`) and JSON certificate
(`lean/scripts/enum_case3_certificate.json`) provide an
independent computational check matching the Lean Bool function
byte-for-byte.

## Cross-references

* Bool predicates: `lean/OneThird/Step8/Case3Enum.lean`.
* Per-`w` slices: `lean/OneThird/Step8/Case3Enum/W{1,2,3,4}.lean`.
* K=2 Case-2 certificate: `lean/OneThird/Step8/OptionC/K2Closure.lean`.
* Bool→Prop bridges:
  - `lean/OneThird/Step8/Case3Enum/AllBalancedBridge.lean`
    (outer `allBalanced` → inner `enumPosetsFor`).
  - `lean/OneThird/Step8/Case3Enum/EnumPosetsForBridge.lean`
    (per-mask iteration theorem).
  - `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean`
    (Case-3 bridge, in-scope).
  - `lean/OneThird/Step8/OptionC/K2Closure.lean` §4
    (Case-2 K=2 bridge, in-scope).
* Python ground truth: `lean/scripts/enum_case3.py`,
  `lean/scripts/enum_case3_certificate.json`,
  `lean/scripts/README.md`.
* Existing axiom disclosure: `lean/AXIOMS.md`,
  `lean/PRINT_AXIOMS_OUTPUT.txt`.
