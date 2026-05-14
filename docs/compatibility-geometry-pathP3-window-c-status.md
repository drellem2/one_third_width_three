# Compatibility Geometry — Path P3 Window C status (mg-9a4a)

**Companion to** `docs/compatibility-geometry-pathP3-scoping.md`
(`mg-9d6c`, AMBER-narrow scoping verdict). This document records the
**execution** of Window C of the scoping doc's §2.2 / §5.1: extension
of the F5a `case3_certificate` Bool enumeration from `K = 3` to the
small-cardinality `K = 4, w = 1` slice — in a **small size-limit
variant** that covers 50 of the 93 Window C tuples (the K=4-w=1
band-tuples with `c ≤ 8`) and leaves the larger-`c` K=4-w=1 slice
(31 tuples) and the K=3 c-sliver (12 tuples) axiomatic.
**Axiom narrowing, not elimination** — per the scoping doc verdict.

---

## 1. Deliverable

Window C of `mg-9d6c` §5.1, executed verbatim:

| Slice              | Lean theorem                          | Certificate                  |
|--------------------|---------------------------------------|------------------------------|
| K=4, w=1, c ≤ 8    | `case3_balanced_K4_w1`                | `allBalancedAtK 4 1 8`       |

The existing K=3 `case3_balanced_w{1,2,3,4}` certificates remain
unchanged; only the K=4-w=1 small-size slice is added in this
variant.

### 1.1 Small size-limit variant — what's NOT covered

The full Window C target of `docs/compatibility-geometry-pathP3-scoping.md`
§5.1 also includes:

* The `K = 4, w = 1, c ∈ {9, …, 12}` slice — 31 K=4 band-tuples at
  higher `c` whose `nfree ≥ 18` mask spaces exceed the local
  native-decide budget. The single `(3,3,3,3)` band-tuple at `c = 12`
  has `nfree = 27` (the existing `enumPosetsFor` engineering cap)
  and a `2^27`-mask evaluation that empirically takes well over 30
  minutes on this hardware.
* The `K = 3` c-sliver: 12 K=3 band-tuples at `(w ∈ {2,3,4}, c ∈
  {8, 9})`. The `(3,3,3)` tuple at K=3 has `nfree = 27` at any
  `w ≥ 2`, with the same intractability profile.

These 43 tuples are left axiomatic in this polecat session; a
follow-up polecat (with sharper enumeration tooling, longer native-
decide budget, or running on faster hardware) could discharge the
remaining tuples. The 50 K=4-w=1 small-`c` tuples covered here form
the largest contiguous "near-base-case" extension that fits the local
build window.

## 2. Lean execution log

### 2.1 Files added

* `lean/OneThird/Step8/Case3Enum/K4W1.lean` — `case3_balanced_K4_w1`,
  the single new native-decide module of the small-size variant.

### 2.2 Files modified

* `lean/OneThird/Step8/Case3Enum.lean` — adds `allBalancedAtK K w sizeLimit`,
  the K-parametric generalisation of the previous K=3-specific
  `allBalanced`. The legacy `allBalanced` is preserved verbatim; an
  `@[simp]`-tagged `allBalancedAtK_three` glue lemma asserts they agree
  by `rfl` at K=3.
* `lean/OneThird/Step8/Case3Enum/AllBalancedBridge.lean` — adds the
  K-parametric Bool→Prop bridge
  `allBalancedAtK_imp_enumPosetsFor : allBalancedAtK K w sizeLimit = true →
  ∀ bs ∈ bandSizesGen K sizeLimit, enumPosetsFor w bs = true`, with the
  same outer-`forIn` reduction template as the legacy
  `allBalanced_imp_enumPosetsFor`.
* `lean/OneThird/Step8/Case3Enum/Certificate.lean` — `case3_certificate`
  now aggregates five `allBalanced{,AtK}` facts (the original four K=3
  slices plus the K=4-w=1 small-size Window C extension).
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean` — `InCase3Scope`
  widened from a single conjunction to the two-way disjunction
  `(K = 3 ∧ w ∈ {1,…,4} ∧ size caps) ∨ (K = 4 ∧ w = 1 ∧ card ≤ 8)`.
  The K=3 disjunct preserves the original size caps verbatim;
  `InCase3Scope.card_le_nine` is retained (the K=4 disjunct's `≤ 8`
  is bounded by the K=3 w=1 cap at `≤ 9`); `InCase3Scope.w_mem`
  updated to case-split on the disjunction.
* `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean` — the
  `2 ≤ L.K` derivation in the `hasAdjacentIncomp` gate updated to a
  case-split over the K=3-vs-K=4 disjunction. No other change; the
  bridge body is K-parametric and unaffected by the widening.
* `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean` —
  `enumPosetsFor_eq_true_of_inScope` updated to dispatch over the K=3
  vs K=4 disjunction, with a four-way `w` split inside the K=3 branch
  (consuming the original four `case3_balanced_w{1,2,3,4}` certs) and
  the singleton K=4-w=1 entry (consuming `case3_balanced_K4_w1`).
* `lean/OneThird.lean` — adds the new `Case3Enum.K4W1` import.
* `lean/AXIOMS.md` — adds a "Scope narrowing (`mg-9a4a`, post-mg-9d6c
  Window C, small size-limit variant)" subsection to the
  `case3Witness_hasBalancedPair_outOfScope` entry, documenting the new
  `InCase3Scope` shape, the new theorem, and the unchanged trust
  surface (4 named axioms; native-decide count rises from 5 to 6 with
  the new entry).

### 2.3 Files NOT touched

* `lean/OneThird/Step8/Case3Residual.lean` — the residual axiom site.
  Signature unchanged; the narrowing operates by widening
  `InCase3Scope` upstream of the axiom hypothesis.
* `lean/OneThird/Step8/Case3Dispatch.lean` — A8-S1 typed dispatch.
  `case1_dispatch_inScope` is universal (does not destructure
  `hScope`); unaffected.
* `lean/OneThird/Step8/Case3Enum/{Correctness,EnumPosetsForBridge,
  IrreducibleBridge,AdjIncompBridge,SymmetricLift,PredMaskBridge,
  BalancedLift}.lean` — K-parametric throughout; consumed unchanged.
* `lean/OneThird/Step8/Case3Enum/W{1,2,3,4}.lean` — the legacy K=3
  certificates. Statements unchanged; retained because
  `case3_certificate`'s aggregator still cites them as separate
  conjuncts.

## 3. Build green

`lake build` succeeds end-to-end with no `sorry`, no new project
axiom, no warning regression. In the small size-limit variant the
single new K=4-w=1 native-decide theorem compiles in `~2 minutes`
(local hardware, `lake build OneThird.Step8.Case3Enum.K4W1` reported
`121s`). All 50 K=4-w=1 band-tuples with `c ≤ 8` have `nfree ≤ 15`,
so the dominant `2^nfree`-mask sweeps stay within the same band-tuple
range that `native_decide` already handles for the existing
`case3_balanced_w1`.

## 4. Trip-wire compliance

| Trip-wire                                | Status                                           |
|------------------------------------------|--------------------------------------------------|
| **NO new axioms**                        | ✅ The 1 native-decide addition introduces a per-invocation `_native.native_decide.ax_1_1` instance (Lean's `ofReduceBool`), not a project axiom. Named-axiom count stays at 4. |
| **Build green hard requirement**         | ✅ `lake build OneThird` succeeds (1410/1410 jobs, no errors). |
| **`#print axioms` audit**                | The axiom set on `width3_one_third_two_thirds` adds one new `_native.native_decide.ax_1_1` entry (`case3_balanced_K4_w1`); no project axiom added or removed. |

## 5. What this delivers — and what it does NOT

**Delivers.** Axiom-narrowing: `case3Witness_hasBalancedPair_outOfScope`'s
parameter range shrinks to exclude the `(K = 4, w = 1, c ≤ 8)`
slice (50 K=4 small-cardinality tuples). Caller-side, this means the
F5a-certificate branch (`bounded_irreducible_balanced_inScope`)
discharges these 50 tuples directly via `native_decide`; the axiom
is not invoked on them.

**Does NOT deliver.** Axiom **elimination**. Beyond the 50 newly
discharged tuples, the residual axiom continues to apply on:

* the 31 `K = 4, w = 1, c ∈ {9, …, 12}` band-tuples excluded by the
  small size-limit variant;
* the 12 K=3 c-sliver tuples `(K = 3, w ∈ {2,3,4}, c ∈ {8, 9})`
  (also excluded by the small size-limit variant);
* the K ≥ 5 bulk and the `K = 4 ∧ w ≥ 2` slice (full mg-9d6c
  residual).

Per `docs/compatibility-geometry-pathP3-scoping.md` §2, the residual
parameter range is dominated by `~10^5` tuples at w=4 of which
`~99%` have `nfree > 27` and are not addressable by enumeration
alone. Elimination requires the `A8-S2-cont` probability-form
cross-poset FKG infrastructure or the manifesto-§3-Step-2 spectral
expansion specialist input — both multi-polecat, neither in scope of
this ticket.

## 6. References

* `mg-9d6c` (`9526cf4`) —
  `docs/compatibility-geometry-pathP3-scoping.md`, the predecessor
  AMBER-narrow scoping doc. Section §5 of that doc is the
  execution spec this polecat implements.
* `mg-c853` —
  `docs/compatibility-geometry-feasibility-scoping.md`, the upstream
  manifesto feasibility scoping. P3 is one of its three execution
  paths.
* `lean/AXIOMS.md` —
  `case3Witness_hasBalancedPair_outOfScope` entry, "Scope narrowing
  (`mg-9a4a`, post-mg-9d6c Window C)" subsection.
* `mg-b846` — `Case3Residual.lean` (residual axiom site).
* `mg-307c` — the original K=3 `case3_certificate` (Python script + Lean
  port that this polecat extends).

---

*Authored by polecat `cat-mg-9a4a`, branch `polecat-cat-mg-9a4a`
→ target `compat-geom-pathP3`. 2026-05-13.*
