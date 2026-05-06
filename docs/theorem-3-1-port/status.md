# Theorem 3.1 in-scope port — STOP report

**Work item:** `mg-ebff` (polecat `pebff`).
**Branch:** `polecat-pebff` (target `theorem-3-1-port`).
**Predecessor (math):** `mg-5bf9` (`docs/case3-port-arc/linear-majority-alignment.md`).
**Disposition:** **STOP — trip-wires #3 and #5 fire.** No Lean
source changes; this artifact is the deliverable per
`feedback_audit_as_deliverable`.

---

## §1 Brief recap

The polecat brief asks for a structural Z/3-cyclic Lean proof
replacing `native_decide` in
`lean/OneThird/Step8/Case3Enum/W1.lean:32`:

```lean
theorem case3_balanced_w1 : allBalanced 1 9 = true := by native_decide
```

Estimated scope per the brief: ~80–150 LoC; trip-wire at 225 LoC.
Goal: drop one `native_decide` axiom from the closure of
`width3_one_third_two_thirds`.

---

## §2 What was investigated

* **`allBalanced`** (`lean/OneThird/Step8/Case3Enum.lean:360-363`) —
  iterates `bandSizesGen 3 9` (27 band-size tuples
  `[n₁, n₂, n₃]` with `n_i ∈ {1,2,3}` and sum ≤ 9). For each tuple
  calls `enumPosetsFor 1 bs`, which iterates over up to `2^nfree`
  predecessor masks (max `nfree = 18` at `[3,3,3]`, hence up to
  `262144` masks for that tuple alone; total ≈ 344243 configurations
  per the docstring).
* **Per-mask body** filters by closure-canonical, NO symmetric pair,
  irreducible, has-adjacent-incomp, then requires
  `hasBalancedPairSlow pred n = true` (the LE-counting DP).
  `findSymmetricPair` already discharges the **Z/2-swap** case;
  residual configs need the **Z/3-cyclic** argument (or a
  full LE count) — that's the heart of `case3_balanced_w1`'s 344243
  config count, of which the symmetric-pair fast path skips most.
* **Existing in-tree infrastructure for the Z/2 case**
  (`lean/OneThird/Step8/Case3Enum/BalancedLift.lean §0`):
  `probLT_eq_half_of_swap_auto` — generic *abstract-poset* form of
  the Z/2 fast path. ~50 LoC. No Z/3-cyclic counterpart in tree.
* **Existing Bool→Prop bridges** (`Case3Enum/{AllBalanced,
  EnumPosetsFor, Irreducible, AdjIncomp, PredMask, Symmetric,
  Balanced, Correctness}Bridge*.lean`) total ~7450 LoC. They lift
  the Bool certificate `enumPosetsFor L.w (bandSizes L) = true` to
  `HasBalancedPair α` for an abstract `LayeredDecomposition L`
  (consumer `bounded_irreducible_balanced_inScope` in
  `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean`).
  These run **Bool → Prop** (one-directional).
* **The reverse direction** — `HasBalancedPair α` for every abstract
  K=3, w=1 in-scope poset implying `allBalanced 1 9 = true` — is
  *not* in tree. The `Case3Enum.lean` module docstring
  (`lean/OneThird/Step8/Case3Enum.lean:30-37`) documents this
  explicitly:

  > The lift of this certificate to an abstract
  > `∀ (L : LayeredDecomposition α), … → HasBalancedPair α`
  > statement requires an encoding argument (choose element
  > labelling within each band; prove probability invariance
  > under relabelling) that is deferred to a separate work item
  > on the F5 recursion.

  The polecat brief's reverse use of this bridge is exactly the
  deferred F5 work.

---

## §3 Why mg-5bf9 §5's 80–150 LoC estimate does not apply here

mg-5bf9's `linear-majority-alignment.md` §5 reads:

> If a future Lean port wants to use Theorem 3.1's argument as
> the in-scope branch's discharge: estimated ~80-150 LoC for the
> cyclic-σ construction in Lean (Aut(Q) construction + rotation
> identity specialisation + Pr = 1/3 conclusion). **Replacing the
> `case3_certificate` Bool-level decision-procedure dispatch.**

The 80–150 LoC estimate is for the **abstract structural theorem
itself** (`for any K=3, w=1 in-scope abstract poset, Pr = 1/3 on
some pair → HasBalancedPair α`), and the bolded clause is for a
**dispatch refactor at the consumer site**
(`BoundedIrreducibleBalancedInScope` → call structural theorem
directly instead of routing through `case3_certificate`).

The polecat brief instead asks for replacement at the **producer
site** (`case3_balanced_w1 : allBalanced 1 9 = true`, *Bool*
proposition), which is materially different work:

| Direction                                         | What's needed                                                       | LoC estimate              |
|---------------------------------------------------|---------------------------------------------------------------------|---------------------------|
| Structural-only theorem (what mg-5bf9 §5 sized)   | `Aut(Q) + rotation-identity + Pr=1/3 conclusion` at abstract level  | 80–150 LoC                |
| **Replace `native_decide` on Bool predicate**     | Above PLUS Prop→Bool encoding bridge (deferred F5 work)             | 750–1300 LoC (estimate §4)|

mg-5bf9's §5 explicitly headlines verdict AMBER and **§5 reads
"N/A under AMBER"**:

> ## §5 Lean port shape — N/A under AMBER
>
> Per the brief, "If GREEN, sketch the Lean port shape." Verdict
> is AMBER, so this section is N/A.

The 80–150 LoC sentence above is in §5 as a parenthetical "if a
future Lean port wants to use Theorem 3.1" remark, not as a
sized commitment to the present polecat's task shape.

---

## §4 LoC blow-up estimate for the brief's scope

Replacing native_decide on `allBalanced 1 9 = true` structurally
requires building:

1. **σ-equivariance of `countLinearExtensions` under bitmask-level
   permutation σ** — the Bool DP commuting with poset
   automorphism. Analogue of `LinearExt.pullback` lifted to the
   `Array Nat`-encoded `countLinearExtensions` DP. Estimate:
   ~200–300 LoC. **Not in tree.**
2. **Z/3-cyclic auto detection on bitmask poset** — a Bool
   predicate `findZ3CyclicTriple : Array Nat → Nat → Option (Fin n × Fin n × Fin n)`
   plus a Bool→Prop bridge (cyclic σ exists with `pred[a_i]`
   appropriately permuted). Estimate: ~150–300 LoC.
   **Not in tree.**
3. **Per-config structural argument** — every config surviving
   `closureCanonical + ¬findSymmetricPair + irreducible +
   hasAdjacentIncomp` at K=3, w=1 has either Z/2 or Z/3 auto;
   the latter forces `hasBalancedPairSlow = true`. Estimate:
   ~300–500 LoC (including the encoding argument deferred per §2
   docstring).
4. **Top-level wiring** — `enumPosetsFor 1 bs = true` for each of
   27 tuples; `allBalanced 1 9 = true` from the conjunction.
   Estimate: ~100–200 LoC.

**Total: ~750–1300 LoC.** Trip-wire #2 fires (>225 LoC).

---

## §5 Trip-wires fired

* **Trip-wire #5 — Bool predicate encodes something subtly
  different than what the structural proof shows.** The Bool
  `allBalanced 1 9` enumerates *bitmask-encoded* configurations
  on `Fin n`; Theorem 3.1 is a statement about *abstract* posets
  with `Case3Witness L` and `LayeredDecomposition L`. Bridging
  one to the other requires the **deferred F5 encoding work**
  (per `Case3Enum.lean:30-37` docstring quoted above). This is
  the **mg-a79e pattern**: a Bool computation hides an
  encoding-bridge obligation that the structural proof does not
  by itself satisfy.

* **Trip-wire #3 — Z/3-cyclic argument fails to formalize at the
  required scope.** The structural Lean machinery present in
  tree (`probLT_eq_half_of_swap_auto`) handles Z/2 only and at
  the abstract-poset level; there is **no** σ-equivariance of
  `countLinearExtensions`/`hasBalancedPairSlow` at the bitmask
  level, and no Z/3-cyclic counterpart of the Z/2 lemma. Building
  both, plus the Bool↔structural bridge, is the substantive
  follow-on to mg-5bf9 §5's structural-theorem-only estimate.

* **Trip-wire #2 — anticipated LoC blow-up.** §4 estimates
  750–1300 LoC, well past the 225 LoC trip-wire (and the 150 LoC
  upper estimate).

* **Math-level caveat (background, doesn't independently fire a
  trip-wire).** mg-5bf9 §3.1's Theorem 3.1 proof handles the
  case where both `S⁺` and `S⁻` are 3-antichains (Z/3 σ exists)
  but gestures at "alignment holds" for the case where one of
  them is not — which is the FKG-style argument that's the
  residual blocker on the wider arc. The K=3, w=1 sub-range is
  cleanly closed by Z/3-cyclic only when both S⁺ and S⁻ are
  3-antichains; the small-band-size sub-cases need separate
  handling that *should* be tractable in tree (since
  `|M_{k±1}| < 3` collapses the 3-antichain count) but isn't
  free LoC. Documented here so the next polecat doesn't trip on
  it.

---

## §6 Pre-port axiom inventory (baseline, unchanged)

From `lean/PRINT_AXIOMS_OUTPUT.txt`:

```
'OneThird.width3_one_third_two_thirds' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   OneThird.LinearExt.brightwell_sharp_centred,
   OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope,
   OneThird.Step8.Case3Enum.case3_balanced_w1._native.native_decide.ax_1_1,
   OneThird.Step8.Case3Enum.case3_balanced_w2._native.native_decide.ax_1_1,
   OneThird.Step8.Case3Enum.case3_balanced_w3._native.native_decide.ax_1_1,
   OneThird.Step8.Case3Enum.case3_balanced_w4._native.native_decide.ax_1_1,
   OneThird.Step8.OptionC.case2_certificate._native.native_decide.ax_1_1]
```

LoC for `lean/OneThird/Step8/Case3Enum/W1.lean`: **37 lines**
(unchanged; no source modification).

---

## §7 Recommended disposition

Per `feedback_polecat_stop_runaway`: block, report, no
auto-extension. Per `feedback_distinguish_arc_chunk_outcomes`:
this STOP is a **scoping correction** for a parallel-cleanup
ticket, not a substantive setback for the headline destination
arc (which is mg-8d39's A8-S2-cont scoping path).

Concrete recommendations to mayor:

1. **Treat the brief's scope as mis-sized.** The 80–150 LoC
   target conflated mg-5bf9 §5's *abstract-theorem-only*
   estimate with the *Bool-replacement* burden, which is
   materially larger because it includes the deferred F5
   encoding work.
2. **If the audit-bar reduction is still wanted**, an
   alternative shape: refactor the *consumer*
   (`bounded_irreducible_balanced_inScope`) to take an
   alternate path through the structural Theorem 3.1
   for the K=3, w=1 in-scope branch, while leaving
   `case3_balanced_w{2,3,4}` and `case3_certificate`
   intact. This is what mg-5bf9 §5's "Replacing the
   `case3_certificate` Bool-level decision-procedure dispatch"
   wording actually points at.
   * Even this refactor needs the structural Theorem 3.1 ported
     (~80–150 LoC) **plus** wiring through
     `bounded_irreducible_balanced_inScope`'s case split
     (~80–200 LoC of new branch logic, since the existing
     consumer hard-codes the Bool certificate path).
   * Net axiom-bar effect: removes the
     `case3_balanced_w1._native.native_decide` axiom only when
     `bounded_irreducible_balanced_inScope`'s K=3, w=1 branch
     is the unique consumer of `case3_balanced_w1`. Currently
     `case3_balanced_w1` is consumed via `case3_certificate` →
     all of `bounded_irreducible_balanced_inScope` (across
     w∈{1,…,4}). Splitting this would require a parallel split
     in the consumer.
3. **Defer until A8-S2-cont is mature** (mg-8d39 path). Once
   the encoding bridge work in F5 lands, the present polecat's
   scope becomes tractable as a clean parallel-cleanup at
   ~150–300 LoC.
4. **Mark the parallel-cleanup ambition unblocked but
   non-trivial** in the audit-bar tracking, citing this
   artifact as the scoping report.

---

## §8 Polecat protocol

* `mg claim mg-ebff` — done.
* `pogo schedule … mail-check-mg-ebff` — done.
* No Lean source changes — STOP fired before implementation.
* This `.md` deliverable — done (the value regardless of verdict
  per `feedback_audit_as_deliverable`).
* Trip-wires #3 and #5 fired; #2 anticipated.
* Mail to mayor — pending immediately after this commit per
  `feedback_polecat_stop_runaway`.

---

## §9 Cross-references

* `mg-5bf9` (archived) — `docs/case3-port-arc/linear-majority-alignment.md`
  (math research; AMBER verdict; §3.1 Theorem 3.1; §5 sizing).
* `mg-8d39` (sibling) — A8-S2-cont scoping arc; the substantive
  destination path. Independent of this STOP.
* `lean/OneThird/Step8/Case3Enum/W1.lean:32` — the
  `native_decide` site (unchanged).
* `lean/OneThird/Step8/Case3Enum.lean:30-37` — the deferred-
  encoding-work docstring.
* `lean/OneThird/Step8/Case3Enum/BalancedLift.lean:79-129` —
  `probLT_eq_half_of_swap_auto` (Z/2 only).
* `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean:97-`
  — the existing Bool→Prop consumer.
* `lean/PRINT_AXIOMS_OUTPUT.txt` — baseline axiom inventory.
* `feedback_polecat_stop_runaway.md` — discipline.
* `feedback_distinguish_arc_chunk_outcomes.md` — applies.
* `feedback_audit_as_deliverable.md` — applies (this artifact
  is the value).
* Daniel directives 2026-05-06T~06:48Z + 07:01Z (per ticket
  body cross-references).
