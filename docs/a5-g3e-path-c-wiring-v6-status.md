# a5-g3e Path C wiring v6 status — block-and-report (5-axiom target infeasible; case (b))

**Author.** `pc-5f0c` polecat (under `mg-5f0c`), 2026-04-27.

**Verdict.** **Block and report — case (b) of mg-5f0c's hard
block-and-report rule.** The brief's planned outcome — `#print
axioms width3_one_third_two_thirds` =
`{propext, Classical.choice, Quot.sound, brightwell_sharp_centred,
<new Case2FKGSubClaim axiom>}` (5 axioms total, 2 paper-faithful
project axioms) — is structurally **unachievable** with the
in-tree infrastructure plus a single new project axiom. The F3
strong-induction step proof, when fed the headline path's
`layeredFromBridges` decomposition, must traverse the K≥3
irreducible leaf, which is closed only via
`case3Witness_hasBalancedPair_outOfScope` (existing project
axiom) and `case3_certificate` (uses `native_decide`, contributing
the `Lean.ofReduceBool` axiom).

The honest minimum axiom set for the planned discharge path is
**7 axioms**, not 5:

* `propext`, `Classical.choice`, `Quot.sound` (mathlib trio)
* `brightwell_sharp_centred` (existing project axiom — paper
  external import)
* `<new Case2FKGSubClaim axiom>` (the new project axiom proposed
  by mg-5f0c)
* `case3Witness_hasBalancedPair_outOfScope` (existing project
  axiom — paper-internal `rem:enumeration` sketch)
* `Lean.ofReduceBool` (mathlib, contributed by `native_decide`
  inside `case3_certificate`)

This matches **case (b)** of mg-5f0c's hard block-and-report
rule:

> (b) the F3 step proof requires additional axioms or hypotheses
> beyond the planned single FKG axiom

and triggers the pre-committed PM-side pivot:

> If (b) more axioms needed → that's a strategic signal and PM
> mails Daniel for re-decision.

`pc-5f0c` did not modify the headline. No code changes were
landed. The brief's option-(a) "drop both hC3 AND hFKG" framing
is incompatible with the planned single-axiom budget. PM should
re-decide between (i) widening the axiom budget to include the
existing `case3Witness_hasBalancedPair_outOfScope` and the
`Lean.ofReduceBool` contribution, (ii) pursuing the
compound-automorphism-extending route to discharge the K≥3 leaves
constructively (substantively new math, ~hundreds of LoC and out
of single-polecat scope), or (iii) returning to option (δ) park
with the v5 audit trail unchanged.

---

## 1. Planned discharge path

mg-5f0c's "Method (depends on full chain landing first)" §3 / §4
prescribes the following composition for the headline:

* `bipartite_balanced_enum_general` (mg-02c2) at the K=2 layered
  leaf;
* the new `Case2FKGSubClaim` axiom to discharge the
  `Case2FKGSubClaim` hypothesis of `bipartite_balanced_enum_general`;
* F3 strong-induction (mg-a735's
  `hasBalancedPair_of_layered_strongInduction_width3`) for the
  K≥3 / reducible / K=1 cases;
* existing dispatchers (`hasBalancedPair_of_K2_w0_incomp`,
  `case3_certificate` for `InCase3Scope`, ambient-match for
  Case 1) where they already apply.

The intended consumer is `OneThird.width3_one_third_two_thirds`
(the headline). Its proof path goes through
`Step8.width3_one_third_two_thirds_assembled`, which builds
`MainTheoremInputs` via `mainTheoremInputsOf`, which calls
`lem_layered_balanced layeredFromBridges …`. The decomposition
that reaches `lem_layered_balanced` is therefore the
**bridge-derived** one (`layeredFromBridges`,
`lean/OneThird/Step8/LayeredBridges.lean:248`), with

```
K := Fintype.card α
w := Lwidth3.bandwidth   -- = Fintype.card α + 1
band := singleton bands via Szpilrajn
```

For `Fintype.card α ≥ 3`, this gives `K ≥ 3`. The F3 step's
universally-quantified IH must therefore handle every value of
`LB.K ∈ {1, 2, 3, …}` for the recursion's sub-posets `β`.

## 2. The K≥3 + irreducible leaf forces a second project axiom

The F3 step proof (`hStep` argument of
`hasBalancedPair_of_layered_strongInduction_width3`) for a layered
β with `LB.K = K_β` and `2 ≤ Fintype.card β` dispatches:

* **K = 1**: trivial via `bipartite_balanced_enum (univ, ∅)`.
  No new axiom.
* **K = 2 + reducible**: descend via
  `OrdinalDecompOfReducible` + IH +
  `OrdinalDecomp.hasBalancedPair_lift_lower / _upper`.
  No new axiom.
* **K = 2 + irreducible + w = 0**:
  `hasBalancedPair_of_K2_w0_incomp` (mg-c0c7-prelude). No new
  axiom.
* **K = 2 + irreducible + w ≥ 1 + |β| ≥ 3**:
  `bipartite_balanced_enum_general` (mg-02c2) consuming the new
  `Case2FKGSubClaim` axiom. **One new axiom.**
* **K = 2 + irreducible + w ≥ 1 + |β| = 2**: forced chain
  (incomparable pair would refute irreducibility of the unique
  cut at `k = 1`). Closed inline.
* **K ≥ 3 + reducible**: descend via `OrdinalDecompOfReducible` +
  IH. No new axiom.
* **K ≥ 3 + irreducible + |β| ≤ 6w+6 + K ≤ 2w+2 + InCase3Scope**:
  `bounded_irreducible_balanced_hybrid` ∘ `case3_certificate`.
  **`native_decide` adds `Lean.ofReduceBool`.**
* **K ≥ 3 + irreducible + |β| ≤ 6w+6 + K ≤ 2w+2 + ¬ InCase3Scope**:
  `bounded_irreducible_balanced_hybrid` ∘
  `case3Witness_hasBalancedPair_outOfScope`. **Adds the existing
  project axiom.**

The K ≥ 3 + irreducible cases are reachable from the headline.
The bridge-derived `layeredFromBridges` has `K = Fintype.card α`
and `w = Fintype.card α + 1`. For an arbitrary width-3 non-chain
input `α`, `Fintype.card α` is unbounded, so `K_β ≥ 4` arises in
many sub-posets the F3 IH will visit. Concretely:

* **Witness 1.** Take `β` to be a width-3 antichain on 4
  elements. Singleton-band Szpilrajn gives `K = 4`, `w = 5`.
  Every `k ∈ {1, 2, 3}` admits an incomparable cross-pair
  (any two antichain elements), so β is fully irreducible.
  `Fintype.card β = 4`, `6w + 6 = 36`, `2w + 2 = 12`, so the F5
  C2 bounds are satisfied. `InCase3Scope` requires `K = 3` —
  fails since `K = 4`. The leaf falls in the `¬ InCase3Scope`
  branch and is closed by `case3Witness_hasBalancedPair_outOfScope`.

* **Witness 2.** Take `β` to be a 3-element antichain
  (`Fintype.card β = 3`, width 3, non-chain). Singleton-band
  Szpilrajn gives `K = 3`, `w = 4`. Fully irreducible (every
  cut admits an incomparable cross-pair). `InCase3Scope` checks:
  `K = 3 ✓`, `1 ≤ w = 4 ≤ 4 ✓`, `w = 1 → |β| ≤ 9` (vacuous),
  `2 ≤ w → |β| ≤ 7` (`3 ≤ 7 ✓`). So `InCase3Scope` holds and the
  leaf falls into the in-scope branch — closed by
  `case3_certificate`. **`case3_certificate`'s body uses
  `native_decide` (`Case3Enum/W{1,2,3,4}.lean:33`), contributing
  the `Lean.ofReduceBool` axiom.**

Both witnesses are realisable inputs to the headline — i.e., they
arise as the actual `β` visited by the F3 IH at some recursive
call. Witness 2's `β` is `α` itself when the headline input `α`
is the 3-antichain. Witness 1's `β` is `α` itself when the
headline input is the 4-antichain.

## 3. Why this is option (a) failure mode (b), not (c)

mg-5f0c's hard block-and-report rule lists four trigger cases
((a) FKG axiom shape too narrow at the case-2 leaf,
(b) additional axioms beyond the FKG axiom, (c) compound-aut
dispatch surfaces uncovered cases, (d) lake-build failure).

The block here is **(b)**, not (a) / (c) / (d):

* The new FKG axiom **does** suffice to discharge the
  case-2 leaf — `bipartite_balanced_enum_general` (mg-02c2)
  consumes only `Case2FKGSubClaim L`, and the proposed axiom
  shape is exactly `∀ L, Case2FKGSubClaim L`. No (a).
* The compound-automorphism dispatch (mg-84f2 / mg-c0c7 /
  mg-02c2) covers the K=2 + irreducible + w≥1 + |β|≥3 regime
  fully. No (c).
* No code was landed, so no `lake build` failure. No (d).

The block is on the **K ≥ 3** leaves of the F3 induction, which
mg-5f0c's "Method §4c" allocates to "F3 strong-induction
(mg-a735's framework) for the K≥3 / reducible / K=1 cases" but
which actually require either the existing
`case3Witness_hasBalancedPair_outOfScope` axiom (out of scope) or
`case3_certificate`'s `Lean.ofReduceBool` contribution (in scope)
to close.

## 4. What this blocks and what stays out

This block does **not** retract:

* The compound-automorphism three-way dispatch infrastructure
  (mg-84f2 / mg-c0c7 / mg-02c2 — all in `main`).
* The chain-form FKG sub-claim's bundling shape (`Case2FKGSubClaim`,
  mg-27c2).
* The candidacy of axiomatising `Case2FKGSubClaim` as a
  paper-faithful project axiom (the new axiom would still be
  faithful and well-scoped — it just doesn't suffice to drop
  `hC3` from the headline alone).

This block **does** retract the inference that a single new FKG
axiom suffices to make the headline unconditional. The K ≥ 3
leaf coverage is **the same gap that the v4 status doc surfaced**
(`docs/a5-g3e-path-c-wiring-v4-status.md` §2c, "K = 2 +
irreducible + w ≥ 1 + |β| ≥ 3"), but inverted: that round flagged
that the K = 2 regime had no in-tree handler; this round
confirms that even with the K = 2 handler now in tree (mg-02c2),
the K ≥ 3 regime has no axiom-free in-tree handler either, and
the existing axiom-based handlers add to the headline's `#print
axioms` set.

## 5. Pre-committed pivot options (PM-side)

mg-5f0c §"Pre-committed next-round pivot" lists three options
when block-and-report fires. For case (b) the brief says:

> If (b) more axioms needed → that's a strategic signal and PM
> mails Daniel for re-decision.

Per the brief, PM should mail Daniel. Plausible re-decisions:

1. **Widen the axiom budget.** Accept that the headline retains
   `case3Witness_hasBalancedPair_outOfScope` and gains
   `Lean.ofReduceBool` (from `case3_certificate`). The headline
   becomes unconditional with **7 axioms total, 3 paper-faithful
   project axioms** (brightwell, new FKG, case3-out-of-scope).
   This requires updating mg-5f0c's acceptance criteria from
   "5 axioms" to "7 axioms" plus AXIOMS.md updates for the new
   FKG axiom (the existing case3-out-of-scope entry already
   covers itself; `Lean.ofReduceBool` is mathlib-level and would
   be added to the disclosure).

2. **Pursue the compound-automorphism-extending route at K ≥ 3.**
   Build infrastructure analogous to mg-84f2 / mg-c0c7 / mg-02c2
   but for K ≥ 3 + irreducible + bounded-cardinality (the F5 C2
   leaf profile). Estimated cost from the path-c-cleanup-roadmap
   §6a: ~300-500 LoC of strictly new structural infrastructure.
   This would replace `case3Witness_hasBalancedPair_outOfScope`
   with a constructive proof and avoid `case3_certificate`
   entirely (constructive Case 3 dispatch via the new
   compound-automorphism + matching machinery). Substantively new
   math; out of single-polecat scope.

3. **Return to option (δ) park.** Keep the headline with `hC3`,
   land mg-5f0c as a no-op (or as a docs-only disclosure update),
   and leave the K=2 / K≥3 dual gap as it stood under v5. The
   compound-automorphism infrastructure landed in main (mg-84f2 /
   mg-c0c7 / mg-02c2) is then a deferred prerequisite that
   helps a future cleanup round but does not by itself unblock
   the headline.

## 6. References

* `mg-5f0c` (this ticket) — option (a) v6 brief.
* `docs/a5-g3e-path-c-wiring-v5-status.md` (mg-94fd) — round 5
  block-and-report, named the K=2 + irreducible + w≥1 + |β|≥3
  regime.
* `docs/a5-g3e-path-c-wiring-v4-status.md` (mg-0fa0) — round 4
  block-and-report, named the K=2 + irreducible + w≥1 regime
  (without the |β|≥3 refinement).
* `docs/path-c-cleanup-roadmap.md` (mg-7261) — option-(δ) park
  deliverable; §6a/§6b lay out the structural-extension and
  finite-enumerator routes.
* `lean/AXIOMS.md` — current axiom disclosures
  (`brightwell_sharp_centred`,
  `case3Witness_hasBalancedPair_outOfScope`).
* `lean/OneThird/Step8/Case3Residual.lean:208` — the existing
  `case3Witness_hasBalancedPair_outOfScope` axiom.
* `lean/OneThird/Step8/Case3Enum/W{1,2,3,4}.lean:33` —
  `native_decide` invocations underlying `case3_certificate`.
* `lean/OneThird/Step8/BipartiteEnumGeneral.lean:210` —
  mg-02c2's `bipartite_balanced_enum_general` (the K = 2 closure
  whose `Case2FKGSubClaim` hypothesis the new axiom would
  discharge).
* `lean/OneThird/Step8/LayeredBridges.lean:248` —
  `layeredFromBridges` (singleton-band, `K = Fintype.card α`,
  `w = Fintype.card α + 1`).

## 7. Final state

* No code changes landed. The headline still carries `hC3`.
* This status doc is the deliverable: it records why the
  v6 plan as written cannot land, lists the realisable witnesses
  that exhibit the K ≥ 3 leaf gap, and surfaces the three
  pre-committed pivot options.
* `pc-5f0c` mailed mayor with a pointer to this doc and the
  summary verdict.
* `pc-5f0c` did **not** call `mg done`; the work item remains
  claimed (not completed) pending PM re-decision.
