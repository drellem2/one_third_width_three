# Case3Witness operational-consumption audit (K=2 enum feasibility)

**Work item:** `mg-e0b8`. Daniel directive 2026-05-04T~23:15Z;
PM commission, polecat audit deliverable. **Doc-only, no Lean
source changes, no signature changes proposed beyond the
restated-witness sketch in §4.**

**Verdict (top-of-page).** **AMBER** — the K=2 finite-enum
certificate alone is **not sufficient** to drop `hC3 :
Step8.Case3Witness.{u}` from the headline. The universal
quantifier in `Case3Witness.{u}` is operationally load-bearing
under the headline's current code shape: the invocation goes
through `layeredFromBridges` which forces `K = Fintype.card α`,
so for the realisable headline input `α` of any cardinality
≥ 3 the universal witness is asked at `K_β ≥ 3` (and not just
at `K = 2`). Daniel's hypothesis ("recursion bottoms at K ∈ {1, 2}")
is wrong about the **current** code — `lem_layered_balanced`
short-circuits to `hC3` at K ≥ 2 with no F3 recursion in tree —
and would still be wrong about a hypothetical F3-recursive rewrite,
because irreducible width-3 leaves persist at K ∈ {3, …, 2w+2}
(the F5 C2 profile), not just at K ∈ {1, 2}. See §3.

A signature restatement to `K2RestrictedCase3Witness` would
require companion machinery for the K ≥ 3 leaves; the existing
in-tree route for those leaves goes through
`case3Witness_hasBalancedPair_outOfScope` (project axiom) and
`case3_certificate` (`native_decide` →`Lean.ofReduceBool`), which
is **the same conclusion the v6 audit `mg-5f0c` already
reached** (`docs/a5-g3e-path-c-wiring-v6-status.md`, 2026-04-27).
This audit confirms that conclusion has not been invalidated by
mg-02c2 / mg-c0c7 / mg-84f2 (the compound-automorphism kit) and
adds the reading of `lem_layered_balanced`'s actual K=2 dispatch
shape that Daniel's hypothesis depends on.

---

## 1. Definitions and the question being audited

Headline-level universal witness
(`lean/OneThird/Step8/LayeredBalanced.lean:438-444`):

```lean
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    HasBalancedPair β
```

The headline `OneThird.width3_one_third_two_thirds`
(`lean/OneThird/MainTheorem.lean:52-57`) carries `hC3 :
Step8.Case3Witness.{u}` as a Prop hypothesis; the universal `∀ β`
quantifier ranges over **every** finite width-3 non-chain layered
β with `|β| ≥ 2`, with no restriction on `LB.K`.

The audit question (Daniel 2026-05-04T~23:15Z, in-session):
**at what K values does Case3Witness actually get invoked
operationally?** If the invocations happen only at `K = 2` (e.g.,
because the F3 strong-induction recursion handles K ≥ 3 by
descent into smaller K), then a K2RestrictedCase3Witness
signature shape paired with the K=2 finite-enum certificate would
discharge `hC3` without changing the headline's load-bearing
content.

The audit conclusion is that this picture is **not** the current
code shape (§2), and is also **not** the shape an F3-recursive
rewrite would take (§3): irreducible leaves persist at K ≥ 3.

---

## 2. Call-site inventory

Every operational consumer of `Step8.Case3Witness.{u}` in the
tree (sites that **use** `hC3`, distinct from sites that merely
**thread** it through). All paths terminate at the single `exact`
in `lem_layered_balanced`'s K ≥ 2 branch.

| Site | File:line | Role | K invoked at |
|---|---|---|---|
| `lem_layered_balanced` (K ≥ 2 branch) | `LayeredBalanced.lean:548` | **Sole operational consumer.** `exact hC3 α L hW3 hNotChain' h2` — applies `hC3` to the **input** α at the input's K. | `2 ≤ L.K` (any K ≥ 2 the input carries) |
| `lem_layered_balanced_subtype` | `LayeredBalanced.lean:602` | Threads `hC3` through to a recursive `lem_layered_balanced` call on `L.restrict D.Mid`. | inherits |
| `layered_implies_balanced` | `LayeredBalanced.lean:719` | One-line wrapper around `lem_layered_balanced`. | inherits |
| `mainTheoremInputsOf` | `MainAssembly.lean:238-247` | Threads `hC3` into `caseC` and `decompReductionOrConclude`. | inherits |
| `width3_one_third_two_thirds_assembled` | `MainAssembly.lean:320-339` | Threads `hC3` through `mainAssembly`. | inherits |
| `width3_one_third_two_thirds_via_step8` | `MainAssembly.lean:352-357` | Re-export. | inherits |
| `width3_one_third_two_thirds` | `MainTheorem.lean:52-57` | Headline. Threads `hC3` to `width3_one_third_two_thirds_assembled`. | inherits |

The single call that **applies** `hC3` (rather than threading it)
is `LayeredBalanced.lean:548`, in the K ≥ 2 branch of
`lem_layered_balanced`:

```lean
-- L548 (LayeredBalanced.lean), inside `lem_layered_balanced`:
· -- **Case `K ≥ 2`** (`step8.tex:3084-3122`).
  -- Discharged by the `Case3Witness` ∀-family, which covers every
  -- width-3 non-chain layered β uniformly via F5a-ℓ's
  -- `bounded_irreducible_balanced` dispatch (see `Case3Witness`
  -- docstring).
  exact hC3 α L hW3 hNotChain' h2
```

Note: this is **`α`**, not a sub-poset. The call passes the
**input** layered decomposition `L : LayeredDecomposition α`
directly. There is **no F3 recursion** in `lem_layered_balanced`;
the K = 1 case closes inline via `bipartite_balanced_enum`
(uniform antichain), and the K ≥ 2 case delegates everything to
`hC3` at the original K. The docstring at `LayeredBalanced.lean:482-486`
acknowledges this:

> The `K ≥ 2` branch is discharged by invoking `hC3` on `(α, L)`
> itself: the `Case3Witness` ∀-family covers every width-3 layered
> non-chain β uniformly, so the direct application closes the
> branch with no residual sub-goals. (This **short-circuits the
> F3 recursion at the top call**; the recursion is materialised
> inside `hC3` at discharge time via F5a-ℓ's enumeration
> certificate.)

So the operational K is "whatever the input has". For the headline
path this is governed by `layeredFromBridges`
(`lean/OneThird/Step8/LayeredBridges.lean:248`), which sets

```lean
K := Fintype.card α       -- the singleton-band Szpilrajn assignment
```

— so `K_input = |α|`, ranging from 2 upwards across realisable
headline inputs. Concretely:

* For a 3-element antichain headline input `α`: `K = 3`,
  `w = Lwidth3.bandwidth = |α| + 1 = 4`. `hC3` is invoked at
  `K = 3` (universal at this K).
* For a 4-element width-3 antichain input: `K = 4`, `w = 5`.
  `hC3` is invoked at `K = 4`.
* In general for headline input on `n` elements:
  `hC3` is invoked at `K = n`.

**Daniel's hypothesis ("operational consumption at K=2 only")
is empirically false for the current code** — the universal is
invoked at K = |α| in the headline's actual call path.

---

## 3. Recursion descent — does the operational ask reduce to K ∈ {1, 2}?

### 3a. Current code: no F3 recursion is in `lem_layered_balanced`

The F3 strong-induction framework
`hasBalancedPair_of_layered_strongInduction_width3`
(`LayerOrdinal.lean:472`, mg-a735) **exists in tree** but is
**not used** by `lem_layered_balanced`. The F3 framework requires
the caller to supply an `hStep` argument that closes each
strong-induction step; in the current `lem_layered_balanced`, no
`hStep` is constructed — the K ≥ 2 branch jumps straight to
`hC3`. So in the current tree, the recursion does **not** reduce
the operational K-range; the universal scope of `Case3Witness.{u}`
absorbs the entire K ≥ 2 sub-poset family at one stroke.

### 3b. Hypothetical F3-recursive rewrite: leaves persist at K ≥ 3

If `lem_layered_balanced` were rewritten to use F3, the descent
would be on `|α|` (not on K), via reducible cuts:

* **Reducible step.** When `LayerOrdinalReducible L k` for some
  `1 ≤ k < L.K`, `OrdinalDecompOfReducible` cuts α into
  `Lower ⊔ Upper` (both strictly smaller in `|α|`). Recurse on
  each via the IH; `OrdinalDecomp.hasBalancedPair_lift_lower /
  _upper` (mg-7f06) lifts back to α.
* **Irreducible leaf.** When no `k` is reducible, the leaf must be
  closed by a separate leaf-closer.

Irreducibility is at the **band** level (no `k`-cut exists), not
at the K level. So irreducible leaves can have **any** K; the F5
C2 leaf-closer's profile (`bounded_irreducible_balanced_hybrid`,
`BoundedIrreducibleBalanced.lean:1660`) covers `K ∈ [3, 2w+2]`
with `|α| ≤ 6w + 6` and `w ≥ 1`. So **K ≥ 3 irreducible leaves
are real and persist past F3 descent**:

* **3-antichain witness.** `α` = 3 antichain, singleton-band
  Szpilrajn gives `K = 3`, `w = 4`, `|α| = 3`. Every cut at
  `k ∈ {1, 2}` admits an incomparable cross-pair (any two
  antichain elements). Layered axioms hold (`forced_lt` vacuous
  with `w ≥ |α|`). So this is fully irreducible at `K = 3`.
  `InCase3Scope` is satisfied (`K = 3`, `w = 4`, `|α| ≤ 7`), and
  the leaf is closed by `case3_certificate` — which uses
  `native_decide` → `Lean.ofReduceBool`.

* **4-antichain witness.** `α` = 4 antichain, `K = 4`, `w = 5`,
  `|α| = 4`. Fully irreducible. `InCase3Scope` requires `K = 3`
  — fails. The leaf falls in the `¬ InCase3Scope` branch and is
  closed by `case3Witness_hasBalancedPair_outOfScope` (project
  axiom).

This matches the witness analysis already documented at
`docs/a5-g3e-path-c-wiring-v6-status.md` §2 (`mg-5f0c`, 2026-04-27).
An F3 recursion does not "bottom at K ∈ {1, 2}"; it bottoms at
**irreducible leaves of arbitrary K**, with K ranging up to
`2w + 2`.

### 3c. Status of the K = 2 leaf class (the "named obstruction")

The K = 2 + irreducible + `w ≥ 1` + `|β| ≥ 3` + N-poset class
(`docs/path-c-cleanup-roadmap.md` §5) is a **distinct** subset of
the irreducible-leaf class. Within K = 2:

* **K = 2, w = 0**: `hasBalancedPair_of_K2_w0_incomp`
  (`Case2BipartiteBound.lean:197`) closes via the bipartite
  enumeration. No new infrastructure needed.
* **K = 2, w ≥ 1, NoWithinBandPreceq (= ¬ Case2Witness)**: the
  case-3 / N-poset class. Closed in tree (post option-(δ) park)
  by mg-84f2 + mg-c0c7 + mg-02c2 — `bipartite_balanced_enum_general`
  (`BipartiteEnumGeneral.lean:210`) consumes
  `matching_exists_of_K2_irreducible_noWithinBand` to discharge
  this regime via compound-automorphism + matching.
* **K = 2, w ≥ 1, Case2Witness (within-band ⪯-pair)**: the
  case-2-strict regime. **Open.** Per `mg-a79e` / `mg-b0de` /
  `mg-b666` (Track 1 round 1, 2026-05-04), the
  `Case2FKGSubClaim` hypothesis that
  `bipartite_balanced_enum_general` falls back on for this
  regime is **provably false** in the K = 2 strict case (3-element
  counterexample, `Pr_Q[a < a'] = 1/3`), and the compound-
  automorphism dispatch cannot close it either due to a
  cardinality obstruction (`upper(a) ⊊ upper(a')` rules out any
  order-preserving permutation `σ` with `σ a = a'`).

So even **within K = 2** the closure is partial. The N-poset
(case-3) regime is closed; the case-2-strict residual is the open
component, and as of `mg-b666` (2026-05-04) the path forward is
either A8-S2-cont's cross-poset probability-normalised FKG
(~2000-3500 LoC, multi-polecat) or a math-simp-arc reframing that
bypasses the regime entirely.

---

## 4. Restricted-witness shape proposal (and why it does not suffice alone)

### 4a. The minimal restricted shape, if the ask were K = 2 only

If the operational ask **were** K = 2 only (it isn't — see §2-§3),
the minimal `Prop` that would discharge the K ≥ 2 branch of
`lem_layered_balanced` after a K = 2-restricting rewrite would be:

```lean
def K2RestrictedCase3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    LB.K = 2 →                           -- <- the new constraint
    HasBalancedPair β
```

This is **only** the change we have authority to propose under PM
+ Daniel review per `feedback_signature_regressions`; the audit
does not implement it. A more aggressive variant (e.g.,
restricting `LB.w ≥ 1` and `LayerOrdinalIrreducible LB`) would
match `bipartite_balanced_enum_general`'s consumer profile more
tightly but bake more dispatch decisions into the witness shape.

### 4b. Why the restricted shape does not suffice alone

Substituting `K2RestrictedCase3Witness` for `Case3Witness.{u}` in
the headline requires **simultaneously**:

1. **Rewriting `lem_layered_balanced`** to do F3 recursion
   explicitly (mg-a735's framework + reducible-step descent +
   leaf dispatch), so that the K = 2 leaf is the only one routed
   through the restricted hypothesis.
2. **Closing K ≥ 3 irreducible leaves** without consuming the
   restricted hypothesis. The existing in-tree route is via
   `case3Witness_hasBalancedPair_outOfScope` (project axiom,
   `Case3Residual.lean:208`) for `¬ InCase3Scope` and
   `case3_certificate` (uses `native_decide`,
   `Case3Enum/W{1,2,3,4}.lean:33`) for `InCase3Scope`.
3. **Closing K = 1 leaves** inline (trivial via
   `bipartite_balanced_enum`).

Even if (1) is in scope and (3) is mechanical, (2) reintroduces
the existing project axiom + `Lean.ofReduceBool` to the headline's
`#print axioms` set, **swapping `hC3` for two axioms**. This is
the v6 conclusion (`mg-5f0c`, 2026-04-27): the planned 5-axiom
target inflates to 7 axioms.

Further, the K = 2 leaf itself (the "actual ask" of
`K2RestrictedCase3Witness`) is **not** unconditionally closed
in tree:

* The case-3 / N-poset sub-regime (K = 2, w ≥ 1,
  NoWithinBandPreceq, |β| ≥ 3) **is** closed by
  `bipartite_balanced_enum_general`.
* The case-2-strict sub-regime (K = 2, w ≥ 1, Case2Witness
  within-band ⪯-pair) **is open** with no in-tree closure path
  (per `mg-b666`, 2026-05-04). The K = 2 finite-enumeration alternative
  (path-c-cleanup-roadmap.md §6b, ~300-500 LoC for a Bool
  certificate over K = 2 / |α| ≤ 6 / w ∈ {1,…,4}) would close
  the strict case structurally, but is the substantive new math
  Daniel's hypothesis presupposes already exists.

So even granted (1)–(3), `K2RestrictedCase3Witness` itself
cannot be discharged from in-tree machinery. The restricted shape
is a **sound** restatement of what the K = 2 leaf needs, but
**not** a discharge: it remains a hypothesis-shaped Prop until the
case-2-strict residual is closed (Track 1 obstruction or A8-S2-cont
infrastructure or math-simp arc 2.0 reframing).

---

## 5. Verdict — AMBER

**AMBER.** The K=2 finite-enum certificate is **not sufficient
alone** to drop `hC3` from the headline. Three independent
gaps must close in concert; closing only the K = 2 piece leaves
two of them open.

### 5a. Why not GREEN

Three independent obstructions, each load-bearing for the headline
discharge:

1. **Operational scope mismatch** (this audit's primary finding).
   The current code invokes `hC3` at `K = |α|` via
   `layeredFromBridges`, not at K = 2. A K = 2-restricted witness
   would not type-check at the call site without a code rewrite.
   Daniel's "recursion bottoms at K ∈ {1, 2}" is wrong about both
   (a) the current code shape (no F3 recursion in
   `lem_layered_balanced`) and (b) any hypothetical F3-recursive
   rewrite (irreducible leaves persist at K ∈ [3, 2w + 2]).
2. **K ≥ 3 leaf coverage** (re-confirmation of `mg-5f0c`'s v6
   conclusion). Even granted an F3-recursive rewrite, the K ≥ 3
   irreducible leaves require either
   `case3Witness_hasBalancedPair_outOfScope` (project axiom) or
   `case3_certificate` (`Lean.ofReduceBool` via
   `native_decide`). The K = 2 enum certificate does not address
   these leaves.
3. **K = 2 case-2-strict residual** (re-confirmation of `mg-b666`
   Track 1 round 1). Even within K = 2, the case-2-strict regime
   is open: `Case2FKGSubClaim` is provably false per `mg-a79e`,
   and compound-automorphism cannot extend per `mg-b666`'s
   cardinality obstruction.

### 5b. Why not RED

The universal-quantifier reading is **not load-bearing in
principle** — the universal scope of `Case3Witness.{u}` is a
modelling choice that absorbs the F3 recursion into the
hypothesis. A signature restatement to a non-universal shape is
mathematically possible (and mechanically natural after a rewrite
of `lem_layered_balanced`), provided the K ≥ 3 and K = 2
case-2-strict gaps are closed by other means. The route is the
one already documented in `docs/path-c-cleanup-roadmap.md` §6c,
just gated behind work that has been parked since 2026-04-27 and
re-blocked on 2026-05-04.

The verdict could decay to RED if a future reading were to
establish that a K=2-restricted (or any non-universal) witness
shape **inherently** loses information that the dispatch consumes
elsewhere — e.g., if some currently-elided sub-poset visit
required the universal scope in a structural way. This audit
finds no such use; the universal scope is purely the F3-recursion
proxy it is documented to be.

### 5c. What additional work would close the gap beyond K = 2

The audit recommends **not** opening implementation work on
K2RestrictedCase3Witness in isolation. The minimum bundle that
closes `hC3` is, per `mg-5f0c` §5 + this audit:

* **K = 2 closure for case-2-strict** (the open piece). Either
  (a) A8-S2-cont's cross-poset probability-normalised FKG
  (~2000-3500 LoC, multi-polecat per `docs/a8-s2-status.md` §5),
  (b) the K = 2 finite-enumeration alternative
  (`docs/path-c-cleanup-roadmap.md` §6b, ~300-500 LoC), or (c) a
  math-simp arc 2.0 reframing that bypasses the case-2-strict
  regime entirely.
* **F3 step proof** (`hStep` for
  `hasBalancedPair_of_layered_strongInduction_width3`), with
  K = 1 / K = 2 / K ≥ 3 dispatch. ~150-250 LoC (`mg-072c` /
  `mg-0fa0` planned scope).
* **Acceptance of the existing
  `case3Witness_hasBalancedPair_outOfScope` axiom** plus the
  `Lean.ofReduceBool` contribution from `case3_certificate` as
  the K ≥ 3 leaf closure. **No new project axioms** beyond what
  is already disclosed in `lean/AXIOMS.md`.
* **Headline rewrite**: drop `hC3`, rewrite `lem_layered_balanced`
  to invoke F3 explicitly, prove `Case3Witness` (the def, now
  promoted) as a theorem composing the leaf closures. ~30-50 LoC.

Total scope estimate: **~480-700 LoC + the case-2-strict closure
(scope dependent on route)**, on top of the ~1400 LoC already
landed across mg-9568 / mg-7f06 / mg-a735 / mg-27c2 / mg-2e58 /
mg-26bb / mg-84f2 / mg-c0c7 / mg-02c2.

The K = 2 finite-enumeration certificate alone (without the
F3 step proof, without the K ≥ 3 axiom acceptance, without
the headline rewrite) is **not** the residual gap; it is one
component of a larger bundle.

---

## 6. Cross-references and load-bearing claims

* **`lean/OneThird/Step8/LayeredBalanced.lean:438-444`** —
  `Case3Witness.{u}` def (universal in K).
* **`lean/OneThird/Step8/LayeredBalanced.lean:548`** — sole
  operational `exact hC3 …` call site, in the K ≥ 2 branch
  (applies `hC3` to the input α, no recursion).
* **`lean/OneThird/Step8/LayeredBridges.lean:248`** —
  `layeredFromBridges` with `K := Fintype.card α` (forces
  `K = |α|` at the headline path's input to `lem_layered_balanced`).
* **`lean/OneThird/Step8/LayerOrdinal.lean:472`** — F3
  framework `hasBalancedPair_of_layered_strongInduction_width3`
  (mg-a735), in tree but **not used** by
  `lem_layered_balanced`.
* **`lean/OneThird/Step8/BipartiteEnumGeneral.lean:210`** —
  `bipartite_balanced_enum_general` (mg-02c2), the K = 2
  three-way dispatch. Consumes `Case2FKGSubClaim`
  (provably false in the strict case per mg-a79e).
* **`lean/OneThird/Step8/CompoundMatching.lean:663`** —
  `matching_exists_of_K2_irreducible_noWithinBand` (mg-c0c7);
  closes the case-3 / N-poset sub-regime within K = 2.
* **`lean/OneThird/Step8/Case2BipartiteBound.lean:197`** —
  `hasBalancedPair_of_K2_w0_incomp`; closes K = 2, w = 0.
* **`lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1660`**
  — `bounded_irreducible_balanced_hybrid` (`3 ≤ L.K`).
* **`lean/OneThird/Step8/Case3Residual.lean:208`** —
  `case3Witness_hasBalancedPair_outOfScope` axiom (`3 ≤ L.K`).
* **`docs/a5-g3e-path-c-wiring-v6-status.md`** (mg-5f0c,
  2026-04-27) — the prior round's audit reaching the same
  conclusion (5-axiom target infeasible; honest minimum is 7
  axioms or substantively new math).
* **`docs/path-c-cleanup-roadmap.md`** (mg-7261, 2026-04-27) —
  option-(δ) park deliverable; §6 lays out the structural and
  finite-enumerator routes.
* **`docs/path-c-track-1-status-1.md`** (mg-b666, 2026-05-04) —
  Track 1 round 1 block-and-report; case-2-strict residual cannot
  close via compound-automorphism due to cardinality obstruction.

The audit found **no contradiction** with arc 1.0, 2.0, 3.0, or
Track 1 status docs. This audit's finding is consistent with v6
+ Track 1 round 1: the universal scope is operationally
load-bearing in the headline path (`K = |α|`), the K = 2 enum
addresses one component of the larger gap (and even that
component is partial — case-2-strict is open within K = 2), and
a K2-restricted signature restatement does not by itself
discharge `hC3`.

---

## 7. Recommendation

**Do not open implementation work on `K2RestrictedCase3Witness`
in isolation.** The audit re-confirms the option-(δ) park
decision and the `mg-b666` Track 1 round 1 block; the headline
should retain `hC3` until either (a) A8-S2-cont's FKG
infrastructure lands and discharges `Case2FKGSubClaim`
constructively, (b) a K = 2 finite-enumeration certificate is
built that bypasses the chain-form FKG sub-claim entirely
(option (α) in `path-c-cleanup-roadmap.md` §6b — and even that
needs to handle the case-2-strict regime, which the existing
mg-02c2 dispatch routes through `Case2FKGSubClaim`), or (c) a
math-simp arc reframing (Track 2) bypasses the regime.

This audit's deliverable is this document. No Lean source
changes were proposed or implemented. The signature restatement
sketch in §4a is for PM + Daniel review only and not for
implementation under the current park decision.
