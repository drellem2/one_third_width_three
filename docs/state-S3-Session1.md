# State — S3 — Session 1: Step 3 port — `lem:local-sign` orientation lemma + the coherence definition

**Ticket:** mg-7a22 (OneThird-S3: Step 3 Lean port — local-sign
orientation lemma plus the coherence definition).
**Branch:** `polecat-mg-7a22`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.1 Piece 1,
Wave-2.
**Depends:** mg-0868 (S2-B, `prop:per-fiber` + `thm:step2`); merged.

**Scope.** Wave-2 ticket of the Piece-1 (Steps 1-6 cascade port)
decomposition.  Ports `step3.tex` `lem:local-sign` (the local-sign
orientation normalization) and `def:coherent` (the coherence
definition), grounded on the Step 2 staircase output, completing the
Step 3 coherence framework Step 4 consumes.

---

## §0. Verdict — **GREEN-S3-delivered**

`lean/OneThird/Step3/LocalSignGrounded.lean` (NEW, ~503 LoC) delivers,
building on the abstract Step 3 scaffold (`Step3.LocalSign`,
`Step3.CommonAxes`, `Step3.Step3Theorem`) and the S2-B grounded
output (`Step2.PerFiberGrounded2`):

* `gridBot` / `gridBot_lt` — a strict lower bound below every
  `j`-coordinate of a grid `D`;
* `plusThreshold` / `plusThreshold_antitone` / `le_plusThreshold_of_mem`
  / `mem_of_le_plusThreshold` — the decreasing column-threshold
  function reading a product-order lower set off as a
  `step3.tex` `def:staircase-type` staircase;
* `isStaircasePlus_iff_isStaircaseType_false` — **the bridge**:
  `WeakGrid.IsStaircasePlus D M` (the literal output type of the S2-B
  `prop_per_fiber_staircase` / `thm_step2`) is *exactly* an
  `IsStaircaseType false D M` staircase (decreasing-threshold, paper
  `σ = -1`);
* `coordinateStrip_of_both_types` — **the substantive content of
  `lem:local-sign`(i)**: a staircase that carries *both* signs *is* a
  coordinate strip.  The abstract `LocalSign.lean` proved only the
  easy `(⇐)` half (`coordinateStrip_has_both_types`) and explicitly
  deferred this `(⇒)` half to the paper.  This port closes it — and
  with a cleaner argument than the paper's (no order-convexity of `D`
  needed; see §2);
* `isStaircaseType_both_iff_coordinateStrip` — the full
  `lem:local-sign`(i) equivalence;
* `localSign_unique` — `lem:local-sign`(i) uniqueness: off the
  coordinate strips the local sign is uniquely determined;
* `lem_local_sign` — **`lem:local-sign` (grounded)**: every Step 2
  staircase `IsStaircasePlus D M` has a local sign (`σ = false`), and
  off the coordinate strips it is the unique type;
* `etaOfDir` / `etaOfDir_e1` / `etaOfDir_neg_e1` / `etaOfDir_neg_ne`
  / `etaOnState` — **`def:eta`** (`step3.tex:626`): the per-state
  local sign `η_{x,y}(L)` *defined from the geometry* — the sign of
  the common axis against `positiveCone σ`.  The abstract
  `Step3Theorem.lean` carried `η` as a *black box*; this port pins it
  to the local sign and the common axis, and proves the
  well-definedness clause (`etaOfDir_neg_ne`: exactly one of `±e` is
  in the positive cone);
* `CoherentPair` / `IncoherentPair` — **`def:coherent`** grounded with
  the `def:eta` `η`;
* `coherence_correlation_grounded` / `incoherentPair_correlation_le`
  / `coherentPair_correlation_ge` — `prop:correlation` grounded with
  the `def:eta` `η`;
* `sampleGrid` / `sampleStaircase` / `sampleStaircase_isStaircasePlus`
  / `sampleStaircase_not_coordinateStrip` — a concrete genuinely
  two-dimensional non-coordinate-strip staircase;
* `localSign_coherence_grounded_nonvacuous` — the mg-7a22 acceptance
  witness.

`lake build OneThird.Step3.LocalSignGrounded` is clean (exit 0).
`lake build OneThird` (full library) is clean.  The new file produces
**no warnings** (the warnings the toolchain still emits are all on
pre-existing files — `Step2/PerFiberGrounded.lean`,
`Step6/ErrorControl.lean` — unchanged here).

**No `sorry`, no new axiom.**  `#print axioms` confirms
`coordinateStrip_of_both_types`, `isStaircasePlus_iff_isStaircaseType_false`,
`lem_local_sign`, `localSign_unique`, `coherence_correlation_grounded`
and `localSign_coherence_grounded_nonvacuous` all depend on exactly
`[propext, Classical.choice, Quot.sound]` — the three standard mathlib
axioms, no `sorryAx`, no project axiom.

---

## §1. What `lem:local-sign` says, and how the port grounds it

`step3.tex` `lem:local-sign` has three parts.

**Existence.**  The Step 2 staircase `M_{x,y}` has *some* type
`σ ∈ {±1}`.  Grounded: the S2-B output is
`WeakGrid.IsStaircasePlus D M` — `M` is a product-order lower set of
`D`.  `isStaircasePlus_iff_isStaircaseType_false` identifies that with
`IsStaircaseType false D M` (the column-threshold staircase notion of
`step3.tex` `def:staircase-type`, `σ = -1`).  So the local sign of a
Step 2 staircase is concretely `σ = false`.

**(i) Structural uniqueness.**  If `M ∉ {∅, D}` and `M` is not a
*coordinate strip* `D ∩ {j ≤ h}`, then `σ` is uniquely determined.
Equivalently (the form ported): `M` carries both signs ⟺ `M` is a
coordinate strip.  The `(⇐)` half (a strip carries both signs) was
already in `LocalSign.lean` (`coordinateStrip_has_both_types`); this
port closes the substantive `(⇒)` half
(`coordinateStrip_of_both_types`).  `localSign_unique` is the
contrapositive operative form, and `lem_local_sign` packages
existence + uniqueness off the strips, consuming an `IsStaircasePlus`
directly.

**(ii) Quantitative uniqueness.**  An `η₀`-robust version of (i): a
staircase `η₀`-far from every coordinate strip keeps its type under
`η₀|D|`-perturbations.  This is the quantitative refinement of (i)
(`step3.tex` proof block "Quantitative uniqueness (G1.1)", the
spread-bound / Markov argument).  **Faithfully scoped out of this
ticket** — see §4.

The **strip-degeneracy remark** (`rem:strip-degeneracy`) is the
recorded exception: on a coordinate strip both signs are valid, by
`coordinateStrip_has_both_types`.

---

## §2. The structural-uniqueness proof is cleaner than the paper's

`step3.tex`'s proof of `lem:local-sign`(i)`(⇒)` (`step3.tex:128-194`)
threads order-convexity of `D` through a diagonal change of variables
and an "active columns" analysis.  The Lean port
`coordinateStrip_of_both_types` needs **no order-convexity of `D`**:

> Given `f` increasing and `g` decreasing both witnessing `M` on `D`,
> take `h := max {p.2 : p ∈ M}`, attained at some `q ∈ M`.  For any
> `p ∈ D` with `p.2 ≤ h = q.2`: if `q.1 ≤ p.1`, the increasing `f`
> gives `p.2 ≤ q.2 ≤ f(q.1) ≤ f(p.1)`, so `p ∈ M`; if `p.1 ≤ q.1`,
> the decreasing `g` gives `p.2 ≤ q.2 ≤ g(q.1) ≤ g(p.1)`, so `p ∈ M`.
> Hence `M = D ∩ {j ≤ h}`.

This works for *any* finite `D` (the empty `M` is the strip at
`gridBot D`).  Order-convexity is a Step-1 chart property `D` does
carry, but the structural-uniqueness fact does not need it; the
direct finite argument is shorter and stronger.

---

## §3. `def:eta` + `def:coherent` — grounding the floating `η`

The abstract `Step3Theorem.lean` carries `Coherent` / `Incoherent` /
`correlation_card_identity` for a **black-box** `η : γ → Sign`.  That
left the coherence predicate floating: `η` could be anything.

This port **defines `η` from the geometry** (`def:eta`):
`etaOfDir σ e` is `+1` iff the grid direction `e` lies in
`positiveCone σ`, and `etaOnState σ a L := etaOfDir σ (a L)` reads
the per-state sign off the common axis `a(L)`.  `etaOfDir_neg_ne`
proves the `step3.tex:644-647` well-definedness clause: exactly one of
`±e` lies in the positive cone, so `η` is a genuine `{±1}` choice.

`CoherentPair` / `IncoherentPair` then re-package the
`Step3Theorem.lean` coherence predicates with this grounded `η`, and
`coherence_correlation_grounded` re-exports `prop:correlation`.  The
full chain `σ` (`lem_local_sign`) → `η` (`etaOnState`) → coherence
(`CoherentPair`) is now grounded; Step 4's two-interface
incompatibility lemma consumes it.

---

## §4. Scope boundary (honest)

This ticket ports `lem:local-sign` existence + structural uniqueness
(i) and `def:eta` + `def:coherent` + `prop:correlation`, all grounded,
0-sorry, no new axiom.  Out of scope, faithfully so:

* **`lem:local-sign`(ii), quantitative uniqueness.**  The `η₀`-robust
  refinement of (i) (the `step3.tex` "Quantitative uniqueness (G1.1)"
  spread-bound / Markov argument).  Not ported here.  Rationale: (a)
  the abstract Step 3 scaffold (`LocalSign.lean`) omitted it entirely;
  (b) structural uniqueness (i) — *delivered in full here, including
  the `(⇒)` half the scaffold deferred* — already makes `σ`
  well-defined on the generic two-dimensional stratum, which is what
  the coherence framework needs to type-check and instantiate
  non-vacuously; (ii) is a quantitative robustness statement, not a
  well-definedness prerequisite.  It is **not ill-posed** — it is a
  genuine quantitative lemma — so this is honest scoping, not a
  block-and-report.  A follow-on may port it (the spread-bound
  argument is self-contained, no further dependencies).
* **`lem:common-axes` / `thm:canonical-orientation` / `lem:eta-theta`
  / `thm:step3`.**  These are the *rest* of `step3.tex` (§§4-8); they
  already exist in abstract form (`CommonAxes.lean`,
  `Step3Theorem.lean`).  This ticket's scope is the two named
  deliverables — `lem:local-sign` and `def:coherent` — not the whole
  Step 3 grounding.

The abstract Step 3 files (`LocalSign.lean`, `CommonAxes.lean`,
`Step3Theorem.lean`) are **unchanged**; `LocalSignGrounded.lean` is
purely additive and reuses their `Sign` / `IsStaircaseType` /
`IsCoordinateStrip` / `positiveCone` / `Coherent` / `Incoherent` /
`correlation_card_identity` API.

---

## §5. Non-vacuity (mg-7a22 acceptance bar)

`localSign_coherence_grounded_nonvacuous` instantiates the framework
at the concrete width-3 non-chain poset `Antichain3`:

* **(local sign)** `lem_local_sign` fires on `sampleStaircase ⊆
  sampleGrid` — an `L`-shaped staircase inside the `2×2` grid
  `{0,1}²` that is genuinely two-dimensional: `Nonempty`, *not* the
  full grid, and *not* a coordinate strip
  (`sampleStaircase_not_coordinateStrip`).  So `lem:local-sign`'s
  structural uniqueness applies *non-vacuously* — `σ = false` is
  pinned as the unique type, not a degenerate both-signs case;
* **(`def:eta`)** the per-direction sign is genuinely two-valued:
  `etaOfDir σ (1,0) ≠ etaOfDir σ (-1,0)` for every `σ`;
* **(coherence)** the dichotomy fires on a genuine overlap
  `Ωreg := (univ : Finset (LinearExt Antichain3))` with
  `2 ≤ |Ωreg|` (`Antichain3.two_le_numLinExt`): the two `def:eta`
  sign functions built from axes `(1,0)` / `(-1,0)` disagree on *all*
  of `Ωreg`, witnessing an `IncoherentPair`, and the grounded
  `prop:correlation` evaluates the correlation sum to `-|Ωreg|`.

No `Subsingleton`-on-empty baseline: `Antichain3` is genuinely
width-3 and non-chain (`Antichain3.hasWidth`,
`Antichain3.not_isChainPoset`); the grid, the staircase, and the
overlap are all non-degenerate.  (Consistent with the S2-A/S2-B
witnesses, which likewise exercised grid-level lemmas at a genuine
`2×2` grid alongside the `Antichain3` poset facts.)

---

## §6. Files

* `lean/OneThird/Step3/LocalSignGrounded.lean` — NEW (~503 LoC).
* `lean/OneThird.lean` — +1 import line.
* `docs/state-S3-Session1.md` — this file.
