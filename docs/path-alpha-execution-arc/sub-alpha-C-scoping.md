# Path α sub-C scoping — Hibi polytope chamber infrastructure for FKG-on-LE (long arc)

**Polecat.** mg-91be (cat-mg-91be).
**Date.** 2026-05-07.
**Branch.** `polecat-p91be` → `a8-s2-cont-execution-arc`.
**Predecessors.**
- mg-bb74 (`73ed85e`) — `lean/AXIOMS.md` framing refresh post-Path-α-RED.
- mg-21a4 (`f862b76`) — sub-α-A scoping (RED).
- mg-dc9d (`a95020e`) — Hibi-1 STOP (`(L(α), ≤_τ)` not distributive).
- mg-b10a (`256f0da`) — A8-S2-cont-4 STOP (FKG-on-LE obstruction
  surfaced).

**Verdict.** **AMBER leaning GREEN.** A critical path of 6–10
load-bearing primitives is enumerated below with explicit Lean
signatures, mathlib-PR-class vs project-internal categorisation, and
per-session polecat estimates. The aggregate is consistent with
state.md §4.2's "2000–4000 LoC + 1450–2700 LoC" working figure for the
long arc, with clearly identified upstream-PR leverage points where
Daniel input could shorten the path. **Three structural unknowns**
keep the verdict short of GREEN: (i) whether mathlib's continuous
FKG/Ahlswede–Daykin needs to be ported or can be discretised, (ii)
whether Stanley log-supermodularity admits a clean combinatorial
proof avoiding Aleksandrov–Fenchel, and (iii) whether the level-`k`
localisation step admits a direct formulation on `J(α)` with a
tilted measure (Path B) or genuinely requires the geometric polytope
(Path A). PM is asked to file the Stanley log-supermodularity port
(EX-1, §6) as the first execution ticket — it is load-bearing for
both Path A and Path B and is the most isolatable mathlib-friendly
chunk. The Path-A-vs-Path-B fork can be re-evaluated after EX-1
lands.

This document is the latex-first deliverable per
`feedback_latex_first_for_math_simp` and per the polecat brief §3.
No Lean source touched.

---

## §1 Read these first

This document assumes the reader has read, in order:

1. `docs/path-alpha-execution-arc/state.md` — the cumulative state
   doc. **§1.3** (Birkhoff distributive lattice on `LowerSet α`),
   **§1.4** (existing product-lattice FKG-on-LE pathway with
   `(2^{|J(α)|})^{n+1}` factor), **§1.5** (Stanley
   log-supermodularity in literature), **§1.6** (sub-α-A RED
   counterexample), **§1.7** (drops `R` is non-level), **§4.2**
   (sub-α-C high-level shape).
2. `docs/path-alpha-execution-arc/sub-alpha-A-scoping.md` (mg-21a4) —
   why per-level FKG between two level-`k` pullbacks fails and why
   even hypothetical fix would not solve drops.
3. `docs/a8-s2-cont-execution-arc/cont-4-stop-report.md` (mg-b10a) —
   §3.2 lattice candidate enumeration, §3.3 product-factor exponential
   blow-up, §6 path γ recommendation.
4. `docs/path-alpha-execution-arc/hibi-1-stop-report.md` (mg-dc9d) —
   §2 S₃ hexagon counterexample, §6 sub-α-A vs -B vs -C re-scoping
   options.
5. **In-tree Lean infrastructure already verified:**
   - `lean/OneThird/Mathlib/LinearExtension/Birkhoff.lean` —
     `LinearExt α ≃ IdealChain α` Birkhoff bijection.
   - `lean/OneThird/Mathlib/LinearExtension/FKG.lean:452`
     (`fkg_uniform_initialLowerSet`) — the lossy product-lattice
     pathway.
   - `lean/OneThird/Mathlib/RelationPoset/FKG.lean:325, :464` — data
     versions and the counting-only `probLT'_mono_of_relExt`.

The cumulative-state-doc tactic
(`feedback_polecat_cumulative_state_doc`) applies: state.md is the
single source of truth and is updated as part of this deliverable
(see §10).

---

## §2 What sub-α-C is — overview

Sub-α-C is the project plan for **building enough Hibi polytope
chamber infrastructure in Lean to enable an FKG-on-LE inequality with
`numLinExt α`-sized normalisation factor**, replacing the lossy
`(2^{|J(α)|})^{n+1}` factor of the existing product-lattice pathway.
The output primitive — `probEvent'_mono_of_subseteq_upClosed`
(state.md §1.7's "drops headline") — closes the FKG-on-LE gap shared
by both `case3Witness_hasBalancedPair_outOfScope` and
`brightwell_sharp_centred`. This is the **only known route** to full
formalisation (axiom-elim of both project axioms; trust surface =
mathlib + native_decide), per the cumulative state of the Path α arc
(state.md §3.1, §4.2).

### §2.1 Mathematical foundation (Stanley 1986; Hibi 1985; Brightwell 1999)

Let `α` be a finite poset with `n = |α|`, and let `J(α)` denote its
lattice of order ideals (lower sets); `J(α)` is the finite
distributive lattice given by Birkhoff's theorem.

* **Order polytope.** `O(α) := { f : α → [0,1] | f order-preserving }
  ⊆ ℝ^α`, the polytope of order-preserving maps `α → [0,1]`.

* **Stanley vertex theorem [Stanley 1986, Theorem 1.2].**
  The vertices of `O(α)` are exactly the indicator functions
  `1_I : α → {0,1}` for `I ∈ J(α)`.

* **Chamber decomposition [Stanley 1986, §3].** For each
  `L ∈ L(α)`, define the chamber simplex
  `σ_L := { f ∈ O(α) | f(L^{-1}(0)) ≤ f(L^{-1}(1)) ≤ ⋯ ≤ f(L^{-1}(n-1)) }`
  (where `L^{-1}(i)` is the element placed at position `i` by `L`).
  Then:
  - `O(α) = ⋃_{L ∈ L(α)} σ_L`,
  - `σ_L ∩ σ_{L'}` has Lebesgue measure zero for `L ≠ L'`,
  - each `σ_L` is a unimodular simplex of volume `1/n!`,
  - hence `Vol(O(α)) = |L(α)| / n!`.

* **Stanley log-supermodularity [Stanley 1981].** The function
  `e : J(α) → ℕ`, `e(I) := |L(α[I])|` (the number of linear
  extensions of the sub-poset on `I`), is **log-supermodular**:
  `e(I) · e(J) ≤ e(I ∪ J) · e(I ∩ J)` for all `I, J ∈ J(α)`.
  Stanley proves this via the Aleksandrov–Fenchel inequality on mixed
  volumes of order polytopes; combinatorial proofs exist (Daykin
  1990; Bjorner 1989) but are lengthy.

* **Daykin–Saks drops [Daykin–Saks 1981, Theorem 1; Brightwell
  1999, §4].** For `Q ⊆ Q'` finite posets on the same vertex set
  (Q' adds at least one comparability), level `k`, and an up-closed
  event `A ⊆ J(α)`:
  `Pr_{L ∼ Unif L(Q)}[L_k ∈ A] ≤ Pr_{L ∼ Unif L(Q')}[L_k ∈ A]`.
  The classical proof uses the chamber decomposition + continuous
  FKG/Ahlswede–Daykin on the cube `[0,1]^α`.

The **drops headline** in state.md §1.7 is the `Q.Subseteq Q'`
counting-form rearrangement of this inequality, which the case3-port
and Brightwell-port both consume.

### §2.2 Why this is the only remaining route to full formalisation

Per state.md §3 and mg-21a4 §3:

* **Sub-α-A** (per-level FKG without LE lattice) is RED — concrete
  counterexample on the discrete 3-antichain.
* **Sub-α-B** (width-2 reduction) is RED — case3 application is
  intrinsically width-3.
* **Path β** (reformulate case3 to avoid drops) is blocked at math
  level (mg-75ef, mg-5bf9).
* **Path γ** (retain axioms) is the recommended status-quo, but
  Daniel has explicitly directed pursuing the long arc to full
  formalisation: *"don't hold off on long arcs if they're still the
  highest value path to full formalization"* (2026-05-07T16:06Z,
  saved to `feedback_long_arcs_are_pm_authority.md`).

Sub-α-C is **necessary** for axiom-elim of either
`case3Witness_hasBalancedPair_outOfScope` or `brightwell_sharp_centred`.
It is **shared infrastructure** between the two; closing both is
roughly the same workload as closing one (state.md §4.2 / mg-b10a §6).

### §2.3 Why the existing product-lattice pathway is insufficient

The in-tree `fkg_uniform_initialLowerSet` (FKG.lean:452) gives
`(2^{|J(α)|})^{n+1}` as the FKG normalisation factor. For width-3
posets of size `n`, `|J(α)|` can grow up to `n^2 / 4` (see Stanley
EC1, §3.5), so the factor is doubly-exponential in `n`. The drops
application requires `numLinExt α`, which is at most `n!`.

Bridging this gap **inside the existing pathway is mathematically
impossible**: the product-lattice FKG is tight, and tightening
requires either (a) replacing the carrier with a direct
distributive-lattice structure on `LinearExt α` (which doesn't exist
— mg-dc9d) or (b) replacing the *measure* with one that captures
the correct level-`k` weighting (which is the Hibi/chamber path
described here).

---

## §3 Verified mathematical context

State.md §1 already verifies: Birkhoff distributivity of `LowerSet α`
(§1.3), the existing product-lattice pathway (§1.4), Stanley
log-supermodularity in literature (§1.5), sub-α-A counterexample
(§1.6), drops `R` non-level (§1.7). Sub-α-C builds on the same
mathematical footing. Three additional verified facts established
during this scoping:

### §3.1 Stanley vertex theorem and chamber decomposition stand independently of distributivity issues on `LinearExt α`

State.md §1.2 records that no canonical lattice on `LinearExt α` is
distributive. This is a fact about lattice structures on
`LinearExt α`. It does **not** affect the chamber decomposition,
which lives in `O(α) ⊆ ℝ^α` and uses `LinearExt α` only as an
**index set** for chambers. The chambers `σ_L` form a partition (up
to measure zero), not a lattice; their geometric union is the order
polytope `O(α)`, which is convex and therefore well-behaved.

This is not a re-litigation of mg-dc9d's STOP — it is a
clarification that the structural obstruction RED'ing the τ-inversion
lattice does **not** RED the chamber path. Confirmed by hand on the
discrete 3-antichain (`α = {a,b,c}`, six chambers, hexagonal Hasse
of inversion sets but unrelated cube tessellation):

* `O(α) = [0,1]^3` (no order constraints since α is discrete).
* Six chambers, each a simplex of volume `1/6 = 1/3!`. ✓
* Total volume `= 6 · 1/6 = 1 = 6/3! = |L(α)|/n!`. ✓
* Vertices `{0,1}^3 = 2^3 = 8 = |J(α)|`. ✓

Stanley vertex theorem and chamber decomposition both verify on this
canonical width-3 instance.

### §3.2 Stanley log-supermodularity ⟹ `μ(I) := e(I)·e(α\I)` is log-supermodular on `J(α)`

This is mg-21a4 §1.5 (cited from Stanley 1981). For completeness:

```
μ(I) μ(J) = e(I) e(J) · e(α\I) e(α\J)
        ≤ e(I∪J) e(I∩J) · e((α\I)∪(α\J)) e((α\I)∩(α\J))   [Stanley + dual]
        = e(I∪J) e(I∩J) · e(α\(I∩J)) e(α\(I∪J))            [De Morgan]
        = μ(I∪J) μ(I∩J).
```

So **mathlib's `fkg`** applies to `(J(α), μ)`. The catch (mg-21a4
§3.2): the resulting inequality sums over **all levels** of `J(α)`,
not at a fixed level `k`. Localising to level `k` is the substantive
remaining work (and is exactly what the chamber decomposition
provides geometrically: the level-`k` event corresponds to a
hyperplane slice `t_(k) = const` of the cube `[0,1]^α`, where `t_(k)`
is the `k`-th order statistic of `f`).

### §3.3 The drops headline reduces to a continuous FKG/AD on the cube

By the chamber decomposition, for `Q ⊆ Q'` and an up-closed event
`A ⊆ J(α)`:

```
Pr_Q[L_k ∈ A] = ∑_{L ∈ L(Q)} 1_{L_k ∈ A} / |L(Q)|
              = ∫_{O(Q)} 1_{L_f,k ∈ A} df / Vol(O(Q))
```

where `L_f` is the linear extension assigned to the chamber
containing `f`, and `df` is Lebesgue measure on `[0,1]^α`. Since
`O(Q') ⊆ O(Q)` (Q' has more constraints) and `1_{L_k ∈ A}` is
**monotone in `f`** (if `f' ≥ f` componentwise and `f` has
`L_f,k ∈ A`, then so does `f'`; sketch: changing `f → f'`
componentwise upward can only push the level-`k` ideal upward in
`J(α)`, which preserves up-closedness), continuous FKG/AD on the
cube gives positive correlation between `1_{O(Q')}` and
`1_{L_k ∈ A}`, yielding the drops.

This is the standard Brightwell §4 / Daykin–Saks 1981 argument. The
continuous FKG/Ahlswede–Daykin on `[0,1]^n` is (per
`Mathlib.Analysis.MeanInequalities` and adjacent files) **not in
mathlib in the form needed** — see §5.5.

---

## §4 The two paths within sub-α-C

Sub-α-C admits two complementary execution paths. PM recommends
Path A as primary, with Path B as parallel investigation; the
Path-A-vs-Path-B fork is best re-evaluated after the Stanley
log-supermodularity port (EX-1) lands.

### §4.1 Path A — full geometric chamber decomposition

Directly port the Hibi/Stanley order polytope, chamber decomposition,
and continuous FKG. Most faithful to the literature, with the largest
mathlib-PR-class footprint.

* Order polytope `O(α)` as a Lean type (a convex subset of
  `α → ℝ`), with Lebesgue measure.
* Chamber simplex `σ_L` for each `L : LinearExt α`.
* Chamber decomposition `O(α) = ⋃ σ_L` (almost-disjoint union) and
  unimodular volume `1/n!`.
* Continuous FKG/AD on the cube (port from Preston 1974, Ahlswede–
  Daykin 1979 continuous version).
* Drops headline via `1_{O(Q')}` × `1_A` continuous-FKG.

**Pros.** Cleanest mathematical narrative; closely follows
Brightwell §4. Each primitive is independently mathlib-friendly.

**Cons.** Heavy on measure theory and convex geometry; requires
formalising convex polytope volumes in Lean (mathlib has Lebesgue
measure but no formalised polytope theory). Continuous FKG is a
substantial mathlib gap on its own.

**Estimated total:** 4000–6000 LoC for the FKG-on-LE primitive,
plus 1500–2500 for the application chain.

### §4.2 Path B — discrete coupling via Stanley + tilted/Holley

Avoid polytopes; do the drops via combinatorial AD/Holley on
`J(α)` with a carefully tilted measure or via direct injection
proofs.

* Stanley log-supermodularity on `J(α)` (combinatorial proof — port
  Daykin 1990 or Bjorner 1989, avoiding Aleksandrov–Fenchel).
* For each `Q ⊆ Q'`, define `μ_Q(I) := e_Q(I) · e_Q(α \ I)` and
  `μ_{Q'}(I) := e_{Q'}(I) · e_{Q'}(α \ I)` on `J(α)`.
* Cross-poset Holley: show `μ_Q · μ_{Q'} ≤ μ_Q' · μ_Q` in the
  pointwise lattice sense (Holley hypothesis).
* Level-`k` localisation: extend to a level-decorated lattice
  `J(α) × Fin (n+1)` with constraints; or use a generating-function
  argument (the tilted-measure family `μ_z(I) := μ(I) z^{|I|}`).
* Drops headline via Holley + a re-summation identity.

**Pros.** Pure combinatorics; smaller mathlib-side footprint.
Stanley log-supermodularity is independently valuable as a mathlib
PR.

**Cons.** The level-`k` localisation step is the substantive
unknown (state.md §3.2 / mg-21a4 §3.2 surveys four discrete
candidates and finds all four fail in the obvious form). It is
**conceivable** but not yet established that some discrete
formulation closes; if not, Path B does not work and the project
falls back to Path A. Also: requires re-proving Stanley
log-supermodularity combinatorially, which the literature considers
the "hard" direction (Daykin 1990 and Bjorner 1989 are non-trivial).

**Estimated total:** 2500–4000 LoC for the FKG-on-LE primitive
(if level-`k` localisation works), plus 1500–2500 for the
application chain.

### §4.3 PM recommendation: pursue both, sequentially gated on EX-1

EX-1 (Stanley log-supermodularity port) is **load-bearing for
both** Path A and Path B and is the natural first execution
ticket. After EX-1 lands:

* If Stanley log-supermod port reveals a clean combinatorial
  localisation argument (Path B works): pursue Path B (smaller
  scope).
* If not: pursue Path A (geometric chamber decomposition).
* In either case, EX-1 is independently valuable as a mathlib PR
  candidate (see §7.1 leverage point).

---

## §5 Critical path with Lean signatures

This section enumerates the load-bearing primitives of sub-α-C with
explicit Lean signatures, mathlib-PR-class vs project-internal
categorisation, and per-session polecat estimates. Primitives are
labelled **EX-N** (executable as a polecat ticket) or **DH-N**
(Daniel-help leverage point — see §7).

### §5.1 EX-1 — Stanley log-supermodularity (combinatorial port)

**Math statement.** For any finite poset `α` and `I, J ∈ J(α)`:
`e(I) · e(J) ≤ e(I ∪ J) · e(I ∩ J)`, where `e(K) := |L(α[K])|` is
the number of linear extensions of the sub-poset on `K`.

**Cite.** Stanley 1981, *Two combinatorial applications of the
Aleksandrov–Fenchel inequalities*, J. Combin. Theory Ser. A;
combinatorial proofs in Daykin 1990 / Bjorner 1989.

**Lean signature.**
```lean
-- lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermod.lean (NEW)
theorem stanley_log_supermod {α : Type*} [PartialOrder α] [Fintype α]
    [DecidableEq α] (I J : LowerSet α) :
    numLinExt (subPoset (I : Set α)) * numLinExt (subPoset (J : Set α)) ≤
    numLinExt (subPoset ((I ⊔ J : LowerSet α) : Set α)) *
    numLinExt (subPoset ((I ⊓ J : LowerSet α) : Set α))
```

(Where `subPoset (I : Set α)` is the sub-partial-order on `I`,
defined in tree at `Subtype.lean` or as a one-line wrapper around
mathlib's `Subtype` partial order.)

**Category.** Mathlib-PR-class. `numLinExt` and `subPoset` are
in-tree but the statement is genuinely about finite posets; the
theorem is independent of the OneThird application. Strongly
upstream-able.

**Dependencies.**
- `LowerSet α` lattice structure (mathlib).
- `numLinExt` definition (in tree at `LinearExtension/Fintype.lean`).
- `LinearExt α` and `subPoset` (in tree at `Subtype.lean`).
- The combinatorial bijection / injection at the heart of the proof
  (project-internal, Daykin 1990 or Bjorner 1989 or fresh).

**Polecat session estimate.** **2 polecat sessions, ~600–1000 LoC,
~250–400k tokens combined.**
- Session A: scope the chosen proof variant (Daykin 1990 / Bjorner
  1989 / fresh combinatorial), give the bijection in latex; estimate
  300–500k tokens.
- Session B: full Lean port; estimate 300–500k tokens.

### §5.2 EX-2 — `μ(I) := e(I)·e(α\I)` log-supermodular on `J(α)`

**Math statement.** With `μ(I) := e(I) · e(α \ I)`,
`μ(I) μ(J) ≤ μ(I ∪ J) μ(I ∩ J)` on `J(α)`.

**Cite.** §3.2 above; Stanley 1981 (corollary).

**Lean signature.**
```lean
-- lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermod.lean (extend)
theorem stanley_mu_log_supermod {α : Type*} [PartialOrder α] [Fintype α]
    [DecidableEq α] (I J : LowerSet α) :
    let μ : LowerSet α → ℕ := fun K =>
      numLinExt (subPoset (K : Set α)) *
      numLinExt (subPoset ((Kᶜ : LowerSet α)ᶜ : Set α)) -- complement workaround
    μ I * μ J ≤ μ (I ⊔ J) * μ (I ⊓ J)
```

(Note: `α \ I` for `I : LowerSet α` is **not** automatically a
lower set — it is an **upper** set. The statement requires writing
`numLinExt` on the dual sub-poset; standard but care needed.)

**Category.** Project-internal corollary of EX-1. Trivial-in-tree
(~50 LoC).

**Dependencies.** EX-1.

**Polecat session estimate.** **0.1 of a polecat session,**
~50–100 LoC. Bundle with EX-1 in Session B.

### §5.3 EX-3 — Order polytope `O(α)` as a Lean type (Path A)

**Math statement.** `O(α) := { f : α → [0,1] | x ≤_α y ⟹ f x ≤ f y }`.

**Cite.** Stanley 1986, *Two poset polytopes*, Discrete Comput.
Geom. 1, 9–23.

**Lean signature.**
```lean
-- lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean (NEW, Path A)
def OrderPolytope (α : Type*) [PartialOrder α] : Set (α → ℝ) :=
  { f : α → ℝ |
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, x ≤ y → f x ≤ f y) }

instance : Convex ℝ (OrderPolytope α) := ⟨...⟩
instance : MeasurableSet (OrderPolytope α) := ⟨...⟩  -- via finite intersection
```

**Category.** Mathlib-PR-class. The order polytope is well-known
in algebraic combinatorics; mathlib has the ambient
`Set (α → ℝ)` and basic convex/measurable infrastructure. Adding
the polytope as a definition + basic properties (convex, compact,
measurable) is upstream-friendly.

**Dependencies.**
- `Mathlib.MeasureTheory.Measure.Lebesgue` — Lebesgue measure on
  `ℝ^n`.
- `Mathlib.Analysis.Convex.Basic`.
- `LowerSet α`.

**Polecat session estimate.** **1 polecat session, ~300–500 LoC,
~200–300k tokens.**

### §5.4 EX-4 — Stanley vertex theorem (Path A)

**Math statement.** The vertices of `O(α)` are exactly
`{1_I : I ∈ J(α)}`.

**Cite.** Stanley 1986, Theorem 1.2.

**Lean signature.**
```lean
-- lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean (extend)
theorem orderPolytope_extremePoints (α : Type*) [PartialOrder α] [Fintype α] :
    Set.extremePoints ℝ (OrderPolytope α) =
    { f : α → ℝ | ∃ I : LowerSet α, f = (Set.indicator (I : Set α) (1 : α → ℝ)) }
```

**Category.** Mathlib-PR-class.

**Dependencies.** EX-3, mathlib `Set.extremePoints`.

**Polecat session estimate.** **1 polecat session, ~400–600 LoC,
~200–300k tokens.**

### §5.5 EX-5 — Chamber simplex `σ_L` and chamber decomposition (Path A)

**Math statement.** For `L : LinearExt α`, define
`σ_L := { f ∈ O(α) | f(L⁻¹(0)) ≤ ⋯ ≤ f(L⁻¹(n-1)) }`. Then:
- Each `σ_L` is a unimodular simplex of Lebesgue volume `1/n!`.
- `O(α) = ⋃_L σ_L`.
- `σ_L ∩ σ_{L'}` has Lebesgue measure zero for `L ≠ L'`.

**Cite.** Stanley 1986, §3.

**Lean signature.**
```lean
-- lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean (extend, Path A)
def chamber {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (L : LinearExt α) : Set (α → ℝ) :=
  { f : α → ℝ |
      f ∈ OrderPolytope α ∧
      ∀ i : Fin (Fintype.card α - 1),
        f (L.toFun.symm i.castSucc) ≤ f (L.toFun.symm i.succ) }

theorem chamber_volume (L : LinearExt α) :
    MeasureTheory.volume (chamber L) = 1 / (Nat.factorial (Fintype.card α))

theorem orderPolytope_eq_iUnion_chamber :
    (OrderPolytope α : Set (α → ℝ)) = ⋃ L : LinearExt α, chamber L

theorem chamber_inter_meas_zero {L L' : LinearExt α} (h : L ≠ L') :
    MeasureTheory.volume (chamber L ∩ chamber L') = 0
```

**Category.** Mathlib-PR-class (with caveats). The chamber
decomposition is the heart of Path A; it requires reasoning about
unimodular simplex volumes, which is currently a mathlib gap.

**Dependencies.** EX-3, EX-4, mathlib measure theory.

**Polecat session estimate.** **2 polecat sessions, ~800–1500 LoC,
~400–800k tokens combined.**

### §5.6 EX-6 — Continuous FKG/Ahlswede–Daykin on `[0,1]^n` (Path A)

**Math statement.** For `f, g : [0,1]^n → ℝ` non-negative
monotone (each coordinate-monotone), the Lebesgue integrals
satisfy `(∫ f)(∫ g) ≤ ∫ f·g · (∫ 1)`, with the analogous AD form.

**Cite.** Preston 1974, *Spatial birth-and-death processes*; or
Ahlswede–Daykin 1979 continuous version.

**Lean signature.**
```lean
-- lean/OneThird/Mathlib/Probability/ContinuousFKG.lean (NEW, Path A)
theorem continuous_fkg {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g)
    (hfL1 : Integrable f) (hgL1 : Integrable g)
    (hfgL1 : Integrable (f * g)) :
    (∫ x ∈ Set.Icc (0 : Fin n → ℝ) 1, f x) *
    (∫ x ∈ Set.Icc (0 : Fin n → ℝ) 1, g x) ≤
    (∫ x ∈ Set.Icc (0 : Fin n → ℝ) 1, f x * g x) *
    (Set.Icc (0 : Fin n → ℝ) 1).indicator 1
```

**Category.** Mathlib-PR-class. Continuous FKG is a classical
result not currently in mathlib. Would require integrating over
the Borel σ-algebra, monotone functions, dominated convergence.

**Dependencies.**
- Mathlib measure theory + Lebesgue integration.
- Discrete FKG (already in mathlib via `four_functions_theorem`).

**Polecat session estimate.** **2–3 polecat sessions, ~1000–2000
LoC, ~600–1000k tokens combined.** This is the **single largest
chunk of Path A**, and it is independently valuable as a mathlib
contribution.

### §5.7 EX-7 — Drops headline via chamber + continuous FKG (Path A)

**Math statement.** For `Q ⊆ Q'` finite posets on `α`, level
`k ∈ {0, …, n}`, and an up-closed event `S : Finset α → Prop`:
`Pr_{L ∼ Unif L(Q)}[S(L_k)] ≤ Pr_{L ∼ Unif L(Q')}[S(L_k)]`.

**Cite.** Daykin–Saks 1981, Theorem 1; Brightwell 1999, §4.

**Lean signature.**
```lean
-- lean/OneThird/Mathlib/RelationPoset/FKG.lean (extend; OR new)
-- Per state.md §1.7 + sub-α-A scoping §4.2 (the "missing primitive"):
theorem probEvent'_mono_of_subseteq_upClosed
    {α : Type*} [DecidableEq α] [Fintype α]
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L : LinearExt' Q  => S (L.initialIdeal' k.val)) ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val))
```

**Category.** Project-internal. Closes the FKG-on-LE gap shared by
case3 and Brightwell ports.

**Dependencies.** EX-3, EX-4, EX-5, EX-6 (Path A) **OR** EX-1 +
EX-2 + Path B level-`k` localisation argument (Path B).

**Polecat session estimate.** **1–2 polecat sessions, ~400–800
LoC, ~250–500k tokens.** The argument itself is short once the
prerequisites land.

### §5.8 EX-8 — case3-port-2: drops → balanced-pair on case3 width-3 antichain

**Math statement.** Specialise the drops headline to the case3
witness scope; conclude `case3Witness_hasBalancedPair` (the
pre-axiom unwrap).

**Cite.** mg-75ef §3 + mg-5bf9 §3, blocked behind EX-7.

**Lean signature.**
```lean
-- lean/OneThird/Step8/Case3Port.lean (NEW or extend Case3Residual)
theorem case3Witness_hasBalancedPair_outOfScope_proved {α} [Fintype α]
    (Q : RelationPoset α) (hCase3 : InCase3Scope Q) ... :
    HasBalancedPair (something derived from Q)
```

**Category.** Project-internal.

**Dependencies.** EX-7.

**Polecat session estimate.** **2 polecat sessions, ~800–1200
LoC, ~400–600k tokens.** Already scoped in mg-8d39 §6 / mg-75ef
§3 (~1450–2700 LoC across the application chain; portion
attributable to case3 alone is ~800–1200 LoC).

### §5.9 EX-9 — Brightwell-port-A: drops → centred-sum on `L(α) × {1,…,m}`

**Math statement.** Apply EX-7 to the `L(α) × Fin m` product to
derive the centred-sum bound currently axiomatised as
`brightwell_sharp_centred`.

**Cite.** mg-3c06 (Brightwell port mathlib-gap ticket).

**Lean signature.**
```lean
-- lean/OneThird/Mathlib/LinearExtension/BrightwellPort.lean (replace BrightwellAxiom.lean)
theorem brightwell_sharp_centred_proved
    (α : Type*) [PartialOrder α] [Fintype α] [DecidableEq α]
    (Pred Succ : Finset α) (hDisj : Disjoint Pred Succ) ...
    (m : ℕ) (hm : 2 ≤ m) (hmQ : m = Fintype.card α + 1)
    (x y : α) :
    m * |N' * sumA - cardA * N| ≤ 2 * N * N'
    -- where N, N', sumA, cardA are as in the existing axiom
```

**Category.** Project-internal.

**Dependencies.** EX-7, plus the in-tree `fiberSize_lipschitz_on_bkAdj`
machinery (already formalised).

**Polecat session estimate.** **1–2 polecat sessions, ~500–800
LoC, ~250–400k tokens.**

### §5.10 EX-10 — Both-axiom-removal via consumer-side rewires

**Math statement.** Remove `case3Witness_hasBalancedPair_outOfScope`
and `brightwell_sharp_centred` from `lean/AXIOMS.md`; rewire all
consumers to use the new theorems from EX-8 and EX-9. Verify with
`#print axioms` that no new axioms appear.

**Cite.** state.md §4.1 / mg-bb74 framing refresh: this is the
"definitively retained" → "removed" transition.

**Category.** Project-internal mechanical refactor.

**Dependencies.** EX-8, EX-9.

**Polecat session estimate.** **0.5 of a polecat session, ~100–200
LoC of consumer-side edits + AXIOMS.md updates, ~100–150k tokens.**

### §5.11 Aggregate critical path

| Primitive | Path | Sessions | LoC | Tokens (k) | Mathlib-PR? |
|-----------|------|----------|-----|------------|-------------|
| EX-1 Stanley log-supermod | A+B | 2 | 600–1000 | 400–700 | Yes |
| EX-2 `μ` log-supermod corollary | A+B | bundled | 50–100 | bundled | No |
| EX-3 Order polytope | A | 1 | 300–500 | 200–300 | Yes |
| EX-4 Stanley vertex theorem | A | 1 | 400–600 | 200–300 | Yes |
| EX-5 Chamber simplex + decomp | A | 2 | 800–1500 | 400–800 | Partially |
| EX-6 Continuous FKG | A | 2–3 | 1000–2000 | 600–1000 | Yes |
| EX-7 Drops headline | A | 1–2 | 400–800 | 250–500 | No |
| EX-8 case3-port-2 | A | 2 | 800–1200 | 400–600 | No |
| EX-9 Brightwell-port-A | A | 1–2 | 500–800 | 250–400 | No |
| EX-10 Axiom-removal | A | 0.5 | 100–200 | 100–150 | No |
| **Total (Path A)** | A | **12–16** | **5050–8700** | **2900–4900** | 5 of 10 |
| **Total (Path B, est.)** | B | **8–11** | **2900–4900** | **1700–3000** | 1 of 4 |

Path A's aggregate is ~5050–8700 LoC, **above** state.md §4.2's
2000–4000 + 1450–2700 = 3450–6700 LoC working figure but within
factor 1.3 at the upper bound. This is consistent with state.md
§4.2's "ballpark" framing; the over-estimate is concentrated in
EX-6 (continuous FKG) and EX-5 (chamber volume), both of which are
mathlib-PR-class and could be amortised across other downstream
applications outside this project.

Path B's aggregate is **within** state.md §4.2's working figure,
but conditional on the level-`k` localisation step working — which
is not yet established (see §6).

---

## §6 Trip-wire status (per polecat brief §6)

* **Token blow-up.** Not fired. Approximate spend on this scoping
  ~85k tokens of the 600k cap. Well under the 80% trip-wire (480k).
* **Scope creep.** Borderline. Path A aggregate at upper bound
  (~8700 LoC) exceeds state.md §4.2 working figure (3450–6700 LoC)
  by ~30%, which is **within** the §4.2's "ballpark" caveat but
  enough to flag as a yellow signal. Path B is within the working
  figure if the level-`k` localisation step works. Not above the
  10000 LoC trip-wire that would force STOP.
* **Structural obstruction.** Not fired. No fresh structural fact
  REDs sub-α-C. The existing structural facts (state.md §1.2 / §1.6
  / §1.7) are accommodated by the chamber path: §1.2 (no LE
  distributive lattice) is bypassed because chambers are not a
  lattice; §1.6 (sub-α-A counterexample) is bypassed because the
  chamber path normalises by `numLinExt α` correctly via the
  geometric volume; §1.7 (drops `R` non-level) is bypassed because
  the chamber path treats Q ⊆ Q' as a polytope inclusion `O(Q') ⊆
  O(Q)`, not as a level-restricted event.
* **Drift to another sub-option.** Not fired. The polecat did not
  pivot to sub-α-D or any new framing; this scoping is sub-α-C as
  brief'd.

---

## §7 Daniel-help leverage points (state.md §3 entries)

Per polecat brief §4: where might Daniel input shorten the path?
The four leverage points below are surfaced as state.md §3 entries
(see §10) for PM follow-up.

### §7.1 DH-1: Stanley log-supermodularity as upstream mathlib PR

**Question.** Is Stanley's `e(I)e(J) ≤ e(I∪J)e(I∩J)` upstream-able
to mathlib in advance of the Path α arc?

**Why it matters.** EX-1 is independently valuable as a mathlib
contribution: linear extensions of a finite poset and their
log-supermodularity are core combinatorics, well within mathlib's
existing scope (`Mathlib.Combinatorics`, `Mathlib.Order`). If
Daniel can secure a mathlib reviewer's interest *before* the
project pursues sub-α-C, the project-internal EX-1 work disappears
into a mathlib PR and EX-2 onward can rely on it.

**Cost saving.** ~600–1000 LoC of project-internal work moved to
mathlib (where it amortises across other future users); ~2 polecat
sessions saved on the project clock.

**Concrete ask to Daniel.** Open a discussion on the mathlib Zulip
or with a mathlib maintainer (Yael Dillies has historically
maintained `Mathlib.Combinatorics.SetFamily.FourFunctions` /
`Mathlib.Combinatorics.LYM` etc.; would be the natural candidate)
about whether Stanley log-supermodularity is in-scope for a PR.
The combinatorial proof (Daykin 1990 or Bjorner 1989) is the
natural form to upstream; Aleksandrov–Fenchel (Stanley 1981) is
significantly heavier and not immediately mathlib-friendly.

### §7.2 DH-2: thin-slice for case3 application only

**Question.** Does the case3 application chain need the full
chamber decomposition for arbitrary finite posets, or only for the
specific width-3 antichain witnessing case3?

**Why it matters.** mg-75ef §3 establishes that the case3
application uses the drops at a specific level `k` for a specific
up-closed event derived from the case3 bipartite structure. If the
specific scope is narrower than "all finite posets", a thin-slice
formulation could shrink EX-3 through EX-7 substantially. For
example: only width-3 + level `k = 2`-or-`k = 3` could halve the
case work in the chamber decomposition.

**Cost saving.** Speculative, ~30–50% on EX-3 through EX-5 if a
case3-specific specialisation works; minimal on EX-6 (continuous
FKG is dimension-agnostic).

**Concrete ask to Daniel.** Confirm whether the case3 application
chain's drops invocation is at a level `k` that admits a
combinatorial special case (e.g., `k = 1` reduces to a single-
element ideal event; `k = n - 1` is the dual). If the answer is
"no, it's at a generic level", thin-slice is not viable and DH-2
is dropped.

### §7.3 DH-3: Brightwell-port-A vs Brightwell-port-B fork (mg-3c06)

**Question.** Does mg-3c06 (the Brightwell mathlib-gap ticket)
benefit from sub-α-C as shared infrastructure, or is the Brightwell
case orthogonal?

**Why it matters.** Per state.md §3.3 and mg-b10a §6, Brightwell-
port-A consumes the τ-inversion product lattice on `L(α) × {1,…,m}`,
which has the same non-distributivity obstruction on `L(α)`. If
sub-α-C's drops headline (EX-7) suffices to discharge Brightwell's
centred-sum bound (i.e. EX-9 is genuinely a ~500–800 LoC
specialisation rather than a separate quarter-scale port), the
two axiom-removal arcs amortise. If not, Brightwell-port-A may
require its own sub-α-C-equivalent infrastructure.

**Cost saving.** Up to ~50% on Brightwell-port if the amortisation
holds (~1500 LoC); none if it doesn't.

**Concrete ask to Daniel.** Confirm — by inspection of
`step8.tex:1042-1276` and Brightwell §4 — whether the centred-sum
bound `eq:sharp-centred` decomposes into a finite combination of
drops invocations, or whether it requires a genuinely different
FKG/AD setup (e.g., on `L(α) × Fin m` with the product lattice
structure that has the same non-distributivity issue mg-dc9d
identified).

### §7.4 DH-4: continuous FKG/AD acceleration

**Question.** Is there a working pathway via discrete FKG that
avoids continuous FKG entirely?

**Why it matters.** EX-6 (continuous FKG on the cube) is the
single largest mathlib-PR-class chunk of Path A
(~1000–2000 LoC). If a fully discrete formulation works (Path B,
or a discretisation of Path A via Riemann sums on an integer
sub-lattice of `[0,1]^n`), the largest mathlib-side risk is
avoided.

**Cost saving.** ~1000–2000 LoC if continuous FKG is bypassed;
EX-6 reduces to a mathlib citation if it lands in advance.

**Concrete ask to Daniel.** This is the most speculative
leverage point; surface only if Daniel has prior knowledge of
mathlib continuous FKG efforts or alternative formulations from
the Brightwell–Tetali / Bjorner–Wachs literature.

---

## §8 Verdict

### §8.1 Headline

**AMBER leaning GREEN.**

Critical path of 6–10 load-bearing primitives is sketched (§5);
each has an explicit Lean signature, mathlib-PR-class vs
project-internal categorisation, and a per-session polecat
estimate. Aggregate Path A scope (5050–8700 LoC) is consistent
with state.md §4.2's "2000–4000 + 1450–2700 LoC" working figure at
factor ~1.3 over the upper bound, and Path B (2900–4900 LoC) is
within the working figure conditional on the level-`k` localisation
step working. Three structural unknowns keep the verdict short of
GREEN: (i) discretisation of continuous FKG (DH-4), (ii)
combinatorial vs Aleksandrov–Fenchel proof of Stanley log-supermod
(EX-1), (iii) Path-A-vs-Path-B fork (level-`k` localisation
viability for Path B).

### §8.2 PM-recommended next step

**File EX-1 (Stanley log-supermodularity port) as the first
execution ticket.** It is load-bearing for both Path A and Path B,
is the most isolatable mathlib-friendly chunk, and is independently
valuable as a mathlib PR candidate (DH-1). After EX-1 lands, the
Path-A-vs-Path-B fork can be re-evaluated with concrete data on
how amenable Stanley's argument is to combinatorial Lean
formalisation.

PM should also surface the four DH leverage points (§7) to Daniel
before EX-1 is dispatched. DH-1 (mathlib upstream PR for Stanley
log-supermod) is the highest-leverage; if Daniel can engage a
mathlib reviewer in parallel, the project-internal EX-1 work may
disappear entirely.

### §8.3 Calendar ETA

* **EX-1:** ~2 polecat sessions, ~3–5 days each, sequential.
  Total ~1–2 weeks elapsed.
* **EX-2 through EX-7 (Path A):** ~9–13 polecat sessions, ~3–5
  days each, partial parallelisation possible (EX-3+EX-4 vs
  EX-6 in parallel after EX-3 lands). Total ~6–10 weeks elapsed.
* **EX-8, EX-9 (applications):** ~3–4 polecat sessions, ~3–5
  days each, sequential after EX-7. Total ~2–3 weeks elapsed.
* **EX-10 (axiom-removal):** ~0.5 of a polecat session, ~1 day.

**Path A total (steady state, no DH leverage):** ~9–15 weeks
calendar, 13–17 polecat sessions, ~5050–8700 LoC.

**Path B total (steady state, no DH leverage, level-`k`
localisation works):** ~6–10 weeks calendar, 8–11 polecat sessions,
~2900–4900 LoC.

If DH-1 lands (mathlib upstream Stanley log-supermod): subtract
~2 polecat sessions and ~600–1000 LoC.

If DH-4 lands (continuous FKG bypassed): subtract ~2–3 polecat
sessions and ~1000–2000 LoC from Path A.

Best-case: ~4–6 weeks (Path B with DH-1).
Worst-case: ~12–18 weeks (Path A with no leverage points
materialising).

### §8.4 What this means for the project

* **Audit-bar economics.** Per cont-4 §6 and state.md §4.2: the
  axiom-elim of both `case3Witness_hasBalancedPair_outOfScope` and
  `brightwell_sharp_centred` against a quarter-scale infrastructure
  effort is the prevailing trade-off. Sub-α-C delivers both axioms
  (state.md §4.2's "shared mathlib-gap dependency" framing), so
  the axiom-removal amortisation is favourable.
* **mg-fb16 unhold.** Path γ remains the recommended status-quo
  for ship velocity (forum-readiness signed off, audit-bar
  economics favour retention). Sub-α-C is **the long arc** in
  parallel; mg-fb16 stays unheld in either case.
* **Forum-post draft.** If sub-α-C is committed, the AXIOMS.md
  framing shifts from "definitively retained" → "scheduled for
  replacement via sub-α-C arc" with a calendar ETA per §8.3.
  ~10–20 LoC doc edit.

### §8.5 Trip-wires (per polecat brief §6) — final status

* **Token overrun:** not fired. ~85k of 600k cap.
* **Scope creep:** at upper bound of state.md §4.2 working figure
  (~1.3× over upper, ~1.5× over lower). Not above the 10000 LoC
  trip-wire that would force STOP. Yellow signal flagged.
* **Structural obstruction:** not fired. No fresh structural fact
  REDs sub-α-C.
* **Drift:** not fired. This polecat did not pivot to sub-α-D or
  any new framing.

---

## §9 What follow-on tickets PM might file

1. **EX-1 (Stanley log-supermodularity port)** — file as long-arc
   execution ticket, ~2 polecat sessions, latex-first then Lean.
2. **DH-1 (mathlib upstream PR for EX-1)** — surface to Daniel as
   highest-leverage mathlib-side coordination.
3. **DH-2, DH-3, DH-4** — surface to Daniel as scoping questions
   for parallel investigation; PM follows up after EX-1 lands.
4. **AXIOMS.md framing refresh** — if Daniel commits sub-α-C, edit
   the "definitively retained" framing to "scheduled for
   replacement via sub-α-C" with §8.3 calendar ETA. ~10–20 LoC.
5. **mg-3c06 (Brightwell mathlib-gap ticket) coordination** —
   resolve DH-3 fork; commit Brightwell-port-A as an EX-9 sub-arc
   of sub-α-C, or as a separate quarter-scale arc.

---

## §10 state.md updates (mandate)

Per polecat brief §5 and `feedback_polecat_cumulative_state_doc`,
this polecat updates state.md as part of the deliverable. The
updates are:

* **§3.4 (NEW)** — sub-α-C scoping in flight + verdict (this
  document).
* **§1.8 (NEW)** — `e(I)·e(α\I)` log-supermodular on `J(α)` (§3.2
  here).
* **§3.5, §3.6, §3.7, §3.8 (NEW)** — DH-1, DH-2, DH-3, DH-4
  leverage points.
* **§4.5 (NEW)** — sub-α-C decision points and triggers.
* **Last update line** — appended to the header.

See state.md commit `73ed85e` → this commit's diff for the
full update.

---

## §11 Cross-references

### Predecessor STOPs and scopings
* mg-b10a (`256f0da`) — A8-S2-cont-4 STOP, FKG-on-LE obstruction
  first surfaced. `docs/a8-s2-cont-execution-arc/cont-4-stop-report.md`,
  esp. §3.3 (product factor blow-up), §6 (Path γ recommendation).
* mg-ff7f (`6b62a77`) — Path α scoping (RETRACTED §2.5).
  `docs/path-alpha-scoping/scoping.md`.
* mg-dc9d (`a95020e`) — Hibi-1 STOP, mg-ff7f §2.5 retraction.
  `docs/path-alpha-execution-arc/hibi-1-stop-report.md`, esp.
  §6 sub-α-C named as the chamber path.
* mg-21a4 (`f862b76`) — sub-α-A scoping, RED verdict.
  `docs/path-alpha-execution-arc/sub-alpha-A-scoping.md`, esp.
  §3.5 mitigation table (rules out the discrete sub-α-A approach).
* mg-bb74 (`73ed85e`) — `lean/AXIOMS.md` framing refresh; sub-α-C
  is named there as "the only surviving theoretical replacement
  route".

### In-tree Lean infrastructure
* `lean/OneThird/Mathlib/LinearExtension/Birkhoff.lean` — the
  Birkhoff bijection `LinearExt α ≃ IdealChain α`.
* `lean/OneThird/Mathlib/LinearExtension/FKG.lean:452`
  (`fkg_uniform_initialLowerSet`) — the existing lossy
  product-lattice pathway.
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:325, :464` — data
  versions; counting-only `probLT'_mono_of_relExt`.
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean` —
  `brightwell_sharp_centred` axiom (target for EX-9).
* `lean/AXIOMS.md` — both project axioms; framing currently
  "definitively retained" pending sub-α-C decision.

### Literature
* Stanley 1981 — "Two combinatorial applications of the
  Aleksandrov–Fenchel inequalities", JCTSA. *(EX-1 source)*
* Stanley 1986 — "Two poset polytopes", DCG. *(EX-3, EX-4, EX-5
  source)*
* Hibi 1985 — "Distributive lattices, affine semigroup rings, and
  algebras with straightening laws". *(historical context)*
* Daykin–Saks 1981 — "A natural generalization of FKG for partial
  orders". *(EX-7 source)*
* Brightwell 1999 — "Balanced pairs in partial orders", Discrete
  Math. *(EX-7, EX-9 source)*
* Daykin 1990 / Bjorner 1989 — combinatorial proofs of Stanley
  log-supermodularity (EX-1 alternative source).
* Preston 1974 — "Spatial birth-and-death processes" (EX-6
  continuous FKG source).
* Ahlswede–Daykin 1979 — original four functions theorem (mathlib
  has the discrete version).

### Feedback / policy
* `feedback_polecat_cumulative_state_doc` — applied (state.md §10
  updates).
* `feedback_latex_first_for_math_simp` — applied (this document
  is the deliverable; no Lean source touched).
* `feedback_complexity_blowup_means_wrong_path` — applied
  (trip-wires §6, §8.5).
* `feedback_polecat_stop_runaway` — applied (no auto-extension; PM
  files follow-on tickets).
* `feedback_pre_execution_dependency_verification` — applied (§5
  primitives have explicit Lean signatures and verified
  dependencies).
* `feedback_long_arcs_are_pm_authority` — invoked (PM commits the
  long arc per Daniel 2026-05-07T16:06Z directive).
* `feedback_audit_bar_for_axioms` — applied (§8.4
  axiom-amortisation analysis).

---

*End of sub-α-C scoping. Lean source unchanged. Verdict: AMBER
leaning GREEN; PM files EX-1 (Stanley log-supermod) as first
execution ticket and surfaces DH-1–DH-4 to Daniel.*

— polecat mg-91be (cat-mg-91be), 2026-05-07.
