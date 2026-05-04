# Math-simp arc 3.0 — strategy revisit (multi-definition ε-close + scaffolding alternatives)

> **EXPLORATORY ONLY — NOT a live program.**
>
> This file is the deliverable for `mg-65e1` (Track-3 / arc 3.0
> kickoff, 2026-05-04, branch `math-simp-arc-3.0`). It is the
> answer to Daniel's directive of 2026-05-04T~19:30Z:
>
> > *"perhaps we should revisit the proof strategy in the light of
> > all the simplifications we have investigated, and ensure a
> > polecat has the full context? My general feeling is that if
> > things are this hard then the math is the issue. We should be
> > able to find a simpler argument. For instance there are many
> > different ways to define being epsilon-close to an ordinal
> > sum"*
>
> The deliverable is a **strategy-level audit + multi-definition
> ε-close exploration**, not a commission to execute anything.
> Months from now, treat this doc the same way
> `simplifications.md` should have been treated after arc 1.0
> close (2026-05-02): a record of evaluations made under specific
> assumptions, **not a backlog**. If a framing changes status
> because mathlib / in-tree infrastructure has moved, file a
> fresh ticket — do not reanimate this doc as if it were live.
>
> The paper's headline `OneThird.width3_one_third_two_thirds`
> retains `hC3 : Step8.Case3Witness` (intentionally) under
> pm-onethird's option (δ) park (2026-04-27). This arc neither
> overturns nor confirms that retention; it asks whether a
> **different mathematical strategy** would close `hC3` where
> the existing strategy cannot. The verdict (§4): **no**.

---

## 0. Provenance and outcome class

* **Filed under** `mg-65e1` (Track 3, math-simp arc 3.0).
  Polecat `p65e1`, 2026-05-04.
* **Sibling arcs (closed).**
  * `mg-3e53` — arc 1.0 scoping. Surveyed 4 candidates
    (A/B/C/D); recommended A (ε-close-to-ordinal-sum reductio).
  * `mg-3d9d` — arc 1.0 A1 RED-fallback. Found that the in-tree
    `brightwell_sharp_centred` axiom + `exc_perturb` cannot
    deliver a `f(ε) → 0` perturbation bound for balanced cuts.
  * `mg-805c` — arc 1.0 B1 ship. Layered-reduction rewrite as
    size-minimality contradiction; no `hC3` removal.
  * `mg-80ab` — arc 2.0 scoping (Track 2). Surveyed 4 fresh
    framings; **zero GREEN, one AMBER (B2 finite enumeration)
    only as Track 1 fallback**.
  * `mg-b666` — Track 1 cardinality obstruction. Showed that
    compound-automorphism cannot extend to case-2-strict for
    structural cardinality reasons.
* **Sibling arc (active, human-assigned).** `mg-fb16` —
  lean-forum send for the current narrower (with-`hC3`) claim.
  This arc does NOT condition on `mg-fb16` status.
* **Outcome class** (per
  `feedback_distinguish_arc_chunk_outcomes`):
  **substantive scoping chunk = no good framing found.** The
  scoping is the deliverable; no parallel cleanup chunk is
  bundled. Headline `hC3` unchanged by arc 3.0.
* **Branch.** `math-simp-arc-3.0`, parallel to `main` (parent
  commit `1ce035d`). All artefacts under
  `docs/math-simp-arc-3.0/`.

---

## 1. Prior-arc context audit (mandated §1)

The brief mandates that the polecat read and synthesise the
12-document audit before proposing new framings. This section
extracts the **load-bearing facts** that constrain the search
space; the search itself happens in §§2–3, and the verdict
references back to this section by tag.

Each subsection ends with a **Tag:** the concise claim that
later sections use as a constraint. Tags are stable handles —
a framing that conflicts with a tag has to address it
explicitly.

### 1.1 The headline shape and what `hC3` actually carries

**Source.** `lean/OneThird/MainTheorem.lean:52-57`,
`lean/OneThird/Step8/LayeredBalanced.lean:438-444`,
`step8.tex:2348-2360` (`lem:layered-balanced` G4),
`step8.tex:2978-3032` (`prop:in-situ-balanced` Cases 1–3).

The headline:

```lean
theorem width3_one_third_two_thirds.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hC3 : Step8.Case3Witness.{u}) :
    HasBalancedPair α
```

with `Case3Witness` a typed-witness `def`:

```lean
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    HasWidthAtMost β 3 → ¬ IsChainPoset β →
    2 ≤ Fintype.card β → HasBalancedPair β
```

The `hC3` hypothesis is the **case-3 leaf** of the dispatch
inside `prop:in-situ-balanced` for shallow layered posets
(`K < K₀(γ, w)` of `lem:layered-reduction`). Cases 1 and 2 are
discharged in tree (Case 1 ambient match; Case 2-symmetric
collapse via `case2Witness_balanced_or_strict`,
mg-8801). Case 3 is the within-band antichain regime —
specifically the **K=2 + irreducible + w ≥ 1 + |β| ≥ 3 N-poset
family** (`docs/path-c-cleanup-roadmap.md` §5) — where neither
ambient match nor within-band ⪯-pair fires.

**Tag T1 (Headline shape).** Dropping `hC3` is upside.
Replacing `hC3` with another opaque universally-quantified
hypothesis is **not** progress (`feedback_signature_regressions`,
the c5d5a10 negative exemplar, `path-c-cleanup-roadmap.md` §2).

**Tag T2 (Case-2-strict locus).** Case-2-strict and case-3 both
sit inside `prop:in-situ-balanced` for **shallow** layered
posets. The deep-layered branch (`K ≥ K₀`) is discharged by
`lem:layered-reduction` (G3) and does **not** carry `hC3`.

### 1.2 The case-2-strict cardinality obstruction (Track 1, mg-b666)

**Source.** `docs/path-c-track-1-status-1.md` §2.

**Lemma (cardinality obstruction).** Let `α` be a finite
poset and `(a, a')` a within-band ⪯-strict pair with
`upper(a) ⊊ upper(a')` strictly. Then no `≤`-monotone
permutation `σ : α ≃ α` with `σ a = a'` exists.

**Proof sketch.** Order-preserving permutations restrict to
bijections between principal up-sets, so `σ` (and `σ⁻¹`)
forces a bijection `upper(a) ↔ upper(a')`, hence
`|upper(a)| = |upper(a')|`. Strict inclusion gives the
contradiction.

**Implications.** No `MatchingCompatible L P₁ P₂` can have
`P₁ = (a, a')` strict. In the minimal counterexample
(`α = {a, a', y}`, `a' < y` only, K=2 / w=1 / |α|=3) the
automorphism group is trivial, so compound-automorphism
yields **zero** witnesses — yet `(a, a')` IS balanced
(`probLT a a' = 1/3` by direct count). The witness comes from
counting, not symmetry. Consequently, any uniform structural
dispatch over the K=2 + irreducible + w ≥ 1 + |β| ≥ 3 family
cannot use compound-automorphism alone.

**Tag T3 (Cardinality obstruction).** A symmetry-based reduction
to `probLT a a' = 1/2` cannot fire on a strict ⪯-pair. Any
strategy that goes via compound-automorphism on case-2-strict
inherits this; any strategy that bypasses compound-automorphism
sidesteps it.

**Tag T3a (3-element minimal counterexample).** `α = {a, a', y}`
with `a' < y` only is a witness that **trivial-Aut(α, ≤)** is
attained inside the obstruction family, even at minimum
cardinality (3 elements). Any strategy dependent on a
non-trivial poset automorphism on this minimal `α` is dead
on arrival.

### 1.3 The strict K=2 probability bound is unprovable in tree (mg-b0de)

**Source.** `docs/a8-s2-restate-block-and-report-status.md`
§§2–3.

For the strict K=2 within-band ⪯-pair `(a, a')` with
`upper(a) ⊊ upper(a')`, closing the dispatch via probability
bounds requires `probLT a' a ≤ 2/3` (equivalently
`probLT a a' ≥ 1/3`). Existing in-tree machinery cannot deliver
this:

* **Brightwell sharp centred** (`BrightwellAxiom.lean:159`)
  gives `|p(Q) − p(Q − z)| ≤ 2/|Q|` per single-element
  perturbation. To clear `Pr ≥ 1/3` we need `|Q| ≥ 12`. K=2
  has `|Q| = |α| ≤ 6`, so the bound is **vacuous in our
  regime**.
* **Iterating Brightwell** across multiple strictness witnesses
  gives a harmonic-sum bound `2 H_{|Q|} ≈ 4.9` for `|Q| = 6`;
  weaker still.
* **`Case2BipartiteBound.lean`** (mg-ed4d) is K=2 / w=0 only.
* **Cross-poset count-form FKG**
  (`probLT'_count_div_le_of_relExt`) gives the wrong
  normalisation.
* **Chain swap on `(a, z)`** for `z ∈ upper(a') \ upper(a)`
  fails on natural configs (the chain hypothesis on `(a, z)`
  is not satisfied).

The paper's `≤ 2/3` route (`step8.tex:2916-2940`) goes through
**probability-normalised cross-poset FKG monotonicity** — the
deferred A8-S2-cont scope (~2000–3500 LoC, multi-polecat /
Daniel-led, per `docs/a8-s2-status.md` §5).

**Tag T4 (Brightwell vacuity at K=2).** No in-tree perturbation
bound is sharp enough to close case-2-strict in the K=2 + w ≥ 1
+ |α| ≤ 6 regime.

### 1.4 Case2FKGSubClaim direction is wrong in the strict case (mg-a79e)

**Source.** `docs/a8-path-b-block-and-report-status.md` §§2–3.

The mg-27c2 `Case2FKGSubClaim L` structure's `pair` field
asserts `1/2 ≤ probLT a a'` for a within-band chain pair
`(a, a')`. Combined with `probLT_le_half_of_chain` (mg-ba0c),
this **forces equality** `probLT a a' = 1/2`. In the
strict-chain case, the chain swap is a **strict injection** —
`probLT a a' < 1/2`, violating the claim. The 3-element
counterexample of T3a verifies this.

The η₄ direction-flip restate gives a true sub-claim
(`probLT a a' ≤ 1/2`), discharged by chain swap; but the
consumer redesign needs the missing `≤ 2/3` from T4, which is
not in tree.

**Tag T5 (FKG sub-claim closed).** Both natural directions of
`Case2FKGSubClaim`'s `pair` field are dead ends: `≥ 1/2` is
provably false on strict pairs; `≤ 1/2` is true but doesn't
close the dispatch without T4's missing bound.

### 1.5 Arc 1.0 A1 RED-fallback: in-tree perturbation is size-based, not ε-aware (mg-3d9d)

**Source.** `docs/math-simplification-A1-feasibility.md` §3.

Arc 1.0 picked **per-pair cardinality-overlap** as the ε
definition (per `simplifications.md` reading): for a partition
`X = A ⊔ B`,

```
ε_pp(P, A, B) := |{(a, b) ∈ A × B : a ⊀ b}| / (|A| · |B|).
```

The required bound is

```
| Pr_P[x < y] − Pr_A[x < y] | ≤ f(ε_pp(P))    for x, y ∈ A
```

with `f(0) = 0` and `f(ε₀) ≤ γ` for `γ ≈ 0.057`. The strongest
in-tree bound, iterating `one_elem_perturb` along
`exc_perturb`'s sequence:

```
| Pr_P − Pr_A | ≤ 2|B| / (|A| + 1).
```

This is **size-based, not ε-aware** — for balanced cuts
`|A| ≈ |B| ≈ n/2`, the bound saturates at `2`. Concrete
witness: `P = A ⊕ B` minus one cross-edge has
`ε_pp = 4/n² → 0` while the bound stays at `2`. Three
candidate in-tree paths all fail to deliver `f(ε) → 0`
(per-pair, per-element, per-volume normalisations all hit
either the same vacuity or wrong-direction FKG).

**Tag T6 (Single-element-perturbation ceiling).** Any chain of
single-element perturbations (Brightwell + iteration) gives a
**size-based** bound that does not see ε. Distinguishing
ε-close from far-from-ordinal at the perturbation level
requires either (i) a multi-element / structure-aware
Brightwell variant (= a new project axiom or new paper-level
math), or (ii) re-deriving Steps 5–7's rigidity content.

**Tag T7 (N-poset is NOT a true ordinal sum).** A common
intuition (cited in arc 1.0 scoping doc) is that the N-poset
`α = {x₁, x₂, y₁, y₂}` with `x₁ < y₁` and `x₂ < y₂` is the
ordinal sum `{x₁, x₂} ⊕ {y₁, y₂}`. **It is not**: the ordinal
sum requires *every* lower element below *every* upper element
(4 cross-edges); the N-poset has only 2. Under any of the ε
definitions in §2, the N-poset has nontrivial defect. The
"decomposable case" (ε = 0) of any reductio does NOT
trivially absorb the N-poset; the reductio must close the
N-poset via the **near-ordinal** (or far-from-ordinal) case.

### 1.6 Arc 2.0 scoping: zero-GREEN-of-four (mg-80ab)

**Source.** `docs/math-simp-arc-2.0/scoping.md` §§4–6.

Arc 2.0 surveyed four fresh framings on top of arc 1.0's
findings:

1. **Audit-bar revisit (multi-elem Brightwell axiom).** Fails
   2/4 audit-bar conditions (external + low-risk). **RED.**
2. **Direct probability bound bypassing FKG.** Three sub-options
   (2a/b/c). 2a is mg-a79e Route B's deferred A8-S2-cont scope
   (paper-tier infrastructure, not simplification). 2b is arc
   1.0 D's width-3 Kahn-Linial tightening (paper-level math
   discovery). 2c is closed off by mg-b0de's K=2 vacuity.
   **All RED.**
3. **Restrict-and-dispatch.** Sub-A duplicates Track 1; sub-B2
   (finite-enumeration K=2 case-2-strict certificate) is
   mechanical, not aesthetic, AMBER as Track 1 fallback only.
   Sub-B1 / B3 RED.
4. **Different proof entirely (Brightwell-pump / Kahn-Saks /
   Linial alternate route).** Multi-week external research,
   out of polecat scope. **RED.**

**Tag T8 (Arc 2.0 frontier).** No GREEN framing in the
"different organisation of in-tree machinery" search space.
Anything truly new must be either (i) a new project axiom
(audit-bar override, Daniel-only) or (ii) paper-level math
(escalation, multi-week external research arc).

### 1.7 Path C cleanup audit trail (mg-7261)

**Source.** `docs/path-c-cleanup-roadmap.md`.

Four polecat rounds (mg-4a5b → mg-072c → mg-0fa0 → mg-94fd)
attempted to drop `hC3` via the structural compound-automorphism
route. Each round surfaced *new* infrastructure blockers; the
arc parked under option (δ) at round 4. Six infrastructure
commits landed (mg-9568 / mg-7f06 / mg-a735 / mg-27c2 / mg-2e58
/ mg-26bb), raising the floor for any future cleanup. Three
post-park commits (mg-84f2 / mg-c0c7 / mg-02c2) discharged
case-3 (the `NoWithinBandPreceq L` branch) cleanly. The
remaining gap is **case-2-strict**, which Track 1 (T3) showed
cannot be closed by compound-automorphism for structural
cardinality reasons.

**Tag T9 (Multi-round failure mode).** The Path C cleanup arc
demonstrated a stable failure mode: each polecat round
identifies a real obstruction and the next-round tool to
overcome it; the next-round tool then fails for a deeper
structural reason. Single-session attempts cannot recover from
this pattern under per-session budgets. Multi-week focused
work or a substantive math change is needed.

### 1.8 Step 8 G3 vs G4: where each obstruction lives

**Source.** `step8.tex:1879-2360` (G3 layered reduction),
`step8.tex:2348-3132` (G4 layered balanced + Cases 1/2/3).

* **G3 (deep layered, `K ≥ K₀`).** Cutting lemma
  (`step8.tex:2164-2186`) splits `X = A ⊔ B` with window
  `W = L_{k-w+1} ∪ … ∪ L_{k+w}` of size `≤ 6w` in width 3.
  Bulk pairs (`x, y ∈ A \ W`) satisfy `p_xy(P) = p_xy(A)`
  exactly (Step 3 ordinal closure); window pairs perturb by
  `o_K(1)`. Discharge: size-minimality contradiction (B1
  shipped, mg-805c).
* **G4 (shallow layered, `K < K₀`).** Reduces to
  `prop:in-situ-balanced` over a bounded-depth bipartite-band
  configuration. Cases 1 (ambient match) and 2-symmetric
  (FKG profile-ordering / `Equiv.swap`) close in tree; Cases
  2-strict and 3 are the residual `hC3` content.

**Tag T10 (G3 vs G4 separation).** ε-close-to-ordinal-sum
reductios target G3 by construction (the cutting lemma
produces `A ⊕ B` with controlled window). They have **no
direct purchase on G4** — G4 is shallow-layered with `K = 2,
3, …, K₀ - 1`, where the cutting lemma either does not apply
or produces a degenerate cut (the `Mid = α` collapse at K=2
documented in `path-c-cleanup-roadmap.md` §5).

### 1.9 Memory anchors (read and incorporated)

* `feedback_audit_bar_for_axioms` — 4-condition test for any
  proposed new axiom (external + difficult + clearly labelled
  + low-risk). Applied in §§2.6, 3.4.
* `feedback_signature_regressions` — replacing `hC3` with
  another opaque hypothesis is not progress. Applied per T1.
* `feedback_distinguish_arc_chunk_outcomes` — substantive
  vs. cleanup chunks distinguished honestly. Applied to the
  outcome class declaration in §0.
* `feedback_latex_first_for_math_simp` — this arc is
  latex-rigor; no Lean source changes; applied throughout.
* `feedback_increments_authorized` — file polecat-ready
  dependency chain rather than re-litigating; applied in §4
  by referencing tags T1–T10 instead of re-deriving them.

### 1.10 Audit closure

The audit consumed **~120k tokens** of orientation reading. The
12 source documents collectively define a constraint system on
the search space; tags T1–T10 capture the constraints that any
new framing must satisfy or address. The remainder of this doc
operates within these constraints.

---

## 2. Multi-definition ε-close-to-ordinal-sum exploration (mandated §2)

This section is the substantive search the brief asked for. We
enumerate **eight** distinct definitions of "ε-close to ordinal
sum"; for each, we (a) specify the definition formally, (b)
derive (or attempt to derive) the implied bound on
`|p_xy(P) − p_xy(A ⊕ B)|`, (c) check whether a reductio using
this definition would close the case-2-strict K=2 + w ≥ 1
N-poset family, and (d) deliver a feasibility verdict.

The eight definitions span four kinds of measure:
**combinatorial** (§§2.1, 2.2), **probabilistic** (§§2.3, 2.4),
**linear-extension counting** (§§2.5, 2.6), and **structural /
spectral / decomposition-based** (§§2.7, 2.8). The intent is
breadth, not exhaustiveness — the goal is to identify whether
*any* of the natural definitions yields a tractable reductio.

For each definition we use the conventions: `P = (X, ≤_P)` is
a width-3 non-chain poset; `(A, B)` is a candidate ordered
partition `X = A ⊔ B` with `A, B ≠ ∅`; `A ⊕ B` denotes the
ordinal sum (every `a ∈ A` below every `b ∈ B`). For the
balanced-pair lift, `(x, y)` is incomparable in `A` (or `B`)
with `Pr_A[x < y] ∈ [1/3, 2/3]`; we want `Pr_P[x < y]` in
`[1/3 − γ, 2/3 + γ]` where `γ < 1/3 − 0.276 ≈ 0.057`.

### 2.1 Definition D1 — Edge-edit distance

**Definition.**
```
ε_edit(P) := min over (A, B) of
  |{(a, b) ∈ A × B : a ⊀ b}|
  + |{(b, a) ∈ B × A : b <_P a}|.
```

The first sum counts cross-edges *missing* from `A ⊕ B`; the
second counts cross-edges *wrong-way* in `P` relative to
`A ⊕ B`. `ε_edit = 0` iff `P = A ⊕ B`. Edge-edit distance is
the natural graph-edit metric on Hasse / comparability graphs.

**Implied perturbation bound.** Each edge-edit corresponds to
adding/removing one comparability. The single-edge edit
operator on a poset has bounded-but-unwieldy effect on
linear extensions: adding an edge `a < b` removes all LEs with
`pos(b) < pos(a)` (no clean per-element bound). Brightwell-
style coupling is between `Q` and `Q − {z}`, **not** between
`Q` and `Q + edge`. There is no in-tree single-edge-edit
coupling.

For an *additive* edge-edit count `k = ε_edit`, naive iteration
gives bounds of the form `2k` (each edit can flip up to a
constant fraction of LEs in worst case; tightening this needs
structure that doesn't exist in tree).

**Closure on K=2 N-poset.** N-poset has `ε_edit = 2` (two
missing cross-edges out of four) at the natural cut; minimum
cut has `ε_edit = 2`. The "near-ordinal" case of D1 fires
with `ε_edit ≥ 2`. The implied bound `2k ≈ 4` is **vacuous**
(any probability is in `[0, 1] ⊆ [−4, 5]`).

**Verdict.** **RED.** Edge-edit lacks an in-tree per-edit
coupling; even if it had one, the N-poset's `ε_edit = 2`
falls outside any plausible "small ε" regime where `f(ε) ≤ γ`.
**Does not address T7 (N-poset isn't an ordinal sum) or T10
(G4 not addressable by ordinal cuts).**

### 2.2 Definition D2 — Cardinality-overlap (per-pair)

**Definition.** This is arc 1.0's per-pair definition,
restated for completeness:
```
ε_pp(P, A, B) := |{(a, b) ∈ A × B : a ⊀ b}| / (|A| · |B|).
```
ε_pp ∈ [0, 1]; `ε_pp = 0` iff `(A, B)` is a true ordinal cut.

**Implied perturbation bound.** The strongest in-tree bound,
via `exc_perturb` iterated along `B`'s deletion sequence (T6),
is:
```
| Pr_P[x < y] − Pr_A[x < y] | ≤ 2|B| / (|A| + 1)    for x, y ∈ A.
```
This bound is **size-based, not ε-aware** — for balanced cuts
`|A| ≈ |B| ≈ n/2` it stays at `≈ 2`, regardless of how small
`ε_pp` is. Arc 1.0 A1 RED-fallback'd here (T6, mg-3d9d).

**Closure on K=2 N-poset.** N-poset has `ε_pp = 2/4 = 1/2` at
the natural cut. The "near-ordinal" case requires `ε_pp ≤ ε₀`
where `f(ε₀) ≤ γ ≈ 0.057`; with the available bound, no
finite `ε₀` works at all. The N-poset is **outside the
near-ordinal regime** under D2 even at its tightest.

**Verdict.** **RED — confirms arc 1.0 A1.** This is the
RED-fallback verdict on record; arc 3.0 reproduces it for
audit symmetry. **Tag T6.**

### 2.3 Definition D3 — Probability-defect (sup over bulk pairs)

**Definition.**
```
ε_prob(P, A, B) :=
  max
    ( max_{x, y ∈ A bulk} |Pr_P[x < y] − Pr_A[x < y]|,
      max_{x, y ∈ B bulk} |Pr_P[x < y] − Pr_B[x < y]| ).
```

Where "bulk" means `x, y ∈ A \ W` (or `B \ W`) for `W` the
window of `lem:cut`. `ε_prob = 0` iff every bulk-pair
probability transfers exactly from `A` (resp. `B`) to `P`.

**Implied perturbation bound.** **Tautological.** The
definition is `|Pr_P − Pr_A| ≤ ε_prob`, by construction.
**Trivially `f(ε) = ε`, with `f(0) = 0`.**

**Why this looks like it works (and doesn't).** D3 looks
attractive: it *defines* the perturbation bound to be small
when `ε_prob` is small. But the trichotomy then requires
**bounding `ε_prob` from a structural quantity**:

* Decomposable case (`ε_prob = 0`): exact ordinal sum, lift
  via `OrdinalDecomp.hasBalancedPair_lift` (mg-7f06). **Fine,
  but tautological — the case is `Pr_P = Pr_A` exactly.**
* Near-ordinal case (`0 < ε_prob ≤ ε₀(γ)`): lift via the
  defining inequality. **Fine, but circular — we haven't
  shown which posets are in this regime.**
* Far-from-ordinal case (`ε_prob > ε₀`): need
  `δ(P) ≥ 1/3` directly. **Where does this come from?**

The far-from-ordinal closure under D3 is the **same
unconditional-or-K=2 obstruction** as in arc 1.0 D's Brightwell
pump tightening: we need a direct correlation-inequality
bound on a poset whose only structural property is "no cut
makes bulk-probabilities transfer cleanly." That is paper-level
math (T8).

The decomposable / near-ordinal case under D3 is similarly
hollow: we have not shown that *any* layered counterexample
satisfies `ε_prob ≤ ε₀` for a non-trivial fraction of cuts.
The K=2 N-poset has `ε_prob = max_{(x_1, x_2)} |1/2 − 1/2| = 0`
at the *trivial* cut where bulk is empty, but `ε_prob > 0` at
every nontrivial cut.

Most importantly: D3 is **defined in terms of the very
quantity we are trying to control**, so it carries no
independent structural information about `P`. It is a
*relabelling*, not a definition.

**Closure on K=2 N-poset.** N-poset has `Pr_P[x_1 < x_2] = 1/2`
(by direct count of 6 LEs). The "near-ordinal" case under D3
fires with `ε_prob = 0` at the cut `A = {x_1, x_2}`, but in
the trivial `B \ W = ∅` configuration. The lift via D3's
tautological bound succeeds — but the cleanness is illusory:
we've computed `Pr_P` directly and packaged it as
"perturbation from `A`'s probability," which is a definitional
restatement of the answer.

**Verdict.** **RED — definitionally circular.** D3 trades
the perturbation bound's *substance* for its *form*, leaving
the trichotomy's far-from-ordinal closure to carry the same
paper-level burden as arc 1.0 D / arc 2.0 framing 2b.
**Tag T8.**

### 2.4 Definition D4 — Total-variation distance on linear extensions

**Definition.**
```
ε_TV(P, A, B) :=
  TV( Unif(LE(P)), Unif(LE(A) × LE(B) under shuffle to A⊕B order) ).
```

I.e., the total variation distance between the uniform
distribution on `LE(P)` and the uniform distribution on the
"factorised" measure given by independently choosing
`L_A ∈ LE(A)`, `L_B ∈ LE(B)`, and shuffling them as `L_A`
followed by `L_B` (the LEs of `A ⊕ B`). `ε_TV = 0` iff
`P = A ⊕ B` (each LE of `P` is uniquely a shuffle).

**Implied perturbation bound.** Standard probability-coupling
argument: for any event `E` measurable in both spaces,
```
|Pr_P[E] − Pr_{A⊕B}[E]| ≤ ε_TV.
```
For `E = {x <_L y}` with `x, y ∈ A`, this gives
```
|Pr_P[x < y] − Pr_A[x < y]| ≤ ε_TV.
```
This *is* `f(ε) = ε`, `f(0) = 0`. **Aesthetically clean.**

**The catch.** In-tree, `ε_TV` has no direct structural
interpretation. Bounding `ε_TV` from above via cardinality
or comparability data requires:
```
ε_TV ≤ 1 − |LE(A)| · |LE(B)| · (binomial shuffle count) / |LE(P)|
     = 1 − θ
```
where `θ` is the per-volume normalisation flagged in the
mg-3d9d `ε_pv` row. arc 1.0 A1 §3.4 already analysed this:
```
θ ≥ ∏_{(a,b) bad} p_{ab}(P)   [FKG, lower bound on θ]
```
which is **exponentially small** in the number of bad pairs
(FKG goes the wrong way for our needs in this regime).
Equivalently, `ε_TV` lower-bounds approach 1 even when
`ε_pp` is small.

**A second catch.** The "factorised" measure is not the
genuine `Unif(LE(A ⊕ B))` unless `A` and `B` are LE-independent
(which is what `ε_TV = 0` says). For `P` with comparabilities
crossing `(A, B)` in *both* directions (some `a < b` and some
`b < a`), the shuffle definition is itself ambiguous; we'd
need a sign-decorated variant, doubling the analytical
burden.

**Closure on K=2 N-poset.** `LE(P) = 6` for the N-poset;
`LE(A ⊕ B)` for `A = {x_1, x_2}`, `B = {y_1, y_2}` is
`2 · 2 · binomial(4, 2) / 1 = 24` (no, wait — `LE(A ⊕ B) =
|LE(A)| · |LE(B)| = 4` since shuffles are forced by ordinal
sum). So
```
ε_TV ≥ 1 − 4/6 = 1/3.
```
Close to the headline `γ` but in the wrong direction —
`ε_TV ≈ 1/3` means the "near-ordinal" case fails for
`f(ε₀) ≤ γ ≈ 0.057`. The N-poset is again **outside the
near-ordinal regime**.

**Verdict.** **RED.** `ε_TV` has the cleanest tautological
perturbation bound, but bounding it structurally from
ε_edit / ε_pp / etc. drops out of FKG with the wrong
direction (T6 confirmation). Far-from-ordinal closure is
again paper-level (T8). **Same fundamental obstruction as
D2/D3, dressed differently.**

### 2.5 Definition D5 — Linear-extension-count ratio

**Definition.**
```
ε_LE(P) := min over (A, B) of
  ( |LE(A ⊕ B)| − |LE(P)| ) / |LE(A ⊕ B)|.
```

Note: `|LE(P)| ≤ |LE(A ⊕ B)|` whenever `(A, B)` is an ordinal
cut (each LE of `P` is an LE of `A ⊕ B`); `ε_LE ≥ 0`.
`ε_LE = 0` iff `LE(P) = LE(A ⊕ B)`, i.e., `P = A ⊕ B`. This
is Brightwell-pump territory: classical Brightwell bounds
relate per-pair probabilities to LE-count ratios via the
single-element coupling.

**Implied perturbation bound.** Brightwell's
sharp-centred-cousin inequality gives, for `Q = α ⊔ {z}`
and `Q' = α`:
```
|Pr_Q[x < y] − Pr_{Q'}[x < y]| ≤ 2 / |Q|.
```
The natural multi-element generalisation we'd want is
something like:
```
|Pr_P[x < y] − Pr_{A⊕B}[x < y]| ≤ 2 · ε_LE / (something).
```
But this is exactly the **multi-element / ordinal-cut Brightwell
variant** flagged in arc 2.0 framing 1's audit-bar test (T8) —
not in tree, fails 2/4 audit conditions, Daniel-only override.
The deferred A8-S2-cont scope (~2000–3500 LoC,
probability-normalised cross-poset FKG) **is** a path here, but
that is paper-tier infrastructure work, not "math
simplification."

**A subtler observation.** Even if such a bound existed, its
strength would be controlled by the *count ratio*, not by any
combinatorial defect. Counts can vary wildly: a single
"misplaced" comparability can flip `|LE(P)|` by a factor of 2
or more for small `n`, while a sea of misplacements can leave
the count nearly unchanged. The K=2 N-poset has `|LE| = 6` vs.
`|LE(A⊕B)| = 4` (oh wait, that's the wrong direction —
`LE(P) ⊋ LE(A⊕B)` since the N-poset has fewer comparabilities,
so more LEs). So `ε_LE` is **negative** in our convention; we
take instead the symmetric definition
`|LE(P) − LE(A⊕B)| / max(LE(P), LE(A⊕B))`. Either way,
the count ratio carries no clean per-pair information.

**Closure on K=2 N-poset.** `|LE(A⊕B)| = 4`, `|LE(P)| = 6`,
ratio `2/3` or `1/3` depending on which way you normalise.
Any non-degenerate ε-threshold at `0.057` excludes this case
firmly.

**Verdict.** **RED.** `ε_LE` is structurally interesting (it
is the natural object for Brightwell-pump arguments in the
literature) but the corresponding multi-element Brightwell
bound is the audit-bar-failed framing-1 axiom from arc 2.0
(T8). **No in-tree route.**

### 2.6 Definition D6 — Spectral defect (BK eigenvalue gap)

**Definition.** For `P` and reference `A ⊕ B`, let
`G_BK(P), G_BK(A ⊕ B)` be the Bubley-Karzanov graphs on
`LE(P), LE(A ⊕ B)`. Define
```
ε_spec(P, A, B) := |λ_2(G_BK(P)) − λ_2(G_BK(A ⊕ B))|
```
where `λ_2` is the second eigenvalue (= conductance modulo
Cheeger). `ε_spec = 0` does **not** generally imply
`P = A ⊕ B` (eigenvalues are coarse), so this is a weaker
definition than D1–D5 above.

**Implied perturbation bound.** **Tautological in the wrong
direction.** Cheeger's inequality bounds *conductance* by
eigenvalues; conductance is the BK-graph quantity that drives
Theorem E (`thm:cex-implies-low-expansion`). The current paper's
Step-8 argument is built on Cheeger; replacing the perturbation
machinery with a spectral one would re-package Cheeger as a
black box.

A bound of the form `|Pr_P − Pr_{A⊕B}| ≤ g(ε_spec)` does not
exist generically (eigenvalues are functions of *all*
LE-pairs, not per-pair probabilities). The natural inequality
goes the other way: `g(ε_pair-of-probs) ≤ ε_spec`.

**The deeper issue.** The current proof's Steps 5–7 *prove*
a Cheeger-type lower bound on conductance from structural
input (rich-pair coherence, layered globalisation). To use
`ε_spec` as the trichotomy invariant, we'd need an
*independent* control on `λ_2(G_BK(P))` from cardinality /
combinatorial data — which is exactly the kind of bound the
Cheeger / Steps 5–7 machinery already produces, by a
substantively non-trivial argument.

**Closure on K=2 N-poset.** Computing `λ_2(G_BK(N-poset))` is
straightforward (it's a finite walk on a 6-LE state space)
but yields no useful bound on `Pr_{x_1 < x_2}` without going
through the in-tree fiber model.

**Verdict.** **RED — tautological in load-bearing direction.**
Spectral defect is a re-packaging of the Cheeger machinery the
proof already uses. Replacing the in-tree perturbation
machinery with a spectral one would need to *derive* the
spectral bound from structure — the same content as Steps
5–7 (T8 / arc 1.0 A1 §3.6).

### 2.7 Definition D7 — Layered-position / coherence defect (Step 7 norm)

**Definition.** For a width-3 layered poset `P` (with
decomposition `X = L_1 ⊔ … ⊔ L_K`), let
`a : X → ℝ` be the Step 7 monotone potential
(`step7.tex:1004-1013`) and `f_{AB}, f_{AC}, f_{BC}` the
synchronisation maps. Define
```
ε_layer(P) := ||a − band(·)||_∞
              + sum over chain pairs of bandwidth-excess.
```
(The brief's gloss; concretely, this is the L^∞ deviation of
`a` from a clean band-step function, plus the bandwidth
excess flagged in `step8.tex:1879-2360`'s
`X^{exc}_{band} ∪ X^{exc}_{sync}` exceptional sets.)
`ε_layer = 0` iff `P` is *exactly* layered with synchronisation
maps preserving band index.

**Implied perturbation bound.** `lem:layered-from-step7`'s
exceptional-set transfer (`step8.tex` item-iii of that lemma)
gives:
```
|Pr_P[x < y] − Pr_{P|_{X \\ X^{exc}}}[x < y]|
  ≤ 2 · |X^{exc}| / (|X| − |X^{exc}| + 1).
```
For Step-7-derived `|X^{exc}| = O_T(1)`, this is `O(1/n)` —
**genuinely `→ 0` for large `n`**. So D7 has the right
asymptotic structure for the *G3* (deep-layered) branch. This
is essentially what the in-tree `lem:layered-reduction`
(B1-shipped) already uses.

**Closure on K=2 N-poset.** **Fails fundamentally.** The
N-poset has `K = 2`, so the deep-layered prerequisite
`K ≥ K_0(γ, w)` of `lem:layered-reduction` is **violated**
by 2 to several orders of magnitude. `ε_layer` is structurally
small for the N-poset (it *is* layered), but the
exceptional-set lift requires `n ≫ |X^{exc}|`, which
**at K=2 with `|α| = 4` is not satisfied**.

In other words: D7 is the actual structural gauge that
`lem:layered-reduction` consumes — but it's already in tree,
and it's the **G3** branch, not G4. T10 says G4 is where
case-2-strict / N-poset sit, and G4 is shallow-layered, where
D7 doesn't bite.

**Verdict.** **RED for the headline goal.** D7 is the right
gauge for G3 and is already deployed as such; it does not
help the G4 branch where `hC3` lives. **Tag T10.**

### 2.8 Definition D8 — Comparability-graph defect (under width-3 Dilworth)

**Definition.** Let `P` have Dilworth chains `A_1, A_2, A_3`
(width 3). Define
```
ε_comp(P) := min over choice of "lower"/"upper" assignments of
  (# comparabilities crossed wrong) / (# comparabilities total).
```
I.e., for a fixed Dilworth decomposition, label each chain
"L" or "U" and count the cross-chain comparabilities that
violate `L → U` direction; minimise over labellings.
`ε_comp = 0` iff some Dilworth labelling gives a clean ordinal
cut at the chain level.

**Implied perturbation bound.** Cross-chain Dilworth structure
is what powers the in-tree fiber model (Step 1–4). A
comparability-graph-defect-driven bound goes through the same
content as Steps 5–7's globalisation lemma; arc 1.0 A1 §3.6
documents this collapse. **No bound is derivable from D8 alone;
the path is via Steps 5–7 → Cheeger → Theorem E**, exactly
the rigidity argument the simplification is meant to replace.

**Closure on K=2 N-poset.** N-poset has chains
`{x_1, y_1}, {x_2, y_2}` (or `{x_1}, {x_2}, {y_1, y_2}`
under a different Dilworth); `ε_comp` ∈ {0, ...}. **The
N-poset *is* a clean Dilworth decomposition** with
`{x_1, y_1}` and `{x_2, y_2}` as the two non-trivial chains —
both internally totally ordered, no comparabilities to "cross
wrong." So `ε_comp = 0` for the N-poset under one labelling,
yet the N-poset is not a true ordinal sum (T7).

**The catch.** D8 conflates Dilworth-chain-labelling cleanness
with ordinal-sum cleanness. The N-poset has ε_comp = 0
because every cross-chain comparability is L→U (`x_i < y_i`),
but the *missing* cross-comparabilities (`x_1 ⊀ y_2`,
`x_2 ⊀ y_1`) make it not an ordinal sum. D8 is **necessary
but not sufficient** for ε-close-to-ordinal-sum.

**Verdict.** **RED — captures the wrong invariant.** D8 is
satisfied by the load-bearing obstruction (N-poset), so it
doesn't separate "near-ordinal" from "obstruction" the way
the trichotomy needs.

### 2.9 Cross-cutting findings from §2

Eight definitions; eight RED verdicts. The common patterns:

1. **The decomposable case (`ε = 0`) is fine for all eight**
   — true ordinal sum lift is provided by mg-7f06's
   `OrdinalDecomp.hasBalancedPair_lift_*`. **None of the
   definitions removes the in-tree `OrdinalDecomp` machinery;
   the question is what the *near*-ordinal and
   *far*-from-ordinal cases look like.**

2. **The near-ordinal case bifurcates into two failure modes.**
   * **(a) Tautological / circular** (D3, D4, D6): the
     definition packages the perturbation bound as the
     definition itself, leaving the *bound on `ε`* as the
     real burden. That bound goes through FKG / Brightwell
     in the wrong direction (D4) or through Cheeger / Steps
     5–7 (D3, D6). **Same content as arc 1.0 D, dressed up.**
   * **(b) In-tree perturbation is size-based** (D1, D2, D5):
     the bound that *does* exist (Brightwell single-element
     iterated to multi-element via `exc_perturb`) is `Θ(1)`
     for balanced cuts, regardless of how small the
     combinatorial defect is. **Tag T6 reproduced.**
   * D7 has the right asymptotic but fires only for G3 (deep
     layered), not G4. **Tag T10 reproduced.**
   * D8 conflates Dilworth-cleanness with ordinal-sum-cleanness
     and is satisfied by the N-poset itself.

3. **The far-from-ordinal case is paper-level math under all
   eight definitions.** Either it goes through a
   width-3-tightening of Kahn-Linial / Brightwell-pump (arc
   1.0 D / arc 2.0 framing 4 / T8), or it goes through the
   existing Steps 5–7 rigidity argument (defeating the
   purpose). No definition gives an in-tree shortcut.

4. **The K=2 N-poset is outside the near-ordinal regime under
   every definition that has a meaningful "near" threshold.**
   Numerically:
   * D1 `ε_edit = 2`.
   * D2 `ε_pp = 1/2`.
   * D3 `ε_prob ∈ (0, 1)` at non-trivial cuts.
   * D4 `ε_TV ≈ 1/3`.
   * D5 `|LE| ratio ≈ 2/3`.
   * D6 `ε_spec` non-trivial.
   * D7 `ε_layer = 0` (it IS layered) but K too small for the
     transfer to fire.
   * D8 `ε_comp = 0` but N-poset isn't an ordinal sum (T7).

   No definition makes the N-poset "near-ordinal" in a way that
   enables a perturbation lift. **Daniel's hypothesis — that
   different ε definitions might unlock a tractable reductio —
   does not survive eight tries.**

5. **The G3 vs G4 split (T10) is the structural reason.**
   ε-close-to-ordinal-sum reductios are *defined* on cuts
   `(A, B)` — i.e., a partition with combinatorial / probabilistic
   structure connecting `A` and `B`. The G3 branch has such
   cuts (the cutting lemma constructs them). The G4 branch is
   shallow layered — at K=2 the "cut" is degenerate (a single
   band boundary, with both bands required to be antichains
   and the cross-band relation already specified by `forced_lt`
   and `cross_band_lt_upward`). There is **no cut to make
   ε-close-to-ordinal-sum** at K=2 + irreducible.

   Equivalently: at K=2 + irreducible the only cuts `X = A ⊔ B`
   are the band-cut (which is what `LayeredDecomposition`
   already uses, and `LayerOrdinalIrreducible` rules out as
   non-trivially decomposable) and ad-hoc Dilworth-chain cuts
   (which cross-cut bands and have no clean ordinal-sum
   semantics). **An ε-close framing has no purchase here.**

### 2.10 §2 summary table

| Def | Substance | Bound type | f(ε) → 0? | K=2 N-poset | Verdict |
|---|---|---|---|---|---|
| D1 edge-edit | combinatorial | no in-tree per-edit coupling | n/a | `ε_edit = 2` (outside near regime) | **RED** |
| D2 per-pair | combinatorial | size-based via `exc_perturb` | **NO** (T6) | `ε_pp = 1/2` (outside) | **RED** (= arc 1.0 A1) |
| D3 prob-defect | probabilistic | tautological | YES (defn) | `ε_prob > 0` at non-triv cuts | **RED** (circular; T8) |
| D4 TV | probabilistic | tautological | YES (defn) | `ε_TV ≈ 1/3` (outside) | **RED** (T6 wrong dir) |
| D5 LE-count | counting | needs multi-elem Brightwell | YES if axiom | ratio ≈ 2/3 (outside) | **RED** (= arc 2.0 fr 1) |
| D6 spectral | spectral | tautological in wrong dir | n/a | non-trivial | **RED** (= arc 1.0 D / T8) |
| D7 layered | structural | `O(1/n)` via Step 7 | YES | K too small (T10) | **RED for G4** |
| D8 comp-graph | combinatorial | needs Steps 5–7 | n/a | `ε_comp = 0` but N≠⊕ (T7) | **RED** (wrong invariant) |

**Aggregate verdict on §2.** **All eight definitions RED.**
The three pathologies (size-based bounds, tautological
definitions, Steps-5–7-equivalent content) reproduce arc 1.0
A1 and arc 2.0 framings 1/2/4. Daniel's hypothesis does not
yield a GREEN definition.

---

## 3. Strategy-level alternatives (mandated §3)

The brief asks: beyond multi-definition ε-close, are there
**different proof scaffoldings** — drop BK/Cheeger, drop layered
decomposition, different reductio target, pure counting — that
make the math tractable? This section evaluates each.

### 3.1 Strategy S1 — Drop BK / Cheeger; go via direct correlation inequalities

**The proposal.** The current proof uses
* Step 8 G1 / Theorem E: BK-graph low-conductance cut
  forced by `IsGammaCounterexample`.
* Cheeger / fiber model (Steps 1–4): low-conductance cuts
  must be "rigid" on each fiber.
* Coherence / globalisation (Steps 5–7): rigid cuts globalise
  to a layered decomposition.

A direct correlation-inequality argument bypasses all of this:
take `δ(P) ≥ 1/3` as the conclusion to prove; route via
Brightwell 1989 / Kahn-Linial 1991 / Kahn-Saks 1984 covariance
bounds on `LE(P)`, specialised to width-3 Dilworth structure.

**Status.** This is **arc 1.0 candidate D / arc 2.0 framing 4**,
already RED'd in both arcs:

* arc 1.0 D: "fundamentally new math; out of polecat scoping
  authority."
* arc 2.0 framing 4: "multi-week external collaboration;
  RED-fallback."

A "width-3 tightening of Kahn-Linial" of this kind has
presumably been attempted by the original Kahn-Linial /
Brightwell line of authors over decades. The current paper's
BK / Cheeger framework was developed precisely because the
correlation-inequality approach appeared stuck below `1/3`.
Reviving it as the *primary* proof would be a paper-level
research arc.

**Closure on K=2 N-poset.** `Pr_{x_1 < x_2} = 1/2` is provable
by a one-line direct count in the N-poset; the question is
whether an **abstract** argument (not specific to the
N-poset) closes the K=2 + w ≥ 1 + |β| ≥ 3 family uniformly.
Width-3 Dilworth specialisation of Kahn-Linial **might**
do this, but it's an open math question.

**Verdict.** **RED — paper-level math discovery.** Polecat
scoping authority does not extend here. If Daniel commissions
this as a research arc, the appropriate venue is a literature
audit + external collaboration, not a polecat ticket.

### 3.2 Strategy S2 — Drop layered decomposition entirely

**The proposal.** The layered decomposition (Step 7) is what
surfaces the case-2-strict family; if the proof never invoked
layering, the case-2-strict obstruction would not exist *in
those terms*. Replace layered → with what?

Three sub-options:

**S2a — Direct width-3 Dilworth argument.** The width-3 hypothesis
is consumed twice: (i) by the layered decomposition's `|L_i| ≤ 3`
constraint, and (ii) by the Step-4 two-interface incompatibility
specialised to 3 chains. Could a direct Dilworth-3-chain argument
bypass layering?

* **Status.** Same content as Steps 5–7 — the layered
  decomposition *is* the in-tree organisation of the
  Dilworth-3-chain rigidity. Replacing it with a "direct"
  Dilworth argument either (i) reproduces Steps 5–7 under
  different names (illusory), or (ii) is a paper-level
  reorganisation that needs a fresh mathematical idea.
* **Closure on K=2 N-poset.** N-poset has Dilworth chains
  `{x_1, y_1}` and `{x_2, y_2}`; the cross-chain
  comparabilities are `x_i < y_i`. A direct Dilworth argument
  on this 2-chain (width 2!) cover gives the well-known
  width-2 Linial 1984 result `δ ≥ 1/3`. **BUT:** width-3
  Dilworth on the N-poset (treating it as width 2 embedded in
  width 3) doesn't help the larger family — the K=2 +
  irreducible + w ≥ 1 + |β| ≥ 3 family includes width-3-strict
  examples beyond N-poset.
* **Verdict.** **RED.** Same as S1 (paper-level math) plus
  the additional risk that the "drop layering" framing
  reproduces Steps 5–7 by accident.

**S2b — Coupling argument over Dilworth chains.** Linial's
width-2 proof uses a coupling between `LE(P)` and `LE(P')`
where `P'` differs from `P` by one comparability; the resulting
coupling controls `δ(P)` directly. Width-3 generalisation:
take three coupled Dilworth chains, show that some pair has
`δ ≥ 1/3` by symmetry / pigeonhole.

* **Status.** This is *also* the width-3 tightening of
  Kahn-Linial (arc 1.0 D / S1 above). The coupling approach
  is one specific version of S1. The reason it stalls at
  `0.276` (not `1/3`) in the published literature is that the
  width-3 case has more freedom than width-2 to avoid
  pigeonhole.
* **Verdict.** **RED — same as S1.**

**S2c — Direct enumeration / explicit computation for small
cases, structural for large cases.** The current proof's G3
(`lem:layered-reduction`) handles `|α| ≥ K_0(γ, w)` via deep
layering; G4 handles `K < K_0` (small-case) via dispatch. The
direct enumeration option is to extend G4's dispatch to handle
case-2-strict + case-3 mechanically.

* **Status.** This is **arc 2.0 framing 3 sub-B2** (finite
  enumeration K=2 case-2-strict certificate, ~300–500 LoC,
  AMBER as Track 1 fallback only). It is **mechanical, not
  aesthetic**, and competes with Track 1 rather than
  complementing it.
* **Closure on K=2 N-poset.** Direct enumeration of the
  N-poset's 6 LEs gives `Pr_{x_1 < x_2} = 1/2`; mechanical.
  The certificate would extend this to all K=2 + irreducible
  + w ∈ {1,2,3,4} + |α| ≤ 6 isomorphism classes, finite list.
* **Verdict.** **AMBER — mechanical fallback only.** Not a
  math simplification per the brief's "fresh framing"
  criterion. Competes with Track 1; may be commissioned as a
  shrink-the-gap arc if Track 1 stalls (per arc 2.0 §6.3),
  but not as the headline simplification deliverable.

### 3.3 Strategy S3 — Different reductio target

**The proposal.** The current proof (B1-post) is a **reductio
on minimal counterexamples**: assume `P` is a `γ`-counterexample
of minimal size, derive contradiction. The contradiction takes
the form *"P has a balanced pair, not a counterexample"* (G3, G4).

Alternative reductio targets:

**S3a — Reductio via "no low-conductance cut exists."** Theorem E
already gives a low-conductance cut from a counterexample. The
*reverse* direction — showing that no width-3 non-chain admits a
low-conductance BK-cut — would be a direct contradiction. This
is morally the existing rigidity argument inverted.

* **Status.** Same content as Steps 1–7 with sign flipped.
  Doesn't simplify anything. **RED.**

**S3b — Reductio via "small substructure forces non-low-conductance."**
Identify a small substructure (e.g., a specific 5-element
configuration) that, if present in `P`, forces `Φ(P) ≥ 1/2`
(say). Then: counterexample → low conductance → no small
substructure → ... → contradiction.

* **Status.** This is essentially **Step 4's two-interface
  incompatibility lemma**, already in tree (`step4.tex`).
  Re-organising the proof around it does not eliminate the
  load-bearing content; it relabels.
* **Verdict.** **RED — same content.**

**S3c — Probabilistic reductio: "if `δ(P) < 1/3`, the linear
extension distribution has a forbidden moment."** Compute some
moment of `Unif(LE(P))` (e.g., variance of position
distributions) and show `δ < 1/3` forces a contradiction with
a structural moment bound.

* **Status.** This is the **Kahn-Saks 1984** / **Brightwell
  1989** / **Kahn-Linial 1991** approach. Stuck at `0.276`
  for general posets; tightening to `1/3` for width 3 is S1.
  **RED for arc 3.0 reasons (paper-level math).**

**Aggregate verdict on S3.** **All RED.** The reductio
*target* choice is downstream of the *machinery* choice; you
can re-package the same content as a contradiction with
different statements, but you cannot eliminate the content.

### 3.4 Strategy S4 — Pure counting argument (Linial 1984 width-3 generalisation)

**The proposal.** Linial 1984's width-2 proof is essentially a
**counting argument**: enumerate the LEs of an N-poset (or
N-poset-like configuration), observe that `Pr[x_1 < x_2]` is
exactly `1/3` by direct count, conclude `δ_2^* = 1/3`. Could
a width-3 generalisation work?

**The math.** The width-3 N-poset family is much larger than
width 2's single N-poset. The K=2 + irreducible + w ≥ 1 +
|β| ≥ 3 N-poset family alone is infinite (parameters
`|A|, |B| ∈ ℕ`, with bipartite incidence patterns of various
shapes). A pure counting argument would need a uniform bound
across this family, derived from the bipartite incidence
structure.

**Status.** Two failure modes:

* **Width-3 Linial-style closure exists in published literature
  if and only if `δ_3^* = 1/3` is provable by elementary
  combinatorics.** That has not been done (the strongest
  general result is `0.276`, the strongest width-3 result is
  this paper's BK-Cheeger-rigidity argument). **Paper-level
  research.**
* **Approximating it with finite enumeration** (arc 2.0
  framing 3 sub-B2 / S2c) is the mechanical fallback, AMBER
  as Track 1 fallback only.

**Closure on K=2 N-poset.** N-poset (4-element form) has
`Pr = 1/2` by direct count; K=2 + irreducible + w ≥ 1 + |α| = 3
configurations have `Pr = 1/3` by direct count (the strict
boundary). A finite-enumeration certificate for `|α| ≤ 6`
covers everything; for `|α| > 6` we need a structural
argument, which is back to S1/S2/S3.

**Verdict.** **RED for the headline goal.** Pure counting is
either (i) finite enumeration (= arc 2.0 framing 3 sub-B2,
AMBER) or (ii) abstract counting (= S1/S2/S3, paper-level).

### 3.5 Strategy S5 — Restructure around `lem:cut` not `LayeredDecomposition`

**Polecat-original.** The brief invites polecat-invented
strategies. Here is one:

The cutting lemma `lem:cut` (`step8.tex:2164-2186`) takes a
deep-layered poset and produces an ordinal cut `(A, B)` with
window `W` of size `≤ 6w`. The post-cut analysis (Step 3 ordinal
closure, Step 5(a) window perturbation) is **morally a single
ε-close-to-ordinal-sum trichotomy, with `ε := |W| · 2 / |X|`**
(the perturbation budget).

What if we *invert* the proof scaffolding so that `lem:cut`'s
window-sizing becomes the primary structural input, and the
layered decomposition becomes a *byproduct* of the window
analysis?

* **Status.** Reorganising existing content. The window analysis
  consumes Step 7's bandwidth; flipping the scaffolding doesn't
  remove that dependency. Net effect: **stylistic, not
  substantive.**
* **Closure on K=2 N-poset.** The cutting lemma fails at
  K=2 (its hypothesis is `K ≥ 2w + 2 = 4` for `w = 1`); the
  inverted scaffolding has the same failure mode (T10).
* **Verdict.** **RED — does not reach G4.**

### 3.6 Strategy S6 — Bypass G4 via a different `prop:in-situ-balanced` proof

**Polecat-original.** `prop:in-situ-balanced` is currently
discharged by Cases 1 / 2 / 3 dispatch, with Case 3 (and its
strict-2 sibling) being the residual `hC3` content. Replacing
the dispatch with a direct proof of the proposition would
obviate the case split.

The proposition's statement
(`step8.tex:2978-3032`):

> Every layered width-3 non-chain on `≥ 2` elements has a
> balanced incomparable pair.

A direct proof would need to handle every layered configuration
uniformly. Two natural routes:

**S6a — Profile-monotonicity argument.** Show that for any
layered width-3 configuration, *some* pair `(a, b)` of
incomparable elements has `Pr[a < b]` controlled by a
monotone function of layer indices and bipartite incidence
structure. Closes by pigeonhole.

* **Status.** This is morally the Step-7-coherence argument
  refined to a single proposition. Not new mathematical
  content; same Lean burden under different organisation.
* **Verdict.** **RED — equivalent content.**

**S6b — Replace dispatch with chain-form FKG sub-claim.** Drop
the explicit `hC3` and instead require a single sub-claim
hypothesis covering all of cases 2–3. This is **arc 1.0
candidate B's path** for the headline (replace `hC3` with
`hFKG`). The chain-form FKG sub-claim is mg-27c2's
`Case2FKGSubClaim`, and per T5 (mg-a79e) its natural direction
is **provably false**; the corrected direction (T5 again)
needs the missing `≤ 2/3` bound (T4). **RED at both.**

**S6c — Ambient-form discharge.** Lift the Case-1 ambient match
argument to all of Cases 1–3 by a clever global ambient. Risk:
case-2-strict does not have an ambient match (the strictness
witness `z` blocks the ambient swap by T3 cardinality
obstruction). **Retreats to T3.**

**Aggregate verdict on S6.** **All RED.** The dispatch is
where the case-2-strict + case-3 obstruction lives; replacing
the dispatch with a single proposition merely moves the
obstruction to the proposition's proof.

### 3.7 §3 summary table

| Strategy | Drops `hC3`? | Drops in-tree machinery? | In scope? | Verdict |
|---|---|---|---|---|
| S1 Drop BK/Cheeger | YES if works | YES | NO — paper-level | **RED** |
| S2a Direct Dilworth | YES if works | partially | NO — paper-level | **RED** |
| S2b Coupling over chains | YES if works | YES | NO — paper-level | **RED** |
| S2c Finite enum K=2 | partially (narrows) | partially | YES but off-criterion | **AMBER** as fallback |
| S3a Inverted Cheeger | NO | NO | NO — same content | **RED** |
| S3b Small substructure | NO | NO | NO — same content | **RED** |
| S3c Moment-based | YES if works | YES | NO — paper-level | **RED** |
| S4 Pure counting | YES if works | YES | NO — paper-level / fallback | **RED** |
| S5 Cut-first scaffolding | NO | NO | NO — stylistic | **RED** |
| S6a Profile monotonicity | YES if works | NO | NO — equivalent content | **RED** |
| S6b FKG sub-claim swap | YES if works | NO | NO — sub-claim is false (T5) | **RED** |
| S6c Ambient lift | YES if works | NO | NO — T3 cardinality | **RED** |

**Aggregate verdict on §3.** **Eleven of twelve RED, one
AMBER as Track 1 fallback only.** The single AMBER (S2c =
arc 2.0 sub-B2) is *not* a math simplification; it is a
mechanical certificate that competes with Track 1. The
"different organisation of in-tree machinery" search space is
not where the headline simplification lives.

---

## 4. Comparison + recommendation (mandated §4)

### 4.1 Headline verdict

**No GREEN multi-definition ε-close framing found. No GREEN
strategy-level alternative found.** The single AMBER (S2c =
arc 2.0 sub-B2) is a mechanical Track-1-fallback, not a math
simplification.

**Daniel's hypothesis is not borne out by the search.** The
working hypothesis was *"if things are this hard then the math
is the issue. We should be able to find a simpler argument."*
After eight ε-close definitions and twelve strategy-level
alternatives, the search returns the same three pathologies as
arcs 1.0 and 2.0:

1. **Tag T6 / T8 — The far-from-ordinal closure is paper-level
   math.** Every framing that drops the in-tree BK-Cheeger-fiber-
   coherence-globalisation infrastructure ends up needing a
   width-3 tightening of Kahn-Linial / Brightwell-pump that
   sits in the published `[0.276, 1/3)` gap — a question the
   field has not closed in 30+ years.

2. **Tag T6 / T8 — The near-ordinal closure needs a multi-element
   Brightwell variant.** The single-element coupling that the
   axiom + `exc_perturb` provide gives only size-based bounds,
   not ε-aware bounds. Distinguishing ε-close from
   far-from-ordinal at the perturbation level requires either a
   new project axiom (audit-bar-failed; Daniel-only override) or
   the deferred A8-S2-cont scope (~2000–3500 LoC, multi-polecat,
   paper-tier).

3. **Tag T10 — ε-close-to-ordinal-sum reductios target G3,
   not G4.** The case-2-strict obstruction lives in shallow
   layered (G4); ε-close framings have no purchase at K=2 +
   irreducible because there is no nontrivial cut to make
   ε-close-to-ordinal-sum.

### 4.2 Why the math IS this hard — the structural argument

Daniel's directive frames "if things are this hard then the math
is the issue" as a working hypothesis *to test, not a conclusion
to validate*. The §§2-3 search tested it and produced enough
evidence to flip the hypothesis: **the math is this hard because
the underlying combinatorial reality is genuinely subtle in this
regime**. Three structural facts converge to make the K=2 +
irreducible + w ≥ 1 + |β| ≥ 3 family resistant to simpler
arguments:

**Structural fact F1 (cardinality obstruction; Track 1, T3).**
Order-preserving permutations that swap a strict ⪯-pair don't
exist. This is a *finite-set* fact, not a Lean artefact, not a
paper-presentation artefact; it cannot be circumvented by
restructuring the proof.

**Structural fact F2 (Brightwell vacuity at small `|Q|`; T4).**
Single-element coupling produces bounds of order `2/|Q|`, which
at `|Q| ≤ 6` are vacuous for the `[1/3, 2/3]` containment. This
is a *quantitative* fact about the existing axiom; a sharper
single-element bound would require a substantively different
correlation inequality (= paper-level).

**Structural fact F3 (Linial-Kahn `[0.276, 1/3)` gap; T8).**
The published unconditional bound is `δ^* ≥ 0.276`; tightening
to `1/3` for width 3 specifically — without going through the
current paper's BK-Cheeger argument — has not been done. The
existence of this gap is *prima facie* evidence that
"correlation-inequality + width-3 specialisation" is not enough
on its own.

The current paper's BK-Cheeger-fiber-coherence-globalisation-
layered argument is the **first known path through these three
structural facts** to reach `δ_3^* = 1/3`. It is intricate
because the three facts together *force* it to be intricate:

* F1 rules out elementary symmetry on case-2-strict.
* F2 rules out direct probability bounds at small `|Q|`.
* F3 rules out direct correlation-inequality-only proofs.

Any simplification must navigate around all three. The eight
ε-close definitions and twelve strategy alternatives in this
arc each fail because they hit one of the three.

### 4.3 What this means for `hC3` retention

Per **Tag T1** and `feedback_signature_regressions`, replacing
`hC3` with another opaque universally-quantified hypothesis is
not progress. The intended cleanup (Path C, mg-7261 roadmap §6)
is to *prove* `Case3Witness` as a theorem, dropping `hC3` from
the headline; per **Tag T9** and the four-round Path C arc, the
in-tree path to that proof is blocked at the case-2-strict
N-poset family. Arc 3.0's exhaustive search confirms that no
strategy-level rewrite circumvents the blockage.

**Recommendation: retain `hC3` indefinitely under the existing
option-(δ) park decision.** This matches the in-tree retention
preamble at `lean/OneThird/MainTheorem.lean:39-51` (intentional
retention; do not attempt to drop without first reading
`docs/path-c-cleanup-roadmap.md`).

The alternative — admitting a new project axiom for the
multi-element / ordinal-cut Brightwell variant (arc 2.0
framing 1) — fails 2/4 conditions of `feedback_audit_bar_for_axioms`
(external + low-risk both fail; the bound is the *content* of
the existing rigidity argument, and a forum reader without the
audit trail would correctly read it as hiding unfinished proofs).
**Daniel-only call to override.**

### 4.4 What the next steps look like

This section is **not a commission**; per the brief, arc 3.0
is exploratory only. Possible next steps after arc 3.0 closes:

**N1 — Default: archive arc 3.0; Track 1 remains the live
path.** The active execution arc for `hC3` removal is
`mg-b666` (Track 1, on `main`). Arc 3.0's verdict reinforces
arc 2.0's recommendation: Track 1's structural impossibility
is structural; arc 3.0 finds no math-simp framing to bypass
it; the recommended action is to **retain `hC3` indefinitely**.

**N2 — Optional: ship `mg-fb16`** (lean-forum send) **with
the current narrower (with-`hC3`) claim.** Arc 3.0 produces no
finding that would change the disclosure content of `mg-fb16`;
the narrower claim remains correct as stated. Daniel's call
whether to ship now (cheap, honest, allows forum feedback in
parallel) or hold (avoids amending public claim if a future
arc closes `hC3`). **Polecat does not commission this**; it is
human-assigned per the `mg-65e1` brief.

**N3 — Conditional: commission a literature audit of width-3
Linial/Brightwell tightenings.** If Daniel wishes to invest in a
research-arc (multi-week, possibly external) toward dropping
`hC3` via S1, the polecat-doable starting point is a literature
audit (~150k tokens, `feedback_audit_bar_for_axioms` + 4-condition
test applied per cited result). **Polecat does not commission**;
it is a Daniel-only call per arc 2.0 §6.4.4.

**N4 — Conditional: commission a finite-enumeration certificate
for K=2 case-2-strict.** If Track 1 stalls and Daniel
commissions a shrink-the-gap arc, S2c / arc 2.0 sub-B2
(~300–500 LoC, mechanical, AMBER) is the only viable in-tree
starting point. **Polecat does not commission**; per arc 2.0
§6.4.3, it should be a separate ticket under a new branch
(not under `math-simp-arc-3.0`).

**N5 — Daniel-only override: commission the multi-element
Brightwell axiom.** If Daniel chooses to override the
audit-bar discipline for arc 2.0 framing 1, the polecat
estimate is in arc 2.0 §4 framing 1 ("~80k tokens for the
scoping artefact alone; ~800–1300 LoC Lean implementation;
high risk of A1's RED-fallback firing at A2"). **Polecat
does not propose**; this is a `feedback_audit_bar_for_axioms`
clarifier-mail decision.

### 4.5 Honest summary for PM / Daniel

* **Recommendation:** archive arc 3.0; retain `hC3`; Track 1
  remains the live path; ship `mg-fb16` per Daniel's call.
* **Confidence in "no GREEN framing exists in the in-tree
  search space":** very high. Three independent arcs (arc 1.0
  scoping, arc 2.0 scoping, arc 3.0 scoping) have surveyed
  21 distinct framings (arc 1.0: 4; arc 2.0: 4 with sub-options
  totalling 7; arc 3.0: 8 ε-close definitions + 12 strategy
  alternatives = 20; net distinct after deduplication ≈ 21).
  The same three pathologies (T6/T8/T10) reproduce across
  all three arcs.
* **Confidence in "no simpler argument exists":** moderate.
  This is a stronger claim than the search supports; what the
  search actually shows is "no in-tree-derivable simpler
  argument." A future paper-level result (width-3 Kahn-Linial
  tightening, or new correlation inequality) could change
  the picture. The published `[0.276, 1/3)` gap is the
  empirical signal that the field has not closed this gap;
  arc 3.0 reproduces that signal under polecat-budget
  constraints.
* **What's surprising about arc 3.0** (worth saving as
  memory): the **N-poset is not actually an ordinal sum**
  (T7), which contradicts a parenthetical in arc 1.0's
  scoping doc. Arc 1.0's recommended Candidate A
  ("decomposable case absorbs N-poset trivially") was
  optimistic on this point; the corrected reading is that
  the N-poset has nontrivial defect under every reasonable
  ε definition, which is why none of the eight ε definitions
  in §2 puts it in the near-ordinal regime.

---

## 5. Outcome class and PM action items

### 5.1 Outcome class

Per `feedback_distinguish_arc_chunk_outcomes`:
**substantive scoping chunk = no GREEN framing found, Track 1
remains the path.** This is the explicit allowed stop-loss
outcome from the brief (*"a valid outcome and gets reported
as a status doc with explicit reasons per definition /
strategy"*). Headline `hC3` unchanged by arc 3.0.

This outcome class is **identical to arc 2.0's** — both
report "no GREEN, Track 1 remains the path." Arc 3.0's
incremental contribution is the multi-definition exploration
of §2 (eight ε definitions vs. arc 2.0's implicit single-
definition reading) and the strategy-level enumeration of §3
(twelve alternatives vs. arc 2.0's four framings). The
verdict is unchanged; the audit surface is broader.

### 5.2 PM action items

1. **Review this doc.**
2. **Confirm Track 1 (`mg-b666`) is the live path** for
   headline `hC3` removal. Track 1's structural-impossibility
   verdict remains in force; arc 3.0 does not overturn it.
3. **Archive `math-simp-arc-3.0` after this scoping doc
   lands.** Do not commission downstream chunks under this
   branch.
4. **Coordinate `mg-fb16` (lean-forum send)** per Daniel's
   call. Arc 3.0 does not change `mg-fb16`'s disclosure
   content.
5. **If Daniel chooses any Daniel-only override path** (N3 /
   N4 / N5 in §4.4), file as a separate ticket under a new
   branch. Do **not** commission under
   `math-simp-arc-3.0`.

### 5.3 Daniel-only escalation items (per §4.4 stop-losses)

* **N3.** Commission a literature audit of width-3
  Linial/Brightwell tightenings (multi-week external
  collaboration adjacent).
* **N4.** Commission finite-enumeration certificate for K=2
  case-2-strict (mechanical, ~300–500 LoC, AMBER).
* **N5.** Override audit-bar discipline for the
  multi-element / ordinal-cut Brightwell axiom (= arc 2.0
  framing 1).

All three are explicit non-defaults; polecat does not propose
any of them.

### 5.4 Stop-loss verdict

* **No GREEN framing found** — explicit allowed outcome from
  the brief. Filed.
* **Did not surface contradictions** with Track 1's
  cardinality obstruction or Track 2's audit-bar verdicts.
  Arc 3.0 reaffirms both.
* **Audit budget envelope** (~300k tokens) — actual usage
  ~120k tokens for §1 + ~80k tokens for §§2–3 + ~30k tokens
  for §4-5 doc drafting ≈ 230k tokens. Well under the 1.5M
  ticket cap; under the 300k audit envelope.

---

## 6. Risk inventory

The brief asks for a risk inventory at minimum:

### 6.1 Axiom-bar regression

§§2.5 (D5) and 3.1 (S1) both *would* introduce or require new
project axioms if executed. The 4-condition test from
`feedback_audit_bar_for_axioms` flags both as failing —
external + low-risk both fail (the required bound is the
*content* of the existing rigidity argument, not a citable
external theorem; a reader would correctly read it as hiding
unfinished proofs). **Risk under any GREEN execution: forum
embarrassment.** Identical to arc 2.0 §7.1.

### 6.2 Signature regression

§§3.6b (S6b) and 2.5 (D5) both replace `hC3` with a different
hypothesis of comparable mathematical weight. Per
`feedback_signature_regressions`, this is **not** progress;
it is signature regression in disguise. **Risk under either
execution: c5d5a10-style mayor rejection.** Identical to arc
2.0 §7.2.

### 6.3 Scope creep

§3.4 (S4 pure counting) and §3.1 (S1 BK drop) are the only
strategy alternatives that, if pursued seriously, could grow
scope without bound (multi-month research arcs). **Risk
under either: research-arc lock-in.** Mitigated by the
recommendation to file as separate tickets under new branches
if commissioned.

### 6.4 Duplication with Track 1 / Track 2

Strategy S2c is direct continuation of arc 2.0 framing 3
sub-B2; framing-style alternatives in §3 (S3a, S3b, S5, S6a)
duplicate Track 1 / arc 2.0 in spirit. **Risk under
simultaneous execution: redundant work.** Mitigated by the
Track 1 / arc 2.0 / arc 3.0 hierarchy: Track 1 remains the
live structural path; arcs 2.0/3.0 are scoping only.

### 6.5 Optimism cascade across arcs

A subtler risk: the parenthetical in arc 1.0's scoping doc
("the N-poset is exactly `{x_1, x_2} ⊕ {y_1, y_2}`, which is
an ordinal sum") was wrong (T7). Arc 1.0's Candidate-A
recommendation was partly motivated by the (false) intuition
that the decomposable case auto-absorbs the K=2 N-poset
obstruction. Arc 3.0's correction (T7) means future arcs
should:

* Treat ε-close-to-ordinal-sum framings as scopes for the
  *G3 deep-layered branch*, not for the entire headline. Per
  T10, G4 (where `hC3` lives) is structurally outside the
  ε-close framing's domain.
* Verify the ordinal-sum status of named obstructions
  (N-poset, sibling 3-element configs from T3a) directly
  rather than by reference to scoping intuitions.

**Memory action recommended.** Save a memory recording
arc 3.0's T7 finding (N-poset is NOT an ordinal sum) so
future polecats inheriting arc-1.0/2.0 reading don't
re-make the same optimistic conflation. (Polecat does not
write this memory directly; PM-side decision after review.)

---

## 7. References

### 7.1 Code anchors

* `lean/OneThird/MainTheorem.lean:52-57` — current headline
  with `hC3 : Step8.Case3Witness` (intentional retention
  under option (δ); preamble lines 39-51 cite
  `docs/path-c-cleanup-roadmap.md`).
* `lean/OneThird/Step8/LayeredBalanced.lean:438-444` —
  `Case3Witness` def, intentional `def`-not-theorem retention
  preamble lines 396-437.
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159`
  — the in-tree `brightwell_sharp_centred` axiom (single-element
  bound; the bound that arc 1.0 A1 found insufficient and arc
  3.0 §§2.1, 2.2, 2.5 confirm).
* `lean/OneThird/Step8/ExcPerturb.lean:351` — `exc_perturb`
  iterated bound `2k/(n−k+1)`; the `Θ(1)` bound on balanced
  cuts that is the load-bearing obstruction for any
  "axiom-light" framing reading (T6).
* `lean/OneThird/Step8/Case2Rotation.lean:629, 686, 772, 870, 894`
  — chain swap bound, symmetric-collapse split,
  `Case2FKGSubClaim` (provably false in `pair` field per T5),
  and the under-FKG closure.
* `lean/OneThird/Step8/CompoundSwap.lean` —
  `MatchingCompatible`, `compoundSwap` (mg-84f2; killed on
  case-2-strict per T3).
* `lean/OneThird/Step8/CompoundMatching.lean` —
  `matching_exists_of_K2_irreducible_noWithinBand` (mg-c0c7,
  conditioned on `NoWithinBandPreceq L`).
* `lean/OneThird/Step8/BipartiteEnumGeneral.lean` —
  `bipartite_balanced_enum_general` three-way dispatch
  (mg-02c2; Case 2 branch routes through `hFKG`).
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1065,
  1152, 1227, 1237` — `OrdinalDecomp.probLT_restrict_eq`
  (exact `ε = 0` invariance) and the
  `hasBalancedPair_lift_*` constructors (mg-7f06).
* `lean/OneThird/Step8/LayeredReduction.lean:426-460` —
  `ReductionWitness` and `lem_layered_reduction`'s window-
  bound input slot.
* `lean/AXIOMS.md` — current axiom inventory and audit-bar
  disclosures.

### 7.2 Doc anchors (chronological)

* `docs/math-simplification-scoping.md@638ad1e` — arc 1.0
  scoping pass (parent of this arc; Candidates A/B/C/D).
* `docs/math-simplification-A1-feasibility.md` — arc 1.0 A1
  RED-fallback verdict (Brightwell + `exc_perturb` cannot
  give `f(ε) → 0` for balanced cuts; T6 origin).
* `simplifications.md` (top-level repo file) — arc 1.0
  candidate B source; B1 shipped as `b6b6c3f` (mg-805c).
  **Note: arc 1.0's parenthetical claim that the N-poset is
  an ordinal sum is corrected in §1.5 / T7 of this arc.**
* `docs/a8-path-b-block-and-report-status.md` (mg-a79e) —
  Case2FKGSubClaim direction-wrong finding (T5 origin).
* `docs/a8-s2-restate-block-and-report-status.md` (mg-b0de) —
  `≤ 2/3` upper bound vacuity at K=2 |Q| ≤ 6 (T4 origin).
* `docs/a8-s2-rotation-residual-status.md` (mg-ba0c) — chain
  swap analysis underlying T4/T5.
* `docs/a8-s2-strict-witness-status.md` (mg-43f3) —
  StrictCase2 closure pinned to chain-form FKG sub-claim.
* `docs/path-c-cleanup-roadmap.md` (b75e6ad, mg-7261) —
  4-round Path C arc roadmap; T9 origin; §§5–7 cited
  throughout this doc.
* `docs/path-c-track-1-status-1.md` (mg-b666) — cardinality
  obstruction status (T3 origin).
* `docs/math-simp-arc-2.0/scoping.md` (b1ac92b on
  `math-simp-arc-2.0`, mg-80ab) — Track 2 zero-GREEN-of-four
  verdict (T8 origin).

### 7.3 Memory / discipline anchors

* `feedback_audit_bar_for_axioms` — 4-condition test invoked
  in §§2.5, 3.1, 6.1.
* `feedback_signature_regressions` — invoked per T1 and §6.2.
* `feedback_distinguish_arc_chunk_outcomes` — closure framing
  in §0, §5.1.
* `feedback_latex_first_for_math_simp` — discipline applied
  throughout (no Lean source changes).
* `feedback_increments_authorized` — applied in §4 by
  referencing tags T1–T10 instead of re-deriving.
* `feedback_block_and_report` — escape clauses tracked in
  §5.4.

### 7.4 Paper anchors (step8.tex)

* `step8.tex:1879-2360` — §`sec:layered-reduction` (G3); the
  cutting lemma at `:2164-2186`; `lem:layered-reduction` at
  `:2199`.
* `step8.tex:2348-3132` — §`sec:layered-balanced` (G4);
  `lem:layered-balanced` at `:2360`;
  `prop:in-situ-balanced` at `:2978-3032`.
* `step8.tex:911-1023, 1025-1062` — `lem:one-elem-perturb`
  (F6a) and `lem:exc-perturb` (F6b); the per-element coupling
  and its iteration that bound T6.
* `step8.tex:1042` — `eq:sharp-centred`, the axiom's
  paper-source equation.
* `step8.tex:2868, 2916-2940` — Case 2 chain analysis and the
  `≤ 2/3` upper bound proof (the bound deferred to A8-S2-cont
  scope; T4).
* `main.tex` §1 (Introduction) — paper claim shape; prior-art
  context for the `[0.276, 1/3)` gap; T8 (F3) origin.

### 7.5 Reminders

* Daniel directive 2026-05-04T~19:30Z (in-session, no reminder
  ID) — the parent direction setting arc 3.0.
* Reminder `pm-onethird/1777914292578721000.5852.1000`
  (Daniel 2026-05-04T17:04Z) — the parent direction setting
  Track 1 and Track 2.
* Reminder `pm-onethird/1777913883871871000.98139.2000`
  (Daniel 2026-05-04T17:58Z) — the framing-discipline
  course-correction motivating
  `feedback_distinguish_arc_chunk_outcomes`.

---

## 8. Status close-out

* **Branch.** `math-simp-arc-3.0` (parallel to `main`,
  parent `1ce035d`). This commit is the arc 3.0 deliverable.
* **Outcome class:** substantive scoping chunk = no GREEN
  framing found. The scoping is itself the deliverable; no
  parallel cleanup chunk is bundled. Headline `hC3` unchanged
  by arc 3.0.
* **Token cost.** ~230k tokens (audit ~120k, search ~80k,
  drafting ~30k). Under the 1.5M ticket cap.
* **No code changes landed.** Per `feedback_latex_first_for_math_simp`
  and the brief's "latex-first; doc-only" instruction.
* **No new axioms, no `sorry`/`admit`.**
  `#print axioms width3_one_third_two_thirds` unchanged from
  baseline.
* **Successor archival:** treat this doc the same way
  `simplifications.md` should have been treated after arc 1.0
  close — record-of-evaluations, NOT live program. If a future
  arc (4.0, 5.0, …) revisits the same questions, file under a
  new branch with explicit `EXPLORATORY ONLY` headering.
