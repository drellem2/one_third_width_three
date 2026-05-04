# Why `hC3` retention is structural, not effort-bound

**Status (2026-05-04):** `hC3 : Step8.Case3Witness` is retained on
the headline `OneThird.width3_one_third_two_thirds` indefinitely
under the option (δ) park decision. This is the canonical
explanation of *why* — three independent structural facts (F1, F2,
F3) converge to make the residual K=2 + irreducible + w ≥ 1 +
|β| ≥ 3 family resistant to every simpler argument the project's
in-tree machinery can express. The current paper's BK-Cheeger
chain is the first known path through all three; the doc maps each
fact to the elementary path it kills and to the audit material that
verifies it.

This artefact is the synthesis-as-deliverable for the three-arc
math-simplification search (arc 1.0 / arc 2.0 / arc 3.0). It is
not a Lean change, and it does not claim that no simpler argument
exists — only that no in-tree-derivable simplification has survived
21 candidate framings across three independent scoping passes, and
that the same three structural facts close every one of them.

---

## Executive summary

`hC3` is the residual case-3 hypothesis on the headline (a
universally-quantified discharge over layered width-3 sub-types;
`lean/OneThird/Step8/LayeredBalanced.lean:438-444`). The locus
where it cannot be closed in tree is **K=2 + irreducible + w ≥ 1
+ |β| ≥ 3** (Path C cleanup roadmap §5). Three structural facts
converge there:

* **F1** — *Cardinality obstruction.* Order-preserving
  permutations cannot swap a strict ⪯-pair. This rules out
  symmetry-based reductions (compound-automorphism, triple-orbit,
  partial-injection variants). It is a finite-set fact, not a
  formalization artefact.
* **F2** — *Brightwell vacuity at K=2 / |Q| ≤ 6.* The in-tree
  single-element perturbation bound is `2/|Q|`; clearing the
  `1/3` target requires `|Q| ≥ 12`, but K=2 has `|Q| ≤ 6`.
  Iteration only makes the bound worse.
* **F3** — *Published `[0.276, 1/3)` gap.* The unconditional
  Kahn-Saks / Brightwell / Kahn-Linial line has not closed the
  `δ* ≥ 0.276 → 1/3` gap in 30+ years; the width-3 specialisation
  has not been achieved without going through a Cheeger-type or
  equivalently structural argument.

F1 rules out elementary symmetry on case-2-strict. F2 rules out
direct probability bounds at small `|Q|`. F3 rules out
direct correlation-inequality-only proofs. Any uniform discharge
of the residual family must navigate around all three; the
existing BK-Cheeger / fiber-coherence / globalisation / layered
proof is the first known way to do so.

The verdict is therefore **substantive, not optimistic**: the math
is this hard because the underlying combinatorial reality in this
regime is genuinely subtle. `hC3` retention is the honest
disclosure of that reality, not a placeholder for unfinished work.

---

## F1 — Cardinality obstruction

**Source:** `docs/path-c-track-1-status-1.md` §2 (mg-b666).

### Lemma

Let `α` be a finite poset and `(a, a')` a pair with
`upper(a) ⊊ upper(a')` strictly (where `upper(x) := {z : x < z}`).
Then there is **no** equivalence `σ : α ≃ α` such that

* `σ a = a'`, and
* `σ` is `≤`-monotone (equivalently, `σ` is a poset
  automorphism, since `α` is finite and `σ` is a bijection).

A symmetric statement holds for `lower(a') ⊊ lower(a)`.

### Proof

Suppose such a `σ` exists. For any `z ∈ α`,

```
a < z   ⟺   σ a < σ z       (σ order-preserving)
        ⟺   a' < σ z        (σ a = a').
```

So `σ` restricts to a map `upper(a) → upper(a')`. Applying the
same argument to `σ⁻¹` (also a poset automorphism) gives the
reverse restriction `upper(a') → upper(a)`. Hence the restriction
is a bijection, forcing `|upper(a)| = |upper(a')|` — contradicting
`upper(a) ⊊ upper(a')`. ∎

### Minimal counterexample (3 elements, trivial automorphism group)

`α = {a, a', y}` with `a' < y` as the only comparability,
`K = 2`, `w = 1`, `band a = band a' = 1`, `band y = 2`. This
configuration satisfies every hypothesis of the
`bipartite_balanced_enum_general` consumer (`HasWidthAtMost α 3`,
`LayerOrdinalIrreducible L`, `K = 2`, `w ≥ 1`, `|α| ≥ 3`).

Enumerating the six permutations of `α` and checking which
preserve the only comparability `a' < y`:

| `σ`                     | preserves `a' < y`?     | poset auto? |
|-------------------------|-------------------------|-------------|
| `id`                    | ✓                       | ✓           |
| `(a, a')` (transp.)     | maps to `a < y` (false) | ✗           |
| `(a, y)` (transp.)      | maps to `a' < a` (false)| ✗           |
| `(a', y)` (transp.)     | maps to `y < a'` (false)| ✗           |
| `(a, a', y)` (3-cycle)  | maps to `y < a` (false) | ✗           |
| `(a, y, a')` (3-cycle)  | maps to `a < a'` (false)| ✗           |

Only `id` survives — `Aut(α, ≤) = {id}`. So compound
`Equiv.swap` produces **zero** balanced-pair witnesses on this
configuration: every non-identity permutation is dead on arrival.

Yet `(a, a')` is a balanced pair: there are three linear
extensions (`a, a', y`; `a', a, y`; `a', y, a`), and one of them
has `pos a < pos a'`, so `probLT a a' = 1/3` exactly — at the
boundary of `[1/3, 2/3]`. The witness comes from **counting
linear extensions**, not from symmetry.

### Implication

Any uniform structural dispatch over the K=2 + irreducible +
w ≥ 1 + |β| ≥ 3 family must close this 3-element configuration.
Compound-automorphism produces no witness here, and the same
cardinality argument rules out:

* **Triple-orbit compound automorphism** (additional orbits do
  not change the cardinality of `upper(a)`/`upper(a')`).
* **Partial automorphism / poset embedding instead of bijection**
  (loses the involutivity needed for `probLT = 1/2` symmetry).
* **Compound automorphism on a different pair `P₁`** (the minimal
  counterexample admits no nontrivial poset automorphism on any
  pair).

Crucially, the obstruction is a property of the strict ⪯-pair
regime, not of the specific Lean encoding. Reformulating the
dispatch predicate or the matching lemma cannot work around it
(`docs/path-c-track-1-status-1.md` §2d).

**Tag T3 in the arc 3.0 audit.** Symmetry-based reduction to
`probLT a a' = 1/2` cannot fire on a strict ⪯-pair.

---

## F2 — Brightwell vacuity at K=2 / |Q| ≤ 6

**Source:** `docs/a8-s2-restate-block-and-report-status.md` §3
(mg-b0de).

### Bound statement

The in-tree project axiom `brightwell_sharp_centred`
(`lean/OneThird/Step8/BrightwellAxiom.lean:159`) gives, in its
rational form (`brightwell_sharp_centred_rat:195`), the per-element
perturbation bound

```
|Σ_{L' ∈ A} f(L') − |A| · f̄|  ≤  2 · N / m,
```

where `m = |Q| = |α| + 1` (the paper's ambient depth-`m` poset)
and `A := {L' : x <_{L'} y}`. After dividing by `N · N'` and
applying the fibre-sum identity (consumed in
`OneElemPerturb.lean:709`), this becomes

```
|p_{xy}(Q) − p_{xy}(Q − z)|  ≤  2 / |Q|.
```

### Numerical instantiation at K=2

For the strict K=2 within-band ⪯-pair `(a, a')` with
`upper(a) ⊊ upper(a')`, take `x = a`, `y = a'`, and `z` the unique
strictness witness in `upper(a') \ upper(a)`. Then `(a, a')` is
symmetric in `Q − z`, and the Case 1 ambient profile match
collapse gives `probLT_{Q−z}[a < a'] = 1/2`. Combining:

```
|probLT_Q[a < a']  −  1/2|  ≤  2 / |Q|.
```

To extract `probLT_Q[a' < a] ≤ 2/3` (equivalently
`probLT_Q[a < a'] ≥ 1/3`) we therefore need

```
1/2  −  2/|Q|  ≥  1/3,    ⟺    |Q|  ≥  12.
```

**K=2 has `|Q| = |α| ≤ 6`** (sum of two band sizes, each `≤ 3`
by `band_size`). At `|Q| = 6` the bound is `≥ 1/2 − 2/6 = 1/6`,
which gives only `probLT_Q[a' < a] ≤ 5/6` — **vacuous for the
`≤ 2/3` target**.

### Why iterating Brightwell does not help

If `|upper(a') \ upper(a)| = k > 1`, the natural move is to add
the strictness witnesses one at a time. Each step is a
single-element perturbation worth at most `2/m_i`, where `m_i`
is the size at step `i`. In the additive bound the cumulative
perturbation is at most `Σ_i 2/m_i`. For fixed `m = |Q| ≤ 6` this
is a harmonic-sum bound `2 · H_|Q| ≈ 4.9` — even weaker than the
single-step `2/|Q| = 1/3`.

A multi-element / chain-form covariance argument might tighten
this, but the existing `brightwell_sharp_centred` infrastructure
gives only the single-element form. Multi-element / chain-form
covariance is **not in tree**.

The other in-tree paths to a `≤ 2/3` bound are also closed at
K=2:

* `Case2BipartiteBound.lean` (mg-ed4d) handles K=2 / `w = 0` only;
  the `hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b` condition fails for
  `w ≥ 1` (`Case2BipartiteBound.lean:182`,
  `bandSet_one_le_bandSet_two_of_w0`).
* Cross-poset count-form FKG (`probLT'_count_div_le_of_relExt` at
  `RelationPoset/FKG.lean:464`) gives the wrong normalisation —
  bounding `|LE(Q'')| / |LE(Q)|` instead of the
  probability-normalised form that `≤ 2/3` requires.
* Chain swap on `(a, z)` for `z ∈ upper(a') \ upper(a)` does not
  apply — the chain hypothesis on `(a, z)` is not satisfied
  in the K=2 / w ≥ 1 regime
  (`docs/a8-s2-restate-block-and-report-status.md` §3.4).

### Audit-bar implication

Closing the gap by introducing a "multi-element / ordinal-cut
Brightwell variant" as a new project axiom was evaluated as
arc 2.0 framing 1 and is **RED-fallback** under the four-condition
audit-bar test (`feedback_audit_bar_for_axioms`):

* **External:** FAIL. The required defect-aware multi-element
  bound is not a transcription of any published result; in tree
  it is mathematically equivalent to the existing Steps 5–7
  rigidity content.
* **Difficult:** PASS (~500–800 LoC of mathlib-tier
  covariance / set-system work, if the math existed).
* **Labeled:** PASS (a `lean/AXIOMS.md` entry is mechanical).
* **Low-risk:** FAIL. A forum reader without the audit trail
  would correctly read this as hiding unfinished proofs — the
  bound is the *content* of the existing rigidity argument.

(Full table: `docs/math-simp-arc-2.0/scoping.md` framing 1.) Two
of four conditions fail; the verdict is "do not retain unless
Daniel overrides," and the override has not been requested.

**Tag T4 / T6 in the arc 3.0 audit.** No in-tree perturbation
bound is sharp enough to close case-2-strict in the K=2 + w ≥ 1
+ |α| ≤ 6 regime; any chain of single-element perturbations gives
a size-based, not ε-aware, bound that does not see the structure
the case requires.

---

## F3 — The published `[0.276, 1/3)` gap

**Source:** `main.tex` §1.3 (Known results, lines 169–211);
`main.tex` §1.6 (Comparison with previous approaches, lines
313–338); arc 3.0 §4.2 (T8 origin).

### Literature gist

The unconditional bounds on `δ*` — the infimum over non-chain
finite posets of the maximum-balanced-pair imbalance — have
followed a 30+ year arc of correlation-inequality refinements:

| Year | Authors | Bound |
|------|---------|-------|
| 1984 | Kahn–Saks (FKG + log-concavity) | `δ* ≥ 3/11` |
| 1989 | Brightwell (sharper XYZ-type covariance) | `δ* ≥ (3-√5)/2 ≈ 0.2764…` |
| 1991 | Kahn–Linial (further covariance refinement) | `δ* ≥ 0.276393…` |
| 1995 | Brightwell–Felsner–Trotter | (matches Kahn–Linial root) |

Each step "operates on `Pr[x < y]` directly, via log-concavity
and correlation inequalities" (`main.tex:183-184`). The current
record `δ* ≥ 0.276393…` matches a quadratic root of an explicit
polynomial.

### The gap

The conjectured value is `δ* ≥ 1/3`. The published unconditional
record is `δ* ≥ 0.276393…`. The **`[0.276393…, 1/3)` gap** has
remained open for 30+ years. As `main.tex:319-322` puts it:

> [the correlation-inequality approach] has yielded the numerical
> bounds `δ* ≥ 0.276…` but appears to be genuinely stuck below
> `1/3`; the functional-analytic slack in the XYZ inequality is
> known to cost a constant factor.

This is *prima facie* evidence that "correlation inequality plus
width-specialisation" is not by itself sufficient to reach `1/3`
in the unconditional setting. The conjecture is, in
Brightwell's own framing, "one of the most intriguing problems
in the combinatorial theory of finite posets"
(`main.tex:164-166`).

### Width-3 specialisation status

For width-3 posets specifically, the conjecture has remained
open prior to this paper (`main.tex:213-220`). Peczarski's gold
partition conjecture (Peczarski 2008) — which would imply the
1/3–2/3 conjecture — has been verified for width 3 in some
formulations, but the standard `1/3–2/3` statement was not
previously known at width 3 without additional structural
hypotheses.

The current paper's argument is **not** a refinement of the
correlation-inequality line; it is a Cheeger-type spectral
argument on the Bubley–Karzanov graph `BK(P)`, ruling out the
existence of a low-conductance cut that any width-3
counterexample would have to produce. Crucially:

> We never compare `Pr[x < y]` to another probability directly;
> instead, we use a counterexample only through its induced
> low-conductance cut, and derive the contradiction entirely
> from the local combinatorial geometry of BK edges across
> that cut.
> (`main.tex:325-328`)

So the published landscape contains *one* width-specialised
attack on `δ_3* = 1/3` (this paper), and it works precisely by
**not** going through correlation inequalities directly. A
direct-correlation-inequality + width-3-specialisation route to
`1/3` is exactly the strategy that has been unable to close the
`[0.276…, 1/3)` gap for three decades.

### Implication

Arc 2.0 framing 4 ("Brightwell-pump / Kahn–Saks / Linial alternate
route") is RED-fallback under polecat scoping authority
(`docs/math-simp-arc-2.0/scoping.md` framing 4): a width-3
tightening of the Kahn–Linial covariance bound is "presumably
attempted by the original Kahn–Linial / Brightwell line of authors
and others over decades; if it were achievable by a routine
refinement of the existing covariance argument, it would likely
already exist." Closing `hC3` via this route is multi-week
external research, not in scope for any polecat-driven arc.

**Tag T8 in the arc 3.0 audit.** No GREEN framing in the
"different organisation of in-tree machinery" search space.
Anything truly new must either introduce a new project axiom
(audit-bar override, Daniel-only) or constitute paper-level
math (escalation, multi-week external research arc).

---

## Why the three together force intricacy

F1, F2, F3 are independent — different mathematical content,
different sources, different levels of generality:

* F1 is a finite-set fact about order-preserving permutations.
  It needs no probability and no axiom.
* F2 is a quantitative property of the existing
  `brightwell_sharp_centred` axiom at small `|Q|`. It is sharp;
  the audit verifies it numerically.
* F3 is a literature-level claim about the field's progress on
  the 1/3–2/3 conjecture over 30+ years.

Each closes a distinct elementary attack:

* F1 rules out **elementary symmetry** on case-2-strict
  (compound-automorphism, triple-orbit, partial-automorphism
  variants — see `docs/path-c-track-1-status-1.md` §3).
* F2 rules out **direct probability bounds at small `|Q|`**
  (single-element Brightwell, iterated Brightwell, count-form
  cross-poset FKG — see
  `docs/a8-s2-restate-block-and-report-status.md` §§3.1–3.6).
* F3 rules out **direct correlation-inequality + width-3
  specialisation** as a stand-alone route to `δ_3* = 1/3` — the
  literature has empirically demonstrated this for 30+ years.

The current paper's BK-Cheeger / fiber-coherence /
globalisation / layered argument is the **first known path
through these three structural facts** to reach `δ_3* = 1/3`.
It is intricate because the three facts together force
intricacy: any candidate simplification that drops one of the
machinery layers immediately runs into one of F1, F2, F3.

This is what the three-arc math-simplification search empirically
demonstrated. Across arc 1.0 (4 framings), arc 2.0 (4 framings,
several with sub-options), and arc 3.0 (8 ε-close definitions ×
12 strategy alternatives), **21 distinct framings** were
evaluated and **zero** were found GREEN. Each failure mapped
back to one of F1 / F2 / F3.

### What this doc does not claim

Arc 3.0 §4.5 (and per discipline `feedback_distinguish_arc_chunk_outcomes`):
"no in-tree-derivable simpler argument" is **strictly weaker**
than "no simpler argument exists." The three-arc search shows
the former with high confidence; the latter is not what the
search supports, and this doc does not claim it.

A future paper-level result — a width-3 Kahn–Linial tightening,
a new correlation inequality, a different proof program — could
in principle make the picture simpler. The published
`[0.276…, 1/3)` gap is the empirical signal that the field has
not closed the gap in 30+ years, but it is not a proof of
impossibility.

The doc's substantive verdict is therefore: **the math is
genuinely this hard, and here is why** — not "we are confident
no simpler proof can be found." `hC3` retention is the honest
disclosure of the former; the latter would be over-reach.

---

## Audit trail

The three-arc search has produced a self-contained corpus. In
chronological order:

* **Arc 1.0 scoping** (`mg-3e53`, 2026-04-29):
  `docs/math-simplification-scoping.md`. Surveyed 4 candidates
  (A/B/C/D); recommended A (ε-close-to-ordinal-sum reductio).
* **Arc 1.0 A1 RED-fallback** (`mg-3d9d`, 2026-05-02):
  `docs/math-simplification-A1-feasibility.md`. In-tree
  perturbation is size-based, not ε-aware (T6).
* **Arc 1.0 B1 ship** (`mg-805c`, 2026-05-02): the layered
  reduction rewrite. No `hC3` removal.
* **Arc 2.0 scoping** (`mg-80ab`, 2026-05-04, parallel branch
  `math-simp-arc-2.0`): `docs/math-simp-arc-2.0/scoping.md`.
  Surveyed 4 fresh framings; **zero GREEN**, one AMBER (B2
  finite enumeration) only as Track 1 fallback. Findings
  F1 / F2 in §3 are the early concise statements of what arc
  3.0 promotes to structural facts F1 / F2.
* **Track 1 Round 1** (`mg-b666`, 2026-05-04, on `main`):
  `docs/path-c-track-1-status-1.md`. Compound-automorphism
  cannot extend to case-2-strict — full statement and proof of
  the cardinality obstruction (this doc's F1).
* **Arc 3.0 scoping** (`mg-65e1`, 2026-05-04, parallel branch
  `math-simp-arc-3.0`): `docs/math-simp-arc-3.0/scoping.md`.
  Eight ε-close definitions × twelve strategy alternatives
  surveyed under Daniel's "if things are this hard then the
  math is the issue" hypothesis-test directive. Verdict: **no
  GREEN framing in the in-tree search space**. §4.2 introduces
  the F1 / F2 / F3 unified framing this doc synthesises.

### Companion disclosures

* `docs/lean-forum-publication-readiness.md` — the PATH A
  disclosure surface. §2 ("What `hC3` is and why it is parked")
  and §7a ("The `hC3` Prop-level hypothesis") summarise the
  structural verdict and point to this doc for the F1/F2/F3
  detail.
* `docs/lean-forum-post-template.md` — the paste-able forum
  post; it carries the structural verdict at the level of
  Track 1 / Track 2 (cardinality + Brightwell vacuity) and
  links to this doc for the unified F1/F2/F3 reading.
* `docs/path-c-cleanup-roadmap.md` — option (δ) park decision;
  revival triggers in §7.
* `README.md` "Please read this before citing" — the README
  entry-point flags `hC3` retention and points to this doc as
  the canonical "why is the formalization conditional" answer.

### Adjacent / superseded material

* `docs/a8-path-b-block-and-report-status.md` (mg-a79e),
  `docs/a8-s2-restate-block-and-report-status.md` (mg-b0de) —
  the round-by-round audit that produced the F2 numerical
  instantiation; superseded by this synthesis for citation
  purposes but retained as primary source.
* `docs/path-c-cleanup-roadmap.md` §§4–6 — the four-round Path
  C cleanup arc (mg-4a5b → mg-072c → mg-0fa0 → mg-94fd) and the
  six landed infrastructure commits (mg-9568 / mg-7f06 / mg-a735
  / mg-27c2 / mg-2e58 / mg-26bb).

---

## Provenance

This document is the synthesis-as-deliverable for the three-arc
math-simplification search, filed under `mg-cda8` on 2026-05-04
following Daniel's in-session directive (~21:15Z) that arc 3.0's
status-and-pivot conclusion warranted a concrete artefact rather
than a parked-and-mailed disposition. It is doc-only (no Lean
source changes) and follows `feedback_audit_as_deliverable`
discipline: when a multi-arc search exhausts, the audit trail
is itself a publishable artefact.

The PATH A disclosure surface and the README entry-point have
been updated to cite this doc rather than re-state F1 / F2 / F3
inline; future polecats inheriting the product line should treat
this doc as the canonical entry point and avoid duplicating the
framing across other docs.
