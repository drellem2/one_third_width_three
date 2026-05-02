# Math-simplification arc — scoping pass

**Filed under `mg-3e53` by polecat `pc-3e53` on 2026-05-02.**
**Branch:** `math-simp-arc` (this commit).
**Parent decision:** Daniel's reminder of 2026-05-02T19:31Z, picking
option 3 of `mg-ba0b` ("open math-simplification arc") via reminder mail
`pm-onethird/1777750261773849000.17061.9000`.

This document is the deliverable for the scoping ticket. It surveys
four candidate simplification approaches for the proof of
`OneThird.width3_one_third_two_thirds`, recommends one, and proposes
a 2-4 chunk delivery plan whose execution the PM will commission as
follow-on tickets.

The document is **non-executing** — no candidate is implemented here.
The `math-simp-arc` branch carries this scoping doc only. Chosen-route
implementation would be filed by PM as follow-on `mg-*` tickets that
branch from `math-simp-arc`.

## Constraints from the brief

* **Selection criterion.** "clear intuitive aesthetic argument that
  also can be formalized as our heuristic." A candidate must satisfy
  both — a beautiful argument that resists Lean is not eligible, and
  neither is a formalizable but ugly one.
* **Signature preservation.** The headline currently reads
  ```lean
  theorem width3_one_third_two_thirds.{u}
      {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
      (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
      (hC3 : Step8.Case3Witness.{u}) :
      HasBalancedPair α
  ```
  with one external project axiom, `brightwell_sharp_centred`. Any
  simplification that **weakens** the conclusion (e.g., adds a
  cardinality side condition), **strengthens** the hypothesis (e.g.,
  asks for more than width-3 + non-chain), or **adds new project
  axioms** counts as a regression (`feedback_signature_regressions`)
  and must be flagged as a tradeoff if proposed at all.
  Dropping `hC3` is upside; introducing it under a different name is
  not.
* **Stop-loss.** If after surveying we find no candidate >50% likely
  to formalize cleanly, the truthful "no good simplification" report
  is a valid outcome and should be filed.
* **No fresh paper-level math.** A simplification that requires a
  new mathematical theorem (rather than a re-organization of the
  existing argument) is out of scope under scoping authority and gets
  escalated.
* **Polecat budget.** 1M tokens. Single session. The scoping doc
  is the deliverable; per-chunk implementation budgets are estimated
  here and committed by PM, not by this session.

## What the current proof actually does (one-paragraph re-cap)

The headline `width3_one_third_two_thirds` is the contrapositive of:
"no width-3 non-chain poset is a `γ`-counterexample for any `γ > 0`."
A `γ`-counterexample is a poset with no incomparable pair `(x, y)`
satisfying `min(Pr[x<y], Pr[y<x]) ≥ 1/3 − γ`. The current proof is
a **rigidity argument**: assume a minimal `γ`-counterexample `P` of
width 3. Then —

1. **(Step 8 G1, Theorem E)** `P` admits a low-conductance cut
   `S ⊆ 𝓛(P)` of the BK graph (`Φ(S) ≤ 2/(γn)`) by an elementary
   averaging argument over pair functions.
2. **(Steps 1–2)** Localize: each "rich" incomparable pair `(x,y)`
   gives rise to a 2-D fiber on which BK moves are unit grid moves;
   low-conductance cuts are forced to look like monotone staircases
   on each fiber.
3. **(Steps 3–4)** Two-interface incompatibility: incoherent rich
   interfaces produce an Ω(1) edge boundary, contradicting low
   conductance.
4. **(Step 5)** Dichotomy: either `P` has many rich interfaces (in
   which case Step 4 bites), or `P` is already layered.
5. **(Step 6)** Coherence forced (otherwise Step 4 again).
6. **(Step 7)** Coherent rich interfaces globalize to a layered
   decomposition with bounded interaction width.
7. **(Step 8 G3 layered reduction)** A layered counterexample with
   depth `K ≥ K₀(γ, w)` admits an ordinal cut `A ⊕ B`; bulk pairs
   satisfy `p_xy(P) = p_xy(A)` exactly, window pairs perturb by
   `o_K(1)`. Either `A` (a smaller counterexample) violates
   minimality or a balanced pair lifts to `P`.
8. **(Step 8 G4 layered balanced)** Shallow layered posets (depth
   `K < K₀`) reduce to a bipartite balanced-pair lemma on width-3
   bands, which case-splits into Cases 1 (ambient match), 2 (within-
   band ⪯-pair), 3 (within-band antichain — the `hC3` Case3Witness
   leaf).

The expensive parts of the formalization are **Steps 5–7** (~2M LoC
of dichotomy/coherence/globalization, partly shared with Steps 1–4
via the fiber model) and **Step 8 G4 Case 3** (the `hC3` parametric
hypothesis, parked under option (δ)). Step 8 G3 is comparatively
clean. The aesthetic critique (per Daniel) is that the rigidity
argument is structurally a "near-ordinal-sum" reductio dressed in
Cheeger-flavored language — the headline conclusion is reached only
after a 7-step preamble whose only output is "the counterexample is
near a layered structure."

## 1. Survey

### Candidate A — ε-close-to-ordinal-sum reductio (Daniel's example)

**The math.** For a width-3 non-chain poset `P`, define a *defect
gauge*

```
  ε(P) := min over partitions X = A ⊔ B (both nonempty) of
            |{(a, b) ∈ A × B : a ⊀ b}| / (|A| · |B|).
```

`ε(P) = 0` iff `P` is a genuine ordinal sum `A ⊕ B`. `ε(P)` measures
how far `P` is from being decomposable into a pair of summands.

The proof becomes a two-clause reductio. Let `P` be a minimal
counterexample.

- **(Decomposable case, ε(P) = 0)**: `P = A ⊕ B`. Every
  incomparable pair lies inside one summand, and `Pr[x<y]` is
  preserved exactly under the embedding, so a balanced pair in
  `A` (or `B`) lifts unchanged. By minimality, `A` (or `B`) has
  a balanced pair, contradicting `P`'s counterexample status.
- **(Near-ordinal case, 0 < ε(P) ≤ ε₀)**: Take the minimizing cut
  `(A, B)`. By a Brightwell-style perturbation lemma (using the
  in-tree `brightwell_sharp_centred` axiom, or a chain-form
  generalization),
  `|Pr_P[x<y] − Pr_A[x<y]| ≤ f(ε)` for some explicit `f` with
  `f(0) = 0`. For `ε ≤ ε₀(γ)` chosen small enough, the
  perturbation budget is below `γ`, so a balanced pair in `A` (or
  `B`) lifts to a `γ`-balanced pair in `P`. Apply minimality to
  `A`.
- **(Far-from-ordinal case, ε(P) > ε₀)**: The defect gauge gives
  a quantitative lower bound on `δ(P)` directly, ideally via a
  Brightwell + Kahn-Linial-style covariance argument specialized
  to width 3. Concretely: a poset with `ε(P) > ε₀` has many
  "2-sided" incomparable pairs, and the existing 0.276 covariance
  bound, sharpened by the width-3 chain-pair Dilworth structure,
  pushes `δ(P) ≥ 1/3` in this regime.

The reductio: `P` falls into one of the three cases, and each gives
a contradiction to the counterexample hypothesis (or to minimality).

**How it changes the formal skeleton.** Replaces Steps 5–7 wholesale
and restructures Step 8 around the trichotomy. Concretely:

* **Survives:** Step 8 G1 / Theorem E (BK / Cheeger machinery, used
  only in the far-from-ordinal case if at all — and possibly not
  needed); Step 8 G3 layered reduction is replaced by the
  "decomposable case" + "near-ordinal case" pair, both of which are
  cleaner; the small-`n` base case (`lem_small_n`); the
  `brightwell_sharp_centred` axiom.
* **Removed/shrunk:** Steps 1–4 (fiber model, two-interface
  incompatibility) — *if* the far-from-ordinal case can be closed
  without the BK rigidity argument, these become unnecessary.
  Step 5 (rich/collapse dichotomy) is replaced by the ε-trichotomy.
  Step 6 (coherence) and Step 7 (globalization to layered) are
  removed — the ε-cut takes their place. Step 8 G4 (bipartite
  balanced-pair, including `hC3`) is replaced by direct ordinal-sum
  lift + minimality. The compound-automorphism N-poset obstruction
  disappears: in the ε = 0 case the N-poset is exactly `{x₁, x₂} ⊕
  {y₁, y₂}`, which is an ordinal sum and discharges via the
  decomposable-case lift.

The new Lean skeleton looks approximately like —

```lean
theorem width3_one_third_two_thirds_v2 (P : Poset α)
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α) :
    HasBalancedPair α := by
  -- Strong induction on |α|.
  induction hα : Fintype.card α using Nat.strong_induction with
  | _ n ih =>
    -- Trichotomy on ε(P).
    rcases ord_defect_trichotomy P ε₀ with hDecomp | hNear | hFar
    · exact ordinal_sum_lift hDecomp ih
    · exact near_ordinal_sum_lift hNear ih (perturbation_bound hε)
    · exact far_from_ordinal_balanced hFar hP -- direct Brightwell
```

with three new lemma blocks:

1. `ord_defect_trichotomy` (~150 LoC) — defines `ε(P)`, computes
   the minimizing cut, performs the case split.
2. `ordinal_sum_lift` + `near_ordinal_sum_lift` (~300 LoC) — uses
   the existing `OrdinalDecomp.hasBalancedPair_lift_*` infrastructure
   from `mg-7f06` plus a new perturbation lemma derived from
   `brightwell_sharp_centred`.
3. `far_from_ordinal_balanced` (~400-800 LoC, **the main risk**) —
   the direct Brightwell + width-3 covariance argument for the
   `ε > ε₀` regime.

**Lean LoC estimate.** ~850-1300 LoC of new content. Removes
roughly: Steps 1, 2, 3, 4, 5, 6, 7 entirely (current LoC: ~10000
across `Step1/`–`Step7/` lean dirs; not all of this is removable,
but the bulk would be), plus Step 8's `LayeredReduction.lean`,
`LayeredBalanced.lean`, `Case2*`, `Case3*` files (current LoC:
~7000). Net delta: roughly **−15000 LoC** if executed cleanly.
This estimate carries significant uncertainty in the
`far_from_ordinal_balanced` chunk (could blow up to 2000+ LoC if
the direct Brightwell argument needs new mathlib infrastructure).

**Risk assessment + failure mode.** **HIGH RISK.**

* **Risk 1 (likely):** the `far_from_ordinal_balanced` lemma is
  *exactly* the math the existing Steps 1–7 prove, just packaged
  differently. The 8-step rigidity argument may be the natural
  proof of the far-from-ordinal case, and "skipping it" would mean
  re-deriving the same content. In that case, the simplification
  is illusory — we'd recover the same ~10000 LoC under different
  names.
* **Risk 2 (medium):** the perturbation bound
  `|Pr_P[x<y] − Pr_A[x<y]| ≤ f(ε)` for the near-ordinal cut
  needs an `f` that is `o(γ)` on small `ε`. The existing in-tree
  `brightwell_sharp_centred` gives `|Pr_Q − Pr_{Q\\{z}}| ≤ 2/|Q|`
  per single-element perturbation. Iterating this `|B|` times
  gives `|Pr_P − Pr_A| ≤ 2|B|/|P|`, which is **O(1)**, not
  `o(γ)`. A finer bound that scales with the *defect* `ε` rather
  than `|B|` is needed; this is plausibly derivable but not
  trivially so. (The Step 8 G3 cutting argument does something
  analogous and is what gives the `o_K(1)` window bound. Lifting
  that bound out of the cutting-lemma context might be 200-400 LoC
  in itself.)
* **Risk 3 (medium):** the trichotomy as stated has a "gap" in the
  middle: the near-ordinal case requires `ε ≤ ε₀(γ)`, the
  far-from-ordinal case requires `ε > ε₀(γ)`, and the choice of
  `ε₀` must be coordinated with both the perturbation bound and
  the Brightwell-pump bound. If the two regimes don't meet at the
  same `ε₀`, the proof has a gap.
* **Failure mode.** "Risk 1 fires" — the simplification turns out
  to be a re-packaging that incurs as much formalization weight
  as the existing proof, while losing the modular Step-by-step
  structure. We'd end up with a less modular proof of the same
  difficulty. *This is the most likely failure mode and would
  block-and-report at the first chunk.*

**Aesthetics.** **HIGHEST.** When it works, this is the cleanest
possible argument: a 3-line reductio at the headline level,
mirroring the classical `width-2` proof structure (Linial 1984 is
essentially the analogous argument with `ε ≡ 0` because every
indecomposable width-2 poset is the N-poset, which is itself an
ordinal sum after one swap). The argument is exactly what Daniel
articulated: *"reduces to the same epsilon under self-reference, or
balance constant too far from 1/3 given known bounds."*

### Candidate B — Direct minimality contradiction in layered reduction

**The math.** Already articulated in the in-tree `simplifications.md`
§1 ("Layered reduction via direct minimality contradiction").
Local rewrite of `lem:layered-reduction` (Step 8 G3,
`step8.tex:1391–1512`) replacing the `γ/2`-recursion with a
size-minimal counterexample contradiction in one shot:

* Fix `P` a *size*-minimal `γ`-counterexample with a deep layered
  decomposition. After the cut `X = A ⊔ B` with window `W` of size
  `≤ 6w`, `|A| < |X|`, so `A` is not a `γ`-counterexample — `A`
  has a balanced pair `(x, y)`.
* If `(x, y) ⊆ A ∖ W` (bulk), `p_xy(P) = p_xy(A)` exactly by
  Step 3 — balanced pair in `P`, contradiction.
* If every balanced pair of `A` meets the window, apply Step 5(a)
  perturbation, get within `γ`-slack — balanced pair in `P` again.

Either way, `P` was not a counterexample. No `γ/2`-decay across
recursive calls; the dependence of `K_0` on `γ` becomes one-sided.

**How it changes the formal skeleton.** Local. Affects:

* `step8.tex` §`sec:layered-reduction` (`step8.tex:1391–1512`)
  — restated as a single-conclusion lemma rather than a disjunction.
* `lean/OneThird/Step8/LayeredReduction.lean` (483 LoC currently)
  — `LayeredReductionConclusion` becomes
  `∀ P minimal counterexample with deep layering, P has a balanced
  pair`, and the calling code in `LayeredBalanced.lean` /
  `MainAssembly.lean` simplifies because there's no
  `γ/2`-counterexample alternative branch to handle.
* `K_0(γ, w)` is recomputed without the recursive halving (cleaner
  constants).

Steps 1–7 are unchanged. The expensive part of the formalization
(Step 5/6/7 dichotomy + globalization, plus Step 8 G4 bipartite
balanced-pair with the `hC3` parametric hypothesis) is **untouched**.
The `hC3` hypothesis remains on the headline; the
compound-automorphism N-poset obstruction is unaddressed.

**Lean LoC estimate.** Net delta ≈ **−200 to −400 LoC** in
`LayeredReduction.lean` + a 50 LoC simplification in
`MainAssembly.lean`. No new infrastructure required; uses existing
size-minimality and the existing perturbation bound.

**Risk assessment + failure mode.** **LOW RISK.**

* The math is articulated in `simplifications.md` §1, which has
  already verified the case split is sound and identified the two
  subtleties (existence of bulk balanced pair vs. window balanced
  pair; size- vs. `γ`-minimality). The "size-minimality + window
  balanced pair fallback" is essentially the standard
  minimal-counterexample argument; it is structurally identical to
  the genuine ordinal-sum minimality argument (one-sentence
  lift), which is well-understood.
* **Failure mode.** Subtle: the current proof's choice of
  `γ/2`-weakening may have been driven by a downstream step that
  needs the weakened-`γ` structure (flagged as "worth checking" in
  `simplifications.md` §1.5). If this is real, the rewrite needs
  to thread a different invariant through the assembly, and the
  −400 LoC saving evaporates.

**Aesthetics.** **GOOD.** Replaces an iterated halving (which is
less natural than necessary, an artifact of the proof presentation
rather than the math) with a direct one-shot reductio. Mirrors the
classical ordinal-sum minimality argument, which is a one-sentence
lift. The simplification is local, well-bounded, and uncontroversial.

### Candidate C — Discharge `hC3` via finite-enumeration certificate

**The math.** The `hC3 : Case3Witness` parametric hypothesis is the
universally quantified Case-3 discharge: for every layered width-3
non-chain `β` with `|β| ≥ 2`, `β` has a balanced pair. The
obstruction (per `path-c-cleanup-roadmap.md` §5) is the **K=2 +
irreducible + w≥1 + |β|≥3 N-poset class**. The minimal failing
instance is the literal N-poset on 4 elements.

Approach: build a Lean-level Bool certificate analogous to F5a's
`case3_certificate`, but for `K=2`, `|α| ≤ N₀`, `w ∈ {1, 2, 3, 4}`,
checking by direct enumeration that every width-3 layered K=2 poset
on `≤ N₀` elements has a balanced pair. For `|α| > N₀`, use a
separate structural argument that exploits cardinality (e.g., a
pigeonhole on bands).

This is roughly option (β) of `path-c-cleanup-roadmap.md` §6b,
estimated ~300-500 LoC of Bool-certificate machinery + Bool→Prop
bridge + dispatch wiring.

**How it changes the formal skeleton.** Surgical. Affects:

* `lean/OneThird/Step8/LayeredBalanced.lean:438` —
  `Case3Witness` predicate is *promoted from `def` to `theorem`*
  (no more parametric hypothesis on the headline).
* `lean/OneThird/MainTheorem.lean:52` — `hC3` argument dropped.
* New file: `lean/OneThird/Step8/Case3Enum/K2Certificate.lean`
  (~300-500 LoC) and a Bool→Prop bridge analogous to mg-26bb.

`main.tex` is untouched. The structural argument of Steps 1–7 is
untouched. The bipartite balanced-pair lemma (G4) gets a new branch
for K=2 dispatch.

**Lean LoC estimate.** Net delta: **+300 to +500 LoC** of new
certificate machinery, **−10 LoC** of `hC3` plumbing. Total: ~+300
to +500 LoC, but the headline gets cleaner (no hypothesis).

**Risk assessment + failure mode.** **MEDIUM RISK.**

* **Risk 1 (low):** The K=2 + width-3 enumeration is finite and
  mechanical for `|α| ≤ N₀`; the only question is what `N₀` is
  forced to be by the structural complementary argument.
  `path-c-cleanup-roadmap.md` §6b gives a plausibility estimate of
  300-500 LoC for the whole pipeline, but doesn't pin down `N₀`.
* **Risk 2 (medium):** Path C cleanup ran four polecat rounds and
  surfaced new infrastructure blockers each round. The blockers
  were structural (compound automorphism, etc.), but the
  finite-enumeration alternative was not attempted under any
  round; if the F5a-style Bool→Prop bridge has hidden complexity at
  K=2 (e.g., the band-major encoding doesn't apply cleanly), this
  could blow up.
* **Failure mode.** Mid-arc surprise — the K=2 certificate
  pipeline turns out to need infrastructure that doesn't exist
  (e.g., a K=2-specific encoding of layered isomorphism classes),
  and the polecat block-and-reports with new blockers, mirroring
  Path C rounds 3 and 4.

**Aesthetics.** **LOW.** This is a *mechanical* fix, not a math
simplification. It addresses the headline obstruction without
restructuring the proof; the `hC3` hypothesis goes away because
it's discharged by raw enumeration, not because the underlying
mathematics is cleaner. *Does not satisfy the "clear intuitive
aesthetic" criterion of the brief.* Included for completeness as the
non-aesthetic baseline; this candidate would be appropriate if
Daniel's primary concern were the headline residual rather than the
math, but the brief is explicit that math is the target.

### Candidate D — Direct Brightwell pump tightened by width-3

**The math.** The current unconditional Kahn-Linial bound is
`δ(P) ≥ 0.276393…` (`KahnLinial1991`), proved by a covariance /
Brunn-Minkowski argument on rank distributions. The bound is `1/3`
sharp on the width-2 N-poset; the question is whether the
`0.057`-gap between `0.276` and `1/3` is genuinely there in width 3
or only in higher widths.

**Hypothesis** (this candidate's bet): in **width-3 specifically**,
the Kahn-Linial covariance argument can be tightened to `δ(P) ≥
1/3`, by exploiting the Dilworth-3-chain decomposition more
carefully than the original argument does. The Step 4
two-interface incompatibility lemma of the current paper is, in
essence, a specific instance of such a tightening; its conclusion
("two incoherent rich interfaces produce Ω(1) edge boundary") is a
covariance-type lower bound dressed in BK language. A direct
covariance / FKG argument on the 3-chain Dilworth decomposition,
without going through the BK / Cheeger framework, might recover the
same conclusion in fewer steps.

This would replace the entire BK / Cheeger framework with a direct
correlation-inequality argument analogous to Brightwell's 1989 /
Kahn-Linial 1991 papers, but with a width-3-specialized refinement.

**How it changes the formal skeleton.** Replaces *everything* —
Steps 1–8 entirely — with a direct covariance argument. The
existing in-tree axiom `brightwell_sharp_centred` becomes the
load-bearing input; the BK / Cheeger / fiber / interface / coherence
/ globalization / layered-reduction infrastructure goes away.

**Lean LoC estimate.** Hard to estimate without deeper math
investigation. If the math works, the Lean side could collapse to
~2000-4000 LoC of covariance / FKG inequalities + a width-3
specialization argument, on top of mathlib's existing FKG
infrastructure. Net delta: **−15000 LoC** (most of the current
tree).

**Risk assessment + failure mode.** **VERY HIGH RISK — paper-level
math discovery.**

* **Risk 1 (almost certain):** This isn't a re-organization of the
  existing argument; it's a fundamentally different proof. The
  brief explicitly puts "fundamentally new math" out of scope under
  scoping authority and asks the polecat to escalate.
* **Risk 2 (large):** A "width-3 tightening of Kahn-Linial" of
  this kind has presumably been attempted by the original
  Kahn-Linial / Brightwell line of authors and others over decades.
  If it were achievable by a routine refinement of the existing
  covariance argument, it would likely already exist. The current
  paper's BK / Cheeger framework was developed precisely because
  the correlation-inequality approach appeared stuck below `1/3`.
* **Failure mode.** Open-ended math research. Not appropriate for
  a polecat session, even at multi-week budget. If executed at all,
  belongs to a separate research program.

**Aesthetics.** **POTENTIALLY HIGHEST**, if it works — the
"natural" proof of the conjecture under the correlation-inequality
tradition would be the most aesthetic possible outcome. But the
brief disqualifies it for scoping under the
"fundamentally-new-math" clause. **BLOCK-AND-REPORT** if pursued
seriously.

### Survey summary

| Candidate | Aesthetic | Formalizable | Net LoC | Risk | Drops `hC3`? | In scope? |
|---|---|---|---|---|---|---|
| **A** ε-close-to-ord-sum reductio | Highest | Plausible (with risk) | ≈ −15k | HIGH | YES | YES |
| **B** Size-minimality in G3 | Good | Yes | ≈ −400 | LOW | NO | YES |
| **C** Finite-enum certificate for `hC3` | Low | Yes | ≈ +400 | MEDIUM | YES | YES (but off-criterion) |
| **D** Brightwell pump | Highest if works | Unknown | ≈ −15k | VERY HIGH | YES | **NO — escalate** |

A satisfies "clear intuitive aesthetic" and is the explicit example
in Daniel's brief. B is a clean local cleanup that does not address
the headline obstruction but is the safest single chunk to land. C
is mechanically-mature but not "math simplification". D is out of
scope under the scoping authority's "no fresh paper-level math" clause.

## 2. Recommendation

**Recommend Candidate A: ε-close-to-ordinal-sum reductio**, **but
explicitly conditional on a "feasibility chunk" landing first.**

Rationale:

* **Aesthetic.** A is the only candidate that satisfies the "clear
  intuitive aesthetic" criterion *as the primary feature*. It mirrors
  the classical width-2 argument structurally: minimality on `|P|`,
  decompose-or-bound dichotomy, balanced pair lifts. The proof
  becomes a 3-line reductio at the headline level. C and D are
  ruled out (C off-criterion, D out of scope); B is local and good
  but not "the simplification arc" the brief asks for.

* **Formalization profile.** A *can* formalize cleanly **iff** the
  perturbation bound (Risk 2) and the far-from-ordinal closure
  (Risk 1) work out. Both are non-trivial, but both are scoped
  questions with concrete Lean targets — they are not open math
  in the sense of the brief's escalation clause. The Brightwell
  axiom and the existing `OrdinalDecomp.hasBalancedPair_lift_*`
  infrastructure (mg-7f06) provide the Lean-level building blocks.

* **Drops `hC3`.** The N-poset that obstructs `hC3` is itself an
  ordinal sum (`{x₁, x₂} ⊕ {y₁, y₂}`), so it discharges trivially
  in the decomposable case. This means A *automatically* solves the
  Path C cleanup problem that four polecat rounds couldn't close
  via the structural / compound-automorphism route. That is a major
  collateral benefit, not a coincidence: the rigidity-argument
  framing forces a parametric Case-3 discharge precisely because the
  argument doesn't have direct access to the ordinal-sum structure.

* **Tradeoffs.** The recommendation is conditional on a
  feasibility chunk (Chunk A1 below) verifying that the
  perturbation bound is tractable. If the feasibility chunk
  block-and-reports with a counterexample to the perturbation bound
  scaling, fall back to **Candidate B** as the sole landed
  simplification this product cycle.

**Signature regression check.** Candidate A *strengthens* the
headline (drops `hC3`, no new hypotheses, conclusion unchanged)
and *removes* one hypothesis. The `brightwell_sharp_centred` axiom
is retained (still needed for the perturbation bound). This is a
**positive signature change**, not a regression, and does not need
to be flagged under `feedback_signature_regressions`.

If Chunk A1 (feasibility) requires introducing a *new* axiom for
the perturbation scaling (e.g., a chain-form Brightwell bound that
isn't derivable from the existing axiom), that *would* be a
signature regression and must be flagged. The feasibility chunk's
deliverable explicitly includes the question "does the perturbation
bound need a new axiom or does it follow from existing in-tree
infrastructure?"

## 3. Delivery plan (4 chunks)

Each chunk is a future polecat session. PM commits or skips chunks
sequentially based on the previous chunk's outcome. No commitment
to execute is made by this scoping doc.

### Chunk A1 — Feasibility / perturbation-bound feasibility study

**Budget:** 500k tokens, single polecat session.
**Deliverable:** `docs/math-simplification-A1-feasibility.md`.

Task: investigate whether the perturbation bound
`|Pr_P[x<y] − Pr_A[x<y]| ≤ f(ε(P))` with `f(ε) → 0` as `ε → 0` is
derivable from the in-tree `brightwell_sharp_centred` axiom alone,
*without* introducing new axioms.

Concrete sub-questions:

1. (Math) For a width-3 poset `P` with cut `(A, B)` of defect `ε`,
   is there an explicit `f(ε) = O(ε^c)` for some `c > 0` such that
   `|Pr_P[x<y] − Pr_A[x<y]| ≤ f(ε)` for all `x, y ∈ A` incomparable?
   The answer should be derivable from a careful application of
   Brightwell's sharp centred bound on the LE space, summed over
   the (small) defect.
2. (Math) What's the right normalization of `ε`? Per-pair (counts
   pairs), per-volume (counts LE-mass), or per-element (counts
   bad cross-edges)? Different choices give different `f(ε)`
   profiles.
3. (Lean) Pseudo-code the key Lean lemma (statement only, no
   proof) and identify which mathlib / in-tree pieces are needed.
4. (Lean) Estimate the LoC for the perturbation-bound lemma
   alone (bracket: 100-400 LoC).
5. (Risk) If the perturbation bound requires a new project axiom,
   stop and report — the cost-benefit analysis flips.

Block-and-report triggers:

* No `f(ε) → 0` bound derivable from existing axioms → fall back
  to Candidate B.
* New axiom required → flag as tradeoff, escalate.
* `f(ε)` not strong enough to clear `γ` for `γ < 1/3 −
  δ_KL ≈ 0.057` → fall back to Candidate B.

### Chunk A2 — Far-from-ordinal closure feasibility study

**Budget:** 500k tokens, single polecat session.
**Deliverable:** `docs/math-simplification-A2-feasibility.md`.

**Conditional on Chunk A1 landing successfully.**

Task: investigate whether the far-from-ordinal case (`ε(P) > ε₀`)
admits a direct Brightwell + width-3 covariance argument that does
**not** reproduce the entire Steps 1–7 framework.

Concrete sub-questions:

1. (Math) For a width-3 non-chain poset `P` with `ε(P) > ε₀`, is
   `δ(P) ≥ 1/3` derivable from the Kahn-Linial covariance argument
   tightened by the 3-chain Dilworth structure? (This is **the**
   risky math content, but the question is concretely scoped: is
   it an explicit refinement of an existing inequality, or a new
   theorem?)
2. (Math) Alternative — does the far-from-ordinal case still
   require a rigidity argument, just more directly than via Steps
   1–7? E.g., does `ε(P) > ε₀` directly produce a low-conductance
   cut without going through the fiber model?
3. (Risk) If the far-from-ordinal case requires reproducing
   Steps 1–7, the simplification is illusory. Quantify how much
   of Steps 1–7 would survive in Lean.

Block-and-report triggers:

* Far-from-ordinal case requires the full BK / Cheeger / fiber /
  coherence framework → simplification is illusory in this
  direction; report and escalate to PM with options:
  - (a) drop the far-from-ordinal case (would weaken to a
    conditional theorem) — flag as signature regression;
  - (b) keep Steps 1–7 underneath the new framing and accept
    less LoC reduction than estimated;
  - (c) abandon Candidate A and pivot to Candidate B.
* Direct covariance argument requires "fundamentally new math" →
  escalate.
* New axiom required → flag, escalate.

### Chunk A3 — Implementation: Lean skeleton + decomposable case

**Budget:** 700k tokens (or split across two sessions).
**Deliverable:** `lean/OneThird/SimplifiedMain.lean` with the new
headline + decomposable-case proof + ordinal-sum lift wired up.
Plus `docs/math-simplification-A3-status.md` reporting build
status, `#print axioms` baseline, and which existing files become
removable (note: do **not** delete files in this chunk — keep them
as the reference point for review).

**Conditional on A1 + A2 both landing successfully.**

Task: implement the new headline theorem, the strong-induction
skeleton, the trichotomy on `ε(P)`, and the decomposable case
(`ε = 0` ordinal-sum lift). Stub out the near-ordinal and
far-from-ordinal cases as `sorry` with explicit hypothesis
statements derived from A1 and A2.

* New file: `lean/OneThird/SimplifiedMain.lean` — new headline
  theorem.
* Modified file: `lean/OneThird/MainTheorem.lean` — keep both
  headlines (old and new) side-by-side, with a docstring on the
  new one explaining the simplification arc.
* New file: `lean/OneThird/Step8/OrdDefect.lean` (~150 LoC) — the
  defect gauge `ε(P)` and trichotomy.
* New file: `lean/OneThird/Step8/OrdSumLift.lean` (~150 LoC) — the
  decomposable-case lift, building on mg-7f06's
  `OrdinalDecomp.hasBalancedPair_lift_*`.

Block-and-report triggers:

* Build breaks in the strong-induction termination — re-scope.
* Decomposable case lift requires new infrastructure beyond
  mg-7f06 — re-scope.
* Token budget exceeded before deliverable lands — file partial
  with sorry'd stubs and report progress.

### Chunk A4 — Implementation: near-ordinal + far-from-ordinal closure

**Budget:** 1M tokens (very likely to require multiple sessions —
PM should split into A4a / A4b before commissioning).
**Deliverable:** Two new files closing the two open cases of
Chunk A3, plus a clean `#print axioms` baseline matching the old
headline modulo the dropped `hC3`. Plus a status doc.

**Conditional on A3 landing successfully.**

Task: implement the perturbation bound (from A1) and the
far-from-ordinal closure (from A2), discharging the two `sorry`s
left in Chunk A3.

* New file: `lean/OneThird/Step8/PerturbationBound.lean` (~200-400
  LoC) — the chain-form Brightwell perturbation lemma identified in
  A1.
* New file: `lean/OneThird/Step8/FarFromOrdinal.lean` (~400-800
  LoC, depending on what A2 found) — the far-from-ordinal closure.
* Modified file: `lean/OneThird/SimplifiedMain.lean` — wire up the
  two closures, drop the `sorry`s, prove the headline.
* Audit: `#print axioms` baseline reproduced and matches the old
  baseline modulo the dropped `hC3`.

Block-and-report triggers:

* Build breaks at the wiring step — file partial, report.
* `#print axioms` shows new project axiom — flag as tradeoff,
  escalate before committing.
* Token budget exhausted — file partial with explicit progress
  bar (% of A4 complete) and request continuation chunk.

### Optional chunk — clean removal of old infrastructure

If Chunks A1–A4 land successfully, an additional chunk (A5) can
sweep the old `Step1/`–`Step7/` directories and the
`Step8/Layered*.lean` files for removal. This is *not* part of the
math-simplification arc proper; it's bookkeeping. Estimated
budget: 500k tokens. Status: out of scope for this scoping doc.

### Fallback path — Candidate B (if A1 or A2 block-and-reports)

If either A1 or A2 finds a blocker that defeats Candidate A, fall
back to a single-chunk implementation of Candidate B:

* **Chunk B1.** Implement the size-minimality version of `lem:
  layered-reduction` per `simplifications.md` §1. Budget: 400k
  tokens. Deliverable: rewritten `LayeredReduction.lean` +
  updated `MainAssembly.lean`. Headline unchanged. ~−400 LoC net.
  Block-and-report if downstream `MainAssembly.lean` resists the
  single-conclusion shape.

This is a clean small win; it does not address `hC3` but it does
ship a real simplification. PM may also choose to ship B1 in
parallel with A1/A2 feasibility — they don't conflict.

## 4. Honest summary for PM

* **Recommendation:** Candidate A (ε-close-to-ordinal-sum reductio),
  conditional on a 500k-token feasibility chunk (A1) verifying the
  perturbation bound is tractable from in-tree axioms. If A1 fails,
  fall back to Candidate B (size-minimality cleanup). Both are
  ship-able simplifications.

* **Confidence in A succeeding all 4 chunks:** ~50%. The
  feasibility chunks A1 and A2 are deliberately structured to
  block-and-report early if the math doesn't support the framing —
  the budget is spent gathering evidence before committing to the
  large implementation chunks A3 and A4. The 50% reflects the fact
  that "the rigidity argument is just a re-packaging" (Risk 1) is a
  real possibility that A1 + A2 will diagnose.

* **If A succeeds:** −15000 LoC, drops `hC3`, gets the proof closer
  to the classical width-2 form. Major simplification.

* **If A fails (B fallback):** −400 LoC, retains `hC3`, cleans up
  one local artifact. Modest improvement; the headline unchanged.

* **Confidence in B succeeding:** ~85%. Low risk, articulated by
  in-tree `simplifications.md`, mostly bookkeeping.

* **Out-of-scope items flagged for separate decisions:**
  - Candidate D (Brightwell pump direct) — paper-level math
    discovery; not appropriate for polecat scoping. If Daniel wants
    this explored, it should go through a separate "research arc"
    file or external collaboration.
  - K=2 + irreducible compound-automorphism work
    (`path-c-cleanup-roadmap.md` §6a) — orthogonal to this arc.
    If A succeeds, this work becomes irrelevant (the N-poset
    discharges via decomposable case). If A fails, the existing
    park stands.

* **No signature regression in the recommended path.** Both A and
  B preserve the headline conclusion and don't add hypotheses or
  axioms (modulo the A1 question about whether a chain-form
  perturbation bound needs a new axiom — flagged inside A1).

## 5. References

Code anchors used in this doc:

* `lean/OneThird/MainTheorem.lean:52-57` — current headline.
* `lean/OneThird/Step8/LayeredBalanced.lean:438-444` —
  `Case3Witness` predicate.
* `lean/OneThird/Step8/LayeredReduction.lean` (entire file, 483
  LoC) — Step 8 G3 layered reduction.
* `lean/OneThird/Step8/MainAssembly.lean` (356 LoC) — Step 8
  capstone.
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean` —
  the in-tree external axiom.
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1227`,
  `:1237` — `OrdinalDecomp.hasBalancedPair_lift_*` (mg-7f06).

Doc anchors used:

* `simplifications.md` §1 (top-level repo file) — Candidate B
  source.
* `docs/path-c-cleanup-roadmap.md` — `hC3` parking decision and
  the K=2 N-poset obstruction.
* `docs/lean-forum-publication-readiness.md` — current shipped
  state, axiom inventory, headline shape.
* `docs/generalization.md` — width-3 dependency inventory (used
  to identify which steps could be removed under Candidate A).
* `~/.pogo/agents/pm/pm-onethird/memory/project_math_simplification_roadmap.md`
  — activation context (deferred 2026-04-27, activated 2026-05-02).
* `mg-3e53` (this ticket) — scoping pass brief.
* `mg-ba0b` (closed) — parent direction-decision.

Paper anchors used:

* `main.tex` — Theorem `thm:main` (line 230) and discussion (lines
  395-503).
* `step8.tex` — §`sec:layered-reduction` (1391-1512), Theorem E
  (lines 154-315), small-`n` base case (lines 757-874),
  `prop:in-situ-balanced` (lines 2965-3048).
* `simplifications.md` §1 (in-repo, top level).

## Provenance

Filed under `mg-3e53` ("Math-simplification arc — scoping pass") by
polecat `pc-3e53` on 2026-05-02. Branch `math-simp-arc` (this
commit). PM commission of follow-on chunks pending review of this
deliverable.
