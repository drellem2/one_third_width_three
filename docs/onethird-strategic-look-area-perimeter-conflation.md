# OneThird strategic-look: does the area-vs-perimeter conflation indict the proof strategy? (mg-0c39)

**Work item:** mg-0c39 (OneThird-Strategic-Look).
**Date:** 2026-05-23.
**Mandate:** mg-5fdd's audit identified an area-vs-perimeter / total-vs-local
conflation recurring in three independent places: Step 2 `prop:per-fiber`,
Step 8 `eq:window-pert`, Step 8 `lem:window-localization`. Decide whether the
recurrence is a strategic mis-design (gap-by-gap patching will not hold) or
three independently patchable local errors. Do not attempt to fix — diagnose.

**Posture.** Probe genuinely; the recurrence is a wrong-path signal, but a
shared surface pattern alone is not a strategic indictment.

---

## 0. Verdict at a glance

**STRATEGY-INDICTED — with refinement.**

The three sites are **three distinct local errors** that share a *common
strategic origin*: the paper builds a "bounded-local witness ⇒ `o(1)` bulk
correction" pipeline in three places, and in each place the correction
mechanism is not the one the framework promises. Patching each site
individually is not a 1-2 week LaTeX/Lean job: of the three, **zero have a
known mathematical fix**. One (Step 8 eq:window-pert) has a structurally
plausible candidate (the *near-twin route* per mg-44f1 §2.3) that is "strongly
supported by the search but not proven." The other two (Step 2; Step 8
window-localization) have *no candidate fix* on the table.

What's strategically indicted is a sharper object than "the whole paper":

> **The Cheeger / cut-and-window framework — extract a bounded-local witness,
> argue the bulk correction is `o(1)` against the depth/size parameter — does
> not work for width-3 in the regime the proof actually needs (rich fibers
> + deep + irreducible).**

It works for the regimes the paper already discharges by *other* means
(width-2 → Linial 1984; large `γ` → Kahn–Linial; shallow `K` → G4 averaging;
bounded `|β|` → enumeration). It does not work for the residual regime —
which is precisely where minimal counterexamples must live.

The three sites are not three rewrites of the same wrong proof step. They
are three pages on which the same *strategic move* fails, by three distinct
mechanisms, against three different bulk parameters (`n`, `K`, irreducibility).
The recurrence is real, not coincidental — and the framework's missing
inputs (perimeter-scaled per-fiber bounds; clean cuts in irreducible posets;
`o(1)` perturbation across bounded windows) are not patchable from inside the
framework as designed.

Forward action: **pm-onethird re-escalates to Daniel** with the structural
finding; gap-closing pauses pending a strategic reframe of the local→bulk
mechanism for the width-3 deep-irreducible regime.

---

## 1. Method

I read each of the three sites against its surrounding proof and against the
hypotheses of the lemma each is calling out to. For each site I asked:

1. *Underlying lemma the proof needs:* what output would suffice here?
2. *Wrong thing actually being used:* which lemma is invoked, with what
   hypothesis, and where does the mismatch land?
3. *Repair scope:* is there a *patch* (a different lemma / a stronger
   hypothesis / a different decomposition) that would close this site
   without touching the surrounding architecture?

Then I compared the three: same wrong-thing? same fix-scope? same upstream
input missing?

Confidence is HIGH on the three site characterizations (I re-read each
against `step2.tex`, `step8.tex` and the layered definition; the mg-5fdd
audit's lines about the failures are consistent with my own re-derivation).
Confidence is MEDIUM-HIGH on the strategic verdict (it is a judgment about
the joint distribution of three independent failures; I argue it carefully
in §3).

---

## 2. The three sites, characterized

### 2.1 Site A — Step 2 `prop:per-fiber` (step2.tex:1086)

**Underlying lemma the proof needs.** A per-fiber staircase approximation:
on each rich good fiber `F_{x,y}` of side `t = t_{x,y}`, the set `A_{x,y} :=
S ∩ F_{x,y}` (pulled back to the order-convex grid domain `D_{x,y}`) is
`o(|F|)`-close to a staircase region `M_{x,y}`. This `o(|F|)` per-fiber
rigidity is what `thm:step2` exports to Steps 3, 4, 6, 7.

**Wrong thing actually being used.** `lem:weak-grid` (step2.tex:202) is a
*perimeter-scaled* stability lemma:

| hypothesis | conclusion |
|---|---|
| `∂_D A ≤ ε·t`, `ε` small | `|A △ M| ≤ δ(ε)·|D|` with `δ(ε) → 0` as `ε → 0` |

The proof writes
- `∂_D A ≤ η · |F| = η · t · t = (η t) · t` (area-scaled budget, `η ∈ (0,1)` a *fixed* threshold), and
- sets `ε := η t`.

For rich fibers, `t = Θ(n)` and `η` is fixed, so `ε → ∞`, and `δ(ε)` does
not tend to 0. The conclusion degenerates to `|E| ≤ |F|` — the trivial
bound.

**Where the conflation actually sits.** Two natural per-fiber boundary
budgets are available:

- *Area-scaled:* `|∂(S∩F)| ≤ η·|F|`, with `η` a fixed `o(1)` parameter.
  This is what falls out of Step 1's *global* conductance budget
  `|∂_BK S| ≤ κ|S|` by Markov in a generic fiber — and `prop:per-fiber`
  Part (i) (the bad-fiber mass bound) uses exactly this, *and is correct*.
- *Perimeter-scaled:* `|∂(S∩F)| ≤ ε·t_F`, `ε` small. This is what
  `lem:weak-grid` requires, and what a stability theorem on a grid of
  diameter `t` actually needs (the staircase reconstruction interpolates
  `t` rows/columns; the only way to keep the symmetric difference `o(t²)`
  is to keep the perimeter `o(t)`).

The proof tries to convert area to perimeter by writing `η|F| = (η t) · t`
and reading the leading factor as a perimeter-scale parameter `ε`. But the
factor `η t = Θ(n)` is not small; it diverges. The conversion is dimensionally
the right shape (perimeter × side-length = area) but kills the smallness on
the side that needed it.

**Fix-scope.** *Not local.* Either:

- (a) Replace `lem:weak-grid` with a true area-scaled-hypothesis stability
  theorem (`|∂(S∩F)| ≤ η|F|` with `η` fixed ⇒ `o(|F|)` rigid structure).
  No such theorem is in the paper or in the literature for the grid domain
  in this regime; it would be a new isoperimetric stability result with a
  fixed-`η` hypothesis that needs to deliver `o(1)` rigidity — and the
  obvious counter (a "diffuse" `A` with `|A| = |F|/2` and `∂A ≈ |F|`) shows
  this is non-trivial / probably *false* at the obvious threshold.
- (b) Replace the per-fiber budget with a *perimeter-scaled* one. The
  upstream pipeline does not deliver this: the global conductance `κ` is
  *not* `n`-dependent (`κ` is the small-conductance parameter that is
  assumed-then-contradicted; it is fixed, not `O(1/n)`), and any single-fiber
  Markov step on a global area-scaled budget cannot produce a
  perimeter-scaled per-fiber witness without further structural input.
  Producing one would require a multi-scale / dyadic restructuring of
  Steps 1 and 2.

There is a parameter squeeze that the audit (and the paper's own GAP note)
makes precise: bad-fiber mass (Part (i)) wants `η` large; good-fiber error
(Part (ii)) wants `η t` small. With `t = Θ(n)` these are incompatible. No
choice of `η` works.

### 2.2 Site B — Step 8 `eq:window-pert` (step8.tex:2420)

**Underlying lemma the proof needs.** A perturbation bound

> `|p_{xy}(P) − p_{xy}(A)| = o_K(1)` as `K → ∞`,

where `A = L_{≤k}` is the heavy side of a cut at index `k ∈ (w, K-w)`, for
incomparable pairs `(x,y) ⊆ A` whose balanced-pair property in `A` is to be
lifted to `P`. The bound must vanish in `K` because the slack budget against
`[1/3, 2/3]` (`γ/2` per step5) is fixed and bounded.

**Wrong thing actually being used.** The proof writes the *valid* inequality
\[
  |p_{xy}(P) - p_{xy}(A)|
  \;=\; |p_{xy}(P) - p_{xy}(P^\sharp)|
  \;\le\; \frac{|\mathcal L(P) \triangle \mathcal L(P^\sharp)|}{|\mathcal L(P)|},
\]
then claims the right-hand side is `o_K(1)` because *"the window `W` has
bounded size `6w` while `|𝓛(P)| ≥ 2^{K-|W|}` grows."*

The bound is wrong by a constant. Working out the right-hand side: since
`𝓛(P^♯) ⊆ 𝓛(P)`, the symmetric difference equals `𝓛(P) ∖ 𝓛(P^♯)`, and
\[
\frac{|\mathcal L(P^\sharp)|}{|\mathcal L(P)|}
  \;=\; \Pr_{L \sim \mathcal L(P)}\!\bigl[L \text{ respects } P^\sharp\bigr]
\]
which is a topological-sort probability *internal to the bounded window* `W`
(by ordinal-sum factorization of `P^♯`). This is a constant in `(0,1)`,
depending only on `w`, lying in `[1/(6w)!, 1)`, **not decaying with `K`**.
So the right-hand side is `Θ(1)`, not `o_K(1)`.

**Where the conflation sits.** The audit phrases it as *"bounded window ≠
bounded count of full extensions"*. Concretely: the window `W` is bounded
(perimeter / local scale); the count of *full* extensions reversing a
specific window pair is *not* bounded — it scales as a constant fraction of
`|𝓛(P)| ∼ 2^K` (bulk scale). The triangle bound used —
`|p(P) − p(P^♯)| ≤ |𝓛(P) △ 𝓛(P^♯)| / |𝓛(P)|` — is a *worst-case*
total-variation bound that gives no credit for the fact that the "swap"
inside `W` is dimensionally a local perturbation. To get the true `o(1)`
behavior one would need a coupling argument that exploits the local nature
(e.g., couple `L ∼ 𝓛(P)` and `L' ∼ 𝓛(P^♯)` and bound `|L − L'|` only on the
event that the indicator `[x <_L y]` changes — that event has *probability*
controlled by `W`, but the *count* does not).

**Fix-scope.** *Plausibly local but unproven.* The mg-44f1 audit (§2.3,
§4.4) names the *near-twin route* as the most promising candidate:

> In a layered width-3 decomposition, within-band incomparable pairs
> `(a, a')` have two-sided profiles that differ only inside the near-band
> window `≤ 3(2w+1) ≤ 27` elements (`w ≤ 4`). Twin-free + bounded `w`
> therefore guarantees a *near-twin* incomparable pair whose profiles differ
> by a small bounded amount; mg-44f1 found such pairs are always
> `safety`-maximizing and consistently balanced across 1.19M+ posets.

A real proof along this line would replace the cut-and-perturbation
mechanism entirely with a *direct production of a balanced pair from the
near-twin structure*. It is structurally plausible and search-supported.
It is **not proven**. mg-44f1 §4.4 is explicit: *"step 3 [the near-twin /
unbounded irreducible regime] is genuinely new mathematics, not a porting
exercise"*.

### 2.3 Site C — Step 8 `lem:window-localization` (step8.tex:2756)

**Underlying lemma the proof needs.** A reduction of `Pr_{L∼𝓛(P)}[x<_L y]`
for an incomparable pair `(x,y) ∈ L_i × L_j` (so `|i−j| ≤ w`) to the same
probability in a *bounded* sub-poset `Q := P|_{W(i,j)}` with `|Q| ≤ 3(3w+1)`,
preserving the layered structure. The point: `Q` is fixed-size, so a brute
averaging / enumeration argument can close balanced-pair existence on it.

**Wrong thing actually being used.** The proof asserts that `(X_-, X_0, X_+)`
with
\[
  X_- := \bigcup_{k < \min(i,j) - w} L_k,
  \quad X_0 := W(i,j),
  \quad X_+ := \bigcup_{k > \max(i,j) + w} L_k
\]
is an *ordinal-sum decomposition witness* — i.e., that every element of `X_-`
lies below (in `P`) every element of `X_0`.

That fails by exactly `w` bands. To force `L_k <_P L_\ell` (for `k < \ell`),
the layered axiom (L2) requires `k + w < \ell`, i.e. `\ell - k > w`. With
`X_-` excluding bands `k < \min(i,j) - w` and `X_0`'s lowest band at
`\min(i,j) - w`, the smallest gap is `\ell - k = (\min(i,j) - w) -
(\min(i,j) - w - 1) = 1`, which is not `> w` unless `w = 0`. Concretely:
elements in bands `k` with `\min(i,j) - 2w \le k < \min(i,j) - w` lie
outside `W` yet are *not* (L2)-forced below `L_{\min(i,j)-w}`. The cut below
`W` is not clean. The audit notes — and I verify — that **no fixed amount of
extra padding repairs this**: shifting `X_-`'s top boundary down by any
finite amount `w'` just shifts the unforced-zone down by the same amount.

**Where the conflation sits.** The proof treats `W`'s `±w` padding as if it
gave a clean ordinal cut. (L2) gives only a *`w`-band-thick transition
zone*: between "everything forced below" and "the window itself" there is
a `w`-band-wide region in which the comparability direction is not
determined by the axioms. A *clean cut* is a single-band index (perimeter,
zero thickness); the axiom system delivers `w`-band-thick interfaces (bulk
of width `Θ(w)`, which can be 1, 2, 3, or 4 in the actual application).
The cut existence is the perimeter property; (L2) delivers the bulk
property; conflation.

The audit also notes the correct restricted reading: the lemma *is* valid
when both boundary indices `min(i,j) - w` and `max(i,j) + w` happen to be
indices of **layer-ordinal reducibility** (`def:layer-reducible`,
step8.tex:2787). In that case the cuts are genuine and the decomposition
witness exists. But that restricted form is then *subsumed* by
`cor:reducibility-transfer` — it adds nothing new. **The lemma in its useful
(irreducible) form has no replacement.** For a layer-ordinal-irreducible
poset, *no* index is a clean-cut index; the only ordinal middle pieces are
`∅` and `X` itself.

**Fix-scope.** *Not local; no candidate fix.* Of the three sites, this is
the only one that the audit flags as structurally *unrepairable* by any
restatement: irreducible posets have no clean cuts, full stop. Any
mechanism that proves the balanced-pair property in the deep-irreducible
case must avoid cuts entirely. (mg-44f1's near-twin route, if it works,
*is* such a mechanism; it does not need or use `lem:window-localization`.)

---

## 3. Same wrong-thing, or three different errors?

This is the question the ticket actually asks.

### 3.1 What's shared (the surface pattern)

All three sites have the *form* "use a bounded-local witness to bound a
global/bulk correction by `o(1)`". The bounded-local witness is, in each
case:

- A (Step 2): a per-fiber boundary count bounded by area `η·|F|`.
- B (Step 8 eq:window-pert): a bounded interaction window `|W| ≤ 6w`.
- C (Step 8 window-localization): a bounded interaction window `|W| ≤ 3(3w+1)`.

The bulk correction being bounded is, in each case:

- A: per-fiber symmetric difference `|A △ M|` on `|F| = Θ(t²) = Θ(n²)`.
- B: total-variation between `𝓛(P)` and `𝓛(P^♯)` on a depth `K → ∞`.
- C: probability of `[x <_L y]` over `𝓛(P)`, with `|𝓛(P)| → ∞` as `|P| → ∞`.

The framework move is the same in all three: assert a *small-relative-to-
bulk* bound by leveraging the *fixed size of the local witness*. The
failure is the same in all three: the bulk does not carry the locality; the
ratio (bulk-correction)/(bulk-quantity) does not decay.

### 3.2 What's different (the proof mechanisms)

The three errors are *not* the same error:

| | A (Step 2) | B (Step 8 eq:window-pert) | C (Step 8 window-localization) |
|---|---|---|---|
| Error class | wrong-scale **hypothesis** fed into a sharp lemma | wrong-decay claim on a valid **upper bound** | a **decomposition witness does not exist** |
| Lemma being misused | `lem:weak-grid` (correct, but stronger hyp required) | triangle bound on `|p(P) − p(P^♯)|` (correct as bound, falsely claimed to decay) | (L2) (correctly stated; falsely claimed to deliver clean cuts) |
| Bulk parameter the error grows in | side length `t = Θ(n)` | depth `K → ∞` | irreducibility (any depth, given irreducible factor) |
| If you tune the local parameter | no `η` works (parameter squeeze) | no `w` choice fixes the `Θ(1)` factor | no `w` padding produces the missing cut |
| Hypothetical fix mechanism | new isoperimetric stability theorem; or upstream perimeter-scaled witness | local coupling argument; or near-twin direct route | structural argument bypassing cuts entirely (near-twin again) |

So the verbatim "wrong-thing" differs:

- A is **rate-calibration** — wrong-scale hypothesis applied to a correct
  lemma. The mismatch is between the *budget the upstream supplies* and the
  *budget the lemma demands*.
- B is **total-variation overshoot** — a worst-case bound on extension-set
  sizes used where a *probability* bound was needed. The math identity is
  correct; the asymptotic reading is wrong.
- C is **fictitious cut** — a non-existent ordinal-sum decomposition
  asserted to exist. The construction fails on its premise.

These are three different errors. None is a rewrite of either of the others.

### 3.3 What is the same: a single strategic decision

But all three are consequences of *one* strategic choice the paper makes:
**route the proof through a local→bulk mechanism whose required inputs the
upstream does not provide**. The mechanism is the Cheeger/cut-and-window
framework: turn a global isoperimetric assumption into a local rigid
witness, then sum/multiply across pieces with `o(1)` correction. This
framework demands, in three places:

- (A) a per-fiber **perimeter-scaled** boundary witness — Step 1 supplies an
  **area-scaled** witness;
- (B) a **probability-scaled** window-perturbation bound — the natural
  triangle bound is **set-size-scaled** and does not decay;
- (C) a **clean cut** of the layered poset at the window boundaries — (L1)–
  (L4) supply only a **`w`-band transition zone**.

In every case the framework calls for a *perimeter/local-flavor* quantity
and the upstream supplies an *area/total-flavor* quantity. That's the
strategic conflation: **the proof treats the upstream as if it produced
perimeter-flavor witnesses when it actually produces area-flavor
witnesses**.

This is a single choice — pursue a width-3 1/3–2/3 proof by extending the
Linial/Brightwell Cheeger-stability machinery — repeated at three load-
bearing nodes. It is the *organizing decision* of the paper.

It is **not** three independently patchable local errors. The reason: the
patches would all need the same kind of new input — perimeter-scaled local
data the upstream does not currently produce — and that input is not
available in the framework as designed.

### 3.4 But — couldn't each site get its own ad-hoc fix?

Pushback question I want to answer honestly: maybe each site can be patched
by a *different* mechanism, even if the strategic shape is shared.

Let me test that:

- **Site A:** ad-hoc fix = new isoperimetric stability theorem with an
  area-scaled hypothesis delivering `o(1)` rigidity at fixed `η`. The
  obvious counter (diffuse `A` with `|∂A| ≈ |F|`) suggests this is *false*
  at the obvious threshold; making it true requires a non-trivial structural
  hypothesis on `A` that is not currently in Step 1's output.
- **Site B:** ad-hoc fix = near-twin route. mg-44f1 §2.3 + §4.4: *"strongly
  supported by the search but not yet proven … genuinely new mathematics,
  not a porting exercise."* Plausible candidate, real research arc.
- **Site C:** ad-hoc fix = a balanced-pair argument that doesn't use cuts.
  The near-twin route again — it doesn't need cuts. If it works for B, it
  *also* covers C (both live in the deep-irreducible regime, and the
  near-twin produces a balanced pair directly, bypassing both the
  cut-and-window decomposition (C) and the perturbation step (B)).

So sites B and C **collapse to one** under the near-twin route: that route,
if proven, simultaneously discharges the open `lem:layered-reduction` case-(b)
and the open `lem:window-localization`-driven `lem:layered-balanced`
case-C1, because it doesn't need either lemma. They are not three
independent fixes; they are *one* candidate alternative route that bypasses
both broken lemmas.

Site A stands alone. It lives in a different module of the proof (Steps 1-2
expansion engine, not Step 8 endgame) and the near-twin idea has nothing to
say about it.

**So the question reduces to:**

1. Is there a candidate alternative mechanism for Site A?
   *Answer: not on the table. No candidate has been articulated in any of
   the mg-* docs I've seen, the paper itself, or the audit.*
2. Is the near-twin candidate for Sites B+C feasible as a "patch" — i.e.,
   tractable within a bounded budget?
   *Answer per mg-44f1 §4.4: "genuinely new mathematics, not a porting
   exercise." Not bounded; it is a research project of its own.*

Both candidate-patch routes are open research arcs. Neither is a write-up.

### 3.5 The recurrence-pattern signal

A final independent angle. The mg-5fdd audit notes that this is the
**11th-13th vacuity discovery** in the OneThird arc, following ten prior
ones (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13, mg-5fbd,
mg-0bd1, mg-fdc2, mg-c2d7). The earlier ten were on the *Lean-formalization
side* (typed-routing fiction, vacuous covers, sham widths, etc.). The
present three are on the *paper-math side*, and all three share a single
length-scale conflation pattern.

A single recurring blind spot across two independent surfaces (Lean
architecture + paper math) — and across many independent ticket-driven
audits — is the strongest empirical signal the project has that the
underlying *strategy* is reaching for structure that isn't there. Patching
the three current sites individually risks the 12th-14th vacuity discovery
landing later, in a place where the patch itself fails the same way.

---

## 4. Verdict

**STRATEGY-INDICTED**, in the following precise sense:

(a) **Not the whole paper.** The Brightwell transcription (eq:sharp-centred)
is sound. The Step 3 coherence bookkeeping, Step 5 interval combinatorics,
Step 7 cocycle-to-potential globalization, Step 8 ordinal-sum factorisation
(`lem:ordinal-factorisation`) are sound infrastructure. The layered-form
machinery in the *reducible* cases works (`cor:reducibility-transfer`). The
shallow-`K` and large-`γ` and small-`|β|` cases are discharged by *other*
mechanisms (G4 averaging, Kahn–Linial, mg-4d7b enumeration). What's
indicted is not the whole paper.

(b) **The Cheeger / cut-and-window local→bulk mechanism is indicted as a
route to the width-3 1/3-2/3 conjecture in the residual regime** — the deep,
rich, irreducible, twin-free case where minimal counterexamples must live.
That mechanism is the paper's organizing framework, and it produces all
three sites as a single strategic failure mode.

(c) **Gap-by-gap patching is *not* the right next step.** Of the three
sites, sites B and C are joint and have one candidate alternative route
(near-twin, mg-44f1 §2.3) that is open research; site A has no candidate
route at all and is a separate problem. Two independent open research arcs
(one for A, one for B+C), one of which has no leads.

(d) **The local-errors verdict would require all three to have plausibly-
local fixes that leave the surrounding architecture intact.** Site A fails
this test (the fix would restructure Step 1's output). Sites B+C fail this
test (the candidate fix replaces, rather than patches, two load-bearing
lemmas). The verdict is STRATEGY-INDICTED.

---

## 5. Characterization of the strategic mis-design

(Per ticket scope: characterize, do not solve.)

### 5.1 The strategic move and what it requires

The paper attempts to prove a *bulk* property (width-3 1/3-2/3 for all `P`
large enough) via a Cheeger contradiction:

> Suppose a low-conductance witness `S` (`|∂_BK S| ≤ κ|S|`). Then on most
> rich fibers, `S` is `o(|F|)`-close to a staircase (Step 2). Sign these
> staircases (Step 3). Two staircase signs at incompatible orientations on
> overlapping fibers produce expansion (Steps 4-6) and a coherent global
> structure (Step 7), eventually producing a balanced pair (Step 8). All
> together contradicts `κ` small.

Two locations in this pipeline call for a *local→bulk `o(1)`-correction*
step:

- **Step 1 → Step 2:** global conductance `κ` (area-scaled) ⇒ per-fiber
  rigidity (perimeter-scaled rigidity needed).
- **Step 7 → Step 8 G3/G4:** per-band layered structure (`w`-thick zones)
  ⇒ balanced-pair existence (clean-cut-bounded reduction needed).

In both locations the framework's *required input* is a perimeter-flavor
quantity; the upstream's *delivered output* is an area-flavor quantity.
The conflation lives in *exactly these two transitions*, and Sites A, B, C
are the three pages where the conflation is visible.

### 5.2 What a corrected approach would need

The corrected approach has to either:

1. **Enrich the upstream to produce perimeter-flavor outputs.**
   - For Step 1 → Step 2: derive a multi-scale / dyadic decomposition of `S`
     in which perimeter-scaled per-fiber bounds *do* fall out at the
     relevant length scales. Plausibility: low to medium. This is a
     significant restructuring of Steps 1 and 2 and would likely require
     genuinely new isoperimetric input (e.g., a Cheeger-type inequality with
     a `1/n`-scaled small parameter, or a co-area integration argument).
   - For Step 7 → Step 8: deliver from Step 7 a *layered decomposition with
     additional cut-existence guarantees* — e.g., a layered + 1-thick
     interface structure rather than `w`-thick. Plausibility: low. The
     `w`-thick interaction width is intrinsic to the Step 5 collapse output
     (it is `O_T(1)` driven by the Step 5 richness constants). Forcing
     `w = 0` or `w = 1` would amount to a new structural theorem on
     Bubley-Karzanov / Cheeger output, with no candidate in sight.

2. **Replace the framework's local→bulk move with a fundamentally different
   mechanism.**
   - Replace Step 2's per-fiber rigidity with a *global* expansion argument
     that does not pass through staircase approximation (e.g., a direct
     entropy / log-Sobolev attack). Plausibility: speculative. This would
     restructure Steps 2-7 wholesale.
   - Replace Step 8 G3+G4 deep-irreducible's cut-and-window argument with a
     *direct* balanced-pair extraction from layered structure (near-twin
     route, mg-44f1 §2.3). Plausibility: medium. Search-supported; not
     proven. mg-44f1 §4.4 flags it as "genuinely new mathematics."

3. **Restate the result as conditional and ship what's actually proved.**
   - The mg-13a5 / mg-2970 / mg-5c32 line of work has already begun this:
     small-`|α|` (`≤ 10`) unconditional (mg-4d7b enumeration); large-`|α|`
     conditional on the Steps-1-7 cascade. The strategic-look here adds:
     **the Steps-1-7 cascade conditionality must be made explicit as a
     conditionality on closing the Step-2 area/perimeter gap, not as a
     "pending Lean port" conditionality** (which is how `AXIOMS.md`
     historically framed `stepsOneToSevenCascade` before mg-5fdd).
     Similarly the Step 8 G4 axiom `lem_layered_balanced_irreducible_base`
     must be explicit about being a genuine open problem with one
     search-supported candidate route (near-twin).

Routes 1 and 2 are mathematical projects on the multi-month scale (route 2
B+C specifically is what mg-44f1 §4.4 step 3 already names as "genuinely new
mathematics, not a porting exercise"). Route 3 is the *honest disclosure*
update that mg-5fdd has largely already done on the LaTeX side; the
strategic-look here recommends finishing that disclosure tightening before
any forward research commitment.

### 5.3 What a "right" framework for width-3 would have to look like

I'll keep this brief — the ticket asks for *characterization*, not a sketch
of a proof.

A successful framework for the width-3 1/3-2/3 conjecture would have to
deliver, in addition to the parts already sound in the paper:

- A *per-fiber stability mechanism* that operates at the
  *area-scaled* boundary budget the upstream actually delivers, OR an
  enriched upstream that delivers perimeter-scaled per-fiber budgets at the
  right scales. The first requires a stability theorem the literature does
  not seem to contain; the second requires a multi-scale Cheeger argument
  the paper does not currently set up.
- A *balanced-pair existence argument* for the layered-deep-irreducible
  case that does not rely on producing an ordinal-sum cut. Near-twin is one
  candidate; correlation-inequality arguments (FKG / Ahlswede–Daykin)
  applied directly to within-band profiles is another (mg-44f1 §4.3 names
  splitting FKG content as the single highest-value refinement of the
  current axiom form). The latter is closer to known mathematics, but the
  width-3 unbounded case is not directly covered by any existing
  correlation-inequality result.

Both lines exist in the literature *for adjacent problems* — Beck's `Q^n`,
Brightwell's `δ* ≥ 0.276`, Kahn–Linial's large-`γ` case, Shepp's XYZ
theorem — but none is known to extend to width-3 small-`γ` deep-irreducible.
That is the genuine open problem the residual sits on.

---

## 6. Forward action

Per ticket: **STRATEGY-INDICTED ⇒ pm-onethird re-escalates to Daniel with
the structural finding; gap-closing pauses pending a strategic reframe.**

Concretely, what to relay:

1. **The recurrence is not a coincidence.** Three distinct local errors,
   each at a load-bearing node of the paper, each a manifestation of a
   single strategic move (local→bulk `o(1)`-correction) breaking against a
   single missing kind of input (perimeter-scaled local data the upstream
   does not deliver).

2. **Gap-by-gap closing will not hold.** Site A has no candidate route at
   all. Sites B+C collapse to a single candidate route (near-twin per
   mg-44f1 §2.3) which is itself open research, not a write-up. Patching
   each site individually is *two* multi-month research arcs, not three
   independent 1-2-week fixes — and one of the two has no leads.

3. **What is salvageable.** The paper's *infrastructure* (Brightwell, Step
   3 coherence, Step 5 intervals, Step 7 cocycle-potential, Step 8 ordinal-
   sum factorisation, mg-4d7b enumeration) is sound. The *headline*
   restated as small-`|α|` unconditional + large-`|α|` conditional-on-
   Steps-1-7-plus-Step-8-G3-G4 (mg-5c32, mg-2970) is honest *given a tighter
   disclosure of what "conditional" means*.

4. **Two open research arcs make up the actual residual:**
   - (R-A) Step 2's per-fiber rigidity mechanism. No candidate route. Likely
     requires restructuring Step 1's output (multi-scale Cheeger or a new
     stability theorem). High-risk.
   - (R-BC) Step 8 deep-irreducible balanced pair. One candidate route
     (near-twin, mg-44f1 §2.3). Search-supported. mg-44f1 §4.4 flags it as
     "genuinely new mathematics." Medium-risk.

5. **Recommendation for Daniel (yours to override; the PM call is
   strategic-look-first as confirmed by mg-0c39).** Before committing the
   deep math-research arc, decide which of the following:

   - (i) Pursue (R-A) and (R-BC) as parallel multi-month research projects.
     Optimistic budget: 6-12 months for (R-BC) given the search support;
     12+ months for (R-A) with no candidate. Worst case: (R-A) fails as a
     research project and the headline shrinks to a conditional result.
   - (ii) Pivot to the conditional form: ship "1/3-2/3 conjectured for
     width-3 conditional on [Step-2-rigidity, Step-8-deep-irreducible
     balanced pair], unconditional for `|α| ≤ 10`." That conditionality is
     already partially in the paper (mg-13a5, mg-5fdd); tighten it. This is
     a write-up scope (weeks, not months).
   - (iii) Abandon the Cheeger / cut-and-window framework entirely and try
     a fundamentally different attack on the conjecture (correlation-
     inequality direct route, entropy methods, Kahn–Saks-style joint
     measure, ...). Highest variance; same multi-month-to-multi-year
     timescale as (i).

   The strategic-look here cannot adjudicate among (i)/(ii)/(iii); that's
   Daniel's call, informed by his read of the math-research market for the
   relevant techniques. What the strategic-look *can* say: option (b) was
   the right PM call before committing (a). The verdict here, refined,
   should now route Daniel toward an explicit (i)-vs-(ii)-vs-(iii) decision
   before any further gap-closing budget is committed.

---

## 7. Cross-reference index

| Source | Role |
|---|---|
| `docs/onethird-math-finished-audit.md` (mg-5fdd) | Origin audit; identifies the 3 conflation sites + 4 other gaps |
| `step2.tex:1027-1138` | Site A — `prop:per-fiber` + GAP note |
| `step2.tex:202-345` | `lem:weak-grid` statement and proof |
| `step8.tex:2317-2462` | Site B — `lem:layered-reduction` (G3) + GAP note on eq:window-pert |
| `step8.tex:2709-2776` | Site C — `lem:window-localization` + GAP note |
| `step8.tex:2007-2031` | `def:layered` — the (L1)-(L4) axioms whose limits the GAPs expose |
| `docs/state-Piece6-Axiom-Verify-Session1.md` (mg-44f1) §2.3 + §4.4 | Near-twin route as candidate for B+C; "genuinely new mathematics" disclosure |
| `docs/width3-residual-statement.md` (mg-5c32) | Residual statement architecture (R1+R2 small/large `|α|`) |
| `docs/state-Piece6-Redo-Session1.md` (mg-65de) | Window-localization gap re-derivation; `P_K = \{1,..,K\}, i<j ⇔ j-i>2` as the unbounded irreducible counterexample family |
| `data/case3witness-cap-light-enum.json` (mg-4d7b, mg-be48) | Small-`|α|` unconditional enumeration (no counterexamples to `|α| ≤ 10` cap-light) |
