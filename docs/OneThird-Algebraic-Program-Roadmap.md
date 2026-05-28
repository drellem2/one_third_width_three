# OneThird — Algebraic Program Roadmap

*Bounded scoping deliverable for mg-9f67, per Daniel's 2026-05-28T11:33Z directive opening the algebraic-objects / counterexample-search program. This is the roadmap; it pins candidate algebraic families, the computability gate, the Phase-0 viability probe, the parameter-space sweep strategy, and the explicit non-goals. No expensive execution is performed here — per the anti-drift / viability-probe-before-hardening discipline, this scoping precedes any execution ticket.*

*Canonical vision: [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md) (commit 6e28060). Every claim below traces to one of the four vision-parts; the §0 mapping is load-bearing per the ticket's VISION CHECK.*

---

## §0 — Vision mapping (load-bearing; read first)

The vision has four parts: **(1) algebraic objects**, **(2) yielding posets with computable Q(P)**, **(3) parameter-space exploration**, **(4) find a counterexample (or bounded null result)**. Each shortlisted family and the Phase-0 probe maps explicitly:

| Roadmap object | Vision-part 1 (algebraic object) | Vision-part 2 (computable Q) |
|---|---|---|
| **A. Hook-length / skew-shape / d-complete families** *(LEADING)* | Cells of a (skew) Young diagram / d-complete poset; symmetric-function theory | Q closed-form via Frame–Robinson–Thrall / Naruse hook-length / Proctor hook-length |
| **B. Series-parallel / ordinal-sum gadget families** | Posets generated from small gadgets under ⊕ (ordinal sum) and ⊔ (disjoint union) | Q via recursive convolution closed-form on the decomposition tree |
| **C. Order-polytope / Ehrhart volume families** | Order polytope `O(P)` of a width-3 lattice family; toric/Ehrhart algebra | Pr[x<y] = ratio of facet sub-polytope volumes; Ehrhart-computable |
| **D. Finite-geometry incidence posets (rank-3, parameter q)** | Truncated incidence poset of a finite geometry over `F_q` | Q via incidence-count-driven width-≤3 linear-extension DP |

| Phase-0 probe | Vision-part 3 (parameter sweep) | Vision-part 4 (counterexample / null) |
|---|---|---|
| **3-row skew-shape probe** (§4) | Shape parameters `(λ,μ)` form the swept lattice; Q is a cheap closed-form to evaluate at each point | Probe confirms the algebra→Q pipeline produces a real Q and reports its distance from 1/3, establishing whether descent toward Q<1/3 is even meaningful in the family |

**Drift test applied:** every recommended execution ticket in §7 states which vision-part it realizes. Any future ticket that cannot name its vision-part is a drift signal and must be reshaped, not filed.

---

## §1 — The computability spine (why this program is non-trivial, and where it is easy)

Everything in this program rests on one fact and one consequence.

**The fact.** Computing `Q(P)` requires the pairwise order probabilities `Pr[x<y]` over uniformly random linear extensions, and computing the number of linear extensions of a general finite poset is **#P-complete** (Brightwell–Winkler, 1991). So "yielding posets with computable balance constants" (vision-part 2) is *not* automatic — for an arbitrary algebraic family it can be intractable, and only Monte-Carlo *estimates* of Q would be available. That is exactly the failure mode the vision warns against ("computable … not just simulable").

**The consequence — width 3 is the friendly regime.** The number of linear extensions of a poset of **bounded width `w`** is computable in polynomial time by the order-ideal / antichain dynamic program: the DP runs over the lattice of order ideals (down-sets), of which there are `O(n^w)` for width `w`, giving `O(n^{w+1})`-ish time. For **width 3** this is `O(n^4)` per instance, and the same DP yields *every* pairwise `Pr[x<y]` (count ideals separating `x` from `y`). 

> **Corollary (the gate is automatically passed for width-3 instances).** For any family of width-≤3 posets, `Q(P)` is polynomial-time computable *per instance* with no algebraic structure required at all. The target case — width 3 — sits inside the tractable regime by construction.

So what does "algebraic" actually *buy* us, given per-instance tractability is free in width 3? Two things the per-instance DP does **not** give:

1. **Closed-form Q as a function of parameters.** An algebraic family (hook lengths, ordinal-sum convolutions) yields `Q` as an explicit rational function of the family parameters. This lets the parameter sweep (vision-part 3) be a *symbolic/analytic* descent and an *asymptotic infimum* computation, not a brute-force per-point enumeration. You can ask "what is `inf Q` over the whole infinite family?" — a question the DP cannot answer.
2. **Structured infinite families to sweep at all.** "Look at the parameter space" (vision-part 3) presupposes a *parameterized* family. Algebraic objects supply the parameterization with a handle on width.

This reframes the program precisely: **the algebra is not needed for computability of any single width-3 Q (that's free); it is needed to make the parameter sweep analytic and the infimum reachable.** Candidates are therefore ranked on *closed-form tractability of Q-as-a-function-of-parameters* and *controllability of width to exactly 3*, not on per-instance computability.

---

## §2 — Survey of the inspiration sources

Daniel's cited inspiration: recent additive-combinatorics breakthroughs and the unit-distance conjecture progress. The survey maps each to its algebraic methodology and asks the operational question: **does it (or could it) produce finite width-controlled posets where Q is computable as a function of algebraic parameters?**

| Inspiration source | Algebraic methodology | Produces width-controlled posets with computable Q? | Verdict for this program |
|---|---|---|---|
| **Croot–Lev–Pach / slice-rank (capset)** | Polynomial method: bound multiplicative/combinatorial structure by rank of a tensor/slice over `F_3^n` | The natural posets (inclusion order on a capset, coordinate-dominance on `F_3^n`) have **width exponential in n** and no product formula for linear-extension counts → Q only Monte-Carlo. The *output* (an exact extremal bound) is what's exact, not a poset's Q. | **INSPIRATION ONLY.** Methodology (get exact bounds via algebra) is the spirit; it does not hand us a tractable poset family. Documented; not shortlisted. |
| **Capset lower-bound constructions (tri-colored sum-free, etc.)** | Explicit algebraic set constructions in `F_p^n` | Same width blow-up; the constructions are *sets*, and the induced posets are wide and formula-less | **INSPIRATION ONLY.** |
| **Plünnecke–Ruzsa / sumset growth refinements** | Inequalities on `|A+B|`, `|A−A|`; graph-entropy / tensor-power tricks | No canonical finite poset; sumset *interval* posets on `Z/nZ` are possible but wide and lack a Q formula | **INSPIRATION ONLY** (sumset-interval posets parked as a stretch idea, §6 reject list). |
| **Unit-distance / incidence (Szemerédi–Trotter, polynomial partitioning)** | Incidence bounds via the polynomial method / algebraic geometry | Incidence *posets* (points < lines < …) are genuine algebraic objects; truncating/restricting to **rank 3 / width 3** is possible, and width-3 DP makes Q computable; q-parameterized via `F_q` | **CANDIDATE D** (weak but vision-faithful to the unit-distance inspiration). |
| **Erdős–Ko–Rado / sunflower-style extremal set theory** | Subset lattices, shifting/compression, eigenvalue methods | Subset lattices `B_n` are wide; *but* the **hook-length / SYT** corner of the same world (Young's lattice, RSK, symmetric functions) yields **closed-form linear-extension counts with width controllable to 3** | **CANDIDATE A** (the productive descendant of this branch). |
| **Hook-length / Naruse / d-complete (Proctor) theory** | Symmetric-function theory; `# SYT = n!/∏ hooks`; Naruse excited-diagram formula for skew shapes; Proctor hook-length for d-complete posets | **Yes — directly.** Closed-form linear-extension counts; pairwise probabilities = ratios of SYT counts; width = controllable via shape | **CANDIDATE A (LEADING).** |
| **Order-polytope / Ehrhart algebra (Stanley)** | `vol O(P) = e(P)/n!`; Ehrhart polynomial; toric variety of the order polytope | `Pr[x<y]` = ratio of sub-polytope volumes; Ehrhart-computable; width 3 keeps the polytope low-complexity | **CANDIDATE C** (algebraic-geometry-flavored reframing/tool). |
| **Series-parallel / N-free poset algebra** | Closure of singletons under ⊕ and ⊔; the substitution-decomposition / modular-decomposition algebra | Linear-extension count and pairwise probabilities satisfy **exact convolution recurrences** on the decomposition tree; width = sum/max controllable | **CANDIDATE B** (where historical near-extremal examples live). |

**One-line survey conclusion.** The additive-combinatorics *headliners* (slice-rank, capset) are **inspiration, not instruments** — they produce exact *bounds*, not tractable *poset families*. The instruments are their algebraic neighbors: **hook-length/SYT theory (A)**, **series-parallel algebra (B)**, **order-polytope/Ehrhart (C)**, and **finite-geometry incidence (D)**.

---

## §3 — Candidate shortlist (per-family assessment)

For each: algebraic object · poset construction · computability claim for Q · parameter-space dimension · counterexample-relevance (does small Q plausibly live here?).

### A. Hook-length / skew-shape / d-complete families — **LEADING**

- **Algebraic object.** A (skew) Young diagram `λ/μ`, or more generally a **d-complete poset** (Proctor); the symmetric-function machinery of standard Young tableaux.
- **Poset construction.** Cells of `λ/μ` under the componentwise (product) order `(i,j) ≤ (i',j') ⇔ i≤i' ∧ j≤j'`. Linear extensions of this poset = **standard Young tableaux** of shape `λ/μ`.
- **Computability of Q.** `e(λ) = n!/∏_{c} h(c)` (Frame–Robinson–Thrall); for skew shapes `e(λ/μ)` via the **Naruse hook-length formula** (sum over excited diagrams) or the Aitken/Jacobi–Trudi determinant. For an incomparable cell pair `(a,b)`, `Pr[a<b] = e(λ/μ with relation a<b)/e(λ/μ)`; the numerator is again an SYT-count of a width-≤3 poset (closed-form when it stays a shape, else width-3 DP). **⇒ Q is a closed-form rational function of the shape parameters.**
- **Width control.** Width of the cell-poset = longest antichain = longest anti-diagonal run. Restrict to **3-row** (resp. 3-column) shapes to pin width ≤ 3; engineer the conjugate to force width exactly 3.
- **Parameter-space dimension.** 3-row skew shape: `(λ₁,λ₂,λ₃,μ₁,μ₂,μ₃)` with `λᵢ≥λᵢ₊₁`, `μᵢ≤λᵢ`, `μ` a partition ⇒ effectively **~5 free integer parameters** after normalization; unbounded in `n`, bounded per sweep by `n ≤ N`.
- **Counterexample relevance.** **Strong.** Small Q needs *every* incomparable pair strongly biased — i.e. near-chain posets. **Near-column skew shapes** (tall, thin, with a few staggered cells) are exactly near-chains with a handful of strongly-biased incomparable pairs ⇒ this family reaches toward the 1/3 boundary while keeping Q closed-form.

### B. Series-parallel / ordinal-sum gadget families

- **Algebraic object.** The free `{⊕ (ordinal sum), ⊔ (disjoint union)}`-algebra on small gadgets (singletons, antichains, N-poset, fences).
- **Poset construction.** Build `P` as an SP-expression; `P` = parse tree.
- **Computability of Q.** `e(P⊕Q)=e(P)·e(Q)`; `e(P⊔Q)=C(|P|+|Q|,|P|)·e(P)·e(Q)`. Pairwise probabilities decompose along the tree: across an `⊕` everything below < everything above (probabilities are 0/1, never the witness pair); within a `⊔` the two blocks interleave with a hypergeometric law. **⇒ Q computable by a recursion over the parse tree (closed-form per fixed tree shape).**
- **Width control.** `width(P⊕Q)=max`, `width(P⊔Q)=sum`. Trivially pinnable to ≤ 3.
- **Parameter-space dimension.** The *tree shape* is discrete-combinatorial; block sizes are integer parameters. Dimension = number of leaves; sweep = over tree shapes up to `n ≤ N`.
- **Counterexample relevance.** **Mixed but historically central.** Pure ordinal-sums-of-antichains give `Q=1/2` (useless — every incomparable pair is symmetric). Small Q requires the *asymmetric* gadgets (N-poset, fences) glued cleverly; this is where the existing repo diagnostic (`3-antichain ⊕ 3-antichain`, mg-2970 — note that one is `Q=1/2`) and the classical near-extremal examples live. Good for *understanding* the boundary; closed form is per-tree, so the sweep is over a combinatorial tree-space rather than a smooth lattice.

### C. Order-polytope / Ehrhart volume families

- **Algebraic object.** The **order polytope** `O(P) ⊂ [0,1]^P` (Stanley) and its toric variety / Ehrhart polynomial.
- **Poset construction.** Any width-3 lattice family; `O(P)` triangulates into `e(P)` unit simplices, one per linear extension.
- **Computability of Q.** `vol O(P)=e(P)/n!`; `Pr[x<y]` = (normalized) volume of the sub-polytope `{x<y}`, a ratio of two order-polytope volumes ⇒ Ehrhart-/volume-computable. For width 3 the polytope is low-complexity.
- **Width control.** Inherited from the chosen base family.
- **Parameter-space dimension.** Inherited; the value of C is as an **alternative computation engine and a continuous relaxation** (volumes vary smoothly ⇒ enables gradient-free continuous descent on a relaxed parameter), not as an independent source of posets.
- **Counterexample relevance.** Indirect — C is the **smoothing/algebraic-geometry lens** on A and B, most useful for the continuous-descent search strategy (§5).

### D. Finite-geometry incidence posets (rank-3, parameter q)

- **Algebraic object.** Incidence poset of a finite geometry over `F_q` (affine/projective plane, generalized quadrangle), truncated/restricted to **rank 3 / width 3**.
- **Poset construction.** Elements = a restricted set of points/lines/(planes); order = incidence/containment, restricted to keep width 3.
- **Computability of Q.** Width-3 DP (per-instance poly-time); incidence counts are closed-form in `q`, but Q-as-a-function-of-`q` is **not** generally closed-form (the restriction needed to force width 3 breaks the clean `q`-formula). **Weaker computability claim** — passes the gate per-instance, fails the "closed-form in parameters" upgrade in general.
- **Parameter-space dimension.** Field size `q` (prime power) + restriction choices ⇒ low-dimensional but lumpy.
- **Counterexample relevance.** Speculative; this is the **vision-faithful nod to the unit-distance/incidence inspiration**, kept on the list so the program visibly honors that source, but ranked below A/B/C.

---

## §4 — Computability gate (sharpened)

The gate: **"computable as a function of algebraic parameters"** must mean closed-form *or* provably polynomial-time in named parameters — **never** "Monte-Carlo estimable only."

| Family | Sharp computability claim | Gate verdict |
|---|---|---|
| **A** | `e(λ/μ)` closed-form (FRT / Naruse, sum over excited diagrams — `O(poly)` terms for fixed #rows); each `Pr[a<b]` a ratio of two such counts; **Q a closed-form rational function of `(λ,μ)`.** Fallback width-3 DP `O(n⁴)` always available. | **PASS — strongest.** |
| **B** | `e(P)` and all `Pr[x<y]` by exact convolution recurrence over the SP parse tree; closed-form for each fixed tree shape; `O(n²)` per instance. | **PASS.** |
| **C** | `Pr[x<y]` = ratio of order-polytope volumes; exact via Ehrhart / Lawrence–Varchenko volume formulas; polynomial for fixed width-3 combinatorics. | **PASS** (as engine/relaxation). |
| **D** | Per-instance width-3 DP `O(n⁴)` (PASS); but closed-form-in-`q` **fails** in general after the width-3 restriction. | **CONDITIONAL PASS** — per-instance only; flag the closed-form gap. |
| Slice-rank / capset inclusion posets | Width exponential, no product formula ⇒ **Monte-Carlo only**. | **REJECT.** |
| Generic matroid / geometric lattices | Width exponential (middle Whitney number) ⇒ **Monte-Carlo only**. | **REJECT.** |
| Sumset-interval posets on `Z/nZ` | No linear-extension formula; width uncontrolled. | **REJECT** (parked). |

**Gate conclusion.** A is the only family that *fully* passes the strongest reading (closed-form Q in the parameters). B passes per-tree. C is an engine. D is per-instance-only. The rejected families are exactly the additive-combinatorics headliners — confirming §2's "inspiration, not instruments."

---

## §5 — Phase-0 viability probe (the immediate next step — GREEN)

**Purpose (vision-parts 3+4).** Before any hardening or large sweep, verify *concretely* that the algebra→Q pipeline runs end-to-end on the leading family (A): one explicit instance, Q computed two independent ways, agreement confirmed, distance-to-1/3 reported. This de-risks the entire program for the cost of a few CPU-minutes. This is the **first execution ticket**; the roadmap flags it GREEN.

**Leading candidate:** **Family A (hook-length / 3-row skew shapes).**

**Probe spec.**

1. **Tiny sanity (`n=3,4`).**
   - Shape `λ=(2,1)` (`n=3`): cells `(1,1)<(1,2)`, `(1,1)<(2,1)`, with `(1,2) ∥ (2,1)`. Hooks `3,1,1` ⇒ `e=3!/3=2`. The lone incomparable pair is symmetric ⇒ `Pr=1/2`, `Q=1/2`. Brute-force enumeration of the 2 linear extensions must reproduce this exactly. *(Confirms the pipeline and the symmetric base case.)*
   - Shape `λ=(2,2)` and `λ=(3,1)` (`n=4`): compute `e` by hook-length, enumerate, cross-check every `Pr[x<y]`, report `Q`.
2. **Real probe (`n≈7–9`, width 3, biased).** Construct one **3-row skew shape engineered to be near-chain** (a tall thin shape with a few staggered cells producing strongly-biased incomparable pairs) — the regime where small Q would live.
   - Compute `e(λ/μ)` via the **Naruse hook-length formula** (excited diagrams) **and** independently by **brute-force linear-extension enumeration** (≤ a few thousand extensions at this size).
   - Compute **all** `Pr[x<y]` and hence `Q(P)` both ways.
   - **Optional third check:** Monte-Carlo estimate of Q (as an *independent spot-check only*, never the source of truth — gate discipline).
3. **Success criteria.**
   - (a) Closed-form and brute-force `e` and `Q` agree exactly. *(Pipeline correctness.)*
   - (b) The probe **reports the achieved Q and its distance from 1/3**, and identifies the local gradient direction in shape-parameter space (which way to deform to lower Q). *(Establishes whether descent toward `Q<1/3` is meaningful in A.)*
   - (c) A reusable, tested computational kernel exists: `shape → (e, {Pr[x<y]}, Q)` with the closed-form and brute-force paths cross-validated. *(Becomes the sweep engine for §6.)*
4. **Effort.** Minutes of compute; ~1 polecat session. No Lean, no paper edits — a standalone script + a short result note.

**Decision rule out of Phase-0.** If (a) holds and (b) shows Q in A descending toward 1/3 as the shape lengthens → proceed to §6 sweep on A. If A's Q is structurally pinned far above 1/3 (e.g. floors at 1/2 for symmetry reasons across the reachable shapes) → pivot the sweep to B's asymmetric gadgets and re-probe. Either outcome is a clean, cheap signal.

---

## §6 — Parameter-space sweep strategy (Phase-1+, conditional on Phase-0 GREEN)

Assume A clears Phase-0. The sweep realizes vision-part 3 → 4.

- **Parameters.** 3-row skew shapes: ~5 free integers after normalization; bound each sweep by `n ≤ N`.
- **Why the closed form matters here.** Evaluating Q at one shape is microseconds (rational-function eval), vs. milliseconds–seconds for enumeration. The closed form also permits an **analytic `inf Q` as `n→∞`** along a parameter ray — the question the per-instance DP cannot answer.
- **Search strategies (in escalating order):**
  1. **Exhaustive grid** for `n ≤ ~12–15`: enumerate all 3-row (skew) shapes, evaluate Q via the closed form, tabulate `min Q(n)` vs `n`. Millions of shapes ⇒ seconds–minutes.
  2. **Gradient-free descent** on the integer shape parameters toward small Q: branch-and-bound (prune shape-subtrees whose closed-form Q lower bound exceeds the incumbent), seeded from the grid minima.
  3. **Continuous relaxation via C** (order-polytope volumes vary smoothly): Nelder–Mead / pattern search on a relaxed shape, then round to the nearest integer shape and re-evaluate exactly. Use only to *propose* candidates; all verdicts come from exact computation.
  4. **Asymptotic analysis:** fit/derive `min Q(n)` and extrapolate `lim inf Q`. A limit `> 1/3` is a (family-restricted) sharpness result; a dip `< 1/3` is a **candidate counterexample → mandatory brute-force re-verification + independent reimplementation** before any claim.
- **Compute budget.** Phase-0: minutes. Phase-1 exhaustive `n≤15`: CPU-minutes–hours. Descent/asymptotics: CPU-hours. No GPU, no cluster; a laptop suffices — this program is deliberately *cheap*, in contrast to the multi-month Cheeger/Lean arcs.
- **No silent caps.** Every sweep result logs `N`, the family restriction, and anything dropped (e.g. "skew shapes only, straight shapes deferred"), so a null result reads as "null over *this* explicit region," never as "null everywhere."

---

## §7 — Recommended execution tickets (for pm-onethird to file)

Per the FULL-REFACTOR-scoping precedent (mg-6ab8 §E: sub-tickets recorded as recommendations only, no `mg new` from the scoping polecat), these are **recommendations**, not filed tickets. Each names its vision-part — the drift test.

| # | Recommended ticket | Vision-part | Status |
|---|---|---|---|
| **AP-0** | **Phase-0 viability probe of Family A** (§5): build + cross-validate the `shape→Q` kernel on `n=3,4` sanity + one `n≈7–9` near-chain 3-row skew shape; report Q and distance-to-1/3. | 2 (pipeline correctness) → 3+4 (first parameter point) | **GREEN — immediate next step** |
| AP-1 | **Exhaustive width-3 hook-length sweep** for `n ≤ 15` (§6.1): tabulate `min Q(n)`, identify small-Q shapes. *Gated on AP-0 GREEN.* | 3 | recommended |
| AP-2 | **Branch-and-bound descent + asymptotic `inf Q`** on Family A (§6.2,6.4). *Gated on AP-1.* | 3+4 | recommended |
| AP-3 | **Family B asymmetric-gadget probe** (N-poset / fence ordinal-sum families): convolution kernel + small-tree sweep. Run if AP-0/AP-1 show A floored above 1/3. | 2→3 | recommended (contingent) |
| AP-4 | **Family C order-polytope continuous-relaxation engine** (§6.3): only if the descent in AP-2 needs a smooth relaxation. | 2 (engine) | recommended (contingent) |
| AP-D | **Family D finite-geometry incidence probe** (rank-3, parameter `q`): honors the unit-distance inspiration; lower priority, per-instance computability only. | 1 (inspiration fidelity) | recommended (low priority) |

---

## §8 — Explicit non-goals

This program **does NOT**:

1. **Re-litigate the Cheeger / cut-and-window route.** mg-0c39 STRATEGY-INDICTED it (area-vs-perimeter conflation). This algebraic track is parallel and independent; it neither fixes nor depends on that route.
2. **Promise a counterexample.** The 1/3–2/3 conjecture (and its width-3 case, which the repo is *proving*) is widely believed **true**. The *expected* outcome is a **bounded null result** — `inf Q ≥ 1/3` over each explicit family — which is **valuable**: it produces sharpness data, identifies extremal sub-families, and stress-tests the conjecture on tractable algebraic regions.
3. **Prove the full conjecture, or interact with the Lean proof / paper.** This is an exploratory *search & data* program. It produces scripts, tables, and result notes — **no Lean obligations, no `main.tex` edits, no new project axioms.**
4. **Rely on Monte-Carlo as the computability mechanism.** The gate (§4) rejects simulate-only families. Monte-Carlo appears only as an independent spot-check against the exact computation.
5. **Widen beyond width 3.** Width 3 is the target and the tractable regime; other widths appear only as sanity controls.
6. **Resurrect the additive-combinatorics headliners as poset engines.** Slice-rank/capset/sumset are **inspiration** (the spirit of exact-bounds-via-algebra), explicitly **rejected as instruments** (§4); the program runs on their tractable neighbors (A/B/C/D).

---

## §9 — Verdict

**GREEN — scoping delivered.** The program is coherent and *cheap*: the computability spine (§1) shows width-3 Q is per-instance free and the algebra's real job is closed-form parameter sweeps; the survey (§2) cleanly separates inspiration from instruments; the shortlist (§3) + gate (§4) name **Family A (hook-length / 3-row skew shapes)** as the leading, fully-gate-passing candidate; the Phase-0 probe (§5) is a concrete, minutes-of-compute, two-independent-methods de-risking step flagged **GREEN as the immediate next execution ticket (AP-0)**; the sweep strategy (§6) and non-goals (§8) bound the work.

**Honest caveat carried forward** (per Daniel's cumulative-vacuity-discovery lens): the expected result is a **null** (`inf Q ≥ 1/3`), not a counterexample. The program's value is the *cheap, exact, parameterized* map of how close to 1/3 algebraic width-3 families get — the opposite failure mode from the Cheeger route's expensive non-computable bulk quantities.

---

## Cross-references

- [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md) — the canonical vision (commit 6e28060); §0 here maps to its four parts.
- [`onethird-strategic-look-area-perimeter-conflation.md`](onethird-strategic-look-area-perimeter-conflation.md) (mg-0c39) — the STRATEGY-INDICTED Cheeger verdict this program runs parallel to (non-goal §8.1).
- [`PROOF-STRUCTURE-ONBOARDING.md`](PROOF-STRUCTURE-ONBOARDING.md) — Q(P), the conjecture, the width-3 specialization.
- Brightwell–Winkler (1991), *Counting linear extensions is #P-complete* — the §1 computability fact.
- Frame–Robinson–Thrall (hook-length), Naruse (skew hook-length / excited diagrams), Proctor (d-complete hook-length), Stanley (order polytopes) — the §3/§4 closed-form engines.
- Predecessor scoping discipline: `OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-6ab8) — sub-tickets-as-recommendations precedent (§7).
