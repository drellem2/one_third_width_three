# OneThird width-3 1/3–2/3 — is the math finished? (audit, mg-5fdd)

**Work item:** mg-5fdd (OneThird-Math-Audit-and-LaTeX).
**Date:** 2026-05-22.
**Question (Daniel reminder 2026-05-22):** *"1/3 — lean has gaps but is
the math finished? Once latex is finished let us try to finish
formalization."*
**Scope:** answer the question — for each of the 5 disclosed Lean
axioms, decide whether it is a *pure formalization gap* (math complete
and correct on paper, only the Lean port missing) or *genuinely
un-done / un-proven math* — then give an overall verdict; and finish
the LaTeX.

---

## 0. Verdict at a glance

**The width-3 1/3–2/3 math is NOT finished.** The gaps are **not**
pure formalization gaps — they are genuine mathematical gaps in the
*paper itself*, several load-bearing and **at least three fatal to the
argument as currently written**. The OneThird result is, at present, a
**proof strategy with substantial genuine gaps**, not a complete proof.
It does not currently prove the width-3 1/3–2/3 conjecture, even
conditionally on Hypothesis A.

| Lean axiom | Shadows (paper) | Verdict |
|---|---|---|
| `brightwell_sharp_centred` | `eq:sharp-centred`, external Brightwell/Kahn–Saks bound | **Pure formalization gap** — math finished |
| `lem_layered_balanced_irreducible_base` | Step 8 G4 deep-irreducible residual | **Genuinely un-done math** — both reduction lemmas flawed here |
| `stepsOneToSevenCascade` | Steps 1–7 cascade | **Genuinely un-done math** — Steps 1–7 are not a complete correct proof (≥2 fatal flaws) |
| `width3_smallN_hasBalancedPair` | `lem:small-n` base case | **Mostly formalization gap** + a disclosed, infeasible, unverified finite-enumeration residual |
| `nonChain_compl_of_no_balancedPair` | `thm:main-step8` perturbation step | **Minor genuine paper gap** — paper's justification is wrong; correct argument exists but is unwritten |

Plus: the headline is conditional on **Hypothesis A**
(`hyp:arith`) — an explicit, undischarged arithmetic assumption (not
one of the 5 axioms, but a standing conditionality of the whole
result).

Of the five axioms, **exactly one** (`brightwell_sharp_centred`) is a
pure formalization gap. The other four shadow genuine mathematical
incompleteness.

---

## 1. Method and confidence calibration

I read `main.tex` and the relevant load-bearing lemmas of
`step1.tex`–`step8.tex` together with their proofs, traced the
quantitative chains of constants, checked cross-file hypotheses, and
cross-referenced `lean/AXIOMS.md`, `docs/PROOF-STRUCTURE-ONBOARDING.md`,
`docs/state-Piece6-Redo-Session1.md` (mg-65de),
`docs/state-Piece6-Axiom-Verify-Session1.md` (mg-44f1). Step 8 I
audited line-by-line myself; Steps 1–7 I audited with a dedicated
skeptical probe and then **independently verified its two highest-stakes
findings** (Step 2, Step 4) against the paper.

Confidence is calibrated below:

* **HIGH — verified directly against the paper text:** the Step 2
  area-vs-perimeter flaw (`prop:per-fiber`); the Step 4 self-admitted
  vacuity (`rem:G3-vacuity`); all Step 8 findings
  (`lem:window-localization`, `eq:window-pert`, `lem:layered-balanced`
  Case C, the `nonChain` one-liner); all per-axiom faithfulness
  cross-checks.
* **MEDIUM-HIGH — probe finding, consistent with verified pattern, not
  re-derived at full depth by me:** the Step 4 route-around
  insufficiency (`lem:many-nonconst` min-scale vs `|R|`-scale); the
  Step 1↔Step 5 circular density dependency; the Step 7 `lem:budget-var`
  density hand-wave.

A recurring **error pattern** unifies the three independently-found
flaws (Step 2; Step 8 `eq:window-pert`; Step 8 `lem:window-localization`):
each conflates an **area / total-scale** quantity with a
**perimeter / local-scale** quantity. That a single systematic blind
spot produces all three raises confidence that the findings are real
(not audit noise) and signals the gaps are not trivially patchable.

---

## 2. Per-axiom verdict

### 2.1 `brightwell_sharp_centred` — PURE FORMALIZATION GAP ✅

**Paper:** `eq:sharp-centred` (`step8.tex:1100`), the centred sharp
bound `|Σ_{L'∈A}(f(L')−f̄)| ≤ 2N/m`, with a complete self-contained
derivation at `step8.tex:1046–1276` (reduction to a covariance on the
product lattice `𝓛(Q−z)×{1,…,m}`, then Ahlswede–Daykin / FKG). It is a
transcription of published external results: Brightwell, *Balanced
pairs in partial orders* (1999), §4 Thm 4.1; Kahn–Saks (1984), Lemma
2.2.

**Verdict.** The math is **finished**. The bound is a published
theorem, and the paper's derivation is a careful, complete transcription
(I read it). The Lean axiom is a faithful integer transcription
(`AXIOMS.md` documents the QA, including a corrected off-by-one). The
only thing missing is the Lean port of a 1999 lemma — a genuine,
clean **pure formalization gap**. This is the only one of the five.

### 2.2 `lem_layered_balanced_irreducible_base` — GENUINELY UN-DONE MATH ❌

**Paper:** Step 8 G4 — `lem:layered-balanced` (`step8.tex:2453`) and its
base case `prop:in-situ-balanced` (`step8.tex:3096`), restricted to the
layer-ordinal-**irreducible**, twin-free regime.

**Finding (verified directly).** The paper's two routes to a balanced
pair for a layered width-3 poset — G4 (`lem:layered-balanced`, shallow)
and G3 (`lem:layered-reduction`, deep) — **both have genuine flaws on
the deep-irreducible case**, which is exactly the case a minimal
counterexample falls into.

1. **`lem:window-localization` (`step8.tex:2654`) is false for `w ≥ 1`.**
   It claims the padded band-window
   `W(i,j) = L_{min(i,j)−w} ∪ ⋯ ∪ L_{max(i,j)+w}` is the middle piece
   `X⁻ ⊔ W ⊔ X⁺` of an ordinal-sum decomposition. For that, every
   `z ∉ W` must be `<_P` (or `>_P`) *every* element of `W`. By axiom
   (L2), `z` in band `k` is forced below band `ℓ` only when `k+w < ℓ`.
   An element `z` in band `k` with `min(i,j)−2w ≤ k < min(i,j)−w` lies
   outside `W` yet is **not** (L2)-forced below the bottom boundary band
   `min(i,j)−w` of `W`. The cut below `W` is not clean. No fixed amount
   of padding repairs this — a layer-ordinal-**irreducible** poset has
   *no* clean cut anywhere, so its only ordinal middle pieces are `∅`
   and `X`. (This confirms the mg-65de finding; I re-derived it.)

2. **Consequently `lem:layered-balanced` Case C1 (`step8.tex:3253`) is
   unsound** — it recurses on a "properly contained window
   `W ⊊ X`" via the broken marginal identity. For an irreducible poset
   the only window is `X` itself; Case C2 then needs `|X| ≤ 3(3w+1)`,
   which **fails** for the deep irreducible posets that genuinely exist:
   `β = {1,…,K}` with `i <_P j ⇔ j−i > 2` is width-3, non-chain,
   layered (band = id, `w = 2`), layer-ordinal-irreducible (every cut
   `k|k+1` is straddled by the incomparable pair `(k,k+1)`), and `K` is
   **unbounded**.

3. **`lem:layered-reduction` (G3) `eq:window-pert` (`step8.tex:2396`)
   is false.** In Step 5 Case (b) the proof asserts
   `|p_{xy}(P) − p_{xy}(A)| ≤ |𝓛(P) △ 𝓛(P^♯)| / |𝓛(P)| = o_K(1)`
   "since the window `W` has bounded size `6w` while `|𝓛(P)|` grows."
   The inequality is valid, but the estimate `o_K(1)` is wrong: the
   extensions that reverse a bounded-window incomparable cross-pair are
   a **constant fraction** of `𝓛(P)` — `|𝓛(P)|/|𝓛(P^♯)|` is a constant
   in `(1, (6w)!]`, independent of `K` (the bounded window has bounded
   internal entropy; the number of *full* extensions reversing a window
   pair scales with `|𝓛(P)| ~ 2^K`, not with `|W|`). So the perturbation
   is `Θ(1)`, not `o_K(1)`; G3 Step 5 Case (b) does not close. (This
   flaw is **newly identified by this audit** — it is not recorded in
   `AXIOMS.md` or the predecessor docs, which discuss only the
   window-localization / G4 side.)

So **both** of the paper's deep-case routes are flawed. A minimal
counterexample is indecomposable (`rem:decomp-reduction`), hence its
layering is layer-ordinal-irreducible, and it is large (deep) — i.e. it
is *exactly* a deep-irreducible layered width-3 poset, and the paper
proves nothing for it.

**Status of the statement.** The *statement* (every deep-irreducible
twin-free layered width-3 poset has a balanced pair) is very likely
**true**: mg-44f1's independent exact-rational search over 1 118 061
posets (including the unbounded family `P_K` to `K = 200`) found zero
counterexamples and a strictly positive safety margin `≥ 1/51`. But
"very likely true, strong numerical evidence" is **not a proof**. There
is no proof on paper and none in Lean. mg-44f1's own verdict:
*"the paper's proof of this region is broken … the most promising route
is the near-twin argument … strongly supported by the search but not
yet proven."*

**Verdict: genuinely un-done math.** The Lean axiom is the honest
shadow of a genuine open problem. **This is the central gap.**

### 2.3 `stepsOneToSevenCascade` — GENUINELY UN-DONE MATH ❌

**Paper:** Steps 1–7 — the BK-expansion / Cheeger cascade
(`step1.tex`–`step7.tex`), the structural engine of the
proof-by-contradiction.

This axiom is *intended* by the project as a pure "Steps 1–7 are a
complete published proof, only the multi-month Lean port is missing"
disclosure (`AXIOMS.md`: *"the paper's Steps 1–7 are a genuine
published proof, but not yet independently Lean-checked"*). **That
framing is wrong.** Steps 1–7 as written are **not** a complete correct
proof. A dedicated skeptical probe found four genuine load-bearing
gaps; I independently verified the two fatal ones.

1. **Step 2 — FATAL (verified directly).** `prop:per-fiber`
   (`step2.tex:1027`, proof line 1086) applies the weak-grid stability
   lemma `lem:weak-grid` (`step2.tex:202`) fiberwise. `lem:weak-grid`'s
   hypothesis is **perimeter-scaled**: `∂_D A ≤ ε·t`, with the stability
   rate `δ(ε) → 0` only as `ε → 0` (the proof gives `δ(ε) = O(ε)`). But
   a "good fiber" in `prop:per-fiber` is defined by an **area-scaled**
   bound `|∂_BK(S∩F)| ≤ η·|F|`, where `η ∈ (0,1)` is a **fixed**
   threshold (not the conductance `κ`, which is the small parameter, and
   not `n`-dependent). The proof writes
   `∂_D A ≤ η|F| ≤ η·t·t = ε·t` and sets `ε := η·t`. With `η` a fixed
   constant and rich fibers having side length `t` as large as `Θ(n)`,
   `ε = η·t` **diverges**, so `δ(η·t)` does not go to 0 — the conclusion
   `|A △ M| ≤ δ(η t)|D|` is the trivial bound `≤ |D|`. The exported
   "`A_{x,y}` is `o(|F|)`-close to a staircase" (`thm:step2`) **does
   not exist**. There is a genuine parameter squeeze with no solution:
   small bad-fiber mass (`∝ Kκ/η`) wants `η` large; small good-fiber
   error (`δ(η t)`) wants `η` small — and `t = Θ(n)` in the rich regime
   makes the two demands incompatible. This is the *same error class* as
   Step 8's `eq:window-pert`: an area/total-scale boundary budget fed
   into a perimeter/local-scale stability inequality.

2. **Step 4 — FATAL (verified directly).** `lem:rect-stable-area`
   ("Stable rectangle incompatibility — Gap G3", `step4.tex:543`) is
   **self-admittedly vacuous**: `rem:G3-vacuity` (`step4.tex:642`)
   states verbatim that its hypotheses `eq:G3-hyp` force `β ≤ 2ε` by the
   triangle inequality while its conclusion is positive only for
   `β > 32ε`, so *"in the regime the conclusion is non-trivial, no `A`
   satisfies the hypotheses."* The `|R|`-scale incompatibility bound
   that `thm:step4` (the expansion engine) needs is therefore never
   actually produced by this lemma. The paper routes around it via
   `lem:many-nonconst` at `min(m,n)`-scale; the probe argues — and it is
   consistent with the same area/perimeter theme — that summed over thin
   blocks this is a factor `t` short of `|R|`-scale, so `prop:G5` Case B
   delivers only an `o(δ)`-proportional boundary bound, not the
   `c(δ−Cε)` claimed in `thm:step4`. [The vacuity is verified; the
   route-around insufficiency is MEDIUM-HIGH confidence.]

3. **Steps 1 & 5 — circular density dependency (probe finding,
   MEDIUM-HIGH).** Step 1's bad-set bound (`thm:interface`(iv),
   `step1.tex:174`) and Step 5's `lem:fiber-mass` (G4, `step5.tex:623`)
   each appear to rely on a positive-`|𝓛(P)|`-fraction fiber-mass fact
   that the other is meant to supply; the probe identifies this as a
   genuine circularity rather than a bookkeeping slip.

4. **Step 7 — `lem:budget-var` (`step7.tex:957`)** asserts an
   `Θ(1)`-density lower bound for `H(L)` near the threshold with an
   "it is easy to see"-style justification; flagged as a soft spot, not
   independently fatal.

Steps 3, 6, 7 are sound *as conditional reductions* but consume the
non-existent Step-2 `o(1)` staircase error and the unproven Step-1/5
density, so they cannot stand on their own.

**Verdict: genuinely un-done math.** `stepsOneToSevenCascade` does not
hide an un-ported-but-complete paper proof; it hides a paper argument
with ≥2 fatal flaws and a circular dependency. The Lean axiom, as
disclosed, **understates** the gap.

### 2.4 `width3_smallN_hasBalancedPair` — MOSTLY FORMALIZATION GAP, with a residual ◑

**Paper:** `lem:small-n` + `rem:small-n` (`step8.tex:809–953`). Three
regimes: width ≤ 2 → Linial 1984 (published); width 3, large `γ`
(`γ ≥ 1/3 − δ_KL`) → Kahn–Linial 1991 `δ* ≥ 0.2764` (published); width
3, small `γ`, `n ≤ n_0` → a finite exhaustive enumeration.

**Finding.** The two large-regime sub-cases are complete published
external mathematics — pure formalization gap. The small-`γ`
small-`n` sub-case is a **fully specified, provably-terminating
decision procedure** (the paper gives it explicitly, with running time
`O(3^{C(n,2)} · n² · n!)`) — *complete in principle* — but it has been
**executed in practice only to `n ≈ 11`**; `n_0(γ,T)` is polynomial in
`1/γ` and `T` and the enumeration to it is computationally **infeasible
by brute force and is not verified**. The paper is honest about this
("effective in principle … not the object of the present structural
argument").

**Verdict: mostly a formalization gap.** The math is "finished modulo a
finite check" — there is no broken proof and no genuinely-new-math
obligation. But there is a real, un-discharged (and brute-force
infeasible) finite-enumeration residual for `11 < n ≤ n_0` in the
small-`γ` regime. Honest status: a formalization gap **plus** a
disclosed finite-check obligation. Materially less severe than 2.2/2.3.

### 2.5 `nonChain_compl_of_no_balancedPair` — MINOR GENUINE PAPER GAP ◑

**Paper:** `thm:main-step8` Case (C), `K < K_0` branch, `step8.tex:766–769`:
*"`P|_{X∖X^exc}` is not a chain (else `P` were, contradicting width 3
with a counterexample)."*

**Finding (verified directly).** The parenthetical justification is
**logically wrong**: deleting `O_T(1)` elements from a non-chain poset
can absolutely yield a chain (a long chain plus one floater, minus the
floater, is a chain). So "`P|_{X∖X^exc}` is not a chain" does **not**
follow from "`P` is not a chain". The conclusion is nonetheless **true**
in the proof-by-contradiction context, by a different argument:
indecomposability gives `≥ n/2` incomparable pairs
(`lem:indec-incompairs`, `step8.tex:164` — already in the paper); over
`O_T(1)` exceptional elements pigeonhole forces one exceptional `z`
incomparable to a long contiguous range of the chain `P|_{X∖X^exc}`;
and a floater incomparable to a long chain-range forms a balanced pair
(`Pr ≈ 1/2`) with the range's midpoint, contradicting the counterexample
hypothesis. This argument is **sound and standard but is not written in
the paper** — the paper has only the wrong one-liner.

**Verdict: a minor but genuine paper gap.** The math is
straightforward; once the correct argument is written it becomes a pure
formalization gap. As the paper stands, it is a small piece of un-done
(mis-stated) mathematics. `AXIOMS.md` already records this honestly
(finding F-Body-2).

---

## 3. Hypothesis A

Independently of the five axioms, the headline `thm:main` /
`thm:main-step8` is **explicitly conditional on Hypothesis A**
(`hyp:arith`, `step8.tex:511`): the arithmetic inequality
`γ² c_5(T) c_6 δ_0(γ) ≥ 8` must hold for some admissible `T`.
The paper states plainly that Hypothesis A *"is not derived from
Steps 1–7, and its verification is external to the structural
argument."* It is plausibly true but **undischarged**: it depends on
the precise values of the Step 5/6 richness constants, which the paper
does not pin tightly enough to verify. It is honestly disclosed (and
threaded as an explicit Lean hypothesis `HypothesisArithmetic`, not an
axiom), but it is a standing conditionality of the entire result.

Note that Hypothesis A presupposes the Step 5/6 constants are
*meaningful* — and §2.3 finds Step 2 (which feeds Step 6) does not
deliver its `o(1)` error. So Hypothesis A is not merely undischarged;
the constants it quantifies over are themselves currently ill-founded.

---

## 4. Overall verdict

**Is the OneThird width-3 1/3–2/3 math finished? No.**

And — the part that matters most for Daniel's question ("lean has gaps
but is the *math* finished?") — **the gaps are not pure formalization
gaps.** They are genuine mathematical gaps in the paper:

* The **structural engine** (Steps 1–7) has **two fatal flaws** (Step 2
  area-vs-perimeter; Step 4 vacuous G3-closure) plus a circular
  Step-1↔5 dependency. The "low conductance ⇒ staircase rigidity ⇒
  expansion" mechanism does not work as written.
* The **endgame** (Step 8 G4) does not cover the deep-irreducible
  layered case — both of its reduction lemmas are flawed there. This is
  genuine open mathematics (very likely true, no proof).
* The **base case** rests on an infeasible, unverified finite
  enumeration.
* A **minor genuine error** in the perturbation step.
* The whole result is conditional on the **undischarged Hypothesis A**.

Of the five disclosed Lean axioms, **one** (`brightwell_sharp_centred`)
is a pure formalization gap. The other four shadow genuine mathematical
incompleteness. The Lean axiomatization, as disclosed, is *honest about
being incomplete* but **understates the severity** for
`stepsOneToSevenCascade` (which is presented as merely un-ported).

**This is consistent with the project's own track record.** The
OneThird arc has recorded ten prior "vacuity discoveries"
(mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13, mg-5fbd,
mg-0bd1, mg-fdc2, mg-c2d7). The findings here are the 11th–13th of the
same kind, now on the **paper-math side** of Steps 2 and 4 (prior
audits of Steps 1–7 — e.g. mg-6ab8 — were *Lean-port-scoping* audits
that tagged steps "rigorous-but-substantial"; they were not genuine
deep math probes). The recurring area-vs-perimeter / total-vs-local
conflation is a systematic authorial blind spot.

**What the paper IS.** It is not nonsense. The Bubley–Karzanov-graph /
Cheeger-expansion framing is a genuine and interesting line of attack;
many components are sound — Step 3's coherence bookkeeping, Step 5's
interval/Dilworth combinatorics, Step 7's cocycle-to-potential
globalization, Step 8's ordinal-sum factorisation, the Brightwell
transcription. It is a **serious proof strategy with serious,
load-bearing gaps**, not a finished proof.

**Direct answer to Daniel.** The math is *not* finished, and the
remaining work is *not* "just formalization." Before any
formalization-finish is worth attempting, the genuine mathematical gaps
must be closed (or the result restated as conditional on them):
the Step 2 area/perimeter mechanism, the Step 4 expansion bound, the
Step 1↔5 circularity, the deep-irreducible Step 8 G4 lemma, and
Hypothesis A. Several of these (Step 2, Step 4, deep-irreducible G4) are
genuine open mathematics, not write-ups. The recommended sequencing
"finish latex → finish formalization" should be revised to "close the
math gaps → then latex → then formalization."

---

## 5. LaTeX disposition (this work item)

Because the audit surfaced genuine, in-places-fatal mathematical gaps,
"finish the LaTeX" cannot mean "produce a complete correct proof" — that
would require solving open problems. It means: bring the LaTeX to a
state that is **internally consistent and honest** — every gap the
audit found is correctly marked, and no claim in the paper is false.
The paper already ships a `\GAP{}` macro and a `gap` theorem
environment for exactly this purpose; this audit puts them to use.

Changes made on `main` under mg-5fdd:

1. **Gap marking.** Genuine gaps marked inline with `\GAP{}` at:
   `lem:window-localization`, `lem:layered-balanced` (Case C),
   `lem:layered-reduction` (`eq:window-pert`), `prop:per-fiber`
   (Step 2), `lem:rect-stable-area` (Step 4), and the `nonChain`
   one-liner.
2. **`lem:window-localization`** restated with the clean-cut hypothesis
   it actually needs (it is true with it), plus a note that an
   irreducible poset has no proper clean window.
3. **Step-8-local gaps section** — `G2`/`G3`/`G4` no longer marked
   "Discharged"; status corrected.
4. **`nonChain` one-liner** replaced with the correct
   indecomposability + floater-balanced-pair argument.
5. **Abstract / introduction / `thm:main` / `thm:main-step8`** —
   corrected to state honestly that the paper presents a proof strategy
   with audit-identified load-bearing gaps; the result is conditional on
   closing them and on Hypothesis A.
6. **Stale Lean-status remarks** (`rem:headline-lean-restatement`,
   `main.tex` §roadmap-residual, `rem:enumeration`, `rem:residual-base`)
   updated to the current 5-axiom architecture and corrected to state
   that the irreducible residual is genuinely *unbounded* (the
   `{1,…,K}, i<j⇔j−i>2` counterexample), not bounded by `3(3w+1)`.

The build (`pdflatex main.tex`) is verified clean after the edits.

---

## 6. Recommendations for the follow-on

The ticket says the formalization-finish is "a separate follow-on,
filed on this ticket's verdict." Given the verdict, that follow-on
should **not** be a formalization push. Recommended instead:

1. **Math first, per genuine gap.** Treat each of these as an open
   mathematical problem, not a write-up: (a) Step 2 — replace the
   area-scaled per-fiber boundary with a mechanism that genuinely
   delivers a perimeter-scaled `o(1)` staircase error, or abandon the
   weak-grid route; (b) Step 4 — produce a genuine `|R|`-scale
   incompatibility bound, or re-derive `thm:step4` from the
   `min(m,n)`-scale lemma honestly; (c) Step 1↔5 — break the circular
   density dependency; (d) Step 8 G4 deep-irreducible — the near-twin
   argument (mg-44f1 §2.3) is the most promising lead.
2. **Hypothesis A** — pin the Step 5/6 constants and discharge it, or
   keep the result explicitly conditional.
3. The two cheap items — `nonChain` (§2.5, write the correct
   argument) and `brightwell` (§2.1, port the 1999 lemma) — are the
   only ones safely classifiable as formalization/write-up work.
4. The stale Lean artifact `lean/PRINT_AXIOMS_OUTPUT.txt` predates the
   FULL-REFACTOR (mg-9add) and lists the old axiom set; it should be
   regenerated. (Out of scope for this LaTeX-focused ticket; flagged.)

**Bottom line for pm-onethird to relay:** the width-3 1/3–2/3 result is
a proof strategy with genuine, partly-fatal mathematical gaps. It is not
finished, and finishing it is a mathematical project, not a
formalization one.
