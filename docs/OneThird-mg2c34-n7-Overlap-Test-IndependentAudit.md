# INDEPENDENT AUDIT — the n=7 overlap test (mg-2c34), audited by mg-09ea

**Target, derived from the merge commit.** Parent `mg-2c34` merged as `87f0424` in
`one_third_width_three`, adding four files. The document under audit is
`docs/OneThird-mg2c34-n7-Overlap-Test.md`; the instrument is
`scripts/onethird_mg2c34_n7_overlap_test.py` and the data is
`data/onethird-mg2c34-n7-overlap.json`. The fourth file
(`.github/workflows/script-controls.yml`) is a CI wiring change and is audited as part of the
instrument. **The parent ticket's body was read as context only; the object audited is the merged
artifact.** Pre-filed audit per `/Users/daniel/research/onethird_program/STATE.md`, Appendix A.

**Auditor did not author the target and did not reuse its code.** Every number below was rebuilt
from definitions by the route in §1. `STATE.md` was not edited. Verdict routes to pm-onethird.

---

## §0 — Verdict

| | |
|---|---|
| **Arithmetic** | **CONFIRMED — exhaustively.** Every measured figure in the document reproduced from definitions by a disjoint route. Not one number is wrong. |
| **Headline (§0.1, the RED)** | **CONFIRMED.** `c = 0.995552 / 0.996857 / 0.996549`, against a corpus prediction of `c ≈ 0`. |
| **Mechanism refutation (Lemma 3.1, §3)** | **CONFIRMED**, including the non-vacuous witness and `137 / 137`. |
| **Population claim (§5, 956 classes)** | **CONFIRMED twice** — once by re-enumeration with a different canonical form, once with **no enumeration at all** (§2.3). |
| **Empty conditioning regime (§7)** | **CONFIRMED**, with one missing clause (F6). |
| **The instrument** | **PARTIAL.** The controls are real, graded, and can fail — genuinely better than this programme's norm. But **`λ₂^BK` has no control that can fail** (F3), and CONTROL B's gate is one-sided in exactly the way the document's own §2.7 warns about (F4). Two mutations pass the CI gate. |
| **Overall, "claims are sound and correctly labelled"** | **OVERSTATED.** |

**The single finding that matters.** §0 point 4 / §6(a) — *"`c` has no explanatory power for the
transfer at `n = 7`: knowing `c` across its whole observed range constrains `R` to its whole
observed range"* — is **BROKEN, and refuted by the deliverable's own dataset**. Its stated derivation
("reduction from 9+11") reads *`c` spans 2%, `R` spans 20×* as *`c` cannot explain `R`*, and range
width is not explanatory power. Measured: `c` accounts for **25%** of `R`'s variance, and
conditioning on the bottom `c`-decile confines `R` to `[1.07, 5.77]` — a quarter of the span, and
under a third of the population maximum. **Ledger claim 12 as *worded* survives** (it says only that
`c` is not a valid control parameter, which the sign result establishes); what fails is its
derivation and the stronger prose in §0.4 and §6(a) — the two places most likely to be quoted.
Details and the full decile table in §4.1.

**This makes the arc five-for-five, at a fifth location.** Appendix A step 4d records four
consecutive deliverables with sound arithmetic and one over-wide generalisation, at a new place each
time. This one is in **§6 — the section the document introduced to *replace* the refuted picture** —
which is the mg-c8c6 shape exactly. The document's own generalisation self-audit (§8) is real and
careful, and it audited §5 and §6 **for scope in `n`**; it did not audit §6(a)'s *inference*, and it
did not audit §6 **for scope in regime** (F2).

**And step 4c fires three separate times in this one document.** In each case the body states a
hypothesis or qualifier correctly and the summary drops it: §6(a) states more than ledger claim 12
does (§4.1); ledger row 14 drops the *"at least one incomparable pair"* clause that §7's body has
(§4.3); and the proposed `STATE.md` row for the population claim drops the *"both-connected"*
qualifier that §8 insists on (§6). Appendix A predicts this ("the bodies are careful; the summaries
destined for the canonical doc are not") — here it is not an occasional slip but the document's
consistent failure direction, and it points at the artifact that outlives the deliverable.

**What survives untouched, and it is most of the document.** The refutation, the hand mechanism, the
population sweep, the completeness correction, and the empty-regime reduction are all sound. §6(b) —
`corr(c, R) = +0.50`, the **wrong sign** for a control inequality — is not merely confirmed but
**strengthened** by the decile table this audit produces. The load-bearing conclusion, *the overlap
form of standard dominance is already true and already insufficient*, is unaffected: `c ≥ 0.978`
holds across all 956 classes while the transfer still needs a modulus of `19.93`.

---

## §1 — Method: what "independent" means here

`scripts/onethird_mg09ea_independent_audit.py` imports **nothing** from the corpus. It shares only
two inputs with the target, both of which are data rather than derivations: the relation sets of the
named posets (transcribed from the merge commit, then re-verified against the committed mg-8b64 rows)
and the committed mg-8b64 dataset itself.

| quantity | mg-2c34's route | this audit's route |
|---|---|---|
| poset representation | dict of frozensets `less` | up/down **bitmasks** |
| linear extensions | corpus `Poset.linear_extensions` | own iterative DFS — **different index order**, so any result that depends on the ordering breaks |
| BK operator | `W` filled entry-wise, diagonal as row-sum complement | `W = I − step·L_G`, `L_G = D − A` the **graph Laplacian** of the BK swap graph |
| `λ₂^BK` | `eigh(W)`, second largest | smallest **nonzero** eigenvalue of `L_G`; `λ₂ = 1 − step·μ₂` |
| slow eigenvector | column of `eigh(W)` | **shifted inverse iteration** on `L_G` with the constant deflated — no `eigh` in the path |
| `P_U` | SVD of the `n²` indicator matrix, then `QQᵀ` | **least squares** `P_U f = M·lstsq(M,f)` (gelsd, not gesdd); column layout `a·n+x`, the transpose of theirs |
| `dim U` | SVD singular values above tol | eigenvalue count of the **Gram matrix** `MᵀM` |
| `p_xy`, `δ` | `before_prob_dp` (subset DP) | **exact integer counting** over the enumerated extensions, as `Fraction` |
| `λ_std` | transport matrix, Helmert basis | transport matrix from the enumerated extensions; `1^⊥` by **explicit deflation** `S − J/n` |
| population | their deduped list, plus their canonicaliser | **own enumeration** of naturally-labelled posets + **own canonical form** (finer invariant: neighbour degree profiles, not just own degrees) |
| iso-class count | canonicalisation | additionally by **generating function on OEIS counts, no enumeration** (§2.3) |

Two numerical routes are run for every `c` (inverse iteration and the Laplacian eigenbasis) and
agree to `≤ 1e-8`, typically `1e-13`. Run:

```
/usr/bin/python3 scripts/onethird_mg09ea_independent_audit.py          # full, ~7 min
/usr/bin/python3 scripts/onethird_mg09ea_independent_audit.py --quick  # named posets + dataset only
```

It **exits non-zero** on any disagreement with the deliverable's published figures beyond the
6-decimal rounding of the printed tables. It exits `0`. Output:
`data/onethird-mg09ea-independent-audit.json`.

---

## §2 — Reproduction ledger

Every figure asserted in the deliverable, re-derived. `=` means agreement to the deliverable's own
printed precision.

### 2.1 The measurement (§4)

| poset | `\|L\|` | `dim U` | `δ` | `λ₂^BK` | `λ_std` | `c` (inv. iter.) | `c` (eigenbasis) | `c_min` | verdict |
|---|---|---|---|---|---|---|---|---|---|
| `enum-n7-#3` | 360 | 24 | 0.5000 | 0.980923 | 0.785048 | 0.995552 | 0.995552 | 0.995552 | **=** |
| `enum-n7-#20` | 198 | 22 | 0.5000 | 0.981202 | 0.767529 | 0.996857 | 0.996857 | 0.996857 | **=** |
| `enum-n7-#600` | 132 | 20 | 0.5000 | 0.979921 | 0.773911 | 0.996549 | 0.996549 | 0.996549 | **=** |
| `enum-n7-#945` | 21 | 7 | 0.3810 | 0.943488 | 0.943926 | 0.987947 | 0.987947 | 0.987947 | **=** |
| `enum-n7-#809` | 25 | 9 | 0.3600 | 0.969495 | 0.902015 | 0.995256 | 0.995256 | 0.995256 | **=** |

`λ₂` is **simple** at all five and `c_max = c_min` — confirmed. The identity of all five is confirmed
independently of the deliverable's check: `|L|`, `λ_std` and `δ` match the committed mg-8b64 rows,
and (see F3) so does `λ₂^BK`, to `≤ 2.5e-15`.

**The RED is real.** The corpus predicted `c ≈ 0`; the measurement is `c ≈ 0.9966` against a
`dim U/|L|` null of `0.067`–`0.152`. There is no reading of the eigenspace under which it comes out
small.

### 2.2 The population (§5, §6)

Measured on **my own 956 isomorphism classes**, not on their list.

| quantity | deliverable | this audit | verdict |
|---|---|---|---|
| naturally-labelled both-connected `n=7` | 52810 | **52810** | **=** |
| isomorphism classes | 956 | **956** | **=** |
| classes in mg-8b64's dedup / dropped | 946 / 10 | **946 / 10** | **=** |
| `min c` over all classes | 0.978492 | **0.9784924284113155** | **=** |
| `max c` | 0.998529 | **0.9985293783328602** | **=** |
| median `c` | 0.994751 *(over their 946)* | **0.994767** *(over 956)* | consistent — the 10 extra classes shift the median, as they must |
| `λ₂` simple | 99.58% | **952/956 = 99.58%**, max eigenspace dim 2 at both `1e-9` and `1e-6` | **=** |
| posets with `c_max ≠ c_min` | none | **0** | **=** |
| `corr(c, δ)` | 0.055 | **0.0573** *(over 956)* | consistent |
| `min δ` at `n=7` | 0.358974 | **0.358974358974359** | **=** |
| posets with `δ < 1/3` | 0 | **0** | **=** |
| `R = (1−λ_std)/(1−λ₂^BK)`, min / median / max | 0.9923 / 5.9703 / 19.9303 | **0.9922549 / 5.9703091 / 19.9302787** | **=** |
| `corr(c, R)` / `corr(c, log R)` | +0.50 / +0.53 | **+0.4991 / +0.5362** | **=** |
| frozen-pair overlap: min / median | 0.7794 / 0.8728 | **0.7794118 / 0.8727848** | **=** |
| frozen-pair overlap **exactly 1** | 137 | **137** | **=** |
| Lemma 3.1 hypothesis holds at those | 137 of 137 | **137 of 137** | **=** |
| the ten lowest `c` | `0.9785 … 0.9800` | `0.978492, 0.978492, 0.978530, 0.978530, 0.979856 ×4, 0.980039 ×2` | **=** |

*Free consistency signal:* the ten lowest `c` come in **exact pairs**, and each pair is an
**order-dual couple** (verified: `canon(P^op)` is the partner's canonical mask, and none is
self-dual). `c` must be order-dual invariant, and it is — a check the deliverable does not run and
passes.

### 2.3 The 956 count, with no enumeration at all

The deliverable establishes 956 by canonicalising 52810 posets and cross-checking against a brute
minimum over all `7!` relabelings. Both are enumerations. Here is a third route that touches no
poset:

Let `T(x)` be the generating function of unlabeled posets (A000112: `1, 1, 2, 5, 16, 63, 318, 2045`)
and `I(x)` that of the **ordinally indecomposable** ones. Every poset factors uniquely as an ordinal
sum of indecomposables, so `T = 1/(1−I)`, giving `I = 1, 1, 2, 7, 31, 184, **1351**`. Ordinally
indecomposable is exactly **incomparability-connected**. A poset with disconnected comparability
graph is a disjoint union, hence has complete-bipartite incomparability between the parts, hence is
incomparability-**connected** — so the comparability-disconnected posets are a subset of the 1351.
There are `T₇ − C₇ = 2045 − 1650 = 395` of them (A000608 connected posets: `…, 238, 1650`). Therefore

  both-connected at `n = 7` = `1351 − 395` = **956**.

The same identity gives **1, 12, 104** at `n = 4, 5, 6` — which is exactly what
`enumerate_both_connected` returns there. So **`iso_signature` is exact below `n = 7` and first
collides at `n = 7`**: a sharper statement than the deliverable makes, obtained more cheaply, and it
localises the defect rather than just measuring it.

### 2.4 The controls and the committed dataset

- CONTROL A's rows, CONTROL B/C's `0.5546 / 0.2905 / 0.1247`, CONTROL D's means and the
  `0.2288` maximum draw, `CHECK-0 = 0.0`, the family table's `min c = 0.978898` at `crown S3^0`,
  the "10 of 29 vacuous" split and the "10 rows with null ≤ 0.5": all read back from the committed
  JSON and all match the document.
- The committed mg-8b64 dataset: **1091 rows**, `min δ = 0.333333333333` to `0.00e+00` of `1/3`,
  **0** rows below. §7's factual premise is confirmed.
- CONTROL D is genuinely reproducible across processes: the deliberate avoidance of Python's salted
  `hash()` is correct and matters.

---

## §3 — Step 2 of the template, applied to the instrument: could it have failed?

The ticket's second requirement. The deliverable answers it well **for `c`** and not at all for the
other half of §6.

**What is genuinely good, and should be said plainly.** CONTROL A is a *graded* analytic control on
a real `L(P)`, with a closed-form answer at a continuum of angles including `c = 0` — an instrument
that cannot output `0` cannot refute SD-quant, and this one can, at `8.8e-18`. CONTROL C makes
CONTROL B non-vacuous. The suite is wired to a non-zero exit code, mutation-tested, and put in CI.
The `1‖chain_m` vacuity caveat in §3 is exactly the discipline this programme keeps needing. This is
the strongest instrument audit trail in the arc so far.

**I ran my own mutations** against the shared dependency modules — so that *both* the measurement
and mg-4a86's reference instrument see the bug, which is the realistic case for a coding error —
and ran the CI gate (`--no-sweep`) on each.

| mutation | what it breaks | gate |
|---|---|---|
| **M1** BK step `1/(n−1)` instead of `1/(2(n−1))` | every `λ₂^BK`; every `R` in §6 | **NOT CAUGHT (exit 0)** |
| **M2** `U` genuinely shrunk (drop element-0 **and** element-1 blocks) | the subspace `c` is measured against | **NOT CAUGHT (exit 0)** |
| **M3** BK walk swaps *comparable* adjacent pairs | the generator entirely | caught (crash) |
| **M4** slow mode read at `λ₃` | which mode is "the slow mode" | caught (crash) |
| **M5** `λ_std` not symmetrised (`S = T`) | the numerator of `R` | **caught by the identity check** |

### F3 — `λ₂^BK` is uncontrolled, and the check that would cover it is *fetched and discarded*

Under **M1** the three headline `λ₂^BK` values become `0.961846 / 0.962405 / 0.959841` instead of
`0.980923 / 0.981202 / 0.979921`, every `R` roughly halves, §4's table column is wrong and §9's
*"the `λ₂^BK` and `λ_std` columns reproduce the corpus's numbers exactly"* is falsified — **and the
gate exits 0.**

Nothing covers it, and each miss has a reason:

- **CONTROL A never calls `bk_walk_matrix`** — it synthesises its own `W` from a chosen spectrum.
- **CONTROL B/C are eigenvector-only.** A global rate rescaling leaves every eigenvector fixed, so
  `c` on the antichain is unchanged.
- **CHECK-0 shares the code** (§3, F5).
- **The identity check reads the reference and throws it away.** The block sets
  `rec["ref_bk_lambda2"] = ref["bk_lambda2"]` and then builds only `match_num_LE`,
  `match_lambda_std`, `match_delta`; the gate loop tests exactly those three. There is no
  `match_bk_lambda2`. The one committed reference value for the only genuinely **dynamical**
  quantity in the document — the denominator of `R`, which is the whole substance of §6 — is loaded
  into the report and never compared.

**The number is nevertheless correct.** My independent Laplacian route agrees with the committed
mg-8b64 `bk_lambda2` to `≤ 2.5e-15` at all five posets. So this is *missing control*, not *wrong
result* — but under Appendix A's own standard ("a passing result whose check could not fail is
unsupported"), §6's `R` range currently rests on an unverified quantity.

**Repair, one line**, using data already in `rec`:
`match_bk_lambda2 = abs(row["lambda2_BK"] − rec["ref_bk_lambda2"]) < 1e-9`, added to the gate's
conjunction. That converts M1 from silent to fatal.

### F4 — CONTROL B gates on `c_max` only, and computes `c_min` without asserting it

Under **M2** the headline values move to `0.986571 / 0.988475 / 0.995959` and the gate exits 0.
CONTROL B does not fire because on the antichain the shrunk `U` still meets the `λ₂` eigenspace, and
`c_max` is a **maximum over that eigenspace** — the most favourable reading survives a shrink that
the adversarial reading would not.

This is the *same one-sidedness the deliverable identifies in §2.7* as the reason to add `c_min` to
the measurement. It added `c_min` to the measurement and not to the control. `control_B_and_C`
already computes `c_min` and stores it in the report; it simply never asserts on it. Measured:

| antichain | true `U`: `c_max` / `c_min` | shrunk `U`: `c_max` / `c_min` |
|---|---|---|
| `A₄` | 1.000000000 / **1.000000** | 1.000000000 / **0.000000** |
| `A₅` | 1.000000000 / **1.000000** | 1.000000000 / **0.000000** |
| `A₆` | 1.000000000 / **1.000000** | 1.000000000 / **0.000000** |

So the already-computed value separates the two cases perfectly. **Repair, one line:**
`B_PASS_c_is_1` should require `abs(c_min − 1) < 1e-8` as well as `abs(c_max − 1) < 1e-8`.

This also bounds §2.6's mutation row 2: CONTROL B catches **position-block** shrinks (their "even
positions only") and does **not** catch **element-block** shrinks. The row is true; the general
claim it implies — that CONTROL B covers `U` shrinks — is not.

### F5 — CHECK-0 is a tautology, and §11.1 mislabels it

§11.1's second risk bullet reads *"CHECK-0 agrees with an **independently-written** instrument to
`0.0e+00`."* It is not independently written. `measure()` and `sd_quant_constant()` call the **same**
`bk_walk_matrix` and the **same** `projector_U`, on the same inputs, and the eigenspace selection in
`slow_eigenspace` is a literal duplicate of the four lines inside `sd_quant_constant`. Identical
floating-point operations on identical inputs give `0.0e+00` **by construction**. It bounds no
numerical risk, and it is invisible to any error in the shared code — which is every error M1 and M2
represent.

The document says this correctly elsewhere: §2.5 — *"the measurement is mg-4a86's own instrument,
extended, **not a re-implementation that could differ from it**"* — and §2.6 row 2 concedes the
shared-`U` blind spot. **§11.1 contradicts §2.5.** Strike the bullet or restate it as *"CHECK-0
verifies the wrapper, not the instrument."* The other two bullets in §11.1 (CONTROL A's `3.3e-16`,
and the margin argument) do carry the risk bound and are sound.

*Net on the instrument:* the controls that exist are good and the gate does fire on three of five
mutations. Coverage is **asymmetric**: `c` is well controlled and `λ₂^BK` is not controlled at all.
Two one-line additions close both gaps.

---

## §4 — Step 4d: the generalisation audit

Per Appendix A, the object to audit first is the most general statement the document wrote, wherever
it sits — not the headline. Two candidates dominate: §7's claim 14 (the only statement quantified
over *all* posets and *all* `n`) and §6's replacement theory. **§6 is where the defect is.**

### 4.1 — F1 (primary): §0 point 4 / §6(a) is BROKEN as an inference

**As written:**

> §0.4 — *"`c` has no explanatory power for the transfer at `n = 7`: knowing `c` across its whole
> observed range constrains `R` to its whole observed range."*
> §6(a) — *"Conditioning on `c` anywhere in its observed range leaves `R` in essentially its whole
> observed range."*
> Ledger claim 12 — **`PROVEN[c]`**, *"reduction from 9+11"*.

**Claims 9 and 11 are the two range facts** (`c` spans 2%; `R` spans a factor of 20). The step from
those to "`c` cannot explain `R`" is **invalid**: a variable confined to a narrow range can
determine a wide-range variable exactly — the affine map `R = 924(c − 0.9785) + 0.99` takes
`[0.9785, 0.9985]` onto `[0.99, 19.47]` with correlation 1. Range width is not explanatory power,
and no conditional-range table appears anywhere in the document or its JSON.

**Computed, from the deliverable's own population (my sweep, all 956 classes):**

| `c` decile | n | `c` range | `R` min | `R` max | `R` median | share of full `R` span |
|---|---|---|---|---|---|---|
| 1 (lowest `c`) | 96 | 0.978492 – 0.987176 | 1.073 | **5.770** | 2.896 | **0.248** |
| 2 | 95 | 0.987176 – 0.991508 | 0.992 | 8.704 | 3.810 | 0.407 |
| 3 | 96 | 0.991508 – 0.992428 | 1.361 | 9.006 | 4.154 | 0.404 |
| 4 | 95 | 0.992428 – 0.993597 | 3.945 | 12.079 | 6.960 | 0.430 |
| 5 | 96 | 0.993597 – 0.994767 | 2.017 | 15.463 | 7.405 | 0.710 |
| 6 | 95 | 0.994767 – 0.995528 | 1.738 | 16.805 | 6.396 | 0.796 |
| 7 | 96 | 0.995528 – 0.996466 | 2.205 | 18.273 | 9.526 | 0.848 |
| 8 | 95 | 0.996466 – 0.997245 | 2.835 | 16.582 | 9.132 | 0.726 |
| 9 | 95 | 0.997245 – 0.997866 | 4.094 | 13.731 | 7.054 | 0.509 |
| 10 (highest `c`) | 97 | 0.997866 – 0.998529 | 2.245 | **19.930** | 7.986 | 0.934 |

- The bottom decile leaves `R` in **24.8%** of its span, not "essentially its whole range", and caps
  `R` at `5.77` — under a third of the population maximum.
- The bottom **three** deciles all cap `R` below `9.01`.
- Median `R` rises from **2.90** to **7.99**, a factor of `2.8`, essentially monotonically.
- `corr(c, R) = +0.4991` ⟹ **`c` accounts for 25% of `R`'s variance**; mean within-decile variance
  is `7.98` against a total of `11.89`.
- Reading the other way: `R > 15` (14 posets) **forces** `c ≥ 0.994228`.

So `c` carries real, substantial information about `R` — and it is exactly the **wrong**
information. **That is §6(b), and §6(b) is correct.** The decile table is a strictly stronger
statement of it than the single correlation coefficient, because it shows the relation is monotone
and not an artifact of a few outliers.

**Verdict, stated precisely — because the ledger and the prose do not say the same thing.**

- **Ledger claim 12, as worded** (*"`c` does not control the L1b transfer at `n=7`, and
  `corr(c,R)=+0.50` has the wrong sign for a control inequality"`*) — **CONFIRMED.** Under the
  reading "`c` is not a valid control parameter for an *upper bound* on `R`", it is true, and §6(b)
  carries it.
- **The derivation offered for it** (*"reduction from 9+11"*) — **INVALID.** Claims 9 and 11 are the
  two range facts, and they do not entail the conclusion by any route.
- **The §0.4 and §6(a) prose** (*"no explanatory power"*, *"conditioning on `c` anywhere in its
  observed range leaves `R` in essentially its whole observed range"*) — **BROKEN**, and refuted by
  the deliverable's own population. It states something strictly stronger than claim 12 and does so
  in the two places most likely to be quoted.

This is the Appendix A step 4c shape again: *the ledger row is careful, the sentence that survives
is not.*

**Consequence for the document's conclusion: none.** *"The overlap form of standard dominance is
already true and already insufficient"* rests on the coexistence of `c ≥ 0.978` with `R = 19.93`,
not on §6(a). §6(a) should be **replaced by the table above**, which supports the same conclusion
more strongly.

**Why this is the 4d shape.** An incidental property of the sample — that `c` happens to sit in a
narrow band — was read as a law about `c`'s informativeness. Which property of the instance is doing
the work (narrow range), and was it ever hypothesised to imply the conclusion (no)? The document's
own §8 asked this of §5's population claim and §6's *scope in `n`*, and got both right. It did not
ask it of §6(a)'s *inference*.

### 4.2 — F2 (secondary): §6's conclusion is drawn entirely off the class L1b quantifies over

§7 establishes — correctly, and it is one of the document's best findings — that **no poset in the
ensemble satisfies the conditioning hypothesis** `δ < 1/3`, and it criticises the corpus for
inferring a conditional picture *"entirely from a `δ = 0.5` vs `δ ≈ 0.37` contrast and then
labelling it with a regime boundary at `1/3` that neither side is on."*

§6 then closes: *"The missing ingredient in L1b is not standard dominance in the overlap sense."*
But L1b, as the corpus states it, is the **conditional** *all-pairs-frozen ⇒ standard dominance*, and
**every one of the 956 posets §6 measures is outside that hypothesis** (`δ ∈ [0.359, 0.5]`). §6
refutes the *unconditional* implication `high c ⇒ small R`, which L1b does not assert. That is the
same category error §7 diagnoses in the corpus, applied to §6, and unflagged.

The document is not uniformly guilty of this — §7 handles the *`c`* claim correctly (*"the
conclusion `c ≈ 1` already holds without the hypothesis"*, a valid a-fortiori). The gap is specific
to §6's `R` claim, where no a-fortiori is available: `R` being large off-regime says nothing about
`R` in-regime.

Ledger **claim 20 already carries the honest form** (`CONDITIONAL`, *"conditional on `n=7` and on
this population… not a proof that no overlap-based route can work"*). The **prose in §6 and §0.4 is
flat.** This is Appendix A step 4c in miniature — *the body is careful, the sentence that gets
quoted is not* — and it is the sentence that would land in `STATE.md`.

**Free by-product, which the deliverable should want.** §6 never asks whether **`δ`** controls `R`.
I measured it: `corr(δ, R) = +0.096`, `corr(δ, log R) = +0.076`, and the eight lowest-`δ` posets
(`δ ≤ 0.3929`) still span `R ∈ [0.99, 6.96]` with median `3.73`, against `5.88` in the `δ = 0.5`
block. So at `n = 7`, **`δ` does not control `R` either.** This removes the obvious escape from
§6's conclusion (*"but the conditional picture is fine in-regime"*) and points the same way the
document does — while remaining, by §7's own argument, unable to reach `δ < 1/3` at any `n`. It
belongs in §6 as the analysis that closes the off-class objection rather than leaving it open.

### 4.3 — F6: claim 14, the document's most general statement, is missing a clause

Claim 14 (`PROVEN`, "definitional reduction"): *"`δ(P) < 1/3` ⟺ `P` is a counterexample to the
1/3–2/3 conjecture; hence the all-pairs-frozen regime is empty at every `n` unless the conjecture is
false."* This is the only statement in the document quantified over **all posets and all `n`**, so by
4d it is the first thing to press.

- **`⟸` holds.** A counterexample has every incomparable pair outside `[1/3, 2/3]`, so every
  `min(p, 1−p) < 1/3`, so `δ < 1/3`.
- **`⟹` holds for non-chains** by the same equivalence.
- **`⟹` fails for chains.** A chain has no incomparable pairs, so `δ = max ∅`; under any convention
  making `δ < 1/3` (the code leaves it `None`), a chain satisfies the hypothesis and is **not** a
  counterexample — the conjecture is stated for posets that are not total orders.

So the correct statement is *"the all-pairs-frozen regime contains **no non-chain poset** unless the
conjecture is false."* **A vacuity hole, not a wrong conclusion**: chains have `|L(P)| = 1`, no BK
dynamics and no content, and the operative consequence (the regime is untestable by enumeration) is
unaffected and if anything reinforced. But a `PROVEN` biconditional over all posets should be correct
on all posets, and this programme has been bitten by vacuous satisfaction before. **One clause.**

**And the document's own §7 already has that clause** — *"For any poset **with at least one
incomparable pair**, `δ(P) < 1/3` says every incomparable pair has `p_xy ∉ [1/3,2/3]`"*. The
hypothesis is stated correctly in the body and **dropped in ledger row 14**. That is the third
instance in this one document of the same defect — careful body, unqualified summary — after claim 12
(§4.1) and the 956 row (§6). **The pattern Appendix A step 4c names is not an occasional slip here;
it is systematic, and it is systematic in the direction of the artifact that survives.**

Second clause, in the same paragraph: *"Exhibiting one would refute the conjecture this programme
exists to prove (in the width-3 case)."* A `δ < 1/3` witness of width ≥ 4 refutes the **general**
conjecture and leaves the width-3 case untouched. The sentence is right about the general conjecture
and should say so.

---

## §5 — Step 4b: strength check and falsifier quantifier

**The target proposed in §13** is *"Is `R(P)` bounded uniformly in `n`?"*. Run forward: `R ≤ K`
uniformly **is** L1b's transfer, restated. So §13 is not proposing a cheap step below the crux and
mis-pricing it — it is naming the crux, and it says so (*"That, not overlap, is what L1b needs"*).
**No 4b defect.** The document explicitly declines to answer it from an `n = 7`-chosen family and
names the locked-parameter error by name. That is the right call and worth recording as such.

**Falsifier quantifier.** The falsifier of §0.1 is per-poset and evaluated at the three named posets
plus the whole population — no quantifier slippage. §6's falsifier of the control inequality is
`enum-n7-#94` (`c = 0.998001`, `R = 19.9303`), a single witness against a universal implication,
which is the correct quantifier for that job. `argmax R` tracked to larger `n` can only ever
**falsify** boundedness, never establish it; §13 states this. **Clean.**

**Lemma 3.1 forward.** Its hypothesis is a strong structural condition (the pair indicator is a
position threshold on all of `L(P)`), and it is used only to exhibit witnesses against an inference,
where one witness suffices. The vacuity of the `1‖chain_m` illustration (`dim U = |L(P)|`) is flagged
by the document itself and a non-vacuous witness supplied — `enum-n7-#86`, which I re-derived
independently: `|L| = 90`, `dim U = 14` (null `0.156`), Theorem-E frozen pair `(2,6)` at `p = 0.80`,
overlap with `U` exactly `1.000000`, threshold `k = 2`. **CONFIRMED, and the vacuity discipline is
exemplary.**

---

## §6 — Step 4c: the text destined for `STATE.md`, clause by clause

§9 is this document's proposed record change. Audited as an artifact.

| clause | verdict |
|---|---|
| *"Predicted outcome `c ≈ 0`" → **REFUTED**, measured `0.9966 ± 0.0007`* | **CONFIRMED.** Quote verified verbatim at `OneThird-StandardDominance-ComparisonRoute.md:625-630`. |
| *"A genuinely degree-2 slow mode has small overlap with `U`" → **REFUTED** (Lemma 3.1 + 137 witnesses)* | **CONFIRMED.** Quote verified at `:620-621`. The direct refutation is `c ≈ 0.9966` (the slow mode is inside `U`); Lemma 3.1 explains *why the inference was invalid*. Both roles correctly kept apart. |
| *"My sweep does not reach those posets" → **CONFIRMED and now moot*** | **CONFIRMED.** Quote verified. |
| *`Reverse-Cheeger:302-306` "non-standard (degree-2, the lone frozen pair) … wrong irrep" → **REFUTED as stated**, numbers reproduced exactly* | **CONFIRMED.** Quote and table verified at `:290-306`; `1−λ_std ≈ 0.226/0.215/0.232` and `1−λ₂^BK ≈ 0.020/0.019/0.019` reproduce from my figures. |
| *`:290` "standard dominance is not universal" → **CONFIRMED only under the equality reading*** | **CONFIRMED.** Sound and correctly attributed to mg-4a86's audit. |
| *`:310` "L1b ⟺ all-pairs-frozen ⇒ standard dominance" → the off-regime half loses its support* | **PLAUSIBLE.** This reads a slogan's `⟸` direction as if it had been argued formally; the corpus never derived it. The hedge (*"loses its support"*, not *"is refuted"*) is the right strength. Leave as is. |
| *`STATE.md` mg-4a86 row: "already indicated by L1b's off-regime `n=7` refuters" → **the stated indication does not hold*** | **CONFIRMED.** Those refuters have `c ≈ 0.9966`. |
| *"The one uncomputed decisive check … is blocked" → **Discharged*** | **CONFIRMED.** |
| *`roadmap.md:12` "Standard dominance is CONDITIONAL on all-pairs-frozen" → not supported by the overlap form* | **CONFIRMED.** Quote verified verbatim in `/Users/daniel/research/union_closed/docs/roadmap.md`. |
| *`STATE.md` mg-4a86 row: "SD-quant `c ≥ 0.979`, `n ≤ 6`" → **CONFIRMED and extended** to `c ≥ 0.978492` at `n = 7` across all 956 isomorphism classes* | **CONFIRMED but the row drops a qualifier the body insists on.** §8 is explicit that the sweep covers **both-connected** posets only. The proposed row says *"956 isomorphism classes"* without it. **Must read "all 956 `n = 7` *both-connected* isomorphism classes."** This is precisely the 4c failure mode — the body restricts correctly, the row that survives does not. |
| *mg-8b64's `n=7` list "undercounts by 10 … the count is wrong wherever it is quoted"* | **CONFIRMED, and here is the site the row does not name:** `docs/OneThird-L1b-BK-Transport-Transfer-Probe.md:86` — *"Exhaustive both-connected posets **n = 3..7** (3, 9, 12, 104, 946 posets)"*. Name it in the row; *"wherever it is quoted"* is not actionable. |
| *"What is NOT changed": Steps 1–8, the `λ₂^BK ≠ λ_std` refutation, C8/C9, the Cayley-walk catch* | **CONFIRMED.** None depends on `c`. |

**Two required edits before any of §9 is pasted into `STATE.md`:** add *both-connected* to the
956 row, and name `OneThird-L1b-BK-Transport-Transfer-Probe.md:86` in the undercount row. Plus the
§4.1 correction, which changes what §6's row should say.

---

## §7 — Step 5: object / coordinate check

**Clean, and this is one of the deliverable's real strengths.** §1.3 pins the measure (`W` symmetric
doubly stochastic ⟹ `π` uniform ⟹ `L²(π)` is Euclidean up to a global constant ⟹ `P_U` is the
ordinary orthogonal projector), and §1.4 separates `U` (the one-particle span **restricted to
`L(P)`**) from the standard irrep, which coincide only on `S_n`. That distinction is the entire
content of §3, and it is stated correctly: on `S_n` the span `{σ ↦ 1[σ(a)=x]}` is the
matrix-coefficient span of `triv ⊕ std`, dimension `(n−1)²+1`, so `U ⊖ constants` is the standard
isotypic component — **verified, and `dim U = (n−1)²+1` on the antichains confirms it numerically.**

`λ_std` (a functional of the stationary marginal alone) and `λ₂^BK` (a generator gap) are kept
distinct throughout, and §4's closing paragraph correctly identifies the `c ≈ 1` / `λ_std ≪ λ₂^BK`
coexistence as a **quantitative instance** of a mismatch mg-4a86's audit had established
qualitatively — claim 19 is labelled to say exactly that ("adds a magnitude, not the phenomenon").
No conflation found.

One footnote, in the deliverable's favour: §2.4's null `dim U/|L|` is exactly right for CONTROL D's
construction (random subspace, fixed vector) but is not the right null for `U` itself — the `λ₂`
eigenvector is orthogonal to `1` and `1 ∈ U`, so the honest null for a subspace *containing the
constant* is `(dim U − 1)/(|L| − 1)` = `0.145` at `#600`, not `0.152`. The error is **conservative**:
it understates the measured margin. Footnote only.

---

## §8 — Step 6: cross-doc consistency, and Step 7: constraint compliance

**Cross-doc:** every quotation in §1, §3 and §9 was checked against the source file and is verbatim
and in context. The refutations of `ComparisonRoute.md §7.3` and `Reverse-Cheeger:290-310` are sound.
No merged claim is refuted without being named, labelled and located.

**Constraints:** computation was in scope for mg-2c34 (the 2026-07-29 clarification), and **the check
every prior audit in this arc ran — "no computation" — correctly does not apply, and its absence is
not a finding.** What replaces it:

- Everything run is committed (script, data, CI wiring) ✔
- Every table in the document is a projection of the committed JSON ✔ — verified by reading the JSON
  back for §2, §4, §5, §5.2, §6 and the controls
- Every figure is re-derivable from the repo ✔ — with the caveat in F7 below
- A positive control demonstrating the instrument can be wrong ✔ **for `c`**, ✘ for `λ₂^BK` (F3)
- Claims labelled including prose reductions ✔ — 23 rows, and the reductions (claims 7, 12, 14, 15)
  are in it

**F7 (reproducibility, minor).** §12 instructs `python3 scripts/onethird_mg2c34_n7_overlap_test.py`.
On this machine the default `python3` is homebrew 3.14.6 with **no numpy**; only `/usr/bin/python3`
(3.9.6, numpy 1.25.2) can run it. CI installs numpy so the gate is unaffected, but §12 is the
reproduction instruction and it does not run as written on the host the work was done on. Name the
interpreter.

---

## §9 — Claim-by-claim ledger

`=` means re-derived independently and agreeing.

| # | claim | label there | audit |
|---|---|---|---|
| 1 | `c(#3)=0.995552`, `c(#20)=0.996857`, `c(#600)=0.996549` | PROVEN[c] | **CONFIRMED =** (two numeric routes) |
| 2 | `λ₂^BK` simple at all three, `c_min = c_max` | PROVEN[c] | **CONFIRMED =** (dim 1 at `1e-9` and `1e-6`) |
| 3 | exceeds the null by 6.6–15× | PROVEN[c] | **CONFIRMED**; null slightly conservative (§7) |
| 4 | the corpus's `c ≈ 0` is refuted | PROVEN[c] | **CONFIRMED** |
| 5 | the three posets are the ones the corpus names | PROVEN[c] | **CONFIRMED**, and further: `λ₂^BK` also matches the reference to `2.5e-15` — a check the gate omits (F3) |
| 6 | **Lemma 3.1** | PROVEN | **CONFIRMED.** Proof is three correct lines; hypothesis and conclusion both checked computationally at 137 posets |
| 7 | hence "degree-2 ⟹ small overlap" is an invalid inference | PROVEN | **CONFIRMED.** One witness suffices; the witness is non-vacuous |
| 8 | frozen-pair overlap `≥ 0.779`, exactly `1` in 137/946 | PROVEN[c] | **CONFIRMED =** (`0.7794118`; 137) |
| 8b | Lemma 3.1's hypothesis holds at 137/137 | PROVEN[c] | **CONFIRMED =** |
| 8c | `enum-n7-#86` is a non-vacuous witness | PROVEN[c] | **CONFIRMED =** (`|L|=90`, `dim U=14`, pair `(2,6)`, `p=0.80`, `k=2`) |
| 9 | over all 956 classes `c ∈ [0.978492, 0.998529]`, median `0.994751` | PROVEN[c] | **CONFIRMED =** (median `0.994767` over 956 vs their `0.994751` over 946 — both correct for their stated base) |
| 10 | `corr(c, δ) = 0.055` | PROVEN[c] | **CONFIRMED** (`+0.0573` over 956) |
| 11 | `R ∈ [0.9923, 19.9303]` while `c` spans 2% | PROVEN[c] | **CONFIRMED =** to 7 digits |
| 12 | `c` does not control the transfer at `n=7`; `corr(c,R)=+0.50`, wrong sign | PROVEN[c] | **CONFIRMED as worded** (`+0.4991`, and strengthened by the monotone decile table) — **but its stated derivation "reduction from 9+11" is INVALID, and the §0.4 / §6(a) prose states a strictly stronger claim that this population REFUTES.** §4.1 |
| 13 | 0 of 1091 rows have `δ < 1/3`; `min δ = 1/3` exactly | PROVEN[c] | **CONFIRMED =** (`1091` rows; `min δ − 1/3 = 0.00e+00`) |
| 14 | `δ < 1/3` ⟺ counterexample; regime empty at every `n` unless the conjecture is false | PROVEN | **CONFIRMED for non-chains; the ledger row drops the "at least one incomparable pair" hypothesis that §7's body states correctly** (F6). Conclusion unaffected |
| 15 | both the "off-regime" and "in-regime" rows lie outside the hypothesis | PROVEN[c] | **CONFIRMED** |
| 16 | exactly **956** classes; dedup keeps 946, drops 10 | PROVEN[c] | **CONFIRMED three times** — their canonicalisation, mine (finer invariant), and a generating-function argument with no enumeration (§2.3) |
| 16b | the 10 dropped give `c ∈ [0.992696, 0.998412]` | PROVEN[c] | **CONFIRMED** |
| 16c | mg-8b64's count undercounts by 10 | PROVEN[c] | **CONFIRMED**; site located (§6) |
| 17 | the instrument returns `c ∈ {0,…,1}` correctly to `<1e-15` | PROVEN[c] | **CONFIRMED**; this is the control that does the work |
| 18 | `c = 1` on antichains is about `U`, not `dim U` | PROVEN[c] | **CONFIRMED**, but the control is one-sided (F4) |
| 19 | `c ≈ 1` with `λ_std ≪ λ₂^BK` is a quantitative instance of the category mismatch | PROVEN[c] | **CONFIRMED**, correctly labelled as adding a magnitude only |
| 20 | overlap is already true and already insufficient | CONDITIONAL | **CONFIRMED as labelled.** The ledger row is honest; §6/§0.4's prose is not (F2) |
| 21 | `c ≥ 0.979` at `n ≤ 6` extends to `≥ 0.978492` at `n = 7` | PROVEN[c] | **CONFIRMED**, correctly called a pattern not a law |
| 22 | `c ≥ 0.9789` on the family posets to `n = 10` | HEURISTIC | **CONFIRMED** and correctly labelled; the vacuous-row exclusion is right (10 of 29 vacuous, 10 with null ≤ 0.5, `min c = 0.978898`) |
| 23 | do not revert the mg-4a86 dataset | not a claim | **Reasonable and correctly scoped as a recommendation.** Reason 1 is the decisive one and is right; reason 2 is right on the facts (the mg-4a86 script *is* the instrument). Sound; pm-onethird's call |

---

## §10 — Honest net

**Real progress, and a lot of it.** A prediction the corpus called *"the single highest-value
follow-on"* — `c ≈ 0` — is refuted at the opposite end of the range (`c ≈ 0.9966`, against a null of
`0.067`–`0.152`), its mechanism is refuted by
a three-line lemma with 137 exact witnesses, a merged enumeration count is corrected, and the
conditioning hypothesis of the whole conditional picture is shown to be **empty by definition** —
that last is the most durable thing in the document, because it is a reduction rather than a
measurement, and it retires an entire class of future experiments. The instrument is the best-audited
one this arc has produced.

**Relocation, not progress, in one place.** §6 replaces "overlap is the control parameter" with "we
do not know what the control parameter is" — which is honest, and §13 says so. The `R` question it
displaces onto is L1b's transfer restated, so the crux has not moved; the document does not pretend
otherwise.

**Not vacuous anywhere.** Every claim measured is measured on a population with a stated null, the
vacuous rows are excluded by name, and the one illustration that is vacuous is flagged as such by the
author before anyone else could.

**Required before pm-onethird pastes anything into `STATE.md`:**

1. **Strike §6(a) and §0 point 4's "no explanatory power" clause**; replace with the decile table
   (§4.1). §6(b) — the sign — is the finding, and it is stronger than stated.
2. **Add "both-connected"** to the 956 row of §9.
3. **Restore to ledger row 14 the "at least one incomparable pair" clause that §7's body already
   states**, and split the width-3 / general conjecture in the same paragraph.
4. **Flag §6's conclusion as off-class** (F2) — no measured poset satisfies L1b's hypothesis — and
   fold in `corr(δ, R) = +0.096`, which closes the objection in the document's favour.
5. **Name `OneThird-L1b-BK-Transport-Transfer-Probe.md:86`** as the site of the 946 undercount.

**Recommended repairs to the instrument** (one line each, both using values it already computes):

6. Assert `match_bk_lambda2` in the identity gate — `λ₂^BK` currently has no control that can fail
   (F3).
7. Assert `c_min` in CONTROL B alongside `c_max` (F4).
8. Strike or restate §11.1's *"independently-written instrument"* bullet (F5), and name the
   interpreter in §12 (F7).

**Verdict: OVERSTATED.** The arithmetic is right — every figure, checked from definitions. One
generalisation step is broken, in §6, the section written to replace the refuted picture. That is the
fifth consecutive deliverable in this arc with sound arithmetic and an over-wide generalisation, at a
fifth distinct location, and the first one where the document's own 4d self-audit was run, was
genuinely good, and still missed it — because it audited the *scope* of §6's claim and not its
*inference*.

**One process observation for pm-onethird, offered rather than asserted.** All three 4c instances
here share a mechanism: a claim is written correctly where it is derived and then restated
without its hypothesis where it is summarised. A self-audit cannot catch that by re-reading the
derivation, because the derivation is right. What catches it is diffing the summary against the
body clause by clause — which is what step 4c already asks an *external* auditor to do. If it is
worth a template line, the line is: **a deliverable's own §0 and ledger should be audited against
its own body before the deliverable is submitted, not only after.** That is a cheaper fix than
another audit round, and this document — whose body is genuinely careful throughout — is the case
that shows the gap is between the two, not inside either.

---

*Audit instrument: `scripts/onethird_mg09ea_independent_audit.py`; data:
`data/onethird-mg09ea-independent-audit.json`. Mutation results in §3 are reproducible by patching
the shared dependency modules as described there. Auditor: mg-09ea, on `origin/main` at `87f0424`.
`STATE.md` not edited. This audit is the first-line research gate; the verdict routes to pm-onethird,
who reviews it critically as second line and owns the `STATE.md` row.*
