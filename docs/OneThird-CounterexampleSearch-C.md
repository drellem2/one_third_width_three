# OneThird — Counterexample Search C: coherence-guided perturbation search for low-`δ` **primitive** posets at the 1/3–2/3 boundary

*Work item **mg-0eac**. Computation AUTHORIZED for this ticket. Date 2026-07-20.*

*Work item **mg-0eac**; §§0–8 dated 2026-07-20, **§9 added 2026-07-21 by the resume session** (§9.6).*

*Deliverable scripts: [`scripts/onethird_mg0eac_primitive_delta_search.py`](../scripts/onethird_mg0eac_primitive_delta_search.py) (§§0–8), [`scripts/onethird_mg0eac_width3_gap_search.py`](../scripts/onethird_mg0eac_width3_gap_search.py) (§9). Certificates: [`data/onethird-mg0eac-primitive-delta-search.json`](../data/onethird-mg0eac-primitive-delta-search.json), [`data/onethird-mg0eac-ladder-profile.json`](../data/onethird-mg0eac-ladder-profile.json), [`data/onethird-mg0eac-width3-gap.json`](../data/onethird-mg0eac-width3-gap.json).*

*Read-first: [`OneThird-AP-2-Prong3G-alpha-NonSelfDual-n10-13-Empirical.md`](OneThird-AP-2-Prong3G-alpha-NonSelfDual-n10-13-Empirical.md), [`OneThird-AP-2-Prong3F-beta-SelfDual-n11-13-Empirical.md`](OneThird-AP-2-Prong3F-beta-SelfDual-n11-13-Empirical.md) — the five-engine `Q`-harness reused verbatim here as the `δ` engine (`Q` and `δ` are the same quantity).*

---

## 0. Headline

**OUTCOME (iii) — nothing below `β`. The gap conjecture is corroborated on the primitive arena, by a new (coherence-guided) path, out to `n` well beyond the exhaustively verified range — PLUS one load-bearing correction to the ticket's framing.**

The lowest `δ` found over **primitive** posets with `n ≥ 4`, anywhere in this search, is

> **`δ = 7451/21359 = 0.34884591975279744…` at `n = 25`**, attained by the ladder with broken rungs `L₂₅;₁,₅,₈,₉,₁₂,₁₃,₁₆,₂₀`.

| quantity | exact | decimal (14 dp) | relation |
|:--|:--|:--|:--|
| `1/3` (conjecture floor) | `1/3` | `0.33333333333333` | — |
| **`β`** (Sah/Peczarski) | `(5864893 + 27√57)/16812976` | `0.34884346742241` | **`β` < our min** |
| **this search's minimum** | **`7451/21359`** | **`0.34884591975280`** | — |
| `κ` (Chen) | `(93 − √6697)/32` | `0.34889999217940` | our min **< `κ`** |

The margin above `β` is `7451/21359 − β ≈ 2.45·10⁻⁶` — the search gets within about two parts per million of the conjectured boundary **and does not cross it**.

**No poset with `δ < 1/3` was found. No poset with `δ ∈ (1/3, β)` was found.** Every comparison against `β` in this document is **exact rational-vs-algebraic arithmetic**, not floating point (§1.2) — necessary, because the search operates within `~10⁻⁶` of `β`.

> **§9 (added by the resume session) extends this to the width ≥ 3 arena**, which §§0–8 left as their one uncovered region: exhaustive at width **exactly 3** for `n ≤ 11` (min `6/17` at `n = 10`, a proven minimum) and a bounded width-≥3 beam for `12 ≤ n ≤ 16`. **Nothing below `β` there either**, and nothing close — the width-3 best sits `4.1·10⁻³` above `β` versus the ladder record's `2.45·10⁻⁶`. The headline above is unchanged.

### The correction

The ticket asserts that the only posets attaining `δ = 1/3` are "ordinal sums of singletons and the 3-element one-relation poset `T` — which are decomposable and therefore OUT of the primitive search."

**This is false for `T` itself, and the error matters.** `T = ({a,b,c}, a<b)` is **primitive**: its incomparability graph is the path `a — c — b`, which is connected, so `T` is *not* an ordinal sum. And `δ(T) = 1/3` exactly (verified through all five engines, §3.2).

> ⟹ **`T` is a primitive poset with `δ = 1/3`.** The statement "primitive ⟹ `δ ≥ β`" is therefore **false as stated**. Every threshold claim in this document is scoped to `n ≥ 4`, and this is why.

This is not pedantry about a corner case — it undercuts the ticket's stated *motivation* for moving to the primitive arena, namely that primitivity would exclude every `1/3`-attaining poset and so raise the operative boundary from `1/3` to `β`. It does not. Primitivity excludes the infinite *families* (ordinal sums of `1`s and `T`s) but leaves their generator `T` behind.

**The literature gets this right; the ticket's paraphrase dropped it.** Sah states the hypothesis as *"`P` cannot be formed from `1` and `E` using direct sum"* (Thm 1.4, Conj. 5.1–5.2), where `E = T`. That condition **does** exclude `T` (as a one-term sum). So the correct comparison is:

| condition | excludes `T`? | excludes ordinal sums of large primitive blocks? |
|:--|:--|:--|
| Sah's "not formable from `1` and `E` by direct sum" | **yes** | no |
| **primitive** (= not an ordinal sum), this ticket | **no** | **yes** |

Neither condition contains the other. The right primitive-arena statement is:

> **every primitive poset other than `T` has `δ ≥ β`** — which is what our data supports, for `n ≥ 4`, within the scope of §6.

---

## 1. Conventions, and the two `β` constants

For a finite poset `P` with `e(P)` linear extensions,

```
Pr[x < y] = #{linear extensions placing x before y} / e(P),
δ(P)      = max over INCOMPARABLE pairs (x,y) of min(Pr[x<y], Pr[y<x]).
```

`δ(P)` is undefined (reported `None`) exactly for chains. The 1/3–2/3 conjecture is `δ(P) ≥ 1/3` for every finite non-chain `P`. Peczarski writes `b(P)` for the same quantity; this repo's Prongs 3B–3G write `Q`.

**Primitive** = not an ordinal sum = indecomposable under `⊕`. Criterion used (independently validated, §3.4a):

> `P` with `n ≥ 2` is primitive **iff** its **incomparability graph is connected**.

### 1.1 Reconciling `β` — RESOLVED: the two constants are different numbers

The ticket asks whether Chen's `(93−√6697)/32 ≈ 0.348900` and Peczarski/Sah's `≈ 0.348843` are the same. **They are not.** They are distinct algebraic numbers lying in **different quadratic fields**, hence provably unequal:

| | **Chen `κ`** | **Sah / Peczarski `β`** |
|:--|:--|:--|
| radical form | `(93 − √6697)/32` | `(5864893 + 27√57)/16812976` |
| minimal polynomial | `32x² − 186x + 61` | `33625952x² − 23459572x + 4091717` |
| field | `ℚ(√6697)` | `ℚ(√57)` |
| decimal (20 dp) | `0.34889999217940447361` | `0.34884346742240945893` |

`κ − β ≈ 5.65·10⁻⁵`; they agree only to 4 decimal places, which is why they are easily conflated.

**Which is operative: `β`.** Chen's `κ` is the exact limit of his own period-5 family and is *superseded* — Sah explicitly frames his Theorem 1.5 construction as an improvement over Chen's family and over Peczarski's finite posets. `β` is the smaller, and is the conjectured optimum (Sah Conj. 5.1; Peczarski's independent numerics give `0.348843`, matching `β` to all quoted digits).

**We use `β` as the threshold** — the stronger of the two claims. Our data also independently *demonstrates* the supersession: §5 exhibits primitive posets with `δ < κ` **exactly certified**, which would be impossible if `κ` were the true infimum.

### 1.2 Exact comparison, not floating point

The search operates within `~10⁻⁶` of `β`, so float comparison is not trustworthy. For a rational `q`:

```
q < β = (5864893 + 27√57)/16812976   ⟺   (16812976q − 5864893) < 27√57
                                     ⟺   L ≤ 0,  or  L² < 27²·57 = 41553
q < κ = (93 − √6697)/32              ⟺   (93 − 32q) > 0  and  (93 − 32q)² > 6697
```

Both are pure integer/rational arithmetic (`lt_beta_sah`, `lt_kappa_chen`). Every `β`/`κ` verdict in this document is produced this way.

---

## 2. What is deliberately NOT redone

* **Peczarski, *The Gold Partition Conjecture*, Order 23(1) 89–95 (2006)**: GPC ⟹ 1/3–2/3, and **GPC verified by computer for all posets with `n ≤ 11`** — confirmed. Extended in *The Gold Partition Conjecture for 6-thin posets*, Order 25(2) 91–103 (2008) (787 CPU-hours). This search claims **no new verification** in `n ≤ 11`. Sweeps in that range are used **only** as positive controls and seed harvest.
* **Peczarski, *The Worst Balanced Partially Ordered Sets — Ladders with Broken Rungs*, Experimental Mathematics 28(2) 181–184 (2019)**: already computer-searched the smallest-`δ` poset per size and formulated the gap conjecture. The novelty here is **method** (coherence-guided `e`-aligned perturbation), not range.

---

## 3. The `δ` engine and the positive-control gate

### 3.1 The engine is not new code

`δ` is computed by the **five-engine harness already validated in this repo** (mg-7237, mg-5406), imported verbatim:

| engine | method | role |
|:--|:--|:--|
| **M1** | all-pairs order-ideal placed-set DP, `O(2ⁿ·n)` | primary; every poset |
| **M2** | AP-0 kernel `Q_via_dp` (independent subset DP) | cross-check |
| **M3** | Prong-2 `IndPoset` minimal-element recursion (independent codebase) | cross-check |
| **M4** | brute-force linear-extension enumeration | cross-check when `e ≤ 2·10⁵` |
| **MC** | Family-C Ehrhart order-polynomial (volume engine) | cross-check |

M1 extracts all pairwise before-counts from a single DP pass, as the ticket's step 1 specifies. Monte-Carlo is never a source of truth.

### 3.2 Internal positive controls — ALL PASS

Asserted at the top of every invocation, so a regression halts the search rather than silently producing false negatives.

| control | `n` | `e(P)` | `δ` | engines agreeing | expected | result |
|:--|--:|--:|:--|:--|:--|:--|
| `T` (3-elt one-relation) | 3 | 3 | `1/3` | `M1=M2=M3=M4=MC` | `1/3` | **PASS** |
| antichain `A₃` | 3 | 6 | `1/2` | `M1=M2=M3=M4=MC` | `1/2` | **PASS** |
| antichain `A₄` | 4 | 24 | `1/2` | `M1=M2=M3=M4=MC` | `1/2` | **PASS** |
| antichain `A₅` | 5 | 120 | `1/2` | `M1=M2=M3=M4=MC` | `1/2` | **PASS** |
| ordinal sum `T ⊕ T` | 6 | 9 | `1/3` | `M1=M2=M3=M4=MC` | `1/3`, **decomposable** | **PASS** |

`T ⊕ T` is the ticket's "small ordinal sum reduces" check: `δ = 1/3` and the primitivity test correctly reports **not primitive**.

### 3.3 EXTERNAL positive control — the engine reproduces Peczarski's published values

This is the strongest control in the module, because it checks against an **external published source** rather than against our own other engines. All seven published `(δ, e(P))` pairs — *including the linear-extension counts* — are reproduced **exactly**:

| poset | `e(P)` | `δ` computed | published | result |
|:--|--:|:--|:--|:--|
| `L₆;₁` | 14 | `5/14` | `5/14` | **PASS** |
| `L₉;₁,₂,₃,₄` | 85 | `6/17` | `6/17` | **PASS** |
| `L₁₀;₁,₅` | 106 | `37/106` | `37/106` | **PASS** |
| `L₁₁;₁,₆` | 171 | `20/57` | `20/57` | **PASS** |
| `L₂₀;₁,₅,₈,₁₁,₁₅` | 17 366 | `6059/17366` | `6059/17366` | **PASS** |
| `L₂₁;₁,₅,₈,₉,₁₂,₁₆` | 30 970 | `5402/15485` | `5402/15485` | **PASS** |
| `L₂₅;₁,₅,₈,₉,₁₂,₁₃,₁₆,₂₀` | 256 308 | `7451/21359` | `7451/21359` | **PASS** |

**The ladder family `L_{n;i₁,…,i_k}`** (ground set `{0,…,n−1}` by height; **rails** `j ⋖ j+2` for `0 ≤ j ≤ n−3`; **rungs** `j ⋖ j+3` for `0 ≤ j ≤ n−4` *except* the broken `iⱼ`; then transitive closure) was reconstructed from Peczarski's published Hasse-diagram figures — the paper body is paywalled with no arXiv version. **The reconstruction is validated by the table above, not assumed**: reproducing seven independent `(δ, e)` pairs including exact denominators is a stringent test of the construction and of the engine simultaneously.

### 3.3b Record witnesses re-verified through all five engines

The ticket requires any near-boundary claim to be re-verified by independent linear-extension enumeration. The record-holding large-`n` witnesses were forced through the **full** harness *including* M4 brute-force enumeration:

| poset | `e(P)` | `δ` | engines | matches published | `< β` (exact) | `< κ` (exact) | primitive |
|:--|--:|:--|:--|:--|:--|:--|:--|
| `L₁₇;₁,₅,₈,₁₂` | 3 737 | `1304/3737` | `M1=M2=M3=M4=MC` | yes | **no** | no | yes |
| `L₂₀;₁,₅,₈,₁₁,₁₅` | 17 366 | `6059/17366` | `M1=M2=M3=M4=MC` | yes | **no** | no | yes |
| `L₂₁;₁,₅,₈,₉,₁₂,₁₆` | 30 970 | `5402/15485` | `M1=M2=M3=M4=MC` | yes | **no** | **yes** | yes |

All five engines — including a brute-force walk over all 30 970 linear extensions at `n = 21` — agree exactly, and agree with Peczarski's published values.

### 3.4 Two further controls specific to this ticket

**(a) Primitivity criterion validated by brute force.** Over **all 4 231 labelled posets on `n ≤ 5`**, incomparability-graph connectivity agrees with a brute-force search for a proper ordinal-sum splitting in **every case** (0 disagreements at `n = 2,3,4,5`). The criterion is checked, not assumed.

**(b) All-width enumerator certified against OEIS A000112.**

| `n` | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|:--|--:|--:|--:|--:|--:|--:|--:|--:|
| iso-classes generated | 2 | 5 | 16 | 63 | 318 | 2 045 | 16 999 | 183 231 |
| A000112 | 2 | 5 | 16 | 63 | 318 | 2 045 | 16 999 | 183 231 |

**(c) Width-2 enumerator certified complete against an independent enumeration.** The width-2 sweep generates by Dilworth 2-chain partition plus monotone lacings; compared iso-class-by-iso-class against the independent all-width canonical-augmentation enumeration restricted to width `≤ 2`:

| `n` | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|:--|--:|--:|--:|--:|--:|--:|--:|--:|
| width-≤2 classes (all-width enumerator) | 2 | 4 | 10 | 26 | 75 | 225 | 711 | 2 311 |
| width-≤2 classes (`width2_families`) | 2 | 4 | 10 | 26 | 75 | 225 | 711 | 2 311 |
| **missing / extra** | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 |

**0 missing, 0 extra at every `n ≤ 9`.** This licenses treating the width-2 sweep as a superset of the named `β`-extremal families — Chen's `P(5k,5k)` and Sah's `Tₙ` are both width 2, so both are swept whether or not we implement them by name.

---

## 4. Method

### 4.1 Coherence / the distinguished order `e`

`x ≺ₑ y` iff `Pr[x<y] > 1/2`, read off the same DP that produces `δ`; ties at `Pr = 1/2` are left unoriented. If acyclic, this is the strict part of a partial order refining `P` — the distinguished order of the coherence route. It is **recomputed after every edge addition**, since `e` shifts.

**Observation.** The majority relation was **acyclic on every low-`δ` witness inspected** (`T`, and the `n = 9, 10, 17, 20, 21` argmins), with few or no ties. We never encountered a cyclic majority relation in the low-`δ` region. Reported as an observation on the witnesses inspected — **not** a claim about all posets.

### 4.2 The moves

* **MOVE A — the perturbation step (ticket step 4).** Add one `e`-**aligned** comparability `x < y`: `(x,y)` incomparable with `Pr[x<y] > 1/2`, i.e. the majority of linear extensions *already* places `x` before `y`. Kept only if the result stays a valid transitively-closed poset, **primitive**, and **non-chain**.
* **MOVE B — the size lift.** Adjoin a new element whose strict down-set is any order ideal (new maximal), or dually a new minimal; filtered to primitive non-chains.

### 4.3 Search discipline — a deliberate departure from the ticket

The ticket's step 5 says "prune branches whose `δ` increases". **We did not do that.**

> `δ` is **not monotone** along `e`-aligned edge additions, so a strict-descent prune manufactures **false negatives** — exactly the failure mode the ticket's own deliverable section warns against. We use a **beam** instead: keep the `beam` lowest-`δ` children at each depth (`beam = 400`, `keep = 30`), with no descent requirement.

This converts a *silent* incompleteness into a *stated* one. The beam remains a **bounded** search — see §4.5 for a measured instance of it missing.

### 4.4 A structural obstruction specific to the primitive arena

The standard `δ`-preserving padding move — adjoin a global top (or bottom) — provably preserves `δ` (a global maximum is forced last in every linear extension, so all pairwise balances are unchanged and the new element contributes no incomparable pair). We verified numerically that lifting the `n = 10` witness this way gives an `n = 11` poset with `δ = 37/106` exactly.

**But that lift is an ordinal sum `P ⊕ {top}`, hence not primitive.**

> ⟹ On the primitive arena the padding move is **unavailable**, so `min δ` over primitive posets of size `n` is **not** non-increasing in `n`. The sawtooth in §5.1 (e.g. `n = 10` at `0.349057` then `n = 11` at `0.350877`) is a **real structural feature**, not an enumeration bug.

We flag this because a rising profile reads as a broken search. It is not; we chased it down explicitly.

### 4.5 Search validation — the beam recovers known optima blind, and where it does not

The engine being correct is not enough; the *search* must be shown not to systematically miss. In each test the beam was seeded **only** from size `n−1` and given no knowledge of the size-`n` answer:

| `n` | beam found | independent truth | source of truth | match |
|--:|:--|:--|:--|:--|
| 10 | `37/106` | `37/106` | exhaustive width-2 **and** Peczarski published | **exact** |
| 12 | `97/277` | `97/277` | exhaustive width-2 | **exact** |
| 14 | `254/725` | `254/725` | exhaustive ladder | **exact** |
| **15** | `137/391` ≈ `0.3503836` | `166/475` ≈ `0.3494737` | exhaustive ladder | **MISSED** |
| 16 | `665/1898` | `665/1898` | exhaustive ladder | **exact** |
| 17 | `1304/3737` | `1304/3737` | exhaustive ladder | **exact** |
| 18 | `387/1108` | `387/1108` | exhaustive ladder | **exact** |

**The beam recovers the true optimum at 6 of 7 sizes and demonstrably misses at `n = 15`.** We report the miss rather than quietly dropping it: it is direct, measured evidence that the beam is *not* complete, which is precisely why §6 records which rows are proven minima and which are only search-reached upper bounds. The independent ladder sweep is what caught it — the two search routes are complementary, and neither alone would be trustworthy.

Additionally, the ladder local search at `n = 20, 21` **blindly recovered Peczarski's published optima** `L₂₀;₁,₅,₈,₁₁,₁₅` and `L₂₁;₁,₅,₈,₉,₁₂,₁₆` (§3.3), having been seeded only from smaller-`n` patterns.

---

## 5. Results — the min-`δ` profile over primitive posets

`δ` values are **exact rationals**; `< β` and `< κ` verdicts are **exact** (§1.2). Coverage: `exhaustive-allwidth` / `exhaustive-width2` / `exhaustive-ladder` = **proven minimum over the stated arena**; `beam` / `local-ladder` = **minimum reached by a bounded search**, i.e. an upper bound on the true minimum.

### 5.1 All-width and width-2 profile (small `n`)

| `n` | min `δ` (primitive) | decimal | coverage | note |
|--:|:--|:--|:--|:--|
| 3 | `1/3` | `0.333333` | exhaustive-allwidth | **`T`** — primitive, attains `1/3` (§0) |
| 4 | `2/5` | `0.400000` | exhaustive-allwidth | |
| 5 | `4/11` | `0.363636` | exhaustive-allwidth | width 3, not width 2 |
| 6 | `5/14` | `0.357143` | exhaustive-allwidth | `= L₆;₁` |
| 7 | `14/39` | `0.358974` | exhaustive-allwidth | Saks' `M₇`; **not** a ladder |
| 8 | `16/45` | `0.355556` | exhaustive-allwidth | Peczarski's `A`; **not** a ladder |
| 9 | `6/17` | `0.352941` | exhaustive-allwidth | `= L₉;₁,₂,₃,₄` |
| 10 | `37/106` | `0.349057` | exhaustive-width2 | `= L₁₀;₁,₅` |
| 11 | `20/57` | `0.350877` | exhaustive-width2 | `= L₁₁;₁,₆` |
| 12 | `97/277` | `0.350181` | exhaustive-width2 | `= L₁₂;₁,₇` |
| 13 | `157/448` | `0.350446` | exhaustive-width2 | `= L₁₃;₁,₈` |
| 14 | `254/725` | `0.350345` | exhaustive-width2 | `= L₁₄;₁,₉` (9 694 843 generated) |

**Cross-validation against the literature.** Our independently computed minima at `n = 6, 9, 10, 11` equal Peczarski's published per-size worst-balanced posets exactly, and our `n = 7` (`14/39`, `M₇`) and `n = 8` (`16/45`, `A`) reproduce precisely the sizes he flags as **exceptions** where the optimum is *not* a ladder. Our width-2-restricted sweep independently gives `9/25` at `n = 7` and the ladder sweep gives `17/46` at `n = 8` — both worse than the true optima, confirming the exceptions from our side.

### 5.2 Ladder-family profile (large `n`) — the descent toward `β`

The `β`-extremal families are all width 2, and Peczarski's ladders are the conjectured worst-balanced primitive posets. All entries below are **primitive**. `n ≤ 19` is **exhaustive over all `2ⁿ⁻³` broken-rung subsets**; `n ≥ 20` is 1-/2-flip local search, i.e. an **upper bound only**.

| `n` | min `δ` over ladders | decimal | broken rungs | coverage |
|--:|:--|:--|:--|:--|
| 10 | `37/106` | `0.3490566038` | `{1,5}` | **exhaustive** |
| 11 | `20/57` | `0.3508771930` | `{1,6}` | **exhaustive** |
| 12 | `97/277` | `0.3501805054` | `{1,7}` | **exhaustive** |
| 13 | `157/448` | `0.3504464286` | `{1,8}` | **exhaustive** |
| 14 | `254/725` | `0.3503448276` | `{1,9}` | **exhaustive** |
| 15 | `166/475` | `0.3494736842` | `{1,5,6,10}` | **exhaustive** |
| 16 | `665/1898` | `0.3503688093` | `{1,11}` | **exhaustive** |
| 17 | `1304/3737` | `0.3489430024` | `{1,5,8,12}` | **exhaustive** |
| 18 | `387/1108` | `0.3492779783` | `{1,5,6,9,13}` | **exhaustive** |
| 19 | `458/1311` | `0.3493516400` | `{1,5,6,9,10,14}` | **exhaustive** |
| 20 | `6059/17366` | `0.3489001497` | `{1,5,8,11,15}` | local search — *= Peczarski published* |
| 21 | `5402/15485` | `0.3488537294` | `{1,5,8,9,12,16}` | local search — *= Peczarski published*; **`< κ`** |
| 22 | `1065/3049` | `0.3492948508` | `{1,5,6,9,12,13,17}` | local search |
| 23 | `28148/80675` | `0.3489061047` | `{1,5,8,11,14,18}` | local search |
| 24 | `25091/71912` | `0.3489125598` | `{1,5,8,9,12,15,19}` | local search |
| **25** | **`7451/21359`** | **`0.3488459198`** | `{1,5,8,9,12,13,16,20}` | local search — *= Peczarski published*; **`< κ`**; **RECORD** |
| 26 | `130769/374798` | `0.3489052770` | `{1,5,8,11,14,17,21}` | local search |
| 27 | `116570/334103` | `0.3489043798` | `{1,5,8,11,14,15,18,22}` | local search |

**Reading the table.** The profile is a **sawtooth** (§4.4), not a monotone descent: the good sizes are `n ≡ 1 (mod 4)` and `n ≡ 0,1 (mod 5)`-ish, reflecting the period-4/period-5 broken-rung patterns, while intermediate sizes have no room for a clean pattern. Every value stays **strictly above `β`** in exact arithmetic; from `n = 21` the record values drop **below Chen's `κ`**.

The local search at `n = 20, 21, 25` **blindly reproduced Peczarski's three published large-`n` optima** (§3.3), having been seeded only from smaller-`n` patterns — a further independent check on both the search and the engine. Sizes `26, 27` did **not** improve on `n = 25`; the local search plateaus there, and we stopped at `n = 27` (cost `≈ 100 s`/level and growing). The research trail suggests the family continues descending toward `β` at `n ≈ 37–41`; **we did not reach those sizes and make no claim about them.**

### 5.3 The extremal structure

`L₁₀;₁,₅` (`δ = 37/106`, `e = 106`) in cover form:

```
chain A:  0 < 1 < 2 < 3 < 4
chain B:  5 < 6 < 7 < 8 < 9
rungs:    0 < 6,  1 < 7,  2 < 8,  3 < 9
extra:    6 < 3
```

— two 5-chains laced by one-step rungs plus a back-rung. This representative came out of our **width-2 sweep**, independently of the literature; it is **order-isomorphic to `L₁₀;₁,₅`** (verified: identical order-canonical forms). The coherence-guided search **rediscovered the ladder shape independently**, before we had the literature construction in hand.

The record holder `L₂₅;₁,₅,₈,₉,₁₂,₁₃,₁₆,₂₀` (`δ = 7451/21359`, `e = 256 308`) is the same shape at larger scale: two interleaved rails with the broken-rung gaps `4,3,1,3,1,3,4` — the period-4/period-5 pattern that drives the descent toward `β`.

The extremum is *tight*: 11 incomparable pairs, with the maximum balance `37/106` attained by **two** pairs simultaneously, next values `18/53 = 36/106` (twice) and `16/53` (twice). A near-degenerate cluster, not one loose pair — the signature of a genuine local optimum. Majority relation acyclic, 0 ties.

### 5.4 Sub-`β` and sub-1/3 hits

**None.** The `δ ≤ 1/3` guard (inherited STRICT from roadmap §8.2 — such a candidate *halts* the search and may not be written up without a fresh independent sixth codebase) **never fired** except on the `T` and `T ⊕ T` controls, where `δ = 1/3` is expected.

**Sub-`κ` hits: many, exactly certified.** From `n = 21` onward the ladder optima satisfy `δ < κ_Chen` in exact arithmetic (e.g. `5402/15485 < (93−√6697)/32`). This is our own independent confirmation that **Chen's constant is not the infimum** and is superseded by Sah's `β` — consistent with, and derived independently of, Sah's framing.

---

## 6. Scope — what is covered and what is not

Stated explicitly so "nothing below `β`" is not read as more than it is. **No silent truncation.**

| arena | sizes | status | strength |
|:--|:--|:--|:--|
| all widths, all posets | `n ≤ 9` | **exhaustive** (A000112-certified) | proven minimum |
| width ≤ 2 | `n ≤ 14` | **exhaustive** (completeness-certified) | proven minimum over width-2 |
| ladder family `L_{n;S}` | `n ≤ 19` | **exhaustive over all `2ⁿ⁻³` broken-rung subsets** | proven minimum over ladders |
| ladder family `L_{n;S}` | `20 ≤ n ≤ 27` | **1-/2-flip local search** | upper bound only |
| ladder family `L_{n;S}` | `n ≥ 28` | **NOT COVERED** | — |
| all widths, beam | `14 ≤ n ≤ 18` | **bounded beam** (misses at `n = 15`, §4.5) | upper bound only |
| width ≤ 3 | `n ≤ 11` | **prior work, not this ticket** (mg-7237/mg-5406; min `Q = 6/17`) | inherited |
| all widths | `n = 10, 11` | **not covered here** (2.6·10⁶ / 4.7·10⁷ classes) | inside Peczarski's verified `n ≤ 11` |
| width **exactly 3** | `n ≤ 11` | **exhaustive** (prune-certified, §9.2) — min `6/17` at `n = 10` | proven minimum over width 3 |
| width ≥ 3, constrained beam | `12 ≤ n ≤ 16` | **bounded beam** (misses at `n = 10`, §9.3c) | upper bound only |
| **widths ≥ 3, `n ≥ 17`** | — | **NOT COVERED** | **residual gap** |
| **widths ≥ 4, `n ≥ 12`** | — | **NOT COVERED** except incidentally by the beam | **residual gap** |

**The honest gap.** *(Partly closed by §9 — this paragraph is the original assessment; read it with §9.5.)* The `§§0–8` search does not speak to **width ≥ 3 at `n ≥ 12`** at all. Two reasons not to weight it heavily, both **heuristics, not arguments**: (a) every known `β`-extremal family — Peczarski's ladders, Chen's `P(5k,5k)`, Sah's `Tₙ` — is **width 2**; (b) `δ` trends upward with width (the antichain, maximally wide, has the largest possible `δ = 1/2`), and Olson–Sagan report the smallest known `δ` at width `> 2` is `14/39 ≈ 0.3590`, far above `β`, with computer search to 9 elements finding nothing smaller. But a genuine low-`δ` wide poset at `n ≥ 12` would be missed here.

Note also that Sah's proven lower bound `δ ≥ (−3+5√17)/52 ≈ 0.338760` applies to **width-2** posets not formable from `1` and `E` — it does not by itself close the `(1/3, β)` gap even in width 2, and says nothing about width `≥ 3`.

**Compute walls actually hit.** All-width exhaustive: `n = 9 → 10` (183 231 → 2 567 284 classes). Width-2 exhaustive: Catalan growth `≈ 3.6×` per level; `n = 14` completed (9 694 843 generated, 843 s), `n = 15` was launched and **did not complete**, so it is *not* reported. Ladder exhaustive: `2ⁿ⁻³` subsets, wall at `n = 19` (65 536 subsets, 30 s); local search stopped at `n = 27` (`≈ 100 s`/level and growing). The beam is bounded by choice, not compute.

---

## 7. Classification, and what would move it

* **(i) `δ < 1/3` = counterexample** — **NOT observed.**
* **(ii) `δ ∈ (1/3, β)` = refutes the gap conjecture** — **NOT observed.**
* **(iii) nothing below `β` = corroborates the gap via a new path** — **THIS IS THE OUTCOME**, as the ticket predicted.

The corroboration is new in **method** (coherence-guided `e`-aligned perturbation, cross-checked against a completeness-certified width-2 sweep and an exhaustive ladder sweep) and in **range** for the ladder family, and it comes with the §0 correction.

**Named follow-ups, priority order.**

1. ~~**Width ≥ 3 at `n ≥ 12`**~~ — **partly addressed in §9** (exhaustive at width exactly 3 to `n = 11`, bounded constrained beam to `n = 16`; nothing below `β`). **Residual:** width ≥ 3 at `n ≥ 17`, and width ≥ 4 at `n ≥ 12`. Closing either needs a faster `δ` engine than Python — see §9.4.
2. **Restate the primitive gap conjecture with the `T` exception** (§0). Worth checking how Peczarski phrases it; Sah's phrasing is already correct.
3. **Prove `δ ≥ β` for ladders.** The ladder sweep is exhaustive only to `n = 19`; the descent to `β` at larger `n` is local search. An exact transfer-matrix analysis of the broken-rung recurrence would settle the whole family at once — Chen's Lemma 3.1 (`E(m+10,n+10) = 164E(m+5,n+5) − 27E(m,n)`) and Sah's `(a,b) ↦ (3a+3b, 4a+6b)` show the machinery exists.
4. **Push the width-2 exhaustive sweep to `n ≥ 14`** — a compute problem, not a method problem; the Python enumerator would need replacing.

---

## 8. Reproduction

```bash
# full production run (controls + exhaustive sweeps + beam ladder)
python3 scripts/onethird_mg0eac_primitive_delta_search.py \
    --exhaustive-nmax 9 --width2-nmax 13 --ladder-nmax 18 \
    --beam 400 --keep 30 \
    --json data/onethird-mg0eac-primitive-delta-search.json

# fast self-test (controls + small sweeps, ~1 minute)
python3 scripts/onethird_mg0eac_primitive_delta_search.py --quick

# the width >= 3 gap pass of sec. 9 (~26 minutes; n=11 level dominates)
python3 scripts/onethird_mg0eac_width3_gap_search.py \
    --exh-nmax 11 --beam-nmax 16 --beam 400 --keep 30 \
    --json data/onethird-mg0eac-width3-gap.json

# fast self-test for the gap pass (~1 minute)
python3 scripts/onethird_mg0eac_width3_gap_search.py --quick
```

Pure standard library. Both scripts **assert** every positive control (internal and the external Peczarski table) and **raise** `SubBetaHalt` on any `δ ≤ 1/3` candidate (scoped to `n ≥ 4`, per the `T` exception of §0), so neither a silent engine regression nor an unreviewed counterexample claim can pass through. The §9 script additionally **asserts** its width-prune certification (§9.2) and imports the `δ` engine from the §§0–8 script verbatim — nothing is re-implemented.

---

## 9. Closing pass on the one named gap — width ≥ 3 at `n ≥ 12`

*Added by the mg-0eac **resume session**, 2026-07-21 (the original session's process was lost in a fleet restart; its work was recovered from disk before this section was begun — see §9.6). Script: [`scripts/onethird_mg0eac_width3_gap_search.py`](../scripts/onethird_mg0eac_width3_gap_search.py). Certificate: [`data/onethird-mg0eac-width3-gap.json`](../data/onethird-mg0eac-width3-gap.json).*

§6 reports exactly one genuine gap, and §7 makes it follow-up 1:

> **widths ≥ 3, `n ≥ 12` — NOT COVERED** … "the only place a counterexample could still hide from this search."

This section attacks that region. **It narrows the gap; it does not close it.**

### 9.0 What is and is not claimed

| | |
|:--|:--|
| **Claimed** | an **exhaustive** min-`δ` profile over primitive posets of width **exactly 3** for `n ≤ 11`; a **bounded** width-≥3-constrained coherence beam for `12 ≤ n ≤ 16`; **nothing below `β` in either** |
| **NOT claimed** | any exhaustive statement at width ≥ 3 for `n ≥ 12`; any statement at width ≥ 4 for `n ≥ 12` beyond what the beam happened to visit |

The gap moves from "width ≥ 3, `n ≥ 12`, **nothing at all**" to "width ≥ 3, `n ≥ 12`, covered by a **stated bounded search**". A width-≥3 *exhaustive* sweep at `n ≥ 12` remains out of reach — §9.4.

### 9.1 Method, and why the width floor is load-bearing

**(A) Exhaustive width-≤3 sweep by width-pruned canonical augmentation.** `children_max` adjoins a new **maximal** element, and width is monotone under deletion of a maximal element (an induced subposet of a width-≤`W` poset has width ≤ `W`). Hence every width-≤`W` poset on `n` elements is reachable from a width-≤`W` poset on `n−1` elements, so pruning each level to width ≤ `W` is **complete** — a genuine enumeration, not a heuristic filter.

**(B) A width-≥3-CONSTRAINED coherence beam at `n ≥ 12`,** seeded from (A)'s width-exactly-3 optima at `n = 11`. The floor is the whole point:

> Adding a comparability can only **decrease** width, so an *unconstrained* beam **drains into the width-2 arena** — which §5/§6 already cover exhaustively to `n = 14`. Without the floor the search would re-derive known width-2 results while appearing to probe the gap.

`children_edge_w3` / `children_lift_w3` enforce the floor on both moves. For the same reason we report the **width-exactly-3** minimum, not the width-≤3 minimum: the latter is just the width-2 minimum at every `n` where a width-2 poset wins, and so says nothing about the gap.

### 9.2 Gates — engine and prune both certified

**Gate 1 — the engine.** The five-engine controls are re-run **inside this module**, so it never trusts a `δ` it did not itself verify: `T → 1/3`, `A₃, A₄ → 1/2`, `L₉;₁,₂,₃,₄ → 6/17`, `L₁₀;₁,₅ → 37/106`, all `M1=M2=M3=M4=MC`. **PASS.**

**Gate 2 — the width prune.** A prune that silently dropped posets would convert the whole sweep into false negatives, so it is certified rather than assumed. At `W = 2` the pruned canonical augmentation must reproduce `width2_families` — the **independent** Dilworth-2-chain-lacing enumerator that §3.4c already certified iso-class-by-iso-class against the unrestricted enumeration. Two independent routes, same set:

| `n` | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|:--|--:|--:|--:|--:|--:|--:|--:|
| pruned canonical augmentation (`W = 2`) | 2 | 4 | 10 | 26 | 75 | 225 | 711 |
| independent `width2_families` | 2 | 4 | 10 | 26 | 75 | 225 | 711 |
| **mismatch** | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

**Prune CERTIFIED.** The sweep also inherits the STRICT `δ ≤ 1/3` guard, **scoped to `n ≥ 4`**: `T` at `n = 3` is the known primitive `1/3`-attainer of §0 and is an *expected* hit, not a counterexample event. **The guard never fired at `n ≥ 4`** anywhere in this section — across 3 195 182 iso-classes at `n = 11` alone.

### 9.3 Results

#### 9.3a Exhaustive, width **exactly** 3, `n ≤ 11` — proven minima

Every row is a **proven minimum** over primitive posets of width exactly 3 at that size. `δ` exact; `< β` exact.

| `n` | iso-classes (width ≤ 3) | primitive, width = 3 | min `δ` | decimal | `< 14/39` | `< β` |
|--:|--:|--:|:--|:--|:--|:--|
| 5 | 55 | 18 | `4/11` | `0.363636364` | no | no |
| 6 | 245 | 106 | `15/37` | `0.405405405` | no | no |
| 7 | 1 285 | 681 | **`14/39`** | `0.358974359` | — | no |
| 8 | 7 790 | 4 715 | `19/50` | `0.380000000` | no | no |
| 9 | 53 108 | 35 057 | `50/139` | `0.359712230` | no | no |
| **10** | 397 222 | 277 180 | **`6/17`** | **`0.352941176`** | **yes** | no |
| 11 | 3 195 182 | 2 312 972 | `134/375` | `0.357333333` | **yes** | no |

**Two external cross-checks fall out of this table.**

1. **`n = 7` reproduces `14/39`** — exactly the value Olson–Sagan report as the smallest `δ` known at width > 2. Independent confirmation that the width-exactly-3 restriction computes the right thing.
2. **`n = 10` gives `6/17 ≈ 0.352941`, strictly below `14/39 ≈ 0.358974`** — and *exhaustively*, not search-reached. Olson–Sagan's computer search covered `n ≤ 9`; `n = 10` is past it, so this is a new data point rather than a contradiction. It is nowhere near `β`.

The two record witnesses were re-verified through **six** engines — the five-engine harness *plus a from-scratch brute-force linear-extension enumerator written solely for this check, sharing no code with the harness*:

| witness | `n` | `e(P)` | `δ` | five-engine | sixth (independent brute LE) | width | primitive |
|:--|--:|--:|:--|:--|:--|--:|:--|
| `below = [0,0,1,1,7,11,43,107,111,255]` | 10 | 187 | `6/17` | `M1=M2=M3=M4=MC` | `e = 187`, `δ = 6/17` **agree** | 3 | yes |
| `below = [0,0,1,1,3,7,47,127,111,39,895]` | 11 | 750 | `134/375` | `M1=M2=M3=M4=MC` | `e = 750`, `δ = 134/375` **agree** | 3 | yes |

**The profile is non-monotone** (`n = 10` at `0.35294` → `n = 11` at `0.35733`), which is §4.4's structural obstruction again: the `δ`-preserving padding move is an ordinal sum, hence unavailable on the primitive arena. A rising profile is a real feature here, not a search failure.

#### 9.3b Bounded width-≥3 beam, `12 ≤ n ≤ 16` — upper bounds only

**These are NOT minima.** Each is the lowest `δ` a bounded beam reached; the true width-3 minimum at each size may be smaller.

| `n` | beam min `δ` | decimal | width | evaluated | `< β` (exact) |
|--:|:--|:--|--:|--:|:--|
| 12 | `217/601` | `0.361064892` | 3 | 76 940 | **no** |
| 13 | `634/1763` | `0.359614294` | 3 | 24 645 | **no** |
| 14 | `295/821` | `0.359317905` | 3 | 34 552 | **no** |
| 15 | `2258/6279` | `0.359611403` | 3 | 34 060 | **no** |
| 16 | `2119/5862` | `0.361480723` | 3 | 48 658 | **no** |

Nothing in `12 ≤ n ≤ 16` came within `10⁻²` of `β`, let alone below it. `sub_beta_records` in the certificate is **empty**.

#### 9.3c Validation of the constrained beam — and a measured miss

Same discipline as §4.5: run the beam blind at sizes where §9.3a knows the exhaustive truth, seeded only from smaller `n`.

| `n` | constrained beam found | exhaustive truth (§9.3a) | match |
|--:|:--|:--|:--|
| 9 | `50/139` | `50/139` | **exact** |
| **10** | `47/130` ≈ `0.361538` | **`6/17`** ≈ `0.352941` | **MISSED** |
| 11 | `134/375` | `134/375` | **exact** |

**2 of 3, with a demonstrated miss at `n = 10`.** Reported, not dropped: this is direct evidence that the width-constrained beam is *not* complete, which is exactly why §9.3b rows are labelled upper bounds. Note the `n = 11` row is a genuine blind recovery — the beam was seeded from `n = 8` and reproduced a minimum that cost 1 430 s and 3.2 M iso-classes to establish exhaustively.

### 9.4 The wall, stated

Measured width-≤3 iso-class counts (this machine, 2026-07-21):

| `n` | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|:--|--:|--:|--:|--:|--:|--:|--:|
| width-≤3 iso-classes | 55 | 245 | 1 285 | 7 790 | 53 108 | 397 222 | 3 195 182 |

Growth is ≈ **7.5× per level**, so `n = 12` is ≈ 2.4·10⁷ classes, each needing an `O(2ⁿ·n)` `δ`. The `n = 11` level alone took **1 430 s**; `n = 12` would be ≳ 3 h and `n = 13` ≳ 1 day in Python. **This is why §9.3b is a bounded beam and not a sweep** — a compute wall, not a method wall. Total run: 1 563 s.

### 9.5 Net effect on the headline

**None — the §0 headline is unchanged.** The lowest `δ` anywhere in this document remains `7451/21359` at `n = 25` (§0), from the width-2 ladder family. The width-≥3 arena's best is `6/17 ≈ 0.35294`, which is **`1.8·10⁻²` above the ladder record and `4.1·10⁻³` above `β`** — not competitive. Outcome **(iii)** stands, now on a materially larger arena.

§6's heuristic for not weighting the width-≥3 gap heavily — that `δ` trends upward with width — is **partly corroborated and partly qualified** by §9.3a. Comparing the width-exactly-3 minimum against the all-width minimum of §5.1:

| `n` | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|:--|:--|:--|:--|:--|:--|:--|:--|
| all-width min `δ` | `4/11` | `5/14` | `14/39` | `16/45` | `6/17` | `37/106` | `20/57` |
| width-exactly-3 min `δ` | `4/11` | `15/37` | `14/39` | `19/50` | `50/139` | `6/17` | `134/375` |
| gap | **0** | `+0.0483` | **0** | `+0.0244` | `+0.0068` | `+0.0039` | `+0.0065` |

**Two honest qualifications.** (a) At `n = 5` and `n = 7` the gap is **zero** — the all-width optimum *is* a width-3 poset (§5.1 already flags both: `n = 5` "width 3, not width 2", and `n = 7` is Saks' `M₇`). So "wider ⟹ worse balance" is **not** a strict rule. (b) The gap **shrinks** from `n = 8` to `n = 10` (`0.0244 → 0.0039`) before widening again at `n = 11`; it is not monotone, and we cannot extrapolate it to `n ≥ 12`. What the data *does* support is the weaker and sufficient claim that **no width-3 poset at `n ≤ 11` comes near `β`** — the closest is `6/17`, still `4.1·10⁻³` away, three orders of magnitude worse than the ladder family's `2.45·10⁻⁶`.

### 9.6 Provenance of this section

The original mg-0eac session was lost mid-flight in a fleet restart. Its committed work (`c583212`) and its *uncommitted* newer worktree state were recovered from disk and re-committed before any new work began. **The recovered δ engine was not taken on trust**: the full positive-control gate was re-run in the resume session, including the external Peczarski table — all seven published `(δ, e)` pairs reproduced exactly, up to `L₂₅;₁,₅,₈,₉,₁₂,₁₃,₁₆,₂₀` with `e = 256 308`. §§0–8 are the recovered original; §9 is new.

---

## 10. References

Bibliographic details independently retrieved and verified for this work item, except where noted.

* M. Peczarski, *The Gold Partition Conjecture*, **Order 23(1), 89–95 (2006)**, DOI `10.1007/s11083-006-9033-1`. GPC ⟹ 1/3–2/3; GPC proven for width-2 posets and semiorders; **verified by computer for all posets with `n ≤ 11`**.
* M. Peczarski, *The Gold Partition Conjecture for 6-thin posets*, **Order 25(2), 91–103 (2008)**, DOI `10.1007/s11083-008-9081-9`. 787 CPU-hours.
* M. Peczarski, *The Worst Balanced Partially Ordered Sets — Ladders with Broken Rungs*, **Experimental Mathematics 28(2), 181–184 (2019)**, DOI `10.1080/10586458.2017.1368050`. No arXiv version; **paper body paywalled and not read** — the ladder construction used here is reconstructed from the author's published figures and validated against seven published `(δ, e)` pairs (§3.3). The gap conjecture and `β ≈ 0.348843` are taken from the abstract.
* E. Chen, *A Family of Partially Ordered Sets with Small Balance Constant*, **Electron. J. Combin. 25(4), Paper 4.43 (2018)**, arXiv:1709.05753. `δ(P(5k,5k)) → κ = (93−√6697)/32`; recurrence `E(m+10,n+10) = 164E(m+5,n+5) − 27E(m,n)`.
* A. Sah, *Improving the ⅓–⅔ Conjecture for Width Two Posets*, **Combinatorica 41, 99–126 (2021)**, arXiv:1811.01500. Thm 1.4: `δ ≥ (−3+5√17)/52 ≈ 0.338760` for width-2 posets not formable from `1` and `E`. Thm 1.5: `δ(Tₙ) → β = (5864893 + 27√57)/16812976`. Conj. 5.1–5.4.
* M. Olson, B. Sagan, *On the 1/3–2/3 Conjecture*, **Order 35, 581–596 (2018)**, arXiv:1706.04985. §6: their posets `A, B, C` with `δ = 6/17, 60/171, 37/106` coincide with Peczarski's `L₉;₁,₂,₃,₄`, `L₁₁;₁,₆`, `L₁₀;₁,₅`; smallest known `δ` at width `> 2` is `14/39`, from a computer search covering `n ≤ 9`. **§9.3a reproduces `14/39` exhaustively at `n = 7` and then lowers it to `6/17 ≈ 0.352941` at `n = 10`** — outside their search range, so an extension of their datum, not a contradiction of it.
* J. Kahn, M. Saks, **Order 1(2), 113–126 (1984)** — `δ ≥ 3/11`. G. Brightwell, S. Felsner, W. Trotter, **Order 12(4), 327–349 (1995)** — `δ ≥ (5−√5)/10 ≈ 0.276393`, still the best general bound.
* In-repo prior work: mg-7237 (Prong 3F-β), mg-5406 (Prong 3G-α) — the five-engine `Q` harness reused here.
