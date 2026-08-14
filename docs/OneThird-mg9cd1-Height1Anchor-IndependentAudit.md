# INDEPENDENT AUDIT of `mg-72e4`'s height-1 anchor result (mg-9cd1)

*Target: [`OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md`](OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md)
at `75fb81dcffa4`, plus the four amendments it landed at `2d4abbf`.
Instruments written for this audit, nothing imported from the target:
[`scripts/audit_mg9cd1_height1_independent.py`](../scripts/audit_mg9cd1_height1_independent.py),
[`scripts/audit_mg9cd1_n7_lowdegree.py`](../scripts/audit_mg9cd1_n7_lowdegree.py),
[`scripts/audit_mg9cd1_n7_census.py`](../scripts/audit_mg9cd1_n7_census.py).
Output: `data/onethird-mg9cd1-independent-audit-{A,B,D,E}.json`,
`data/onethird-mg9cd1-n7-lowdegree.json`, `data/onethird-mg9cd1-n7-census.json`.
Fresh context; not the authoring polecat. Routed to `pm-onethird` for second-line review —
**this is not a settled ruling.***

---

## 0. Verdict

> ### The mathematics holds. **Proposition 3 is correct**, the census reproduces exactly, and the crosscut reduction survives an independent re-derivation at 194/194 vertices of `Δ₄`. Seven defects, all of scope, denominator or instrument conservatism rather than of mathematics — and **one of them is a fourth denominator behind a headline figure**, which is the defect class this audit stage exists to catch.

| | |
|---|---|
| **Proposition 3** (`c ≥ n`, all `n ≥ 6`) | **CORRECT.** Re-derived line by line; inequality direction right |
| **48.3% / 30.8% coverage** | **CONFIRMED** independently — 110 082 / 227 892 and 3 590 / 11 642 |
| **Every labelled and iso-class count, `n = 3..7`** | **CONFIRMED** by two different algorithms |
| **Crosscut reduction (`Δ(U(P)) ≃ Γ(P)`)** | **CONFIRMED** at 194/194 vertices of `Δ₄`, both sides my own code |
| **`n ≤ 6` census and margins 1 / 2 / 3** | **CONFIRMED** exactly |
| **"0 violations at `n = 7`"** | **REPLICATED independently — and now 163 of 163, not 162** (§4.1) |
| **The "162 of 163" gap** | **CLOSED, and it was never a computational wall** — an artifact of the cap *test* (D7) |
| **"min margin 4" at `n = 7`** | **NOT ESTABLISHED as published** — a fourth, unstated denominator (D2) |
| **Conjecture C at `n = 7`** | **STRENGTHENED by this audit** — now verified on all 163 classes |

The single worst outcome available to an audit in this lineage is to find a repeat of the
defect the lineage was filed to catch. **D2 is that defect**, in a milder form than the
`0/132` and `mg-55f2` cases: a headline figure whose population is smaller than any denominator
printed next to it. It is reported as such below, not softened.

Against that: the target document is unusually honest elsewhere. §4.2 leads with *"The `n = 7`
margin row needs its caveat stated, not buried"*, §5 ends with *"This is the honest size of the
proven part"*, and §7 and §8 name every open item correctly. The defects are in what a reader
can lift out of §0, not in what §4–§8 say.

---

## 1. Method — independence, and what it cost

Per the constraint: **nothing from the repo was imported to check the repo.** Where a second
*algorithm* existed I used it rather than a second spelling of the same one:

| Quantity | `mg-72e4`'s route | This audit's route |
|---|---|---|
| labelled height-1 counts | enumerate every poset | **closed form** — inclusion–exclusion over isolated vertices |
| iso classes and class sizes | canonical form, min over `S_n` (and an `S_a × S_b` variant) | **union–find orbit counting** under adjacent transpositions |
| rational Betti | mod `1 000 003`, `999 983` | mod `2 147 483 647`, `1 000 000 007` — and mod 2 for §4 |
| upper link at `n = 4` | its own direct computation | my own direct computation, my own `Γ` |

**Pre-registration: not done, and it should be recorded that it was not.** Several audits in
this corpus (`mg-a266`, `mg-a84b`, `mg-e12a`, `mg-77e6`) commit a predictions document before any
audit code exists. This one did not. The dispatch pointed at `onethird_program/STATE.md` →
*"Appendix A — Audit-stage process"* for the reusable brief; **that file does not exist in this
repository, on `main` or anywhere in its history** (`git log --all -- onethird_program/STATE.md`
is empty). The brief in the dispatch body was followed instead.

---

## 2. START HERE — the three denominators, and a fourth

The dispatch named three populations behind one *"0 violations at `n = 7`"*. All three are real,
and there is a fourth that the dispatch did not know about.

| # | Denominator | What it scopes | Stated in the document? |
|---|---|---|---|
| 1 | **162 of 163** iso classes | the violation census | §7 pt 3 ✅, §4.1 table column ✅, **§0 verdict ❌ — says 163** |
| 2 | **227 850 of 227 892** vertices | the same census | ✅ everywhere it appears |
| 3 | **146 of 163** classes | *"min margin 10"* | ✅ §4.2, explicitly and prominently |
| 4 | **148 of 163** classes (225 554 of 227 892 vertices) | ***"min margin 4"*** — the §0 headline | ❌ **nowhere** |

*(Denominators 1 and 2 are now **complete** — see §4.1. That does not retire D1: the verdict
box asserted them complete before anything had measured them.)*

### D1 — the one place the headline is quotable unscoped is the verdict box

§0, line 19, the most quotable sentence in the document:

> *"the measurement now runs through `n = 7` — **163 iso classes** and 227 850 of the 227 892
> labelled height-1 vertices there, **0 violations**."*

It pairs the **complete** class count with the **scoped** vertex count. The document's own
figure is *162 of 163* (§7 pt 3). A reader who quotes the verdict box carries away a 0-violation
claim over a class that was never measured — and the vertex figure sitting beside it makes the
sentence look already-scoped, which is worse than an unscoped figure standing alone.

**As it turns out the sentence is now substantively TRUE** — §4.1 below measures the missing
class and finds no violation, so 163 of 163 is right. **That does not make it a non-defect.**
When it was written, the instrument had measured 162; the verdict box asserted 163. A figure
that is unsupported when published and vindicated later was still unsupported when published,
and the vindication came from an audit and a second polecat, not from the run behind the claim.

**Repair (superseded — belongs to `mg-bcd7`, not to this audit):** with the class now measured,
§0 and §7 pt 3 should both read *163 of 163* / *227 892 of 227 892*, and §4.1's "over cap"
column should read 0. `pbcd7` is landing exactly this; I have confirmed by mail that I am not
touching those lines.

### D2 — the fourth denominator: *"min margin 4"* stands on 148 of 163 classes

§0's table row reads `| 7 | **4** (see §4.2) |` and §0's prose asserts the margin misses *"by four
at `n = 7`"*. §4.2 resolves this into *"**10 measured / 4 including the star**"* and states the
146 denominator for the 10. What neither says is what happens to **the other sixteen classes**.

The full homotopy type of `Γ(P)` was computed only where `Γ(P)` has ≤ 20 vertices — 146 of 163.
§4.2 says *"the 17 excluded include the star `K_{6,1}`"* and then supplies the star's margin from
F17+F18. Reading the instrument's own rows, the 17 excluded are:

- **2 stars** — `K_{6,1}` and `K_{1,6}` (`c = 6`, 30 atoms, 7 labelled vertices each). Margin 4,
  by inference.
- **15 further classes**, `c ∈ {1,2,3,4,5,6,10}`, **2 338 labelled vertices**, for which the
  document contains **no margin information of any kind** — not a value, not a bound, not a
  mention. Their needed degree `β̃_d` was measured (that is the census); every other degree was
  not.

So `min margin = 4` at `n = 7` is a minimum over 148 classes presented as a minimum over the
population. And it is not a hypothetical worry: of those 15, ten have `d ≥ 0`, so homology
sitting anywhere below `d` would make the margin **negative** — the *"one-degree near-miss"*
reading the whole document exists to refute could have been alive at `n = 7` inside the very
classes the margin measurement skipped.

**This audit measured them.** See §4.3 — the claim survives on 12 of the 15, and 3 remain open.

---

## 3. The adversarial pass — the flashiest claim first

### 3.1 Proposition 3 (§5): CORRECT, and the inequality points the right way

Re-derived without the label. The chain is:

1. `Prop 1` gives `H̃_{n−2}(lk P) ≅ H̃_{n−c−1}(Δ(U(P)))`. **Verified independently at all 86
   height-1 vertices of `Δ₄`: 86/86.** Its imported ingredient, `mg-52c4` Theorem A (A2)
   — `Δ(L̄(P)) ≃_Q S^{c−2}` — was *not* taken on trust either: **86/86 are rational
   `(c−2)`-spheres** by my own computation.
2. `c ≥ n ⟹ n − c − 1 ≤ −1`. Degrees `≤ −2` vanish for free; the only live case is `c = n`,
   where the claim is `H̃_{−1} = 0`, i.e. `U(P) ≠ ∅`. Correct, with the augmented-complex
   convention the instrument actually uses.
3. The counting step. Available slots `|Comp(t) ∖ Cov(t)| = C(n,2) − (n−1) = (n−1)(n−2)/2`;
   a height-1 poset has `|P| ≤ ⌊n²/4⌋` (Mirsky ⟹ bipartite ⟹ Mantel). A `v` exists iff
   `(n−1)(n−2)/2 > ⌊n²/4⌋` — **the pool must exceed what `P` can occupy, and the document's
   inequality points that way.** Tabulated:

   | `n` | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
   |---|---|---|---|---|---|---|---|---|
   | available `(n−1)(n−2)/2` | 1 | 3 | **6** | **10** | 15 | 21 | 28 | 36 |
   | max `\|P\|` `⌊n²/4⌋` | 2 | 4 | **6** | **9** | 12 | 16 | 20 | 25 |
   | strict? | ✗ | ✗ | ✗ (equality) | ✓ | ✓ | ✓ | ✓ | ✓ |

   Strict **exactly** from `n = 6`, with `n = 5` the equality case — precisely what §5's last
   paragraph says. **No lower-vs-upper conflation.** The `Q ≠ t` step (join-irreducibility of
   cover relations, `tc(P) = P`) is also sound.

**The 48.3% is right, and re-derived by closed form rather than by enumeration:** height-1
posets on `[7]` with `c ≥ 7` number **110 082** of **227 892** = 48.30%. At `n = 6`, `c ≥ 6`
gives **3 590** of **11 642** = 30.84%. The full by-`c` split reproduces the target's table
row for row:

    n=7 by c:  1:42  2:630  3:4480  4:17220  5:39144  6:56294
               7:53760  8:35070  9:15680  10:4662  11:840  12:70

**One observation, not a defect.** For `c ≥ 8` the instrument sets `β̃_d = 0` with no
computation (`d ≤ −2`), and for `c = 7` it checks only that `Γ(P)` is non-empty — which *is*
Proposition 3's content. So of the 227 850 vertices §7 pt 3 calls **measured** at `n = 7`,
110 082 (48.3%) are the **proven** slice re-counted, and §7 pt 1 and §7 pt 3 are not independent
evidence about the same vertices. Both statements are true; a reader adding them is double
counting.

### 3.2 The crosscut reduction (§3) and CONTROL H2: H2 genuinely discriminates

H2 is load-bearing, so I asked the specific question in the brief — does it compare two runs of
the same path? **No.** In `scripts/compat_geom_mg72e4_height1_anchor.py` the two sides are
structurally different objects: `betti_vector(upper_link_poset(...))` builds the order complex of
the *whole* upper set, `gamma_faces(atoms_of_upper(...))` builds the crosscut complex on atoms.
They share `tc`, the poset universe, and the homology engine — a genuine common mode — but the
homology engine is independently pinned by H1 against `∂Δ^k`, the `Z₇` torus and the empty
complex, and the poset machinery is pinned by H3 against `mg-e08a`'s published figures.

**And I re-ran H2 from scratch:** my own `PPF₄`, my own atoms, my own `Γ`, my own order complex,
my own Betti routine at different primes.

> **`crosscut == direct` on 194/194 vertices of `Δ₄`** — every vertex, not only the height-1 ones.

The sizes claim checks out too: the largest `Γ(P)` over height-1 classes has **6 / 12 / 20**
vertices at `n = 4 / 5 / 6`, and `#atoms ≤ n(n−1) − 2c` holds with equality at every large-`c`
class I looked at.

### 3.3 `Q`-acyclicity vs contractibility: the direction that matters is right; §1 is outside the caveat

The important half is **correct and explicit**. §3 states that the crosscut theorem yields a
genuine homotopy equivalence `≃` and that `Q` enters only when the document then *measures*
`Γ(P)`; §7's trap note repeats it. There is **no** upgrade of `Q`-acyclic to contractible in the
mathematics, and no conflation of the two directions.

**D6 (minor).** Both caveats are scoped to sections that exclude §1: §3 says *"every 'contractible'
verdict in **the tables below**"*, §7 says *"every `Γ(P)` verdict **in §4**"*. But §1 uses the
word bare four times, and §1 is *above* §3:

- line 87 `38 of 194 links non-contractible at n = 4`
- line 89 `108/108 height-≥2 links contractible at n = 4`
- line 90 `all 12 links at n = 3 non-contractible`
- line 103 (N2) `At the 108 height-≥2 vertices of Δ₄ the link is contractible`

Each is a two-prime rational Betti verdict, i.e. `Q`-acyclicity. Three of them sit in the H3
table where the phrasing is inherited from `mg-e08a` — but the *reproduced* column is this
instrument's own verdict. **Repair:** widen §3's caveat from *"the tables below"* to the whole
document.

### 3.4 The `n = 4` artifact claim, and inferred-vs-measured: **the inference is now MEASURED, and it holds**

The `n = 7` margin 4 for the star was *inferred* from `U(K_{n−1,1}) ≅ PPF_{n−1} ≃_Q S^{n−3}`
(F17+F18), not measured — the dispatch flagged this as the distinction the margin claim rests on.

Two independent checks:

**(a) The inference rule is right where it can be measured.** At `n = 5` and `n = 6` I computed
full homotopy types myself. The class attaining the minimum margin is the star in both cases —
`K_{4,1}`/`K_{1,4}` at `n = 5` (margin 2) and `K_{5,1}`/`K_{1,5}` at `n = 6` (margin 3) — exactly
`n − 3`, exactly as F17+F18 predicts.

**(b) At `n = 7` the star is no longer an inference.** I computed `β̃_k(Γ(K_{6,1}))` for
`k = −1..4` over `Z/2`:

    K_{6,1}  (c=6, 30 atoms):   betti_2(-1..4) = [0, 0, 0, 0, 0, 1]
    K_{1,6}  (c=6, 30 atoms):   betti_2(-1..4) = [0, 0, 0, 0, 0, 1]

Nothing below degree 4, a class in degree 4 = `n − 3`. Since `β̃_Q ≤ β̃_2` for an integer
matrix, the vanishing below degree 4 is **rational** vanishing, so the star's margin is `≥ 4`
by measurement and `= 4` on F17+F18's value for the top class. **The document's inferred figure
is corroborated by direct computation.** The `n−3` growth pattern 1 / 2 / 3 / 4 survives.

*(One direction does not close: `β̃_2 = 1` bounds `β̃_Q ≤ 1` but cannot exclude 2-torsion, so the
star's margin could be `> 4` rather than `= 4`. That would only make the document's figure
conservative.)*

### 3.5 NEGATIVE CONTROL N1: real, but only at `n = 4` — and it is the headline finding restated

The document: *"it is **refuted on 3 of the 8 classes at `n = 4`**. So the instrument is
discriminating at the degree next to the one under test."* Reading the instrument:

| | value |
|---|---|
| instances the instrument actually ran | **144** (all `n = 4..7`) |
| refuted | **3** |
| where | **all 3 at `n = 4`** |
| testable classes at `n = 4` | **7**, not 8 — the `c = 4` class has `d = −1`, so the swapped degree is never computed |
| instances at `n = 5, 6, 7` | 16 + 36 + 85 = **137**, refuted on **0** |

Three things follow. (i) *"3 of the 8"* is not the instrument's denominator even locally — 7 of
the 8 classes are testable. (ii) N1 **is** a real positive control: the instrument demonstrably
reports non-zero at the degree adjacent to the one under test, which N3 does not establish (N3
uses degree `n−1` of a *link*, not the swapped degree of `Γ`). (iii) But it is a control **at
`n = 4` only** — 0 of 137 instances at `n = 5,6,7` — and the 3 refuting classes are exactly the
three `n = 4` classes with `β̃₁ ≠ 0`, i.e. **the same three data points §4.2 reports as the
`n = 4` artifact**. So N1 is not independent evidence; it is the headline finding wearing a
control's label. **Repair:** state it as *"3 of the 7 testable classes at `n = 4`, and 0 of the
137 instances at `n = 5,6,7`"*, and say that the three are the `n = 4` near-miss classes
themselves.

### 3.6 Scope (§6/§7): correctly labelled

Nothing at `n ≥ 8` is measured (§7 pt 5, §8 ✅). Conjecture C is not proven (§6, §7 pt 5 ✅).
`c ≤ 2` is uncovered even if C held (§6 ✅, §7 pt 5 ✅). I found **no section that quietly assumes
any of the three** — §0 pt 4 and §6 both frame the remaining work as a connectivity statement to
be proven, not as proven. The only scope failure is D2, which is about the *margin's* population,
not about C.

### 3.7 §4.3: the characterisation is labelled descriptive where a reader meets it

The dispatch asked whether the "which `P` carry homology" characterisation is flagged as
descriptive at the point of use rather than only in a caveats section. **It is** — §4.3's own
closing paragraph says the `n = 4` non-bipartite class (`c = 3`, class size 24, `K_{2,2}` minus an
edge) means *"the family is not exactly 'the complete bipartite ones' and this document does not
claim it is"*. I reproduced that class and its `β̃₁ = 1`, and `K_{2,2}`'s degenerate
`β̃₀ = 3` at `n = 4`. The `U(K_{a,b}) ≅ (L_a × L_b) ∖ {(∅,∅)} ∖ {(total,total)}` derivation is
correct: cross-block relations can only be added in the cycle-creating direction.

---

## 4. What this audit adds

### 4.1 The `n = 7` census, replicated — and the "162 of 163" gap is not a wall

I recomputed the needed degree `β̃_{n−c−1}(Γ(P))` for **every one of the 163 classes** with my
own atoms, my own `Γ`, my own homology
([`audit_mg9cd1_n7_census.py`](../scripts/audit_mg9cd1_n7_census.py)), over `Z/2` — where
`β̃_Q ≤ β̃_2`, so a mod-2 zero *proves* the rational vanishing the census claims:

> **163 classes, 227 892 labelled vertices, 0 violations, 0 over cap** — 50 seconds, 0.3 GB.

with the population split by how the answer is actually obtained:

| route | classes | labelled | what it is |
|---|---|---|---|
| `degree_arithmetic` (`d ≤ −2`) | 50 | 56 322 | vanishes for free |
| `gamma_nonempty` (`d = −1`) | 27 | 53 760 | Proposition 3's `U(P) ≠ ∅` |
| **`computed_mod2`** (`d ≥ 0`) | **86** | **117 810** | actual homology computation |

**D7 — the over-cap class was computable inside the instrument's own cap.** `mg-72e4` drops the
`c = 1` class at `n = 7` because
`_binom(len(atoms), d + 3) > 3_000_000` (`compat_geom_mg72e4_height1_anchor.py:486`) —
`binom(30, 8) = 5 852 925`. But that is a bound on the **ambient simplex on 30 atoms**, not a
count of `Γ(P)`'s faces. `Γ(P)` is far thinner:

    faces by dim:  30, 425, 3 760, 23 160, 105 032, 362 740, 975 640
    total through dim 6 (all that beta~_5 requires):  1 470 787   -- under the same 3 000 000 cap

**`β̃₅(Γ(P)) = 0`.** No violation. So the single named gap in the headline was an artifact of
testing an ambient bound rather than counting the complex, not evidence that the class was out
of reach.

**Concurrent independent agreement.** `pbcd7` (work item `mg-bcd7`) was dispatched onto this same
computation and reached `β̃₅ = 0` by a route sharing nothing with mine — writing `Γ` as
`X ∖ F` with `X` a cone, and reading the answer off the long exact sequence of the pair through
three small matrices instead of a 975 640-column boundary. Mine is a direct skeleton rank. A
third point of contact: `pbcd7`'s decomposition **predicts** `Γ`'s dim-7 face count as
**2 075 235**, and my enumeration **measures** 2 075 235, neither of us having read the other's
number. Their result is theirs, not re-derived by me; mine is measured here.

### 4.2 Controls on *this* audit's instruments

A remedy is an artifact of the same kind as the defect. Everything above rests on two routines I
wrote tonight, so both are pinned before they are believed:

| control | result |
|---|---|
| homology vs known answers | `∂Δ^k ≃ S^{k−1}` for `k = 1..5`; `Z₇` torus `(0, 2, 1)`; empty complex `= S^{−1}` — all reproduce |
| mod-2 routine vs my own mod-`p` routine | agree on **84/84** `Γ` complexes at `n = 3..6` |
| `Γ` face enumeration (DFS) vs a direct predicate | 4 000 random atom subsets on the `c = 1` class: **4 000 agree, 0 disagree** |
| crosscut reduction vs a direct upper link | **194/194** vertices of `Δ₄` |
| counting, by a second algorithm | closed form vs enumeration; orbit counting vs canonical forms — every figure agrees |

### 4.3 The 17 classes nobody had measured

The one gap that could actually break the headline was D2's 15 classes. I measured all 17 —
`β̃_k(Γ(P))` over `Z/2` for `k = −1 .. dmax`, with `dmax` chosen per class to reach
`margin ≥ 4`. **Mod 2 is the correct field for this job**: `rank₂ ≤ rank_Q`, so `β̃_2 = 0`
*proves* rational vanishing, and rational vanishing low is exactly what the margin claim needs.

| `c` | classes | labelled | atoms | `d` | `β̃₂` computed through | first non-zero | margin |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 42 | 30 | 5 | **5** (§4.1) | none ≤ 5 | ~~**≥ 1 — OPEN**~~ → **CLOSED by `mg-dd84`: no non-zero degree at all** |
| 2 | 2 | 210 | 26 | 4 | 4 | none ≤ 4 | ~~**≥ 1 — OPEN**~~ → **CLOSED by `mg-dd84`: no non-zero degree at all** |
| 3 | 3 | 1 120 | 21–24 | 3 | 6 | none ≤ 6 | ≥ 4 ✅ |
| 4 | 3 | 420 | 22–24 | 2 | 5 | none ≤ 5 | ≥ 4 ✅ |
| 5 | 2 | 84 | 26 | 1 | 4 | none ≤ 4 | ≥ 4 ✅ |
| 6 (stars) | 2 | 14 | 30 | 0 | 4 | **4** | **= 4 ✅ measured** |
| 6 (other) | 2 | 420 | 21 | 0 | 4 | none ≤ 4 | ≥ 5 ✅ |
| 10 | 2 | 42 | 22 | −4 | 4 | **4** | **= 8 ✅** |

Three results:

1. **`min margin ≥ 4` at `n = 7` now stands on 160 of 163 classes** (227 640 of 227 892 labelled
   vertices) by measurement, up from 148 as published — and the two stars moved from *inferred*
   to *measured*. **Still open: 3 classes, 252 vertices** — the `c = 1` class and the two
   `c = 2` classes, all three at `margin ≥ 1`. Reaching `margin ≥ 4` there needs `β̃` through
   degree 8 and 7 respectively; I stopped short of that rather than take more of a shared host
   than my core budget allows. **These three are exactly the `c ≤ 2` slice §6 already names as
   the part Conjecture C would not cover** — the residual is where the document says the
   residual is.

   > **2026-08-14 — this remainder is CLOSED (`mg-dd84`,
   > `docs/OneThird-mgdd84-n7-cLE2-Margin.md`), and the resource judgement above was sound but
   > the resource estimate was not.** All three classes have `H̃_k(Γ(P)) = 0` in **every**
   > degree, so `margin ≥ 4` holds vacuously and the population is **163 of 163 classes /
   > 227 892 of 227 892 labelled vertices**, with `min margin = 4` still attained at the stars.
   > The route is the one this audit named — `mg-bcd7`'s cone/LES decomposition — pushed one
   > step further: the filter `X ∖ Γ` is a direct sum of augmented simplex chain complexes,
   > which are exact, so no degree needed computing separately. **The whole run cost 47.8 s and
   > 277 MB in one process**, against the `β̃`-through-degree-8 brute force this section
   > correctly declined. Declining was right on the information available; what closed it was
   > reading `mg-bcd7`, not more cores.

2. **Conjecture C is now verified at `n = 7` on all 163 classes.** No class among the 17 carries
   any homology below degree `n − 3 = 4`; the 146 already had full homotopy types with homology
   only in degree 4. The document does not claim this and could. *(146 of the 163 rest on the
   target's instrument, 17 on mine.)*

3. **D3 — the `n = 7` homology-carrying count is under-reported.** §4.2's table row says
   *"2 of the 146 within cap"* and §4.3 says *"at `n = 7`, the two within cap are `K_{3,4}` and
   `K_{4,3}`"*. Both are correctly scoped, but **at least 6 of the 163 classes carry homology in
   degree 4**: `K_{3,4}`, `K_{4,3}`, the two stars `K_{6,1}`/`K_{1,6}`, and — new here —
   **`K_{2,5}` and `K_{5,2}`** (`c = 10`, 21 labelled vertices each, `β̃₄ = 1`), which sat among
   the 17 unmeasured. Read down §4.2's column (4 of 8, 4 of 20, 5 of 55, **2 of 146**) and it
   looks like a census trend that fell; it is four incomparable populations, and the `n = 7` entry
   is missing four classes. The finding is in the document's *favour* — all six are complete
   bipartite with homology in degree exactly `n − 3`, which strengthens §4.3 — but the number as
   printed is not the number.

---

## 5. D4 — cross-doc: all four amendments are stale at their destination

`mg-72e4` amended four places at `2d4abbf`, and landed `n = 7` three commits later at `75fb81d`.
**None of the four was updated.** All four still describe a record that stops at `n = 6`:

| Destination | What it says now |
|---|---|
| `mg-52c4` §0 pt 3 | *"the margin … is `1` at `n = 4`, `2` at `n = 5`, `3` at `n = 6`"* |
| `mg-52c4` §3.3 | *"the margin is `1` at `n = 4`, `2` at `n = 5`, `3` at `n = 6`"*; *"`n = 6` **IS** now established"* |
| `mg-52c4` §5 | *"false at `n = 5` and `n = 6`, where the margin is 2 and 3"* |
| `mg-e08a` §7 | *"**`1` at `n = 4`, `2` at `n = 5`, `3` at `n = 6`**"*; *"`n = 6` is now measured complete"* |

Nothing there is **false** — every sentence was true when written and is still true. They are
**stale**: a reader arriving at any of the four destinations gets `n ≤ 6` as the state of the
record, while the source document's own headline is `n = 7`, 163 classes, 227 892 vertices. This
is the failure mode this corpus has a lineage of and a commit vocabulary for — *"land the
correction AT ITS DESTINATION"* (`a8688f2`, `mg-e2a0`).

**Repair:** one clause in each of the four — margin `4` at `n = 7`, `162 of 163` classes /
`227 850 of 227 892` vertices, `0` violations.

---

## 6. Defect list, for `pm-onethird`

| | Defect | Severity | Repair |
|---|---|---|---|
| **D1** | §0 verdict says *"163 iso classes … 0 violations"*; correct is **162 of 163**. The most quotable sentence in the document is the one place the class denominator is wrong. | **HIGH** — quotability | ~~one word in §0 line 19~~ — **NOT a one-word fix; see §6.1.** By the time this was carried the word was *right* and the warrant was still missing. `mg-bcd7` measured the class, so `163` is now true and writing `162` would make the document **false** |
| **D2** | *"min margin 4"* at `n = 7` is a minimum over **148 of 163** classes; 15 classes / 2 338 vertices had no margin information at all. A **fourth denominator**, stated nowhere. **This is the defect class the audit stage exists to catch.** | **HIGH** | state the population in §0 and §4.2; §4.3 above supplies the measurement for 12 of the 15 |
| **D3** | *"2 of the 146"* homology-carrying classes at `n = 7`; **≥ 6 of the 163** actually carry homology in degree 4 (`K_{2,5}`, `K_{5,2}` and both stars are missing). | **MEDIUM** | correct the §4.2 row and extend §4.3's list |
| **D4** | All four cross-doc amendments stop at `n = 6`, three commits stale. | **MEDIUM** | one clause each, at the four destinations |
| **D5** | N1 stated as *"3 of the 8 classes at `n = 4`"*; instrument ran **144 instances**, **7** testable at `n = 4`, **0 of 137** refuted at `n = 5,6,7`, and the 3 are the headline `n = 4` classes themselves. | **MEDIUM** | restate N1's denominator and its scope |
| **D6** | *"contractible"* used bare 4× in §1, outside the stated scope of both `Q`-acyclicity caveats. | **LOW** | widen §3's caveat from *"the tables below"* |
| **D7** | The over-cap test is `binom(#atoms, d+3)` — the **ambient simplex**, not `Γ`. It dropped a class whose actual complex (1 470 787 faces) sits well inside the instrument's own 3 000 000 cap. The gap was a test artifact, not a wall. | **MEDIUM** | cap on `Γ`'s realised face count; the class itself is `pbcd7`'s to land |
| **O1** | 48.3% of the `n = 7` *"measured"* vertices are the Proposition-3 slice set to zero by degree arithmetic, not computed. §7 pt 1 and pt 3 overlap on them. | observation | note the overlap in §7 |

### 6.1 Disposition — all seven carried, 2026-08-14 (`mg-0f24`)

This table was the only place the seven defects existed for the length of one work item. That is
the recurring failure this stage has: an audit that finds defects needs a successor and nothing
files one. `pm-onethird` filed `mg-0f24` on second-line review and it landed them **at their
destinations**, not in a new document.

| | landed where | as what |
|---|---|---|
| **D1** | — | **discharged by `mg-bcd7` before this repair began**, and not by editing a word: `pbcd7` measured the missing class (`β̃₅ = 0`), so §0's `163` became **true** rather than corrected. `mg-72e4` §0 records what the line previously said. Changing it to `162` would have made the document false |
| **D2** | `mg-72e4` §0 result 1 and §4.2 | the margin table gains a population column, and §4.2 **derives** the denominator: `146` (full homotopy type) → `148` (as published, `146` + the 2 stars) → **`160` of 163** (`146` + the 14 §4.3 measured). `148 + 14 = 162` is the trap — the stars are in both, so the overlap is 2 |
| **D3** | `mg-72e4` §4.2 row and §4.3 | `2 of the 146` → **`≥ 6` of 163**, with `K_{2,5}`/`K_{5,2}` and both stars added and each reading labelled by the field it was read over. **Closed to `= 6 of 163 over Z/2` at `mg-c99c` R2**: all 146 re-read over `Z/2`, `β̃₄` agrees with both instrument primes on every one, so `t₄(2) = t₃(2) = 0` and there is no seventh class. The 17 were re-derived in the same run (their degree-4 skeletons sit inside `ELIM_CAP`), reproducing this audit's four exactly |
| **D4** | `mg-52c4` §0 pt 3, §3.3, §5; `mg-e08a` §7 | one dated clause each, carrying `n = 7` complete (163/163, 227 892/227 892, 0 violations) and margin `≥ 4` on 160 of 163 |
| **D5** | `mg-72e4` §1 | N1 restated: **144 instances**, 3 refuted, **7** testable classes at `n = 4`, **0 of 137** at `n = 5,6,7`, and the three are the `n = 4` near-miss classes themselves |
| **D6** | `mg-72e4` §3 | caveat widened from *"the tables below"* to the whole document — **and to both directions**: a mod-`p` zero proves rational vanishing, a mod-`p` one only bounds `β̃_Q ≤ 1` |
| **D7** | `scripts/compat_geom_mg72e4_height1_anchor.py`, `mg-72e4` §4.1 | the gate now counts `Γ(P)`'s **realised** faces. Measured over all 249 classes at `n = 3..7`: the old gate wrongly excluded **exactly one** class, the new one excludes none. At `n = 8` the old gate would decline 6 classes / 1 792 labelled vertices; **`mg-c99c` R1 measured what the new one says there — it declines 3 (392 labelled) and admits 3 (1 400 labelled), so the `n ≤ 7` "artifact every time" reading does not extend**, and the realised gate newly excludes nothing at any `n ≤ 8`. Two findings the one-line remedy did not predict — a naive swap **still** excludes the class, because the near-miss column asks one dimension more (`3 546 022` faces, over the same cap), and the replacement is a materialisation proxy where the resource that failed was the *elimination* |
| **O1** | `mg-72e4` §7 pt 1 | the overlap noted: 110 082 of the `n = 7` *"measured"* vertices are the Proposition-3 slice re-counted |
| **D2 residual** | `mg-72e4` §0 result 1 and §4.2; §4.3 and §7 above | **`mg-dd84`, 2026-08-14.** The 3 classes at `c ≤ 2` / 252 labelled vertices that `mg-0f24` deliberately did not fold in. All three have `H̃_k(Γ(P)) = 0` in **every** degree — `margin ≥ 4` vacuously — so the denominator closes at **163 of 163 classes / 227 892 of 227 892 labelled vertices** and `min margin = 4` is attained, at the stars. `160 + 3 = 163` composes because the 3 are by construction the classes with no margin information after `mg-0f24`; `mg-dd84` checks the disjointness rather than assuming it, which is the same trap as `148 + 14` one level down |

The remainder this audit declined — `margin ≥ 4` for the 3 classes at `c ≤ 2`, 252 labelled
vertices — was **not** folded into that repair, correctly. `pm-onethird` filed it as `mg-dd84`
instead, and **`mg-dd84` closed it on 2026-08-14** (row above). Declining to fold it in is what
made it a work item with a successor rather than a sentence in a document, which is the failure
mode §6.1 opens by naming.

**Not defects, checked and cleared:** Proposition 3 and its inequality direction; Proposition 1
and its imported ingredient (A2); the crosscut reduction and control H2's discriminating power;
the `Q`-acyclic / homotopy-equivalence distinction in both directions; every count and percentage
in the document; §4.3's descriptive labelling; §6/§7's labelling of Conjecture C, `c ≤ 2` and
`n ≥ 8` as open.

## 7. What this audit did **not** verify

- **The margin for 3 classes** (`c ≤ 2`, 252 vertices) is bounded only by `≥ 1`, so
  *"min margin 4 at `n = 7`"* is measured on 160 of 163 classes and remains unestablished on
  three. D2 is reduced, not retired. *(**Retired 2026-08-14 by `mg-dd84`** — all three carry no
  homology in any degree, and the figure now stands on 163 of 163 / 227 892 of 227 892. This
  bullet records what **this** audit did not verify and is left as written.)*
- `n ≥ 8` — untouched here, as in the target.
- `pbcd7`'s cone/LES derivation of `β̃₅ = 0` — I did not re-derive it. What I can say is that my
  own direct computation lands on the same value and that our face counts agree.
- `mg-52c4` Theorem A itself, beyond re-measuring its (A2) conclusion at all 86 height-1 vertices
  of `Δ₄`. Its proof was not re-derived.
- F17+F18 (`PPF_{n−1} ≃_Q S^{n−3}`) was not re-derived; it was corroborated at `n = 5, 6` through
  the star's measured margin and at `n = 7` through `β̃₄(Γ(K_{6,1})) = 1` mod 2.
- The two `Z/2`-non-zero readings (`β̃₄ = 1` at the stars and at `K_{2,5}`/`K_{5,2}`) bound
  `β̃_Q ≤ 1`; they do not exclude 2-torsion, so they are not rational *values*.

## 8. References

`docs/OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md` (target, `75fb81d`);
`docs/OneThird-mg52c4-PerPoset-Subposet-Question.md` §0 pt 3, §3.3, §5 and
`docs/OneThird-mge08a-TheoremA-IndependentAudit.md` §7 (the four amendments, `2d4abbf`);
`scripts/compat_geom_mg72e4_height1_anchor.py` (read, never imported).
Work items: `mg-72e4` (audited), `mg-9cd1` (this audit), `mg-e08a`, `mg-52c4`, `mg-1b3b`.
Literature relied on only for cross-checking: Björner, *Topological methods*, Thm 10.8;
Mirsky (1971); Mantel's bound.
