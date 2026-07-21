# INDEPENDENT AUDIT — `OneThird-Width4-ResidualGap-Scoping.md` (mg-c47a, merge `45526b4`)

*Auditor: `aud7d24`, work item **mg-7d24**, 2026-07-21. Fresh context; I did not author the audited
work and did not read the author's scripts before re-deriving. Process: Appendix A of
`/Users/daniel/research/onethird_program/STATE.md` (absolute path, as that appendix requires).*

**Target read from `git show origin/main:docs/OneThird-Width4-ResidualGap-Scoping.md` — 356 lines,
byte-identical to the worktree copy (verified by `diff`, not assumed).** The brief warns that an
empty grep on a missing file looks exactly like a clean result; the read was confirmed non-empty
before any conclusion was drawn.

---

## 0. Verdict

> **OVERSTATED — with one BROKEN lemma that is repairable in a single word, and one
> genuinely load-bearing scope error.**
>
> Of the 13 `[PROVEN]`-family tags: **10 CONFIRMED, 2 OVERSTATED, 1 BROKEN.**
>
> The document's *recommendation* (DROP the residual gap as a closure target) **survives** the
> audit — but two of the four pillars it rests on are weaker than stated, and one of them
> (§3.6) is partly **circular**.

Every measured number I could reach independently — the arena counts, the prune certification, the
`n = 10` and `n = 11` record witnesses, the §3.6 minima at `n ≤ 8` — **reproduced exactly** on a
from-scratch enumerator sharing no code with the repo. The arithmetic in this document is clean.
The problems are in the *statements*, not the numbers.

---

## 1. Claim ledger (exhaustive — all 13 `[PROVEN]`-family tags + the 4 other labels)

Tags located by a full-document `grep`, not from the §7 ledger, because a curated list is exactly
where an omission would hide. The §7 ledger and the grep agree on membership.

| # | line | claim | verdict |
|:--|:--|:--|:--|
| 1 | 64 | **Obs. 3.1(a)** `(2)` ⟺ the 1/3–2/3 conjecture | **CONFIRMED** |
| 2 | 64 | **Obs. 3.1(b)** `(W₀)` ⟺ conjecture restricted to width `> W₀` | **CONFIRMED** (but see §3 — it is a contrapositive, and the *inference* drawn from it is not) |
| 3 | 87 | **Lemma 3.2a** nested profiles ⟹ `Pr[x<y] ≥ 1/2` | **CONFIRMED** |
| 4 | 91 | **Lemma 3.2b** *"some automorphism **maps `x` to `y`**"* ⟹ `Pr = 1/2`, `δ ≥ 1/2` | **BROKEN** — explicit `n = 9` counterexample, brute-force verified (§2) |
| 5 | 95 | **Corollary (twins)** `D(x)=D(y)`, `U(x)=U(y)` ⟹ `δ ≥ 1/2` | **CONFIRMED** |
| 6 | 105 | **Prop. 3.3** `w > 3^{n−w}` ⟹ twins ⟹ `δ ≥ 1/2` | **CONFIRMED** |
| 7 | 111 | **`[PROVEN, as a limitation]`** the symmetry family ceilings at `w ≤ n − log₃ w` | **CONFIRMED** |
| 8 | 119 | §3.4 coherence adds nothing (`[PROVEN]` content: *none new*) | **CONFIRMED** |
| 9 | 167 | §3.8 *"the form of Q1 **that would dissolve the residual gap** (`δ<1/3 ⟹ width ≤ 2`)"* | **OVERSTATED** (§3) |
| 10 | 168 | §3.8 symmetry mechanisms ceiling out (Lemmas 3.2a/b + Prop 3.3) | **CONFIRMED** — survives finding F1, because it consumes only the twin corollary |
| 11 | 169 | §3.8 `[PROVEN — already merged]` coherence contributes zero | **CONFIRMED** |
| 12 | 187 | §4.1 the width prune extends to `W = 4` unchanged | **CONFIRMED** — and independently re-certified to `n ≤ 8` |
| 13 | 327 | §5 `[PROVEN — trivially]` the residual is not closable by any finite search | **CONFIRMED** (trivially, as labelled) |

Non-`[PROVEN]` labels, audited for correctness of the label itself:

| line | claim | label | verdict |
|:--|:--|:--|:--|
| 170 | §3.5 width enters every existing tool anti-monotonically | `[MEASURED — three merged probes]` | **label CORRECT** — not re-run here, and the doc says so |
| 171 | §3.6 width-3 penalty small and shrinking | `[EMPIRICAL, non-monotone]` | **OVERSTATED** — the label is honest but the *data* is mislabelled (F3) |
| 322 | §3.7 separator-2 pairs in a `δ = 6/17` poset | `[PROVEN by witness]` | **CONFIRMED** — both witnesses, fully |
| 324–325 | §4.1 certification / §4.2 arena sizes | `[MEASURED]` | **CONFIRMED**, extrapolated rows correctly flagged |
| 326 | §4.4 a width-4 beam is worthless | `[REASONED]` | **label CORRECT** |

---

## 2. F1 — Lemma 3.2b is FALSE as boxed. `[BROKEN]`

### The statement and its proof

> **Lemma 3.2b (symmetry) `[PROVEN — trivial]`.** If some automorphism of `P` maps `x` to `y` for
> an incomparable pair `x ∥ y`, then `Pr[x <_σ y] = 1/2` and hence `δ(P) ≥ 1/2`.
>
> *Proof.* The automorphism induces a bijection of `L(P)` carrying `{x<y}` onto `{y<x}`. ∎

**The proof step is invalid.** If `φ(x) = y` but `φ(y) = z ≠ x`, the induced bijection of `L(P)`
carries `{x<y}` onto `{y<z}` — *not* onto `{y<x}`. The bijection only complements the event when
`φ` **swaps** `x` and `y`. And no power of `φ` ever swaps two *adjacent* elements of an orbit of
length `k ≥ 3`: `φ^j(x)=y` forces `j ≡ 1`, while `φ^j(y)=x` forces `j ≡ −1 (mod k)`, so `k = 2`.

This is not a pedantic gap. It is the whole hypothesis.

### The counterexample

An automorphism orbit is always an antichain (`x < φ^j(x)` iterates to `x < x`), so the hypothesis
is satisfiable at every orbit length. Searching `Z/3`-invariant posets, the smallest chiral case
appears at `n = 9`:

```
below = (256, 64, 128, 322, 196, 385, 0, 0, 0)          n = 9
covers: 8<0, 6<1, 7<2 | 1<3, 8<3 | 2<4, 6<4 | 0<5, 7<5
sigma  = (0 1 2)(3 4 5)(6 7 8)   is an automorphism, of order 3
Aut(P) = Z/3 exactly  (|Aut| = 3, brute force over all 9! permutations)
```

A three-layer *twisted* cyclic poset: bottom `{6,7,8}`, middle `{0,1,2}`, top `{3,4,5}`, with the
middle and top layers twisted by *different* amounts. That mismatch is what kills every reflection
— `Aut(P)` is the bare cyclic group, with **no** element swapping `0` and `1`.

Verified by **brute-force enumeration of all `9! = 362 880` permutations**, filtering linear
extensions and counting directly — no DP, no shared code with the repo or with my own toolkit:

```
e(P)        = 1431
x = 0, y = 1        x || y : True        sigma(x) = 1
Pr[0 < 1]   = 711/1431 = 79/159 = 0.496855346      LEMMA CLAIMS 1/2      FALSE
delta(P)    = 79/159            = 0.496855346      LEMMA CLAIMS >= 1/2   FALSE
automorphisms sending 0 -> 1 : 1        SWAPPING 0 and 1 : 0
```

**Both clauses of Lemma 3.2b fail on this poset.** `Pr ≠ 1/2`, and `δ(P) < 1/2`.

**`n = 9` is minimal.** Exhaustively over **every iso-class to `n ≤ 8`** (2, 5, 16, 63, 318, 2 045,
16 999 classes) the hypothesis is never satisfiable without a swapping automorphism also being
present — **0 chiral instances at every `n ≤ 8`**. So the lemma is *vacuously* true below `n = 9`,
which is exactly why the defective proof survived checking: the gap has no witness until the first
size at which a poset can carry a bare `Z/3` automorphism group.

### Blast radius: contained

- **The Corollary (twins) is sound.** `D(x)=D(y)`, `U(x)=U(y)` makes the *transposition* of `x, y`
  an automorphism — a genuine involution — so the proof applies verbatim. Exhaustively verified:
  1 424 twin-containing posets at `n ≤ 7`, **0 violations**.
- **Prop. 3.3 is unaffected** — it consumes only the twin corollary. Verified: 779 posets with
  `δ < 1/2` at `n ≤ 7`, **0 violations** of `w ≤ 3^{n−w}`.
- **§3.2's rhetorical uses are unaffected** — layered posets, the standard example `S_w`, products
  and near-twin semiorders are all symmetric by *transpositions*, which the corollary covers.
- **§3.8 bullet 2 (ledger #10) survives**, since it routes through Prop. 3.3.

**The repair is one word.** Require the automorphism to *swap* `x` and `y`. With that hypothesis
the proof is correct and the conclusion holds. **Note that §7's ledger row already states it
correctly** — *"automorphism-**swappable** or twin incomparable pair"* (line 317), as does the
commit message. So the document contradicts itself, and **the sound version is the one already
written down**. This is a boxed-statement defect, not a conceptual one.

---

## 3. F2 — the headline equivalence is proved for a form the residual gap does not need. `[OVERSTATED]`

### The mathematics is CONFIRMED

I re-derived both directions independently.

**(a, ⟹).** Assume `(2)`. Let non-chain `P` have `δ(P) < 1/3`. Then `width(P) ≤ 2`, and `width = 1`
is a chain, so `width(P) = 2`. Width-2 posets satisfy `δ ≥ 1/3`. Contradiction. ✓

**(a, ⟸).** Under the conjecture, `{P : δ(P) < 1/3}` is empty (or, under a `δ := 0` convention for
chains, contains only chains, of width `1 ≤ 2`). Either way `(2)` holds. ✓ **The vacuity direction
is robust to the chain convention** — worth stating, since the repo reports `δ = None` for chains
(`C.md:68`) and the doc leans on "`δ` undefined".

**(b).** `(W₀)` is the contrapositive of "width `> W₀` ⟹ `δ ≥ 1/3`". ✓ Tautologically.

I also checked the exceptional-family clause the doc attaches to Sah. With `E = T = ({a,b,c}, a<b)`
and `⊕` the ordinal sum, I computed directly: `δ(T) = δ(1⊕T) = δ(T⊕T) = δ(T⊕1⊕T) = 1/3`, and
sums with no `T` are chains (`δ = None`). **The doc's characterisation is correct** under the
ordinal-sum reading.

**Robustness note in the document's favour:** the `⟹` direction needs only *"width 2 ⟹ `δ ≥ 1/3`"*.
So Obs. 3.1(a) survives **either** reading of Sah's "direct sum" (under disjoint union the width-≤2
exceptions are `T`, the 2-antichain and chains, with `δ ∈ {1/3, 1/2, undefined}` — still `≥ 1/3`),
and survives even if Sah's constant or exceptional family were misquoted entirely.

### The scope error

§0 and §3.8 both assert:

> "the form of Q1 **that would dissolve the residual gap** (`δ < 1/3 ⟹ width ≤ 2`)"

**That is the wrong statement.** The residual gap is *width ≥ 4 at `n ≥ 10`*. Dissolving it requires
`(3)`, not `(2)`. `(2)` is strictly stronger — by the doc's own Obs. 3.1(a) it proves the *entire*
conjecture, including width 3, which the residual gap does not contain.

And for the gap-relevant `W₀ = 3`, Obs. 3.1(b) says `(3)` ⟺ *"the conjecture holds at width > 3"* —
which **is the residual gap itself, restated by contraposition**. So:

- For `W₀ = 2` the equivalence has real content (it imports Linial/Sah) but targets **more** than
  the gap.
- For `W₀ = 3` the equivalence is a **tautology** and carries **no information** about difficulty.

The document has proved a non-trivial statement about `(2)` and a trivial statement about `(3)`, and
the headline attributes the force of the first to the target of the second.

### The inference "a programme pursuing it goes in a circle" does not follow

Consequence 1 (line 77) reads: *"A programme that sets out to prove 'low `δ` ⟹ narrow' as a lemma
en route to the conjecture is going in a circle."*

**Logical equivalence of statements says nothing about the difficulty of proofs.** Every true
theorem is logically equivalent to itself; that is not an argument against proving it. A structural
mechanism establishing `δ < 1/3 ⟹ width ≤ 3` would be a perfectly good — and gap-closing — proof
strategy, and Obs. 3.1(b) is no obstruction to it whatsoever. Circularity is a property of a
*derivation*, not of an equivalence between statements. The doc's own Consequence 2 concedes the
substance (`(W₀)` "is a genuine reduction... worth pursuing only if the wide case is genuinely
easier"), which is the correct framing — but §0 and §3.8 do not carry that hedge.

**What is actually established:** aiming at `(2)` overshoots the gap and lands on the full
conjecture; aiming at `(3)` is definitionally the gap. Neither is a *proof* that no structural
route is easier than enumeration. The real weight against Q1 is carried by §3.3 (the proven coding
ceiling) and §3.5 (the measured anti-monotonicity) — both of which are sound, and neither of which
needs Obs. 3.1.

---

## 4. F3 — §3.6's trend rests on two cells that are not what they are labelled. `[OVERSTATED, partly circular]`

§3.6's table row is headed **"all-width min `δ`"** for `n = 5 … 11`. I reproduced it independently
over **primitive** posets (repo definition: incomparability graph connected):

| `n` | 5 | 6 | 7 | 8 |
|:--|:--|:--|:--|:--|
| my all-width min | `4/11` | `5/14` | `14/39` | `16/45` | 
| my width-exactly-3 min | `4/11` | `15/37` | `14/39` | `19/50` |
| penalty | `0` | `+0.0483` | `0` | `+0.0244` |

**Exact agreement at `n ≤ 8`**, including the doc's point 1 — I confirm the all-width optimum *is*
attained at width 3 at `n = 5` and `n = 7`, and at width 2 at `n = 6, 8`.

**But at `n = 10` and `n = 11` the row is not an all-width minimum.** Per `C.md:334`, all-width
coverage stops at `n = 9`: *"all widths | `n = 10, 11` | **not covered here***". The `n=10` figure
`37/106` is the **width-≤3** minimum (it is printed as such in the prior audit's own stdout,
`IndependentAudit.md:137`).

Consequences:

1. **The document contradicts itself.** §1.1 quotes the audit-settled wording — *"Width ≥ 4 received
   no coverage at any `n ≥ 10`"* — and then §3.6 tabulates an "all-width min `δ`" at `n = 10, 11`.
   Both cannot be true.
2. **The direction of the error matters.** True all-width min `≤` width-≤3 min, so the *true*
   penalty at `n = 10, 11` is `≥` the tabulated `+0.0039` / `+0.0065`. The tabulated values are
   **lower bounds**, not measurements.
3. **The claimed trend is therefore not established.** §3.6 point 2 and §3.8's `[EMPIRICAL]` bullet
   rest on *"`0.0244 → 0.0068 → 0.0039`, shrinking over `n = 8 → 10`"*. The `n = 8` and `n = 9`
   cells are genuine; **the `n = 10` cell — the one that makes it a trend — is not**. The true value
   could exceed `0.0068` and reverse the direction.
4. **It is circular.** Knowing the true all-width minimum at `n = 10` requires width-≥4 coverage at
   `n = 10` — precisely the search this document recommends against. §3.6 uses the *absence* of
   width-4 data as if it were evidence about width-4 behaviour.

§6 compounds this by re-citing *"`+0.0244 → +0.0068 → +0.0039` at widths-3 `n = 8,9,10`"* as the
trend its proposed measurement would test. That framing is right in spirit — the `n = 10` width-4
datum *would* be new — but the baseline it would be compared against is misdescribed.

The doc's hedging (*"non-monotone; no extrapolation is licensed"*) is honest and partially
inoculates the claim. It does not fix the mislabelled row. **The defect is inherited from
`C.md` §9.5**, whose header says "the all-width minimum of §5.1" while §5.1 marks `n = 10, 11` as
`exhaustive-width2` — so this is a **pre-existing error in already-merged work**, propagated here
without the caveat. Flagged in both places.

---

## 5. What I independently reproduced (all exact)

A from-scratch enumerator (canonical augmentation by adding a maximal element; canonical form by
refinement-pruned lexicographic minimisation; exact `Fraction` linear-extension DP), sharing no
code with the repo:

**§4.1 certification table — reproduced in full, `n ≤ 8`:**

| `n` | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|:--|--:|--:|--:|--:|--:|--:|--:|
| my unpruned (all widths) | 2 | 5 | 16 | 63 | 318 | 2 045 | **16 999** |
| OEIS A000112 | 2 | 5 | 16 | 63 | 318 | 2 045 | **16 999** |
| my unpruned, filtered to width ≤ 4 | 2 | 5 | 16 | 62 | 308 | 1 921 | **15 079** |
| my **pruned** width-≤4 enumeration | 2 | 5 | 16 | 62 | 308 | 1 921 | **15 079** |
| **disagreements** | 0 | 0 | 0 | 0 | 0 | 0 | **0** |

**The width-4 prune certification is CONFIRMED independently, not merely reproduced.** Width-≤3 and
width-≤2 columns likewise agree at every `n ≤ 8` (`7 790` / `711` at `n = 8`), and width-exactly-4
(`1, 7, 63, 636, 7 289`) and primitive-width-exactly-4 (`1, 5, 48, 501, 5 932`) both match §4.2.

I also re-ran the committed `onethird_mgc47a_width4_arena_count.py --nmax 8` and it reproduces its
own committed JSON and my independent counts exactly (`self-check mismatches: 0`).

**§3.7 witnesses — both fully CONFIRMED** (the doc's indices are 0-indexed):

| | `n = 10` witness | `n = 11` witness |
|:--|:--|:--|
| `e(P)` | **187** ✓ | **750** ✓ |
| `δ` | **`6/17`** ✓ | **`134/375`** ✓ |
| width | 3 ✓ | 3 ✓ |
| incomparable pairs | **14 of 45** ✓ | 17 |
| maximum antichains | **exactly 2**, both size 3: `(1,2,3)`, `(4,7,8)` ✓ | — |
| nesting on `(1,2)`, `(1,3)` | both nested ✓ | — |
| separator-2 pairs | `(1,3)`, `(7,8)` ✓ (also `(0,1)`, `(8,9)`) | `(2,3)`, `(8,9)` ✓ |
| minimum separator | **2** ✓ | **2** ✓ |

Every §3.7 claim checks out, and the `f(2) ≤ 6/17` refutation of the quantitative near-twin
heuristic is sound.

**Lemmas verified exhaustively over all iso-classes `n ≤ 7`:** Lemma 3.2a — 19 284 hypothesis
instances, **0 violations**. Twin corollary — 1 424 posets, **0 violations**. Prop. 3.3 — 779
posets with `δ < 1/2`, **0 violations**.

**§4.2 / §4.3 internal arithmetic — checked, all consistent:** `4.06×` (1 124 519 / 277 180 =
4.057); level ratios `3.20 … 11.73` and `7.48` at width 3; primitive fractions 39.3 / 53.2 / 65.5 %;
per-class costs `2.09/2.32/2.50 · 10⁻⁴` s; the `1.9×` `δ` multiplier (1430/743); `430 × 1.9 ≈ 14`
min; the `7.5×` memory multiplier; `≈16×` for `n = 12`; ratio-of-ratios `1.21–1.28` at width 4 (I
measure 1.209–1.282) and the decaying width-3 sequence. **§4.4's beam claim is correctly sourced** —
it cites the **width-3** beam (`n = 9,10,11`, missed at `n = 10`, found `47/130` vs truth `6/17`),
**not** the separate all-width beam that missed at `n = 15`. No conflation. Confirmed against
`C.md:501-507`.

---

## 6. Object / coordinate check (brief item 5)

**Nothing to report, and that is the honest finding.** Every quantity in this document is `δ(P)` —
a static functional of the uniform measure on `L(P)`: `max` over incomparable pairs of
`min(Pr[x<y], Pr[y<x])`. No generator gap, no `λ₂^BK`, no `λ_std`, no dynamical object appears
anywhere. The one place a mixed object could have crept in — §3.5's citation of the `λ` probes
(mg-210d) — correctly reports them as *bounds on `δ`* degrading with incomparability density, and
does not equate a spectral quantity with `δ`. **No conflation found.**

---

## 7. Cross-document consistency (brief item 6)

- **§1.1 is quoted faithfully** from the audit-settled `C.md` §9.7 wording. Width exactly 3,
  `n ≤ 11`, `6/17` at `n = 10`, proven minimum, `4.10·10⁻³` above `β`, bounded incomplete beam for
  `12 ≤ n ≤ 16`, width ≥ 4 uncovered at `n ≥ 10`. **No silent contradiction of the prior round** —
  except the §3.6 row (F3), which contradicts §1.1 *within this document*.
- **`β` margins confirmed.** `β = 0.34884346742240945893`; `6/17 − β = 4.0977·10⁻³` (doc:
  `4.10·10⁻³` ✓); ladders `2.4523·10⁻⁶` ✓; ratio `≈ 1 673` (doc: "≈1 700" ✓).
- **This document refutes no prior merged claim**, and supersedes nothing. It *inherits* one
  (the §9.5 "all-width" label, F3), which I am flagging against `C.md` as well.
- **`STATE.md` is quoted accurately.** §5's parenthetical *"Width-3 baggage to keep out: … The
  skeleton above has zero width dependence"* is verbatim `STATE.md:91`. The unquoted gloss
  "any-width by construction" is the doc's own phrasing and is fairly supported by `STATE.md:3`
  (*"Everything here is any-width"*). **No misattribution.**
- **F5 (minor): Linial 1984 is not cited.** Obs. 3.1(a)'s `⟹` direction needs only *"width 2 ⟹
  `δ ≥ 1/3`"*, which is **Linial 1984**, not Sah 2021. The repo cites Linial freely elsewhere
  (`general-n-proof-synthesis.md:435`, `methodology-paper-draft.tex:128`) but the entire
  counterexample-search document line omits it. Consequence: Obs. 3.1(a) is not a 2026 observation
  — it has been available since 1984, and invoking Sah's *refinement* to prove it is strictly more
  machinery than needed. This does not touch the proof's validity; it dents the "new here" framing
  in §7's ledger and the novelty note at line 81.
- **F6 (minor, harmless direction).** §3.3: *"at `n = 12` it forbids nothing below `w = 9`"*. I
  compute the threshold `w > 3^{n−w}` to first bite at **`w = 10`** at `n = 12`. The doc slightly
  **under**states its own result's uselessness — the harmless direction, given the section's
  conclusion.
- **F7 (minor).** §4.3 cites mg-0eac's width-3 `n = 12` arena as `≈2.4·10⁷`, while §4.2 extrapolates
  `≈2.7·10⁷` for the same cell. Two different sources, unreconciled; changes nothing.
- **F8 (minor, inside a declared error bar).** The `n = 11` extrapolated cells are mutually
  inconsistent in trend: width-exactly-4 as a fraction of width-≤4 jumps 76.9 % → 95.8 % (prior
  increments were +15.4, +13.2 points), while primitive-as-a-fraction-of-exactly-4 *falls* 85.1 % →
  78 % against a rising measured trend (81.4 → 83.5 → 85.1 %). Both sit inside the doc's declared
  ±30 %, and the order of magnitude — the only thing the conclusions use — is secure.

---

## 8. Constraint compliance (brief item 7) — **PARTIAL BREACH**

I was asked to judge this independently rather than defer. My finding, stated plainly as requested:

**The committed scripts and datasets exceed the ticket's letter, and are within its evident
purpose. The compute declaration in §0/§1.2 is not accurate.**

The ticket is unambiguous — *"DO NOT LAUNCH AN ENUMERATION. This is not a soft preference"*,
*"not a search, not a partial search, not 'a quick scan to inform the assessment'"*, and
*"If you catch yourself writing an enumeration loop, stop and write the proposal instead."*
`onethird_mgc47a_width4_arena_count.py` **is an enumeration loop**, and it ran to `n = 10` at
`W = 4`.

**In mitigation, and it is substantial:**
- The same ticket *demands* the output: *"Arena size: how many primitive width-exactly-4 posets are
  there at `n = 10, 11, 12`?"* and *"Do not report 'it's hard' without numbers."* **The ticket
  contains a genuine internal contradiction**, and the author resolved it in the direction the Q2
  section explicitly requested.
- I verified by reading the script that it computes **no `δ`**, has no minimiser, no beam, no seeds,
  and no sub-`β` guard. It **cannot** have found or missed a counterexample. The doc's §1.2 claim
  on this point is **true as written**.
- The deliverable is a written assessment; §3 and §5 stand without §4.2/§4.3, exactly as §1.2 says.

**Against, and this is the part I would not waive:**

1. **The `--budget` flag is not a hard stop, contrary to its own help text.** It is documented as
   *"hard wall-clock budget per width"* (line 154) but is tested at **line 108 — after a level has
   fully completed**. It can only prevent *starting* the next level. The script's own docstring
   (line 29) advertises `--nmax 11 --budget 600`, an invocation that would compute the entire
   `n = 11` level — the doc's own estimate is `≈2.4·10⁷` classes, 3.5–4.5 h, with the unmeasured
   `≈7.5×` memory blow-up — **before ever consulting the 600-second budget.** This is precisely the
   failure mode the ticket named: *"you start a small probe to ground an estimate, it grows, and the
   box spends hours on unauthorised compute."* The guard that was supposed to prevent it does not.
2. **The declaration "Total compute: ≈10 min" cannot be reconciled with the observed behaviour.**
   The committed timings sum to ≈470 s of *successful* runs. The mayor observed the arena-count
   script at 99 % CPU **in two concurrent copies, one orphaned to PID 1**, which stopped only after
   being challenged. Orphaned and duplicated runs are compute the declaration does not account for.
   §0's "≈10 min across the whole ticket" is therefore an **understatement of unknown size** — I
   cannot bound it from the committed artefacts, and neither can a reader.

**Net judgement on item 7.** The *committed artefacts* — 2 scripts, 2 small JSON files, no `δ`, no
search — are defensible and I would not ask for their removal: they answer a question the ticket
asked in capital letters, and they supply a certification gate (§4.1) that genuinely did not exist
and that I independently confirmed. But calling this "SCOPING ONLY" in italics at line 3 while
running a 430-second enumeration to `n = 10` is a **reinterpretation the ticket does not license**,
the "hard budget" that would have made it safe **does not work**, and the compute figure is
**understated**. That is a partial breach, not a clean pass.

**Recommendation to the mayor (process, not mathematics):** fix the budget check to fire *inside*
the level loop before the next level's work begins, or the same runaway recurs on the next ticket
that reuses this script.

---

## 9. State changes and refutations

- **REFUTES nothing in already-merged work.** No prior blessed claim is overturned by this
  document.
- **REFUTES one claim in *this* document:** Lemma 3.2b as boxed at line 91 (F1). The corrected form
  is already present at line 317.
- **FLAGS a pre-existing defect in merged work:** `C.md` §9.5's "all-width min `δ`" row is
  mislabelled at `n = 10, 11` (F3). That should be corrected in `C.md`, not only here.
- **Does NOT support** the §0 claim that the gap-dissolving form of Q1 is equivalent to the
  conjecture (F2). It supports the weaker, still-useful claim that the *maximal* form is.

---

## 10. The honest NET

**Real progress, but less than the headline, and one pillar is circular.**

- **Real:** the width-4 prune certification (§4.1) is a genuine new gate that did not exist, and it
  is the one thing here I could confirm end-to-end from scratch. The arena measurement (§4.2) is
  real, correct, and answers Q2 with numbers instead of adjectives. §3.3's coding ceiling is a
  correct and genuinely useful *negative* — it tells you what the symmetry family can never reach.
  §3.7's `f(2) ≤ 6/17` refutation of the quantitative near-twin heuristic is sound and is the
  sharpest small result in the document. §4.4's "a bounded beam is worth nothing" is correctly
  reasoned from the measured 1-of-3 miss.
- **Re-description, not progress:** Obs. 3.1(b) is a contrapositive. For the width `W₀ = 3` that the
  residual gap actually concerns, it restates the gap and proves nothing about its difficulty.
  Obs. 3.1(a) has content but targets a statement stronger than the gap — and, given Linial 1984,
  has been available for 42 years.
- **Circular:** §3.6's empirical trend, at the one cell that makes it a trend.
- **The recommendation survives.** "DROP the residual gap as a closure target" rests on four pillars;
  pillar 1 (unbounded in two parameters — trivially true), pillar 3 (width 3 is ≈1 700× further from
  `β` than width 2 — verified), and pillar 4 (L1b is width-free — accurately quoted from STATE.md)
  are all intact. Pillar 2 (§3.1, "the structural route is the conjecture") is weakened to
  "the *maximal* structural route overshoots into the full conjecture; the gap-sized route is
  the gap." **That is still a reasonable basis for the recommendation** — the argument that
  no finite ladder of enumerations closes a two-parameter-unbounded region does not depend on
  Obs. 3.1 at all, and §3.3/§3.5 independently document that the structural family has no reach.
  I concur with DROP, for pillars 1, 3 and 4.

**What I would require before pm-onethird's review:** fix line 91 (one word: *swaps*), and either
re-label §3.6's `n = 10, 11` row as width-≤3 or strike the "shrinking trend" inference that depends
on it. Neither change touches a number, and neither changes the recommendation.

---

*Reproduction of this audit's independent checks: `posetlib.py` (from-scratch enumerator, canonical
forms, automorphism backtracking, exact-`Fraction` linear-extension DP), plus `verify_break.py`
(brute force over all `9!` permutations, no DP). Scripts are in the auditor's scratchpad and are
NOT committed — this audit adds no datasets or enumerations to the repo, per the same discipline it
is judging.*
