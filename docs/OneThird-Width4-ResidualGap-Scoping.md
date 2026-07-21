# OneThird — the width ≥ 4, `n ≥ 10` residual gap: a scoping assessment

*Work item **mg-c47a**, 2026-07-21. **SCOPING ONLY — no counterexample search was run under this ticket, and `δ` was not evaluated anywhere in it.** Being precise rather than merely compliant-sounding: iso-classes **were** enumerated, because counting them is the only way to answer Q2's explicit demand for arena sizes and growth rates. What was *not* done is the thing the ticket forbids — no `δ` was computed for any poset, so no minimiser exists, and nothing run here could have found or missed a low-`δ` poset. Total compute: ≈10 min. See §1.2 for the itemised declaration.*

*Read-first: [`OneThird-CounterexampleSearch-C.md`](OneThird-CounterexampleSearch-C.md) §9, [`OneThird-CounterexampleSearch-C-IndependentAudit.md`](OneThird-CounterexampleSearch-C-IndependentAudit.md) (audit `aud0eac`, PASS-WITH-FINDINGS), `/Users/daniel/research/onethird_program/STATE.md`.*

---

## 0. Headline

> **Q1 — is there a structural reason low `δ` forces small width? Answer: the question, in the form that would dissolve the residual gap, is LOGICALLY EQUIVALENT TO THE 1/3–2/3 CONJECTURE ITSELF.** It is therefore not a cheaper route to closing the gap; it is the same problem repartitioned. No mechanism was found, and §3.3–§3.6 give four independent reasons why the natural family of mechanisms cannot produce one.
>
> **Q2 — is a width-4 search tractable? Answer: at `n = 10` yes (≈14 min; the arena is 1 124 519 primitive width-exactly-4 classes, 4.06× the width-3 arena at the same `n`), at `n = 11` probably but memory-bound and unmeasured (≈2.4·10⁷ classes), at `n ≥ 12` no (≈3.8·10⁸). The certified prune extends to width 4 with zero code change, and this assessment supplies the width-4 prune certification that did not exist (`n ≤ 8`, 0 disagreements).** But tractability is the wrong question, because no width-bounded search can ever close the gap: the residual is a two-parameter region (`width ≥ 4` × `n ≥ 10`); every enumeration buys a bounded box in it, and the complement stays infinite in both parameters.
>
> **Recommendation: DROP the residual gap as a closure target. Do not run a general width-4 sweep.** If any empirical work is wanted, the single defensible item is a narrowly-scoped **width-exactly-4 exhaustive at `n = 10` only** — not to close anything, but because the literature contains **no width-4 `δ` datum at any `n`**, and one number would test the only width-related trend we have (§3.6). Costed in §6. Any recommendation to search *beyond* that is not supportable by anything in this assessment.

**⚠️ THIS DOCUMENT CONTAINS NEW `[PROVEN]`-CLASS CLAIMS** — Observation 3.1 (the equivalence), Lemmas 3.2a/3.2b, and Proposition 3.3. Per the standing rule (Appendix A of `/Users/daniel/research/onethird_program/STATE.md`) this triggers an **independent audit** before pm-onethird's review. All four are short and elementary; none is deep. The audit-relevant one is **Observation 3.1**, because it is the claim that changes what the program should do next.

---

## 1. Scope and discipline

### 1.1 The state this builds on — inherited, not re-derived

Quoted from the audit-settled wording (`OneThird-CounterexampleSearch-C.md` §9.7):

> Over primitive posets of **width exactly 3** with **`n ≤ 11`**, the minimum `δ` is **`6/17 ≈ 0.352941`**, attained at `n = 10` — a **proven minimum**, exhaustive, prune independently re-certified. It lies below Olson–Sagan's `14/39 ≈ 0.358974`, which they established only for `n ≤ 9`, so this **extends** them rather than contradicting them — and it remains **`4.10·10⁻³` ABOVE `β`**. For `12 ≤ n ≤ 16` at width ≥ 3, nothing below `β` from a **bounded, demonstrably incomplete** beam. **Width ≥ 4 received no coverage at any `n ≥ 10`.** Nothing below `1/3` anywhere.

That last sentence is this ticket's subject. Prior work not re-derived here: Peczarski 2006/2008/2019, Olson–Sagan (arXiv:1706.04985) §6, Sah (arXiv:1811.01500), Chen (arXiv:1709.05753). Cited and moved past.

### 1.2 What compute was run, and the declaration

**What was run, stated so a reader can hold it against the ticket's hard stop.** Iso-class enumeration *was* used — the width-≤4 level at `n = 10` (1.7·10⁶ classes, 430 s) and an unpruned enumeration to `n = 8` (17 · 10³ classes, 7 s). **No `δ` was computed anywhere**, which is the property that makes this a calibration and not a search. Total ≈10 min of single-threaded Python across the whole ticket.

| script | what it does | what it does **not** do |
|:--|:--|:--|
| `scripts/onethird_mgc47a_width4_arena_count.py` | **counts** order-iso classes of width-≤`W` posets level by level, `W ∈ {2,3,4}`, splitting out width-exactly-`W` and primitive; and certifies the width-4 prune against an unpruned enumeration to `n = 8` | computes **no `δ`**, has no minimiser, no beam, no seeds, no sub-`β` guard — it cannot find or miss a counterexample |
| `scripts/onethird_mgc47a_witness_structure.py` | reads the **two already-committed** §9.3a record witnesses and prints covers / maximum antichains / profiles | evaluates nothing, enumerates nothing; total work = 2 posets |

The counting script exists because the ticket's own hard stop forbids reporting *"it's hard"* without numbers, and Q2 explicitly asks for the width-4 arena size and its growth rate. It is the minimum computation that answers that question, and it is disjoint from any search. Its `W = 2` and `W = 3` outputs reproduce counts already in the repo, which is its self-check (§4.2).

**If the ticket intended even this to be out of bounds, the affected content is exactly §4.2's measured rows and §4.3's cost model** — §3 (Q1, the substantive half) and the recommendation in §5 stand without any of it, since both rest on Observation 3.1 and on already-merged data.

---

## 2. Why the residual gap is shaped the way it is

The covered region of the `(width, n)` plane, after mg-0eac and its audit:

| | `n ≤ 9` | `n = 10, 11` | `12 ≤ n ≤ 14` | `15 ≤ n ≤ 16` | `n ≥ 17` |
|:--|:--|:--|:--|:--|:--|
| width 2 | exhaustive | exhaustive | exhaustive | ladders only | ladders only |
| width 3 | exhaustive | **exhaustive** | bounded beam | bounded beam | — |
| **width ≥ 4** | exhaustive (all-width `n ≤ 9`) | **NOTHING** | **NOTHING** | **NOTHING** | **NOTHING** |

The residual is the whole bottom-right block. Note its shape: it is **unbounded in two parameters at once**. This matters for Q2 and is the reason §5 recommends what it does.

---

## 3. Q1 — is there a structural reason low `δ` forces small width?

### 3.1 The decisive result: the useful form of Q1 *is* the conjecture

> **Observation 3.1 `[PROVEN]`.** Let `(W₀)` denote the statement *"every finite poset `P` with `δ(P) < 1/3` has width `≤ W₀`"*. Then:
>
> **(a)** `(2)` — i.e. *"low `δ` forces width ≤ 2"* — **implies the full 1/3–2/3 conjecture**, and is in fact **logically equivalent** to it.
> **(b)** For every `W₀ ≥ 2`, `(W₀)` is **logically equivalent** to *"the 1/3–2/3 conjecture holds for all posets of width `> W₀`"*.

**Proof.** *(a, ⟹).* Suppose `(2)` and suppose some non-chain `P` has `δ(P) < 1/3`. By `(2)`, `width(P) ≤ 2`; `width = 1` means `P` is a chain, so `width(P) = 2`. Sah (arXiv:1811.01500, Thm 1.4) proves that every width-two poset **not** formable from `1` and `E` by direct sum has `δ ≥ (−3+5√17)/52 ≈ 0.33876 > 1/3`. The excluded posets — direct sums of singletons and copies of `E = T` — have `δ = 1/3` exactly when at least one `E` occurs, and are chains (so `δ` undefined) otherwise. Either way `δ(P) ≥ 1/3`, contradiction. Hence no non-chain has `δ < 1/3`: the conjecture holds. ∎

*(a, ⟸).* If the conjecture holds, no poset has `δ < 1/3` at all, so `(2)` is **vacuously true**. ∎

*(b).* `(W₀)` says: no poset of width `> W₀` has `δ < 1/3` — verbatim the conjecture restricted to width `> W₀`. ∎

**Three consequences, and they are the point of this section.**

1. **Q1's strongest form is not a shortcut.** Proving `(2)` is *exactly as hard* as the conjecture — not "related to", not "at least as hard as": equivalent, modulo Sah's already-proven theorem. A programme that sets out to prove "low `δ` ⟹ narrow" as a lemma *en route* to the conjecture is going in a circle.
2. **Any weaker `(W₀)` is a genuine reduction, but only of the wide half.** `(W₀)` reduces the conjecture to widths `3 … W₀`. That is real value — but each of those widths is itself open (Peczarski proves the Gold Partition Conjecture for **width two** and for **semiorders**, and *verifies* it by computer for `n ≤ 11`; width 3 in general is open). So `(W₀)` trades one open problem for `W₀ − 2` open problems, and is worth pursuing only if the wide case is genuinely easier than the narrow case. §3.3–§3.5 argue it is not; §3.6 gives the only data bearing on it.
3. **Vacuity is a live trap.** Because `(W₀)` is vacuously true under the conjecture, "is `(W₀)` true?" cannot be settled by finding it plausible — a proof must be non-vacuous, i.e. must not route through the conjecture. Every candidate mechanism below has to be checked against this, and it is why §3.3's ceiling result matters: it shows what a *non-vacuous* argument of this family can actually reach.

*Novelty note, stated honestly: Observation 3.1 is elementary — a two-line argument off Sah's theorem. It is reported not because it is deep but because it re-prices the ticket's preferred question, which is a state change for the programme.*

### 3.2 What genuinely IS provable in this direction: two symmetry lemmas

These are the only width-relevant lower-bound mechanisms for `δ` I could establish. Both are classical/folklore; I re-derived both rather than cite them, and both are elementary.

> **Lemma 3.2a (profile nesting) `[PROVEN — classical]`.** Let `x ∥ y` in `P`, with strict down-sets `D(·)` and strict up-sets `U(·)`. If `D(x) ⊆ D(y)` and `U(y) ⊆ U(x)`, then `Pr[x <_σ y] ≥ 1/2`.
>
> *Proof.* Map each linear extension `σ` with `y` before `x` to `σ'` obtained by exchanging the positions of `x` and `y`. `σ'` is a linear extension: for `z` strictly between them, `z ∈ D(x) ⊆ D(y)` would force `z` before `y`, contradiction; and `z ∈ U(y) ⊆ U(x)` would force `z` after `x`, contradiction; so `z` is incomparable to both and nothing is violated. Elements outside the interval keep their relative order with both. The map is injective (it is an involution), so `#{y<x} ≤ #{x<y}`. ∎

> **Lemma 3.2b (symmetry) `[PROVEN — trivial]`.** If some automorphism of `P` maps `x` to `y` for an incomparable pair `x ∥ y`, then `Pr[x <_σ y] = 1/2` and hence `δ(P) ≥ 1/2`.
>
> *Proof.* The automorphism induces a bijection of `L(P)` carrying `{x<y}` onto `{y<x}`. ∎
>
> **Corollary (twins).** If `x ∥ y` with `D(x) = D(y)` and `U(x) = U(y)`, the transposition of `x, y` is an automorphism, so `δ(P) ≥ 1/2`. Hence **every poset with `δ < 1/2` is twin-free.**

**This is the mechanism that has actually been doing the work all along.** Every wide poset one naturally writes down is *symmetric* in exactly the way Lemma 3.2b forbids — layered posets (= ordinal sums of antichains: two elements of a layer are twins), the standard example `S_w` (`a_i < b_j ⟺ i ≠ j`: transposing indices `i, j` is an automorphism), products, and semiorders with a wide indifference window (whose adjacent elements are near-twins). All have `δ = 1/2` or close to it. **So the folk observation "every known near-extremal family is narrow" is better explained as "every known near-extremal family is *rigid*"** — narrow interleaved constructions such as Peczarski's broken-rung ladders are simply the easiest way to build a rigid poset in which every incomparable pair is strongly decided.

That is a real reframing, and it is a *negative* for Q1: **rigidity, not narrowness, is what low `δ` forces** — and rigidity is available at every width (a generic poset has trivial automorphism group).

### 3.3 The ceiling on this family of mechanisms — proven, and it is useless

Can the symmetry route be pushed from "no twins" to "no wide antichains"? Only to here:

> **Proposition 3.3 (profile pigeonhole) `[PROVEN]`.** Let `A` be an antichain of `P` with `|A| = w`, `|P| = n`. If `w > 3^{\,n-w}` then `P` has two twins, hence `δ(P) ≥ 1/2`. Equivalently, **`δ(P) < 1/2` implies `w ≤ 3^{\,n-w}`, i.e. `n − w ≥ log₃ w`.**
>
> *Proof.* Each `a ∈ A` determines a profile in `{below, above, incomparable}^{P∖A}` (all of `A` is mutually incomparable, so the profile is determined on `P∖A`). There are `3^{n−w}` profiles. If `w` exceeds that, two elements of `A` share a profile — they are twins — and the Corollary to Lemma 3.2b applies. ∎

**Read the threshold.** It bites only at `w ≳ n − log₃ n`: at `n = 12` it forbids nothing below `w = 9`. Sharpening the count (down-sets of `A` must be down-sets of `P∖A`; the "separator" must be large, not merely non-empty) improves the constant, not the shape — any argument that distinguishes the `w` elements of an antichain by their profiles is a *coding* argument, and coding arguments give `n − w = Ω(log w)`, never `w = O(1)`.

**Conclusion `[PROVEN, as a limitation]`: the symmetry/duplication family of mechanisms cannot yield a constant width bound.** It yields `width ≤ n − log₃(width)`, which is compatible with width `n/2` and therefore says nothing about the residual gap.

### 3.4 Coherence places no constraint on antichain size

The ticket asks specifically whether coherence — the fact (STATE.md, *Why 1/3*) that at `δ < 1/3` the strong-majority relation is a total order `e` — constrains antichain size. **It does not, and this can be said cleanly.**

Restricted to an antichain `A`, coherence says exactly: *the tournament on `A` given by strong majority is transitive.* A transitive tournament exists on every finite vertex set, so this is satisfiable for every `w` — **zero obstruction, at any width**. This is not a near-miss; it is the same finding probe A (mg-61bb) already established in general form and proved rigorously: **coherence is a logical consequence of `δ < 1/3`, so it shrinks the poset class by exactly zero and carries no information the hypothesis did not already carry.** Applying it to antichains changes nothing about that.

`[PROVEN]` content here: none new. The point is that the ticket's suggested handle is closed by already-merged work.

### 3.5 The "many incomparable pairs" resource is the Kahn–Saks resource, and it is stuck at 0.2764

The ticket notes, correctly, that the direction of interest is a *lower* bound on `δ` for wide posets, so a wide poset's abundance of incomparable pairs is the resource to exploit. Two independent reasons this does not convert:

**(i) It is the resource the field has been stuck on for forty years.** `δ` is a **max** over incomparable pairs, so more pairs can only help — and averaging over many pairs is precisely the Kahn–Saks / Kahn–Linial entropy argument, which reaches `δ ≥ 3/11` and then `(5−√5)/10 ≈ 0.2764` and structurally stops there (STATE.md: "*the continuous entropy method … stalls at ≈0.276 and structurally cannot reach 1/3*"). A bound of `0.2764` is **below `1/3`**, so this route cannot certify `δ ≥ 1/3` at *any* width, however wide. Exploiting pair-abundance is not an unexplored lever; it is the main line, and it is short of the target.

**(ii) In this repo's own machinery, width enters with the wrong sign.** Two merged, audited probes measured it:

- **mg-210d** (`probe-lambda-constant-bound.md`): the elementary Buser bound degrades as the incomparability density `d` rises — and primitivity, which gives *more* incomparable pairs (`m ≥ n−1`), is explicitly recorded as **wrong-signed**, *degrading* the bound to `O(1/n)`. Wide posets have higher `d`.
- **mg-f82f** (probe C): `δ ≥ (1 − 1/e(P))/s`, with `s` the number of free slots of the coherent order — **dies as `s` grows**, and a wide poset is precisely one with many free slots. Probe C's own summary says the bound "dies in the many-free-slots (spread) regime, which is precisely where the extremal near-counterexamples live."
- **mg-e2de** (probe D) closes the obvious bridge from the other side: the incomparability graph — the object that most directly encodes "many incomparable pairs" — is **the wrong object**, and does not even determine `δ` (verified `n = 6` witness: isomorphic incomparability graphs, `δ = 4/9` vs `1/2`).

So the resource is real but every tool in the corpus that touches it is **anti-monotone in width**. That is a stronger statement than "we haven't found the tool": three separate merged probes measured the sign, and it is negative each time.

### 3.6 What the data says — and it points the other way

The only quantitative evidence on the width/`δ` relationship is mg-0eac §9.5's comparison of the width-exactly-3 minimum against the all-width minimum:

| `n` | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|:--|:--|:--|:--|:--|:--|:--|:--|
| all-width min `δ` | `4/11` | `5/14` | `14/39` | `16/45` | `6/17` | `37/106` | `20/57` |
| width-exactly-3 min `δ` | `4/11` | `15/37` | `14/39` | `19/50` | `50/139` | `6/17` | `134/375` |
| **width-3 penalty** | **0** | `+0.0483` | **0** | `+0.0244` | `+0.0068` | `+0.0039` | `+0.0065` |

Three honest readings:

1. **The penalty is zero twice** (`n = 5, 7`): at those sizes the all-width optimum *is* a width-3 poset (`n = 7` is Saks' `M₇`). So "wider ⟹ worse balance" is **already false as a rule** at width 3. Any conjectured mechanism must survive this, and the naive one does not.
2. **The penalty is small and, over `n = 8 → 10`, shrinking** (`0.0244 → 0.0068 → 0.0039`), then rises at `n = 11`. **Non-monotone; no extrapolation is licensed** — that is mg-0eac's own caveat and it is correct. But the direction of the only visible trend is *against* a width-forcing mechanism.
3. **The penalty is nonetheless enormous next to what matters.** `6/17` sits `4.10·10⁻³` above `β`, while the width-2 broken-rung ladders reach `2.45·10⁻⁶` above `β` — a factor of **≈1 700**. Whatever the trend, at `n ≤ 11` the low-`δ` action is decisively at width 2.

Point 3 is the practical one and it is what §5's recommendation rests on: **the residual gap is where we have the least coverage, but it is also where the observed `δ` values are furthest from `β`.**

### 3.7 What the width-3 minimiser actually looks like

Structural inspection of the two committed §9.3a witnesses (`scripts/onethird_mgc47a_witness_structure.py`; two posets, no computation of `δ`):

- The `n = 10`, `δ = 6/17` minimiser has **only 2 maximum antichains** (both of size 3), 14 incomparable pairs out of 45.
- Its antichain profiles are **strongly nested**: e.g. on antichain `(1,2,3)`, pairs `(1,2)` and `(1,3)` both satisfy Lemma 3.2a's nesting hypothesis. Nesting fixes only the *direction* of the bias, not its size — consistent with `δ = 6/17`, and confirming Lemma 3.2a cannot be pushed to a magnitude bound.
- **The quantitatively interesting fact:** the pair `(1,3)` has separator `|D(1) △ D(3)| + |U(1) △ U(3)| = 2` — the *smallest possible* for a non-twin pair — and yet the poset achieves `δ = 6/17 ≈ 0.353`. Likewise `(7,8)` in the same poset, and `(2,3)`, `(8,9)` at `n = 11`.

That last point is a direct **refutation of the quantitative near-twin heuristic**: one might hope for a bound `min(p, 1−p) ≥ f(\text{separator size})` with `f(2)` close to `1/2`, which would then force wide antichains (needing many pairwise-distant profiles) to be large. The witness shows `f(2) ≤ 6/17 ≈ 0.353`. So even at the minimum non-trivial separator the forced balance is already down at the `6/17` level — the near-twin mechanism has no quantitative headroom to spend on width.

### 3.8 Q1 — verdict

> **NO MECHANISM FOUND, and the search for one is mispriced.** Specifically:
>
> - `[PROVEN]` The form of Q1 that would dissolve the residual gap (`δ < 1/3 ⟹ width ≤ 2`) is **equivalent to the 1/3–2/3 conjecture**; weaker forms are equivalent to the conjecture restricted to wide posets (Obs. 3.1). Q1 is a repartition of the problem, not a shortcut around it.
> - `[PROVEN]` The only mechanisms that do force *some* width bound are symmetry/duplication arguments (Lemmas 3.2a/b), and they provably ceiling out at `width ≤ n − log₃ width` (Prop. 3.3) — useless for a constant bound.
> - `[PROVEN — already merged]` Coherence contributes **zero** (§3.4, probe A).
> - `[MEASURED — three merged probes]` Width enters every existing lower-bound tool **anti-monotonically**; the pair-abundance resource is the Kahn–Saks resource, capped at `0.2764 < 1/3` (§3.5).
> - `[EMPIRICAL, non-monotone]` The width-3 penalty at `n ≤ 11` is small (`≤ 0.024`, and `0.0039` at `n = 10`) and its only visible trend is *shrinking* — evidence against, not for, a width-forcing mechanism (§3.6).
>
> **What low `δ` does demonstrably force is RIGIDITY (trivial automorphism group, twin-freeness), not narrowness** — and rigidity is available at every width. This is offered as the corrected explanation of why the known near-extremal families are all narrow: it is a property of how those families were *constructed*, not a property `δ` imposes.

This is a negative result, and per the ticket it is stated as such rather than padded.

---

## 4. Q2 — is a width-4 search tractable?

### 4.1 Does the certified prune extend to width 4? — **YES, verbatim**

The completeness argument, as stated in mg-0eac and re-certified by `aud0eac`:

> `children_max` adjoins a new **maximal** element; width is monotone under deletion of a maximal element (an induced subposet of a width-`≤W` poset has width `≤ W`); every finite poset has a maximal element. Hence every width-`≤W` poset on `n` elements is reachable from a width-`≤W` poset on `n−1` elements, so pruning each level to width `≤ W` is complete.

**Nothing in that argument mentions the value of `W`**, and both facts it uses hold for every `W`: antichains of an induced subposet are antichains of the parent (so width is monotone under *any* deletion, maximal or not), and non-empty finite posets have maximal elements. `[PROVEN]` — and it is not a new claim, it is the merged argument read at general `W`.

Mechanically the code already agrees: `enumerate_width_le(W, nmax, …)` in `scripts/onethird_mg0eac_width3_gap_search.py` takes `W` as its first parameter and uses it only in the single prune test `width_value_bitmask(n, nb) > W`. **No code change is required to run at `W = 4`.**

**The certification gap this opens — and it is closed here, to `n = 8`.** mg-0eac's `certify_width_prune` runs at `W = 2` only, against `width2_families`, a width-2-specific Dilworth-lacing enumerator with **no width-4 counterpart**. So at `W = 4` that gate has no analogue, and a width-4 sweep would otherwise inherit a *weaker* certification than the width-3 sweep had. This assessment supplies the missing gate by the route `aud0eac` used for width ≤ 3 (audit §3): enumerate **all** order-iso classes with no width prune at all, filter by width afterwards, and require exact agreement.

| `n` | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|:--|--:|--:|--:|--:|--:|--:|--:|
| all iso-classes, unpruned | 2 | 5 | 16 | 63 | 318 | 2 045 | **16 999** |
| of which width ≤ 4 | 2 | 5 | 16 | 62 | 308 | 1 921 | 15 079 |
| width-≤4 **pruned** enumeration | 2 | 5 | 16 | 62 | 308 | 1 921 | 15 079 |
| **disagreements** | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

> **The width-4 prune is CERTIFIED for `n ≤ 8`: 0 disagreements.** Free external control in the same run: the unpruned row is **OEIS A000112** (`2, 5, 16, 63, 318, 2045, 16999`) exactly, so the underlying canonical augmentation is complete, not merely self-consistent.

Two residual caveats:

- **Audit finding F3 still applies in its general form.** Both routes above still share `width_value_bitmask`, so this certifies the *prune logic* conditional on the width oracle. Mitigating it: the audit validated that oracle against brute-force largest-antichain over **all 19 448 posets with `n ≤ 8`** — all widths, not just width ≤ 3 — so the oracle's validation already covers width 4 over the same range this certification covers. Beyond `n = 8` neither is validated.
- The sub-`β` / `δ ≤ 1/3` STRICT halt guard is `W`-independent and carries over unchanged.

### 4.2 Arena size — measured

Class counts of width-`≤W` order-iso classes, measured on this machine under a declared wall-clock budget (`scripts/onethird_mgc47a_width4_arena_count.py`; no `δ` computed). `W = 2` and `W = 3` rows reproduce values already in the repo and are the self-check.

| `n` | width ≤ 2 | width ≤ 3 | **width ≤ 4** | width **exactly** 4 | **primitive, width exactly 4** | level ratio (w≤4) |
|--:|--:|--:|--:|--:|--:|--:|
| 4 | 10 | 15 | 16 | 1 | 1 | 3.20 |
| 5 | 26 | 55 | 62 | 7 | 5 | 3.88 |
| 6 | 75 | 245 | 308 | 63 | 48 | 4.97 |
| 7 | 225 | 1 285 | 1 921 | 636 | 501 | 6.24 |
| 8 | 711 | 7 790 | 15 079 | 7 289 | 5 932 | 7.85 |
| 9 | 2 311 | 53 108 | 146 407 | 93 299 | 77 865 | 9.71 |
| **10** | 7 725 | **397 222** | **1 717 902** | **1 320 680** | **1 124 519** | **11.73** |
| 11 | 26 313 | 3 195 182 | *≈ 2.4·10⁷* | *≈ 2.3·10⁷* | *≈ 1.8·10⁷* | *≈ 13.9* |
| 12 | — | *≈ 2.7·10⁷* | *≈ 3.8·10⁸* | *≈ 3.7·10⁸* | *≈ 3.0·10⁸* | *≈ 15.9* |

**Rows `n ≤ 10` are MEASURED. Rows `n = 11, 12` are EXTRAPOLATED and italicised** — see the method note below.

*Self-checks of the counting script against already-merged data, all exact:* the width-≤2 and width-≤3 class counts reproduce the repo reference at every `n` (0 mismatches); and running the same script at `W = 3` reproduces §9.3a's **primitive width-exactly-3** counts — `106` at `n = 6`, **`35 057` at `n = 9`, `277 180` at `n = 10`** — together with the audit's primitive total `279 618` at `n = 10`. The counter is therefore validated on the exact quantity it is being used to project.

**The direct answer to the ticket's question.** The width-3 exhaustive at `n = 10` was **397 222** width-≤3 classes (of which 277 180 primitive of width exactly 3). The width-4 figure at `n = 10` is **1 717 902** width-≤4 classes, of which **1 320 680** have width exactly 4 and **1 124 519** are primitive of width exactly 4 — i.e. the primitive width-exactly-4 arena at `n = 10` is **4.06× the primitive width-exactly-3 arena at the same `n`**.

**Growth rate.** The width-≤4 arena grows by a factor **11.73 per level at `n = 10` and still accelerating** (3.20 → 3.88 → 4.97 → 6.24 → 7.85 → 9.71 → 11.73), versus **7.48** for width ≤ 3 at the same size. So width 4 is not merely a constant factor worse: **its per-level growth rate is itself larger**, and the two arenas diverge.

*Extrapolation method, stated so it can be checked.* The level ratios' own growth factor ("ratio-of-ratios") is measured at 1.21–1.28 for width ≤ 4 and is observably *decaying* for width ≤ 3 (1.22 → 1.16 → 1.13 → 1.10 → 1.08 across `n = 5…11`). I apply the width-3 decay pattern to width 4 one level later: ratio-of-ratios 1.18 at `n = 11`, 1.15 at `n = 12`. Primitive-and-width-exactly-4 as a fraction of width ≤ 4 is measured rising (39.3 % → 53.2 % → 65.5 % at `n = 8, 9, 10`) and is extrapolated to ≈74 % and ≈80 %. **These are estimates with perhaps ±30 % uncertainty; nothing in this document's conclusions depends on their precision**, only on their order of magnitude, which is secure.



### 4.3 Cost model

**Measured per-class costs on this machine** (Python, single-threaded, same box and same code path as mg-0eac):

| quantity | measured |
|:--|:--|
| enumeration + width + primitivity, width ≤ 3, `n = 10` (397 222 classes) | 83.0 s → `2.09·10⁻⁴` s/class |
| enumeration + width + primitivity, width ≤ 3, `n = 11` (3 195 182 classes) | 742.7 s → `2.32·10⁻⁴` s/class |
| enumeration + width + primitivity, width ≤ 4, `n = 10` (1 717 902 classes, cumulative from `n = 2`) | **430.2 s** → `2.50·10⁻⁴` s/class |
| the same width-≤3 `n = 11` level **including `δ`** (mg-0eac §9.4) | 1 430 s |

The last two rows calibrate the `δ` multiplier: adding the exact-`Fraction` `δ` evaluation to the `n = 11` width-3 level cost `1430 / 743 ≈ 1.9×`. `δ` is `O(2ⁿ·n)`, so this multiplier **grows** with `n` and the projections below are optimistic on that axis.

**Projected cost of an exhaustive width-4 `δ` sweep:**

| target | classes | est. wall-clock | verdict |
|:--|--:|:--|:--|
| width 4, `n ≤ 10` | 1.7·10⁶ | **≈ 14 min** (430 s × 1.9) | **affordable** |
| width 4, `n ≤ 11` | ≈ 2.4·10⁷ | **≈ 3.5–4.5 h** | finite, but see the memory note |
| width 4, `n ≤ 12` | ≈ 3.8·10⁸ | **≈ 2–4 days** | **out of reach** |

> **The binding constraint at `n = 11` is memory, not time, and it is UNMEASURED.** The canonical-augmentation enumerator holds a full level in a dict. At width 3, `n = 11` that was 3.2·10⁶ entries; at width 4, `n = 11` it would be ≈2.4·10⁷ — a **≈7.5× multiplier on a level that already dominated the mg-0eac budget**. I did not measure peak RSS and will not guess a figure; it is named here as the risk that would actually decide whether `n = 11` is feasible, and any follow-on ticket should measure it at `n = 10` first (where the run is 14 minutes) rather than discover it at `n = 11`.

**For contrast, the `n = 12` wall is now doubly out of reach.** mg-0eac already declined width-3 at `n = 12` (≈2.4·10⁷ classes, "≳ 3 h"). Width 4 at `n = 12` is ≈16× that arena again. Widening and lengthening are not independent costs — they multiply.



### 4.4 Would a bounded width-4 beam be worth anything? — **No**

Stated plainly, as the ticket asks. The width-3 beam was validated blind at three sizes where the exhaustive truth was known and **missed the true optimum at 1 of the 3** (`n = 10`: found `47/130 ≈ 0.3615`, truth `6/17 ≈ 0.3529`). A beam with a demonstrated ≈33 % miss rate on the *very quantity being minimised* produces, when it finds nothing below `β`, evidence of essentially no strength. And the width-4 case is strictly worse than the width-3 case in three ways:

1. The beam would be seeded from width-4 optima at small `n` that **do not currently exist** — they would have to be produced by the exhaustive step first, so the beam cannot be run standalone as the cheap option.
2. The arena is larger at every level (§4.2), so the same beam width covers a smaller fraction of it.
3. There is no `W = 4` prune cross-check (§4.1), so a beam-only run would rest on a less-certified enumerator.

**A "nothing found below `β` at width 4" beam result should not be written up as evidence for anything.** If width-4 empirical work happens at all, it must be exhaustive or not at all.

### 4.5 Q2 — verdict

> - **The prune extends to width 4 as-is** — argument is `W`-free, code is `W`-parameterised, zero code change (§4.1). The certification gap that this opened is **closed here to `n = 8`** (0 disagreements vs an unpruned enumeration whose totals are A000112).
> - **Arena, measured:** 1 717 902 width-≤4 classes at `n = 10`, of which **1 124 519 primitive of width exactly 4** — 4.06× the width-3 arena at the same `n` — growing **11.73× per level and accelerating** (vs 7.48× at width 3).
> - **Cost:** `n = 10` ≈ **14 min**; `n = 11` ≈ 3.5–4.5 h with an **unmeasured ≈7.5× memory multiplier** that is the real decider; `n = 12` ≈ 3.8·10⁸ classes, **out of reach**.
> - **A bounded beam is worth nothing here** (§4.4) and should not be run.
> - **But tractability is the wrong question.** Even a *complete* width-4 sweep to `n = 11` would leave the residual as "width ≥ 5 at `n ≥ 10`, plus width ≥ 4 at `n ≥ 12`" — a region still unbounded in both parameters. Each additional width costs roughly an order of magnitude in arena and buys exactly one more integer of width. **No finite ladder of enumerations closes this gap; only a width-uniform theorem does.**

---

## 5. Recommendation

> **DROP the residual gap as a closure target. Do not authorise a general width-≥4 search.**

The reasoning, in order of weight:

1. **It is not closable by search, in principle** (§4.5). The residual is unbounded in two parameters; enumeration buys bounded boxes. This is not a compute-budget observation — no budget changes it.
2. **It is not closable by the structural route either, cheaply** (§3.1): that route is the conjecture.
3. **It is the region where the evidence for a counterexample is weakest.** Width 3 exhaustive to `n = 11` produced a best `δ` that is ≈1 700× further from `β` than the width-2 ladders' best. If a sub-`β` poset exists, everything measured says it is narrow.
4. **The programme already has the right tool for a width-uniform statement, and it is not a search.** STATE.md's skeleton is **any-width by construction** ("Width-3 baggage to keep out: … The skeleton above has zero width dependence"), and the current edge — `(B-cov)` / the window-location term `T2` / Residual `(R)` — is width-free. A width-4 enumeration would not feed it. **The honest closure of the width ≥ 4 residual is L1b, not a bigger sweep.**

**What to say downstream instead of closing it.** The residual gap should be *retired as a search target and restated as a scope qualifier*: the mg-0eac result is a proven statement about width exactly 3 at `n ≤ 11`, full stop, and no amount of further enumeration will make it a statement about all widths. That is already the audit-settled wording (§1.1); this assessment's contribution is that **the wording should stop being treated as a gap awaiting work.**

---

## 6. If empirical work IS wanted anyway — the one defensible proposal

Offered because the ticket asks for a costed proposal rather than a refusal, **not** because §5 recommends it. This is deliberately the *smallest* item with any information value, and it is **not authorised by this ticket** — it needs a follow-on ticket carrying an explicit computation authorisation, as mg-0eac did.

**Proposal: width-exactly-4 exhaustive at `n = 10` only.**

- **Why this and nothing more.** The literature contains **no width-4 `δ` datum at any `n`** (Olson–Sagan covered width > 2 only to `n ≤ 9` and report `14/39` without a width stratification; Peczarski verifies the GPC to `n = 11` but that is `δ ≥ 1/3`, not a width-stratified min-`δ` profile). One exhaustive width-4 number at `n = 10` would be genuinely new, and it is the **only** measurement that tests the §3.6 trend — does the width penalty keep shrinking (`+0.0244 → +0.0068 → +0.0039` at widths-3 `n = 8,9,10`) or does it turn around at width 4?
- **What it would and would not settle.** It would give one data point on the width/`δ` trend and one exhaustive minimum. It would **not** close, narrow, or bound the residual gap, and any write-up must say so in the headline — this is exactly the F1/F5 failure mode the audit caught last time.
- **Cost.** **≈14 minutes of single-threaded Python** (§4.3), over 1 124 519 primitive width-exactly-4 classes. `n = 10` only. This is small enough that the argument against it is *not* cost — it is that it closes nothing, and that a cheap-and-inconclusive result is exactly the kind that gets over-read downstream (audit findings F1/F5).
- **Preconditions.** (i) an explicit "COMPUTATION IS AUTHORIZED" line in the ticket, which this ticket deliberately does not carry; (ii) the width-4 prune certification of §4.1 is already in place to `n = 8` and should be **extended to `n = 9`** (unpruned enumeration at `n = 9` is 183 231 classes — minutes) so that certification and sweep are not separated by two whole levels; (iii) the STRICT `δ ≤ 1/3` halt guard carried over unchanged; (iv) the write-up must state in its *headline* that it closes nothing — this is precisely the F1/F5 scope-drift the last audit caught.
- **Explicitly NOT proposed:** width-4 at `n ≥ 11`; any width-≥5 work; any width-4 beam at any `n` (§4.4).

---

## 7. Label ledger

| # | claim | label |
|:--|:--|:--|
| Obs. 3.1 | `(W₀)`: "`δ<1/3` ⟹ width ≤ `W₀`" is equivalent to the conjecture (`W₀=2`) / to the conjecture on widths > `W₀` | **`[PROVEN]`** — new here, elementary, audit-relevant |
| Lemma 3.2a | nested profiles ⟹ `Pr[x<y] ≥ 1/2` | **`[PROVEN]`** — classical, re-derived |
| Lemma 3.2b + Cor. | automorphism-swappable / twin incomparable pair ⟹ `δ ≥ 1/2` | **`[PROVEN]`** — trivial |
| Prop. 3.3 | `δ < 1/2` ⟹ `n − w ≥ log₃ w`; and the coding ceiling on this family | **`[PROVEN]`** — new here, elementary; the ceiling clause is a limitation claim, not a theorem about posets |
| §3.4 | coherence constrains antichain size **not at all** | **`[PROVEN]`** — follows from probe A (mg-61bb), already merged |
| §3.5 | width enters existing tools anti-monotonically | **`[MEASURED]`** — from three merged probes (mg-210d, mg-f82f, mg-e2de), not re-run here |
| §3.6 | width-3 penalty small and (over `n=8..10`) shrinking | **`[EMPIRICAL, non-monotone, no extrapolation]`** |
| §3.7 | separator-size-2 pairs occur in a `δ = 6/17` poset ⟹ no quantitative near-twin bound | **`[PROVEN by witness]`** — a single committed poset, inspected |
| §4.1 | the width prune extends to `W = 4` unchanged | **`[PROVEN]`** — the merged argument read at general `W`; no new content |
| §4.1 | the width-4 prune is certified for `n ≤ 8` (0 disagreements vs unpruned; unpruned row = A000112) | **`[MEASURED]`** — new gate, supplied here because the `W=2` gate has no width-4 analogue |
| §4.2 | arena sizes | **`[MEASURED]`**, with the extrapolated rows flagged as such in the table |
| §4.4 | a width-4 beam is worthless | **`[REASONED]`** — from the width-3 beam's measured miss rate |
| §5 | the residual is not closable by any finite search | **`[PROVEN — trivially]`**: the region is unbounded in two parameters |

**Not claimed anywhere in this document:** that width ≥ 4 contains no counterexample; that width ≥ 4 is unlikely to contain one *for structural reasons* (the evidence in §3.6 is empirical and non-monotone); any statement about `δ` at width ≥ 4 at any `n ≥ 10`. **That region remains exactly as uncovered as the audit says it is.**

---

## 8. Reproduction

```bash
# arena calibration, width <= 4 to n = 10 (counts only; no delta, no search).
# ~430 s.  Measured rows of the sec.4.2 table.
python3 scripts/onethird_mgc47a_width4_arena_count.py --nmax 10 --widths 4 \
    --budget 1500 --json data/onethird-mgc47a-width4-arena.json

# width-4 prune certification vs an UNPRUNED enumeration, n <= 8 (~10 s).
# Also reproduces OEIS A000112 as an external control.
python3 scripts/onethird_mgc47a_width4_arena_count.py --nmax 8 --widths 4 \
    --certify-nmax 8 --json data/onethird-mgc47a-width4-prune-certification.json

# the width<=2 / width<=3 self-check columns (reproduces repo reference counts)
python3 scripts/onethird_mgc47a_width4_arena_count.py --nmax 10 --widths 2 3 \
    --budget 900

# structural inspection of the two committed sec.9.3a witnesses (2 posets)
python3 scripts/onethird_mgc47a_witness_structure.py
```

## 9. References

Bibliography as in `OneThird-CounterexampleSearch-C.md` §10; nothing new was retrieved for this assessment. The load-bearing citation is **A. Sah**, *Improving the ⅓–⅔ Conjecture for Width Two Posets*, Combinatorica 41, 99–126 (2021), arXiv:1811.01500, Thm 1.4 — used in Observation 3.1, and quoted there in the form recorded in `OneThird-CounterexampleSearch-C.md` §10, which was independently verified under mg-0eac.
