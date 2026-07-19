# A direct count on the coherent reference order

**Work item:** mg-f82f (Entropy probe C).
**Scope:** self-contained and elementary. Nothing outside this note is used or cited.
**Verdict:** GREEN-technique-found. Coherence buys a real, quantified reduction —
the union bound runs over the `≤ n-1` *consecutive slots of the coherent order*
instead of over all `m` incomparable pairs. It yields `δ ≥ 1/2` at `s = 1`,
`δ ≥ 1/3` at `s = 2` (both tight), beats the 0.2764 record on part of `s = 3`,
and dies at `s ≥ 4` for a reason identified precisely in §7.

---

## 1. Setup

`P` a finite poset on `n` elements, not a chain. `L` a uniformly random linear
extension, `e(P) = |L(P)|`. `Inc(P)` is the set of incomparable pairs,
`m = |Inc(P)|`. For a pair `p = {x,y}`,

    q_p := min( Pr[x <_L y], Pr[y <_L x] ),      δ = δ(P) := max_{p ∈ Inc(P)} q_p.

Throughout we argue by contradiction and **assume `δ < 1/3`**. Everything in
§§2-6 is proven; §§7-8 separate what is proven from what is measured.

## 2. The coherent reference order (proven)

**Lemma 1.** If `δ < 1/3` there is a linear extension `e = a_1 < a_2 < ... < a_n`
of `P` such that `Pr[a_i <_L a_j] > 2/3` for all `i < j`.

*Proof.* For every pair `{x,y}` — incomparable or not — exactly one of
`Pr[x <_L y]`, `Pr[y <_L x]` exceeds `2/3`: for a comparable pair the larger is
`1`, and for an incomparable pair the smaller is `q_p ≤ δ < 1/3`. Write `x ≺ y`
for that orientation; `≺` is a tournament on `P`.

`≺` has no 3-cycle. If `x ≺ y ≺ z ≺ x` then
`Pr[x<y] + Pr[y<z] + Pr[z<x] > 2`. But for *any* linear order the indicators
`1[x<y] + 1[y<z] + 1[z<x]` sum to at most `2` (all three would be a cycle), so the
expectation is `≤ 2`. Contradiction.

A tournament with no 3-cycle is transitive, so `≺` is a linear order `e`. If
`x <_P y` then `Pr[x <_L y] = 1`, so `x ≺ y`; hence `e` extends `P` and is itself
a linear extension. ∎

This is the whole of the "coherence" input, and §4 shows exactly what it is worth.

## 3. The encoding

Fix `e`. For a linear extension `L` set

    inv(L) := { p ∈ Inc(P) : L orders p opposite to e }.

Only incomparable pairs can be inverted (`L` and `e` both extend `P`), and `L` is
determined by its full set of pairwise comparisons, so

**Lemma 2 (proven).** `L ↦ inv(L)` is injective, and `inv(L) = ∅ ⟺ L = e`.
Consequently `H(L) = H(inv(L))` and `log e(P) = H(L)`.

Write `q_p = Pr[p ∈ inv(L)]`; by Lemma 1 this is the *minority* probability, so
`q_p ≤ δ` for every `p`. **That inequality is the payoff of coherence** — relative
to an arbitrary reference order the inversion probabilities need not be minority
probabilities at all, and no bound of the form `q_p ≤ δ` is available.

## 4. The consecutive-slot count

Call `i ∈ {1,...,n-1}` a **free slot** if `a_i` and `a_{i+1}` are incomparable in
`P`. Let `T` be the set of free slots and `s = |T|`. Write `q_i := q_{{a_i,a_{i+1}}}`.

**Lemma 3 (proven).** `s ≥ 1`, and every `L ≠ e` inverts some free slot.

*Proof.* If `L` inverts no consecutive pair then `a_1 <_L a_2 <_L ... <_L a_n`, so
`L = e`. An inverted consecutive pair must be incomparable: if `a_i <_P a_{i+1}`
then `a_i <_L a_{i+1}`. Taking `L` to be any linear extension `≠ e` (one exists,
`P` is not a chain) gives `s ≥ 1`; if instead every consecutive pair were
comparable, transitivity would make `P` a chain. ∎

**Theorem A (proven).** If `δ(P) < 1/3` then

        δ  ≥  ( 1 - 1/e(P) ) / s .

*Proof.* `Pr[L = e] = 1/e(P)`. By Lemma 3 and a union bound over the free slots,

    1 - 1/e(P) = Pr[L ≠ e] ≤ Σ_{i ∈ T} Pr[a_{i+1} <_L a_i] = Σ_{i ∈ T} q_i ≤ s·δ. ∎

**Lemma 4 (proven).** `e(P) ≥ i(T) :=` the number of subsets of `T` containing no
two consecutive integers.

*Proof.* For `S ⊆ T` with no two consecutive integers, swap the pair `(a_i,a_{i+1})`
for each `i ∈ S`. The swaps act on disjoint pairs of positions, and each swapped
pair is incomparable, so the result is a linear extension; distinct `S` give
distinct inversion sets, hence distinct extensions by Lemma 2. ∎

If `T` is a block of `s` consecutive slots, `i(T) = F_{s+2} ≥ φ^s` (Fibonacci,
`F_1 = F_2 = 1`); if no two slots of `T` are adjacent, `i(T) = 2^s`. Combining:

**Corollary A0 (proven).** `δ ≥ (1 - 1/i(T)) / s ≥ (1 - φ^{-s}) / s`.

## 5. What it gives

| `s` | `i(T)` worst (block) | bound | `i(T)` best (spread) | bound |
|----|----|----|----|----|
| 1 | 2 | **1/2** | 2 | **1/2** |
| 2 | 3 | **1/3** | 3 | **3/8** |
| 3 | 5 | 4/15 ≈ 0.2667 | 8 | **7/24 ≈ 0.2917** |
| 4 | 8 | 7/32 ≈ 0.2188 | 16 | 15/64 ≈ 0.2344 |
| 5 | 13 | 12/65 ≈ 0.1846 | 32 | 31/160 ≈ 0.1938 |

**Corollary A1 (proven).** If `s ≤ 2` then `δ ≥ 1/3`. Hence *the 1/3-2/3
conjecture holds for every poset whose coherent order has at most two free slots*,
and any counterexample has `s ≥ 3`.

(`s = 1`: `e(P) ≥ 2`, so `δ ≥ 1/2`. `s = 2`: `e(P) ≥ 3`, so `δ ≥ (2/3)/2 = 1/3`,
contradicting `δ < 1/3`.)

**Corollary A2 (proven).** If `s = 3` and `T` is not a block of three consecutive
slots, then `i(T) ≥ 6` and `δ ≥ 5/18 ≈ 0.2778 > 0.2764`. On that sub-family this
elementary count is strictly better than the general record. (Only the fully
consecutive `s = 3` case falls short, at `4/15 ≈ 0.2667`.)

Both corollaries are **tight**: `δ = 1/3` with `s = 2, e(P) = 3` is realised by
`{a < b, c}` (its coherent order is `a, c, b`), and `δ = 1/2` with `s = 1` by the
2-element antichain. The numerics of §8 hit gap `0` at `n = 3,4,5,6`.

## 6. How much coherence is worth

The same argument without coherence gives a strictly weaker bound, and the
comparison quantifies the gain exactly.

**Lemma 5 (proven, coherence-free).** For an incomparable pair `p = {x,y}`,
swapping `x` and `y` when they are *adjacent in `L`* is an involution on
`{L : x,y adjacent}` that exchanges the two orientations. Hence
`Pr[p adjacent, minority first] = Pr[p adjacent]/2 ≤ q_p`. Also, every linear
extension of a non-chain has at least one adjacent incomparable pair, so
`Σ_{p ∈ Inc} Pr[p adjacent] ≥ 1`. Therefore `1 ≤ 2 Σ_p q_p ≤ 2mδ`, i.e.

        δ ≥ 1/(2m)      (no coherence used).

So the ledger is: **coherence replaces `m` (up to `n²/4`) by `s` (at most `n-1`)**,
and supplies the tight small-`s` constants. That is the technique, stated plainly.

**Entropy form.** By Lemma 2 and subadditivity, `log₂ e(P) = H(inv(L)) ≤ Σ_p h(q_p)
≤ m·h(δ)` (`h` = binary entropy, increasing on `[0,1/2]`). With Lemma 4's
`e(P) ≥ φ^s` this gives

        h(δ)  ≥  (s/m) · log₂ φ  =  0.694242 · (s/m).

When `s = m` — every incomparable pair is a free slot — this reads
`δ ≥ h⁻¹(0.694242) = 0.18657`. This route is weaker than Theorem A wherever both
apply; it is recorded because it degrades gracefully in `s/m` rather than in `1/s`,
and §8 finds `s = m` on *every* tight poset checked.

## 7. The barrier, stated honestly

Theorem A loses a factor `s` at the union bound. Improving Lemma 4 cannot repair
this: even with `e(P) = ∞` the bound is `≤ 1/s`, so **`s ≥ 4` is unreachable by
this count**, whatever the lower bound on `e(P)`.

That would be harmless if small `δ` forced small `s`. It does not. §8 finds posets
with `δ = 1/3` exactly and `s = 4` at `n = 6`. So the extremal posets sit outside
the window where the argument bites, and the technique as stated cannot reach `1/3`.
The union bound is not merely lossy here — it is tight in the intended regime
(each `L ≠ e` typically inverts exactly one slot), so the loss is real and must be
removed by changing the *event*, not by sharpening the inequality.

**The refinement that changes the event (proven, plus one named gap).** Lemma 3
applies verbatim to any interval `W = {a_k, ..., a_l}` of `e`: if `L|_W ≠ e|_W`
then `L` inverts a free slot inside `W`. Writing `s_W` for the free slots inside
`W` and `p_W = Pr[L|_W = e|_W]`,

**Theorem B (proven).**  `δ ≥ (1 - p_W) / s_W` for every `e`-interval `W`.

Theorem A is the case `W = P`, where `p_W = 1/e(P)` comes free. The point of
localisation is that `s_W` can be `2` even when `s` is large — so the fatal factor
`s` is replaced by `2`. The missing ingredient is exactly an upper bound on `p_W`;
the swap injection that bounds `p_W` globally fails locally, because the induced
distribution of `L|_W` is not uniform on `L(P|_W)`.

The needed statement is sharp and non-circular:

> **Window conjecture W3 (open; not proven here).** If `δ(P) < 1/3` and
> `W = {a_k, a_{k+1}, a_{k+2}}` is an `e`-window whose two slots are both free,
> then `p_W = Pr[L|_W = e|_W] ≤ 1/3`.

W3 + Theorem B give `δ ≥ (1 - 1/3)/2 = 1/3` — the full conjecture — for every
poset having two *adjacent* free slots. §8 measures `p_W ≤ 1/3` with **equality
attained** on all `6909` such windows with `n ≤ 6`, so W3 is exactly calibrated
rather than guessed.

Two honest caveats. (i) W3 is a statement about the ambient measure, not a
counting identity, and this note does not prove it. (ii) W3 does not close the
conjecture even if true: a counterexample whose free slots are all *isolated*
has no such window, and the corresponding `s_W = 1` windows are circular
(`p_W = 1 - q_k`, so the target `p_W ≤ 2/3` restates `q_k ≥ 1/3`). The isolated-slot
case is the genuine residual, and Corollary A0 only reaches `(1-2^{-s})/s` there.

## 8. Numerical verification

`scripts/entropy_probe_direct_count_verify.py` and `..._probe.py` enumerate one
representative of every isomorphism class of poset on `n ≤ 6` elements (relabel
along a linear extension; `δ`, `e(P)`, `s` are isomorphism invariants). Exact
rational arithmetic; no sampling. Results:

- **Theorem A holds on all 2036** classes with a strict transitive majority
  tournament, with gap `0` attained at every `n` (tightest cases: `δ = 1/3` at
  `n = 3,4`; `δ = 2/5` at `n = 5,6`).
- **Lemma 4 (`e(P) ≥ i(T)`) holds on all 2036**, tight at `i(T) = 3, 5, 8, 13` —
  the Fibonacci values, as predicted.
- **Lemmas 1, 5 hold on every non-chain class**, including `δ ≥ 1/(2m)`.
- **Theorem B holds on all 6909** size-3 windows with both slots free.
- **The barrier (§7) is measured, not assumed:** among classes with `δ ≤ 1/3`,
  `s` reaches `4`. Small `δ` does *not* force small `s`.
- **`s = m` on every one of the 39 classes with `δ ≤ 1/3`** (`(s,m) ∈ {(2,2),(4,4)}`)
  — every incomparable pair is a free slot in the tight regime. *Empirical only;
  no proof is offered, and it is the hypothesis under which the §6 entropy form is
  strongest.*
- **W3 is tight:** `max p_W = 1/3` exactly over the `δ ≤ 1/3` classes (and `1/2`
  overall, attained where `δ = 3/8 > 1/3`, consistent with W3's hypothesis).

Also recorded: no majority cycle occurs at `n ≤ 6` even without assuming
`δ < 1/3`. This is **empirical only** — Lemma 1's proof needs the `2/3` threshold
and says nothing about cycles among bare majorities.

## 9. Proven vs. heuristic

| Statement | Status |
|---|---|
| Lemma 1 (coherent order `e` exists when `δ < 1/3`) | **proven** |
| Lemma 2 (`inv` injective), Lemma 3 (free-slot detection) | **proven** |
| Theorem A, Lemma 4, Corollaries A0/A1/A2 | **proven** |
| Lemma 5 and the coherence-free `δ ≥ 1/(2m)` | **proven** |
| Entropy form `h(δ) ≥ (s/m)·log₂φ` | **proven** (conclusion `δ ≥ 0.18657` needs `s = m`) |
| Theorem B (localised bound) | **proven** |
| Window conjecture W3 | **open**; tight on `n ≤ 6` |
| `s = m` in the `δ < 1/3` regime | **empirical**, `n ≤ 6` only |
| Absence of majority cycles without the `2/3` threshold | **empirical**, `n ≤ 6` only |

## 10. Reproduction

```
python3 scripts/entropy_probe_direct_count_verify.py   # Theorem A + Lemma 4, n <= 6
python3 scripts/entropy_probe_direct_count_probe.py    # Lemma 5, barrier table, s vs m
```

Both run in seconds and assert every claim rather than printing it.
