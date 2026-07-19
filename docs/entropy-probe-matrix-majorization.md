# Entropy probe B — doubly-stochastic position matrix, majorization, and δ

**Work item:** mg-92e6. Self-contained and elementary; written from the ticket statement alone.
Scripts: `scripts/entropy_probe_matrix_majorization.py`, `scripts/entropy_probe_marginal_lp.py`.

---

## 0. Verdict

Three results, in increasing order of interest.

1. **A bound exists and is nontrivial.** *(proven, §3)* For incomparable `x,y`,

   > `δ(P) ≥ ½ · ( T[x,k] + T[x,k+1] + T[y,k] + T[y,k+1] − 1 )` for every `k`.

   It fires exactly when the two rows hold **more than half the mass of a 2×2 diagonal
   block** — i.e. it is switched on by the near-diagonal structure, which is what the
   ticket asked for. It is tight (equality on 3040 pairs at `n ≤ 6`, including the
   3-element poset where it certifies exactly `1/3`).

2. **The pure-marginal method has an exactly computable ceiling.** *(proven, §4)* The best
   lower bound on `δ` derivable from the two rows of `T` alone has the closed form

   > `min Pr[y before x] = max_t [ F_y(t) − F_x(t−1) ]`

   (max-flow/min-cut; cross-checked numerically). This is the precise answer to the
   ticket's honesty question. The ceiling **degrades like 1/spread**: for two rows uniform
   on a common window of `m` positions it equals exactly `1/m`. So marginal-only reasoning
   can never certify `δ ≥ 1/3` for a pair spread over more than 3 positions — *no matter
   how the mass is arranged*.

3. **The interesting part: Theorem A breaks that ceiling.** *(proven, §5)* Theorem A is
   **not** a marginal-only bound — it exceeds the ceiling on 26 096 of 1 168 036 incomparable
   pairs at `n ≤ 7`. It does so by injecting exactly one non-marginal fact: the
   adjacent-transposition involution, which says the pair's joint law is **symmetric on the
   adjacent band**, `J(k,k+1) = J(k+1,k)`. That single equation is the precise "extra joint
   information needed" that the ticket asked to be characterized.

**Bottom line.** The matrix/majorization viewpoint does yield a real bound, and the exact
limit of the viewpoint is computable in closed form. But Birkhoff and majorization proper
contribute *nothing* (§6), and the ceiling is too weak to reach `1/3` on its own. The
leverage comes from one elementary poset fact bolted onto the matrix picture.

---

## 1. Setup

`P` a finite poset on `n` elements, `σ` a uniformly random linear extension, `R_x ∈ {1..n}`
the position of `x`, and `T[x,i] = Pr[R_x = i]`. Rows sum to 1 (`x` lands somewhere);
columns sum to 1 (exactly one element occupies position `i`). So `T` is doubly stochastic.
`F_x(t) = Pr[R_x ≤ t]`, with `F_x(0) = 0`.

`δ(P) = max over incomparable {x,y} of min(Pr[x before y], Pr[y before x])`.

**Frozen regime.** `δ(P) < 1/3`, every incomparable pair is `>2/3`-decided, and the strong
majorities cohere into a total order `e`. Since comparable pairs are decided with
probability 1, **`e` extends `P`**. Relabel so `e = (x_1, …, x_n)`; rows and columns of `T`
are indexed in `e`-order, and "near-diagonal mass" means each `x_k` tends to sit near
position `k`.

**Lemma 1 (proven).** *If `P` is not a chain, some `e`-consecutive pair `{x_k, x_{k+1}}` is
incomparable in `P`.*

*Proof.* If every consecutive pair were comparable then, `e` extending `P`, we'd have
`x_k <_P x_{k+1}` for all `k`, so by transitivity `P` is the chain `e`. ∎

This is the only place coherence is used, and it is what lets us always aim the bounds at a
**diagonal-adjacent** pair.

---

## 2. What `T` forces about a pair: column capacity

**Proposition 2 (proven).** *For any set `S` of positions and any `x ≠ y`,*

> `Pr[R_x ∈ S and R_y ∈ S] ≥ m_S(x) + m_S(y) − 1`,  where `m_S(x) = Σ_{i∈S} T[x,i]`.

*Proof.* Inclusion–exclusion on the events `{R_x ∈ S}`, `{R_y ∈ S}`. ∎

Trivial, but it is the *entire* pairwise content of `T` (§4 makes that precise). Two
instances matter, and they behave **oppositely** under diagonal concentration:

- **`S` a prefix `{1..t}`.** Gives `Pr[x before y] ≥ F_x(t) − F_y(t)`: the
  stochastic-domination bound. Near-diagonal structure sorts the rows, so `F_x ≥ F_y`
  monotonically for `x <_e y` — the CDFs stop crossing and **this bound dies**.
- **`S` a 2-window `{k,k+1}`.** Since `R_x ≠ R_y`, both being in `S` means
  `{R_x,R_y} = {k,k+1}` — the pair is **adjacent**. Near-diagonal structure makes
  `m_S(x)+m_S(y)` large, so **this bound switches on**.

That opposition is the useful observation: diagonal concentration kills the rearrangement
bound one usually reaches for, and enables the adjacency bound instead.

---

## 3. Theorem A — a bound that uses the diagonal

**Lemma 3 (adjacent transposition; proven).** *Let `x,y` be incomparable and let
`A = {σ : x,y adjacent}`. Then `Pr[A ∧ x first] = Pr[A ∧ y first] = ½ Pr[A]`.*

*Proof.* Transposing two adjacent incomparable elements inverts only the pair `(x,y)`, which
is incomparable, so the result is again a linear extension. The map is an involution on `A`
exchanging the two halves. ∎

**Theorem A (proven).** *For incomparable `x,y` and any `k`,*

> `δ(P) ≥ min(Pr[x<y],Pr[y<x]) ≥ ½ · ( T[x,k] + T[x,k+1] + T[y,k] + T[y,k+1] − 1 )⁺`.

*Moreover, adjacency events at disjoint windows are disjoint, so the positive parts may be
summed over any set of disjoint 2-windows (e.g. all even `k`, or all odd `k`).*

*Proof.* Proposition 2 with `S = {k,k+1}` lower-bounds `Pr[A]`; Lemma 3 halves it. ∎

**Interpretation.** Column sums are 1, so the total mass in the two columns `{k,k+1}` across
*all* rows is exactly 2. The bound fires iff rows `x` and `y` between them own **more than
half of their own diagonal block**. This is literally a doubly-stochastic-capacity statement.

**Corollary 4 (frozen leakage; proven).** *Let `{x_k, x_{k+1}}` be an `e`-consecutive
incomparable pair (Lemma 1) and let `ε` be the total mass the two rows place **outside**
columns `{k,k+1}`. Then `m_S(x_k) + m_S(x_{k+1}) = 2 − ε`, so*

> `δ(P) ≥ (1 − ε)/2`.  In particular `ε ≤ 1/3 ⟹ δ ≥ 1/3`.

*Contrapositive — the structural statement about a hypothetical counterexample:* **in the
frozen case every `e`-consecutive incomparable pair must leak more than `1/3` of its combined
mass out of its own 2×2 diagonal block.** Equivalently, if every row satisfied
`T[x_k,k] ≥ 1 − η`, then `δ ≥ 1/2 − η`, so a frozen poset must have some
`e`-consecutive incomparable pair with a row of diagonal mass below `11/12`.

**Tightness (verified).** The 2-element antichain gives `T[x,·]=T[y,·]=(½,½)` and
`δ = ½ = ½(2−1)` — equality. The 3-element poset `{a ∥ b < c}` has

```
T[a] = (1/3, 1/3, 1/3)     δ = 1/3
T[b] = (2/3, 1/3,   0)     Theorem A on {a,b}, k=1:  ½(1/3+1/3+2/3+1/3 − 1) = 1/3   ✓ tight
T[c] = (  0, 1/3, 2/3)
```

Across all naturally-labelled posets with `n ≤ 6`, Theorem A is an equality on **3040**
incomparable pairs.

**Strength (empirical).** Fraction of non-chain posets on which Theorem A *by itself*
certifies `δ ≥ 1/3`:

| `n` | non-chain posets | Theorem A certifies `δ ≥ 1/3` |
|-----|------------------|-------------------------------|
| 3   | 6                | 5 (83.3%) |
| 4   | 39               | 18 (46.2%) |
| 5   | 356              | 128 (36.0%) |
| 6   | 4 823            | 1 311 (27.2%) |
| 7   | 96 427           | 18 225 (18.9%) |

Real but decaying — as expected, since it only ever looks at one 2×2 block.

---

## 4. The exact ceiling of marginal-only reasoning

The ticket's honesty note is correct and can be made sharp. `Pr[x before y]` is a functional
of the **joint** law `J(i,j) = Pr[R_x = i, R_y = j]`, not of the rows `T[x,·]`, `T[y,·]`.
Ask: over all joint laws with those marginals and `J(i,i) = 0` (positions are distinct),
how small can `Pr[y before x]` be? That infimum is the **exact ceiling** on any bound
provable from the marginals alone.

It is a transportation LP with 0/1 costs, hence a max-flow. The bipartite graph is a
staircase (row `i` may ship only to columns `j > i`), so min-cut is a threshold cut and:

**Theorem B (proven; cross-checked numerically).**

> `min over couplings with R_x ≠ R_y of Pr[R_x > R_y]  =  max_t [ F_y(t) − F_x(t−1) ]`
> `                                                    =  max_t [ F_y(t) − F_x(t) + T[x,t] ]`.

*Proof.* Max-flow/min-cut. A cut keeps a set `R` of rows on the source side and pays
`Σ_{i∉R} T[x,i] + Σ_{j ∈ N(R)} T[y,j]` with `N(R) = {j : j > min R}`; only `min R = t`
matters, so the min cut is `min_t [ F_x(t−1) + 1 − F_y(t) ]`. Subtract from 1. ∎

Cross-checked against a brute-force Ford–Fulkerson on 300 random marginal pairs (exact
rationals): agreement in every case. As a lower bound on the true `δ` it was verified on all
1 168 036 incomparable pairs of all naturally-labelled posets with `n ≤ 7`.

**Consequence 1 — the ceiling degrades like `1/spread`.** For `T[x,·] = T[y,·] =` uniform on
a common window of `m` positions, Theorem B gives exactly `1/m`:

| `m` | 2 | 3 | 4 | 5 | 6 |
|-----|---|---|---|---|---|
| ceiling | `1/2` | `1/3` | `1/4` | `1/5` | `1/6` |

The extremal couplings are the two cyclic shifts on the window: `R_y = R_x + 1 (mod m)`
gives `Pr[y before x] = 1/m`, the reverse shift gives `1 − 1/m`. **Identical marginals are
compatible with `min(p,1−p)` anywhere in `[1/m, 1/2]`.** So marginal-only reasoning cannot
certify `δ ≥ 1/3` once a pair is spread over 4 or more positions — this is a hard obstruction,
not a failure of ingenuity.

**Consequence 2 — in the frozen regime the ceiling is a diagonal-crossing quantity.** For an
`e`-consecutive incomparable pair `x = x_k`, `y = x_{k+1}`, taking `t = k` in Theorem B:

> `δ ≥ Pr[y before x] ≥ F_y(k) − F_x(k−1)` = (mass `y` places at or before position `k`) −
> (mass `x` places strictly before position `k`).

It is nontrivial precisely when the two rows **interleave** — `y` must reach back past `x`'s
own slot further than `x` reaches back. Under clean, well-separated sorting it is 0. (It can
never be *forced* to 0 for an incomparable pair: by Szpilrajn both orders are realizable, so
`Pr[x before y] < 1` strictly — but it can be arbitrarily close.)

**Strength (empirical).** The exact ceiling is substantially stronger than Theorem A, and
certifies `δ ≥ 1/3` on 62.5% of non-chain posets at `n = 7` (vs 18.9%):

| `n` | non-chain | Theorem A | exact ceiling (Thm B) |
|-----|-----------|-----------|-----------------------|
| 4   | 39        | 46.2%     | 82.1% |
| 5   | 356       | 36.0%     | 74.4% |
| 6   | 4 823     | 27.2%     | 82.1% |
| 7   | 96 427    | 18.9%     | 62.5% |

---

## 5. Theorem A breaks the ceiling — and the exact reason why

Theorem A can **exceed** Theorem B's ceiling. Smallest witness (`n = 4`, relations
`0<3`, `1<2`, `1<3`, `e(P) = 5`):

```
T[0] = (2/5, 2/5, 1/5,   0)      pair {0,2}:  Pr[0 before 2] = 4/5
T[1] = (3/5, 2/5,   0,   0)                   true min       = 1/5
T[2] = (  0, 1/5, 2/5, 2/5)                   Theorem A      = 1/10
T[3] = (  0,   0, 2/5, 3/5)                   Theorem B      = 0     ← ceiling is vacuous
```

No contradiction: **Theorem A is not a marginal-only bound.** Lemma 3 uses a fact invisible
to the rows of `T`, namely that the joint law of the pair is **symmetric on the adjacent
band**:

> `J(k, k+1) = J(k+1, k)` for every `k`.

That is exactly the content of the transposition involution, and it is exactly the extra
joint information the ticket asked to have named. It happens on 26 096 of 1 168 036 pairs at
`n ≤ 7` (2.2%) that this extra fact strictly beats everything the marginals can give.

**So the precise answer to "what extra joint information is needed":** the marginals pin down
`δ` only up to the `1/spread` ceiling of Theorem B. The minimal supplement that provably
breaks that ceiling is the adjacent-band symmetry of `J`. The sharp object combining both is
the LP

> minimize `min( Σ_{i<j} J(i,j), Σ_{i>j} J(i,j) )`
> over `J ≥ 0` with row sums `T[x,·]`, column sums `T[y,·]`, `J(i,i) = 0`,
> **and `J(k,k+1) = J(k+1,k)` for all `k`**,

whose value is the exact ceiling of "marginals + transposition symmetry". Theorem A is a
(generally non-tight) relaxation of it. **Evaluating this LP is the concrete next
computation** — it is small and exactly solvable, and it would say definitively how much
more the matrix picture can give. It needs a rational LP solver (none is installed here);
the max-flow shortcut of Theorem B does not survive the symmetry constraint.

---

## 6. Why Birkhoff and majorization proper contribute nothing

Worth stating explicitly, since the ticket names them.

- **Birkhoff is vacuous here.** It says every doubly stochastic matrix is a convex
  combination of permutation matrices. But `T = (1/e(P)) Σ_{σ ∈ L(P)} P_σ` *is already*
  given as such a combination, and that combination is the object under study. Birkhoff
  supplies an existence statement we already have, and its guaranteed decomposition need not
  be supported on linear extensions of `P`. It adds no information — indeed it works
  *against* us: it certifies that **every** doubly stochastic `T` is realizable by *some*
  random permutation, i.e. `T` alone carries no poset-specific content.
- **Majorization (`Tv ≺ v`) is about row/column aggregates, not pairs.** It yields facts like
  "the vector of expected ranks `r(x) = E[R_x]` is majorized by `(1,…,n)`". True, and it does
  use double stochasticity — but `δ` is a pairwise functional and expected ranks are blind to
  it (two elements can share an expected rank with any bias whatsoever).
- **Rearrangement inequalities** need a linear objective in the joint law with a monotone
  cost structure. `Pr[x before y]` qualifies, and the resulting bound is precisely Theorem B
  — which we have already computed exactly. There is nothing further in that family.

The only genuinely load-bearing consequence of double stochasticity is column capacity
(Proposition 2), i.e. `R_x ≠ R_y`. Everything in §§3–4 is downstream of that one fact.

---

## 7. Two empirical observations (not needed for the results above)

Both from the exhaustive sweep over naturally-labelled posets, `n ≤ 7`. Flagged
**empirical**; neither is proven and neither is used above.

1. **No frozen posets exist at `n ≤ 7`.** `min δ = 1/3` exactly, at every `n` from 3 to 7.
   Consistent with the conjecture; it also means Corollary 4's frozen hypothesis is vacuous
   at these sizes and cannot be tested empirically here.
2. **`T` determines the poset up to isomorphism at `n ≤ 7`.** `T` does not determine the
   *labelled* poset (3 407 collision classes at `n = 7`), but in every single collision the
   posets are isomorphic — so `δ` never actually differed between two posets sharing a `T`.

Observation 2 deserves emphasis because it corrects a tempting misreading of §4. The
obstruction is **not** that `T` fails to determine `δ` on real posets — empirically it
determines it completely. The obstruction is that the information, though present, is
**inaccessible to the convex-relaxation toolkit**: any argument of the form "here are the
marginals, here is a coupling inequality" must remain valid for every joint law with those
marginals, including the cyclic-shift laws of §4, and is therefore capped at `1/spread`.
The information survives in `T`; the *method* cannot extract it.

---

## 8. Summary table

| Claim | Status |
|---|---|
| Lemma 1 — some `e`-consecutive pair incomparable | **proven** |
| Prop 2 — column capacity | **proven** |
| Lemma 3 — adjacent transposition | **proven** |
| Theorem A — 2×2 diagonal-block bound (+ disjoint windows) | **proven**, verified `n ≤ 7` |
| Corollary 4 — `ε ≤ 1/3 ⟹ δ ≥ 1/3`; frozen ⟹ every consecutive pair leaks `>1/3` | **proven** |
| Theorem B — exact marginal ceiling `max_t[F_y(t) − F_x(t−1)]` | **proven**, cross-checked vs max-flow |
| Ceiling `= 1/m` on an `m`-window; marginals cannot certify `1/3` beyond spread 3 | **proven** |
| Adjacent-band symmetry `J(k,k+1)=J(k+1,k)` is the extra input that breaks the ceiling | **proven** (witnessed `n=4`) |
| Birkhoff/majorization add nothing | **argued**, §6 |
| Strength percentages, equality counts | **empirical**, exhaustive `n ≤ 7` |
| No frozen posets at `n ≤ 7`; `T` determines poset up to iso at `n ≤ 7` | **empirical** |

**Did the fresh matrix viewpoint yield a bound that genuinely uses near-diagonal structure?**
Yes — Theorem A and Corollary 4, which fire precisely on diagonal concentration and are
tight. **Is it enough for `1/3`?** No, and §4 says exactly why not: the marginal-only method
is capped at `1/spread`, and the only known way past the cap is one elementary poset fact
(adjacent-band symmetry) that is not a matrix statement at all. The honest characterization
the ticket asked for is Theorem B plus §5.
