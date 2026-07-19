# Entropy probe D — the local geometry of the incomparability graph

**Work item:** mg-e2de.
**Scope:** self-contained, elementary graph theory. The only objects are a finite poset
`P`, its incomparability graph `G`, a uniformly random linear extension `σ`, and the
balance constant `δ(P)`. No spectral/transport/correlation-inequality machinery is used
or needed anywhere below.

**Verdict:** **mixed, and sharply so.** The local geometry of `G` *does* give a genuine
bound — but only at the very sparsest local configurations, and it provably stops one
step later. Specifically:

* **§2 (proven).** If some edge `{x,y}` of `G` has *local co-degree*
  `m(x,y) := |(N_G(x) ∪ N_G(y)) \ {x,y}| ≤ 1`, then `δ(P) ≥ 1/3`.
  Hence **frozen ⟹ every edge of `G` has local co-degree ≥ 2.** This is a bona fide
  graph-only theorem: it holds for *every* poset with that incomparability graph.
* **§3 (proven + data).** The theorem is **sharp**: at `m = 2` a pair can already have
  balance `1/6`, and the best-possible local bound decays like
  `1/C(m+2, ⌊(m+2)/2⌋) ≈ 2^{-m}`. So no degree / local-density / expansion parameter of
  `G` can ever produce a *constant* like `1/3` beyond the `m ≤ 1` regime.
* **§4 (proven).** The first-moment ("degree budget") identity that a Cheeger-type
  argument would want to exploit is **exactly conserved** — it is identically zero and
  therefore carries no information.
* **§5 (proven, with a minimal example).** `G` alone does not determine `δ`. Minimal
  witness at `n = 6`: two posets with the *same* incomparability graph and
  `δ = 4/9` vs `δ = 1/2`. What `G` throws away is precisely the **mean-position
  profile**: `G` controls how far an element's position can *spread*, but says nothing
  about *where* it sits — and `δ` is a statement about location, not spread.

Scripts: `scripts/entropy_probe_D_incomparability_local.py` (same-`G` classes),
`scripts/entropy_probe_D_local_bounds.py` (per-pair local bounds). Both run in seconds
over all posets on `n ≤ 6`.

---

## 1. Setup and the two elementary levers

`P` is a finite poset on `n` elements; `x ~ y` in `G` iff `x ‖ y` in `P`.
`σ` is a uniformly random linear extension. For an incomparable pair write

```
b(x,y) := min( Pr[x <σ y], Pr[y <σ x] )        δ(P) = max over edges of G of b(x,y)
```

"Frozen" means `δ(P) < 1/3`, i.e. **every** edge of `G` is more than `2/3`-decided.
Note the quantifier: `δ` is a *max*, so to refute freezing it suffices to find **one**
pair that is balanced. Every argument below is therefore a per-pair argument, and that is
the right shape for a local one.

Two elementary levers do all the work.

**Lever 1 (contraction).** If `x ‖ y`, contracting `{x,y}` to a single vertex `*`
(`* > z` iff `z < x` or `z < y`; `* < z` iff `x < z` or `y < z`) yields a poset `P/xy`
— transitivity cannot fail, since `z < x` and `y < z` would force `y < x`. Linear
extensions of `P` in which `x,y` are *consecutive* are in bijection with
(extension of `P/xy`) × (2 orders of `x,y`). Hence

> **(L1)** `Pr[x,y consecutive] = 2·e(P/xy)/e(P)`, and conditioned on that event the two
> orders are equally likely. Therefore **`b(x,y) ≥ ½·Pr[x,y consecutive]`.** *(proven)*

**Lever 2 (the between-set is local).** If `x <σ z <σ y` then `z ≮ x` (it is after `x`)
and `z ≯ y`; if `z` were comparable to both we would get `x < z < y`, contradicting
`x ‖ y`. So every element lying between `x` and `y` is incomparable to at least one of
them:

> **(L2)** In *every* linear extension, the number of elements strictly between `x` and
> `y` is at most `m(x,y) = |(N_G(x) ∪ N_G(y)) \ {x,y}|`. *(proven; 0 violations over all
> 2195 incomparable pairs with `n ≤ 6`)*

(L2) is the precise, correct form of the ticket's motivating heuristic: **`G`-degrees
bound how far apart two incomparable elements can ever be driven.** It is a statement
about *spread*. §4–§5 explain why that is exactly the wrong quantity.

An immediate corollary of (L1)+(L2), worth recording because it is the purest
graph-only statement in the note:

> **Twin lemma (proven).** If `x ~ y` in `G` and `N_G(x)\{y} = N_G(y)\{x}`, then
> `b(x,y) = 1/2`, so `δ(P) ≥ 1/2` — for **every** poset whose incomparability graph is
> that `G`.
>
> *Proof.* Every `z ∉ {x,y}` is comparable to both. If `z > x` then `z` is comparable to
> `y`, and `z < y` would give `x < z < y`; so `z > y`. Symmetrically for `z < x`. Hence
> `{x,y}` is a module, the transposition `x ↔ y` is an automorphism of `P`, and the two
> orders are equinumerous. ∎ *(0 violations in the `n ≤ 6` sweep)*

So "frozen" already forbids a purely local graph pattern: **`G` has no adjacent twins.**
The rest of the note asks how much further this style of argument reaches.

---

## 2. The main positive result: local co-degree ≤ 1 forces `δ ≥ 1/3`

> **Theorem A (proven).** Let `x ‖ y` with `m(x,y) ≤ 1`. Then
> `1/3 ≤ Pr[x <σ y] ≤ 2/3`, hence `b(x,y) ≥ 1/3` and `δ(P) ≥ 1/3`.

*Proof.* Let `Z = (N_G(x) ∪ N_G(y)) \ {x,y}`, so `|Z| ≤ 1`. Every `w ∉ {x,y} ∪ Z` is
comparable to both `x` and `y`, hence (as in the twin lemma) either below both or above
both; write `D` and `U` for those two sets, so `V = D ⊔ {x,y} ⊔ Z ⊔ U` with `D < x,y < U`.

Condition on `τ = σ` restricted to `V \ {x,y}`. Linear extensions of `P` are in bijection
with pairs (`τ`, a valid placement of `x` and `y`), so conditionally on `τ` the placement
is uniform over the valid ones. `x` and `y` must be placed after all of `D` and before
all of `U`, i.e. inside the `τ`-interval between them; the only element of `V\{x,y}` that
can occupy that interval is the single element `z ∈ Z` (elements of `D`, `U` are outside
it by definition). Two cases:

* `z` is not in the interval (or `Z = ∅`). Then `x,y` sit in an empty gap and both orders
  are valid and equally likely: `Pr[x <σ y | τ] = 1/2`.
* `z` is in the interval. If `z ‖ x` and `z ‖ y`, all six orders of `x,y,z` are valid and
  equally likely, so `Pr[x <σ y | τ] = 1/2`. If `z` is comparable to exactly one of them
  — say `y < z` (the other three sub-cases are symmetric) — the valid orders are
  `(y,x,z), (y,z,x), (x,y,z)`, all equally likely, so `Pr[x <σ y | τ] = 1/3`.

Every conditional probability lies in `[1/3, 2/3]`; averaging preserves the interval. ∎

> **Corollary A′ (proven, purely graph-theoretic).** If `G` has an edge `{x,y}` with
> `|(N_G(x) ∪ N_G(y)) \ {x,y}| ≤ 1`, then `δ(P) ≥ 1/3` for **every** poset `P` with
> incomparability graph `G`. Equivalently:
>
> **frozen ⟹ every edge of `G` has local co-degree ≥ 2.**

Two remarks on what this does and does not say about degrees:

* Since `m(x,y) ≤ (deg x − 1) + (deg y − 1)`, it implies `deg_G(x) + deg_G(y) ≥ 4` for
  every edge. More usefully, *every* edge needs two distinct further neighbours, which
  rules out `G` being a matching (`m = 0`), a path or any graph with a pendant edge whose
  far endpoint has degree ≤ 2 (`m = 1` on that edge), or having a triangle component
  (`m = 1`). A cycle survives (`m = 2` on every edge). It does **not** imply minimum
  degree `≥ 2`: a degree-1 vertex `x` survives freezing provided its unique neighbour has
  degree `≥ 3`.
* Combined with the standard ordinal-sum factorisation (if `G` is disconnected then `P`
  is a linear sum of the pieces and the relative order inside each piece is unaffected by
  the others, so `δ(P) = max over components`), a *minimal* frozen poset also has **`G`
  connected**, in particular no isolated vertex.

---

## 3. Why the bound stops immediately: the local law is exponential

Theorem A is sharp, and the failure at the next value of `m` is not marginal.

> **Proposition B (proven).** For `P = C_p ⊔ C_q` (disjoint union of two chains), the
> pair `x =` bottom of `C_p`, `y =` top of `C_q` has
> `m(x,y) = p+q-2` and `b(x,y) = 1/C(p+q, p)`.
>
> *Proof.* `y <σ x` iff all of `C_q` precedes all of `C_p`, which is 1 of the `C(p+q,p)`
> equally likely interleavings. `N_G(x) ∪ N_G(y)` is everything. ∎

Choosing `p = ⌊(m+2)/2⌋` gives `b = 1/C(m+2, ⌊(m+2)/2⌋) ≈ 2^{-m}`. An exhaustive sweep
over all posets on `n ≤ 6` says this family is exactly extremal in the range it can
reach:

| local co-degree `m` | min `b(x,y)` over all posets, `n ≤ 6` | `1/C(m+2, ⌊(m+2)/2⌋)` | witness |
|---|---|---|---|
| 0 | 1/2  | 1/2  | 2-antichain (twin lemma) |
| 1 | 1/3  | 1/3  | `{a} ⊔ {b<c}` |
| 2 | 1/6  | 1/6  | `C_2 ⊔ C_2` |
| 3 | 1/10 | 1/10 | `C_2 ⊔ C_3` |
| 4 | 1/20 | 1/20 | `C_3 ⊔ C_3` |

*(Rows `m ≤ 1` are Theorem A + twin lemma, hence proven for all `n`. The claim that the
table's right-hand column is the exact minimum for `m ≥ 2` is **verified for `n ≤ 6`
only** — label: heuristic. The inequality `min b ≤ 1/C(m+2,⌊·⌋)` is proven for all `m`
by Proposition B.)*

**This is the structural answer to question 2.** Any bound of the form
`b(x,y) ≥ f(local geometry of G at {x,y})` must satisfy `f(m) ≤ 1/C(m+2,⌊(m+2)/2⌋)`.
The target constant `1/3` is only available at `m ≤ 1`. A hypothetical frozen poset is
by Corollary A′ locally dense everywhere (`m ≥ 2` at every edge), which is exactly the
regime where the local bound has already collapsed below `1/3` — and thereafter decays
exponentially. **Local geometry cannot be sharpened into a constant; the decay is a
property of posets, not an artefact of the argument.**

Note also that `C_2 ⊔ C_2` — the poset that kills `m = 2` — has `δ = 1/2`. Its balanced
pair is elsewhere in the graph. This is the recurring failure mode: local data correctly
predicts that *this* pair is unbalanced, and is silent about the pair that saves the
conjecture.

---

## 4. The degree/Cheeger budget is exactly conserved (so it is inert)

The natural Cheeger-flavoured attempt: freezing orients every edge, so compare `σ` with
that orientation and count across cuts. It goes through, and it yields nothing. Here is
why, precisely.

**(a) Freezing produces a reference linear order.** *(proven, folklore)* Orient each edge
`{x,y}` of `G` by the majority direction and each comparable pair by `P`. If three
elements formed a directed 3-cycle, then each of the three relations fails with
probability `< 1/3`, so all three hold with probability `> 1 - 3·(1/3) = 0` — but they
cannot all hold in a linear order. So the tournament has no 3-cycle, hence is transitive:
freezing yields a linear order `L ⊇ P` in which every incomparable pair is `>2/3`-decided.

**(b) Positions decompose into a poset offset plus a `G`-local fluctuation.** *(proven)*
For any `x`,

```
pos_σ(x) = 1 + d⁻_P(x) + Σ_{y ∈ N_G(x)} 1[y <σ x]          (∗)
```

where `d⁻_P(x) = #{z : z < x}`. Likewise `rank_L(x) = 1 + d⁻_P(x) + #{y ∈ N_G(x) : y <_L x}`.
So `|pos_σ(x) − rank_L(x)| ≤ deg_G(x)` always, and under freezing

```
|E[pos_σ(x)] − rank_L(x)|  <  deg_G(x)/3 ,
```

with `Pr[|pos_σ(x) − rank_L(x)| ≥ t] ≤ deg_G(x)/(3t)` by Markov. The mobility heuristic
in the ticket is therefore **correct and quantitative** — an element's position is pinned
to a window of width `deg_G(x)`.

**(c) And the budget cancels identically.** *(proven)*

```
Σ_x ( E[pos_σ(x)] − rank_L(x) )
   = Σ_{ {x,y} ∈ E(G) } ( Pr[x<y] + Pr[y<x] − 1 )
   = 0.
```

Both sides sum to `n(n+1)/2` for trivial reasons. **The first-moment degree data is a
conservation law, not a constraint.** No summation over vertices, no weighting by
degree, and no cut-based aggregation of (b) can produce a contradiction, because the
quantity being aggregated is identically zero before freezing is even invoked.

**(d) The cut version, for completeness.** *(proven)* Let `S` be an `L`-prefix and `T` the
`σ`-prefix of the same size. Any `x ∈ S \ T` is `σ`-preceded by some `y ∉ S`, and such a
pair must be incomparable (else `σ` and `L` would disagree on a comparable pair), so it is
a `G`-edge crossing the cut, inverted relative to `L`. Hence under freezing
`E|S Δ T| ≤ (2/3)·e_G(S, S̄)`. Sparse cuts in `G` do force `σ` to track `L`. But a genuine
split of `G` means `P` is an ordinal sum, and `δ` factorises over ordinal sums —
`δ(A ⊕ B) = max(δ(A), δ(B))` — so the conclusion the cut argument delivers is precisely
the case in which `δ` is already known not to move. **Small cuts are δ-inert.**

---

## 5. Insufficiency: what `G` throws away, and a minimal example

> **Theorem C (proven, by exhibition).** `δ` is not a function of the incomparability
> graph. Minimal witness: `n = 6`.

Let `f` be an element incomparable to everything else, and let

```
A = ({a < b})  ⊕  ({c < d} ⊔ {e})        with f adjoined incomparably   (δ = 4/9)
B = {a} ⊕ ({b < c} ⊔ {d}) ⊕ {e}          with f adjoined incomparably   (δ = 1/2)
```

Both have 6 elements and `e(P) = 18`. Their incomparability graphs are **equal**: in `A`
the incomparable pairs among `{a..e}` are `{c,e}, {d,e}`, a path `c–e–d`, with `a, b`
isolated; in `B` they are `{b,d}, {c,d}`, a path `b–d–c`, with `a, e` isolated; and in
both cases `f` is joined to all five. So `G = K_1 ∨ (P_3 ⊔ 2K_1)` for both.
Yet `δ(A) = 4/9` (witness pair `{f,c}`, `8/18`) and `δ(B) = 1/2` (witness pair `{f,d}`,
`9/18`). An exhaustive sweep confirms this is the *only* such class for `n ≤ 6` and that
none exists for `n ≤ 5`.

**The mechanism, and the exact statement of what `G` loses.**

> **Free-point lemma (proven).** If `f` is incomparable to every other element and
> `Q = P \ {f}`, then `f`'s position in `σ` is uniform on `{1,…,n}` and independent of
> `σ|_Q`, so for every `x ≠ f`
>
> ```
> Pr[f <σ x] = E[ rank_Q(x) ] / n .
> ```

So the balance of every `f`-pair is read directly off the **mean-rank profile** of `Q`.
For `A`: the mean ranks of `a,b,c,d,e` are `1, 2, 10/3, 14/3, 4`, giving
`Pr[f < c] = 10/18` — balance `4/9`. For `B`: `1, 7/3, 11/3, 3, 5`, and the element `d`
sits at mean rank exactly `3 = n/2`, giving `Pr[f < d] = 9/18` — balance `1/2`.
The two posets have the same incomparability graph; they do **not** have the same
mean-rank profile.

Reading this against `(∗)`:

```
rank(x) = 1 + d⁻_P(x)  +  Σ_{y ∈ N_G(x)} 1[y <σ x]
          └── invisible to G ──┘   └── exactly what G sees ──┘
```

**`G` determines the number of fluctuating terms — the spread — and nothing about the
offset `d⁻_P(x)` — the location.** In the example, the "free" element of the middle
factor has `G`-degree 2 in both posets; what differs is that it has 2 elements below it
in `A` and 1 in `B`, which slides its mean rank from `4` to `3` and slides the `f`-pair
from `4/9` to the balanced `1/2`. Since `δ` is a statement about whether some element's
position distribution straddles another's — a *location* question — and `G` only sees
*spread*, `G` is structurally the wrong object.

**A calibrating remark on how much this rules out.** Theorem C does not by itself kill
every graph-only approach: Corollary A′ *is* a graph-only theorem, and a hypothetical
statement "`δ ≥ 1/3` for every transitive orientation of `Ḡ`" is *equivalent* to the
conjecture (every poset arises this way), so it is not refuted — it is merely no easier.
What Theorem C does kill is any hope that `G` *determines* `δ`, or that a `G`-invariant
computes it. Combined with §3 (any local bound decays exponentially in local density) and
§4 (the aggregate degree budget is identically zero), the honest conclusion is:

> **The incomparability graph's local geometry yields exactly one nontrivial theorem —
> `m ≤ 1 ⟹ δ ≥ 1/3` — and that is the end of the line. It is sharp, the next case
> collapses to `1/6`, the general local law is exponential in `m`, the first-moment
> budget is a conservation law, and small cuts are δ-inert. `G` measures mobility; `δ`
> is about position; a frozen poset would be locally dense, which is precisely where
> mobility data says nothing.**

*Side observation, not needed above:* over all `n ≤ 6`, posets sharing an incomparability
graph always share `e(P)` (144 graph classes, zero splits) — consistent with the known
comparability-invariance of the order polynomial (Dreesen–Poguntke–Winkler; Stanley).
Cited, not proven here. It sharpens the picture: `G` retains the *global* extension count
exactly, and loses the *per-element* position profile — which is the half `δ` needs.

---

## 6. Status summary

| Claim | Status |
|---|---|
| (L1) `b ≥ ½ Pr[x,y consecutive]`; contraction bijection | **proven** |
| (L2) between-set of `{x,y}` is contained in `N(x) ∪ N(y)` | **proven** (0/2195 violations `n ≤ 6`) |
| Twin lemma: adjacent twins in `G` ⟹ `δ ≥ 1/2`, for all `P` with that `G` | **proven** (0 violations `n ≤ 6`) |
| **Theorem A / A′**: local co-degree `≤ 1` ⟹ `δ ≥ 1/3`; frozen ⟹ co-degree `≥ 2` everywhere | **proven** |
| Proposition B: `C_p ⊔ C_q` gives `b = 1/C(m+2,p)` — Theorem A is sharp | **proven** |
| The table's `m ≥ 2` rows are the *exact* minima | **heuristic** (verified `n ≤ 6`) |
| Freezing ⟹ majority tournament is a linear order `L` | **proven** (folklore) |
| `|E[pos(x)] − rank_L(x)| < deg_G(x)/3` under freezing | **proven** |
| Degree/first-moment budget sums to zero ⟹ inert | **proven** |
| Cut bound `E|S Δ T| ≤ (2/3) e_G(S,S̄)`; small cuts δ-inert via ordinal-sum factorisation | **proven** |
| **Theorem C**: `δ` not determined by `G`; minimal example `n = 6`, `4/9` vs `1/2` | **proven** (exhaustive for `n ≤ 6`) |
| Free-point lemma `Pr[f<x] = E[rank_Q(x)]/n` | **proven** |
| `e(P)` is a comparability invariant | **cited** (verified `n ≤ 6`) |
