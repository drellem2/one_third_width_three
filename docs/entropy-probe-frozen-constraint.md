# Entropy probe A — does the frozen/coherence condition improve the 0.2764 bound?

**Work item:** mg-61bb. Self-contained, elementary. No machinery from elsewhere in this
repo is used or needed.

---

## 0. Verdict

**INERT.** The frozen/coherence condition buys nothing over `0.2764` — and the reason is
sharper (and more discouraging) than "the extremal configuration happens to be coherent".

The reason is that **coherence is not an extra hypothesis at all.** It is a *logical
consequence* of the hypothesis `δ(P) < 1/3` that any lower-bound proof is already working
under. Adding it as a constraint does not shrink the class of posets under consideration by
a single element, so it cannot change any constant.

Its residual content — the thing that is not literally circular, namely the triple
inequality that produces coherence — is a system of **upper** bounds on balances that is
satisfied by a chain. No such system can ever force a *positive lower* bound on any balance.

Three independent statements of this, in increasing sharpness, are §3.1 / §3.2 / §3.3
below. Each is proven. §4 examines the one door that is not obviously closed (using
coherence to *select* the pair rather than to constrain it) and explains why it also does
not move the constant.

---

## 1. Setup and the two elementary facts

`P` a finite poset, `σ` a uniformly random linear extension, `e(P)` the number of linear
extensions. For a pair `{u,v}` write

```
β(u,v) := min( Pr[u ≺ v], Pr[v ≺ u] )   ∈ [0, 1/2]        (the balance of the pair)
δ(P)   := max over incomparable pairs of β(u,v)
```

Comparable pairs have `β = 0`. A chain has no incomparable pairs at all.

### Fact 1 (the triple inequality). *Proven.*

For any three distinct `x,y,z ∈ P`,

```
Pr[x ≺ y] + Pr[y ≺ z] + Pr[z ≺ x]  ≤  2.
```

*Proof.* Fix a linear extension `L`. The three events "`x` before `y`", "`y` before `z`",
"`z` before `x`" cannot all hold in `L` (they would form a cycle in a total order). So at
most two of them hold, and averaging over the `e(P)` linear extensions gives the claim. ∎

Brute-force check over 4000 random posets on 3–6 elements (all triples, exact rational
arithmetic): the maximum of the cyclic sum observed is exactly `2`, never exceeded. The
bound is tight (e.g. an antichain on 3 elements gives `3 · 1/2 = 3/2`; a 3-chain `x≺y≺z`
gives `1 + 1 + 0 = 2`).

### Fact 2 (coherence in the frozen regime). *Proven.*

Suppose `δ(P) < 1/3`. Orient every pair `{u,v}` by its majority: `u → v` iff
`Pr[u ≺ v] > 1/2`. Then:

1. every pair is **>2/3-decided** (`Pr > 2/3` on the majority side): incomparable pairs
   because `β < 1/3`, comparable pairs because `Pr = 1`;
2. this tournament has no 3-cycle — a 3-cycle would give three probabilities each `> 2/3`,
   summing to `> 2`, contradicting Fact 1;
3. an acyclic tournament is a total order. Call it `e`. Since `u < v` in `P` forces
   `Pr[u ≺ v] = 1`, `e` is a linear extension of `P`.

So under `δ(P) < 1/3` there is a distinguished linear extension `e` with which **every**
incomparable pair agrees with probability `> 2/3`. ∎

This is the "frozen/coherence condition" of the ticket. **Note the direction of the
implication: it is derived from `δ(P) < 1/3`, not assumed alongside it.** That single
observation is already most of the answer; §3.1 spells it out.

---

## 2. What the `0.2764` argument actually is

### 2.1 The constant

```
(5 − √5)/10 = 0.2763932022500210…  =  1/(φ + 2)  =  1/(φ² + 1),   φ = (1+√5)/2
```
(identity verified numerically). Equivalently the extremal *odds ratio* is
`(1−δ)/δ = φ² = (3+√5)/2 ≈ 2.618`. The golden ratio is not decoration — it is the
signature of a geometric-progression extremal, which is what a log-concavity-constrained
optimization produces.

### 2.2 Provenance — a correction to the ticket's framing

The ticket describes `0.2764` as coming from "an entropy / convexity argument
(Brunn–Minkowski on the order polytope)". That conflates two different lineages, and the
distinction matters here because the question is *which optimization* to perturb:

| bound | authors | mechanism |
|---|---|---|
| `1/(2e) ≈ 0.1839` | Kahn–Linial 1991 | Brunn–Minkowski / log-concave marginals on the order polytope. The "entropy/convexity" route. **Weaker.** |
| `3/11 ≈ 0.2727` | Kahn–Saks 1984 | discrete: log-concavity of the *gap sequence* of a chosen pair |
| `(5−√5)/10 ≈ 0.2764` | Brightwell–Felsner–Trotter 1995 | Kahn–Saks route + one extra correlation inequality on a **triple** |

So the record-holding `0.2764` is the **Kahn–Saks / BFT discrete lineage**, not the
Brunn–Minkowski one. The probe must be aimed there.

### 2.3 The ingredients — *verified against the literature*

For distinct `x, y ∈ P` let

```
F(k) := #{ L ∈ E(P) : L(y) − L(x) = k },      k ∈ ℤ \ {0}.
```

**(KS-1) Kahn–Saks log-concavity.** `F(k)² ≥ F(k−1)·F(k+1)` for all `k > 1`; i.e. the
one-sided sequences `(F(k))_{k≥1}` and `(F(−k))_{k≥1}` are log-concave. (Stated verbatim
as [KS84, Thm 2.5] in Chan–Pak–Panova; its proof is geometric and is not needed here.)

**(KS-2) The reflection identity.** `F(1) = F(−1)`.
*Proof (elementary):* if `L(y) = L(x)+1` then `x,y` are adjacent in `L` and incomparable,
so transposing them yields a linear extension with `L(x) = L(y)+1`; this is an involution
and hence a bijection between the two sets. ∎

**(BFT) The cross-product input.** For distinct `x,y,z` let
`F(k,ℓ) := #{L : L(y)−L(x) = k, L(z)−L(y) = ℓ}`. BFT conjectured
`F(k,ℓ)F(k+1,ℓ+1) ≤ F(k,ℓ+1)F(k+1,ℓ)` for all `k,ℓ ≥ 1`, and **proved the case
`k = ℓ = 1`** via the Ahlswede–Daykin four-functions theorem. That single case is the extra
input that lifts `3/11` to `(5−√5)/10`.

**(SEL) The selection step.** The pair is not arbitrary: it is chosen so that the two
elements have nearby expected heights `h(u) = E[L(u)]` (pigeonhole on the `n` expected
heights, which span an interval of length `≤ n−1`, forces an incomparable pair with
`|h(x) − h(y)|` small; non-chain-ness is used exactly here).

**Honesty ledger.** (KS-1), (KS-2), (BFT) and the constant are verified. The precise final
optimization of BFT — the exact objective and constraint list whose optimum is
`(5−√5)/10` — I could **not** obtain from a primary source: the BFT paper (Order 12, 1995)
and Brightwell's survey (Discrete Math 201, 1999) are both paywalled, and the modern papers
that build on this material (Chan–Pak–Panova, Aires–Kahn, Chen) cite the constant without
reproducing the derivation. **This does not weaken the verdict**, for the reason given in
§3.2: the verdict turns only on *which elements the optimization's variables live on*, and
that is verified — `F(k)` lives on a pair, `F(k,ℓ)` on a triple.

---

## 3. Imposing the frozen constraint

### 3.1 Reason 1 — the classes coincide (the constraint is not a constraint)

By Fact 2,

```
{ P : δ(P) < 1/3 }   =   { P : δ(P) < 1/3  and  P is frozen-coherent }.
```

These are the *same set*. A proof of "`δ(P) ≥ c` for all `P`" is exactly a proof that the
left-hand set contains no poset with `δ(P) < c`; adding a condition that every member of
that set already satisfies changes nothing that any argument could exploit. Any apparent
gain from "assuming coherence" must in fact be a gain from the *derivation* of coherence,
i.e. from Fact 1 itself. §3.3 shows Fact 1 gives nothing.

### 3.2 Reason 2 — locality: the optimization cannot see coherence

The KS/BFT **inequalities** are statements about at most three elements: (KS-1) and (KS-2)
about a pair `{x,y}`; (BFT) about a triple `{x,y,z}`. The feasible region of the resulting
optimization is a set of admissible numerical data attached to those `≤ 3` elements.

Now restrict the frozen condition to any `≤ 3` elements. What does it say?

- On a **pair**: exactly `β(x,y) < 1/3`. That is the contradiction hypothesis itself — it
  is what we are trying to refute, so using it as a constraint is circular, and in any case
  it adds nothing to a feasible region that already contains all data with `β < 1/3`.
- On a **triple**: that the three majorities do not cycle. But **by Fact 1 that is true for
  every finite poset whatsoever, coherent or not**, as soon as the three pairs are
  `>2/3`-decided — and `>2/3`-decidedness is again just the contradiction hypothesis.

So the frozen condition contributes **zero** constraints to the KS/BFT feasible region. The
extremal configuration, whatever it is, is untouched. This is the precise sense in which
"the existing bound does not use coherence": it *cannot*, because coherence has no content
on `≤ 3` elements.

### 3.3 Reason 3 — the residual content is a homogeneous system of *upper* bounds

Here is the only non-circular content Fact 1 has in the frozen regime — and it is worth
recording, because it is a genuinely pretty inequality, just useless for this purpose.

Let `e` be the distinguished order and take `u <_e v <_e w`. Write
`a = Pr[u ≺ v] = 1 − β(u,v)`, `b = Pr[v ≺ w] = 1 − β(v,w)`, `c = Pr[w ≺ u] = β(u,w)`
(the last because the majority on `{u,w}` is `u ≺ w`). Fact 1 says `a + b + c ≤ 2`, i.e.

> **Subadditivity of balance along the distinguished order.**
> For all `u <_e v <_e w`:  `β(u,w) ≤ β(u,v) + β(v,w)`.

Corollaries in the same vein: if `u < v` in `P` (so `β(u,v) = 0`) then `β(u,w) ≤ β(v,w)`
for every `w` above both in `e` — comparabilities propagate decidedness outward.

Every one of these is an **upper** bound on a balance. The system is **homogeneous**: if a
balance profile `β` satisfies it, so does `t·β` for every `t ∈ [0,1]`. In particular:

1. the identically-zero profile `β ≡ 0` is feasible — **a chain is frozen-coherent**
   (vacuously: no incomparable pairs, distinguished order = itself);
2. every constant profile `β ≡ δ` is feasible, since `δ ≤ δ + δ`. In particular the
   extremal profile `β ≡ 0.2764…` is feasible, and so is `β ≡ 10⁻¹⁰⁰`.

A homogeneous system of inequalities satisfied by `0` cannot imply *any* positive lower
bound on *any* monotone functional of `β` — in particular not on `max β = δ(P)`. That is
the whole story in one line: **the frozen condition pushes balances down, never up, and the
thing we need is a push up.**

Iterating subadditivity along `e = z₁ <_e ⋯ <_e z_n` gives
`β(z₁,z_n) ≤ Σᵢ β(zᵢ, zᵢ₊₁)`, which telescopes in the wrong direction and bottoms out at
the vacuous `β(z₁,z_n) ≥ 0`. There is no reverse-telescoping available.

---

## 4. The one door that is not obviously closed, and why it also fails

The frozen condition *is* a global structural statement (there exists a total order `e`
with which everything agrees strongly), and §3.2 only shows it cannot enter the
**inequalities**. It could conceivably enter the **selection step (SEL)**: instead of
choosing the pair by the expected-height pigeonhole, choose an incomparable pair `x,y` that
is **consecutive in `e`**.

This is a real structural handle. If `x,y` are `e`-consecutive then every other `z` is
either `>2/3`-below both or `>2/3`-above both — the poset looks, in the majority sense,
like `[block] ≺ {x,y} ≺ [block]`. Two reasons this does not move `0.2764`:

1. **It does not deliver the quantity (SEL) needs.** Writing
   `h(u) = 1 + Σ_{z≠u} Pr[z ≺ u]`, `e`-consecutiveness gives, for each `z <_e x`, both
   `Pr[z ≺ x] > 2/3` and `Pr[z ≺ y] > 2/3` — so each difference `Pr[z≺y] − Pr[z≺x]` is only
   confined to `(−1/3, 1/3)`, and `n−2` such terms are summed. `e`-consecutiveness gives
   **no** bound on `|h(x) − h(y)|`. It is a different, incomparable selection rule, not a
   stronger one.
2. **Even if it did, it changes only which pair is picked, not what can be proved about a
   picked pair.** The `0.2764` is the optimum of the local optimization over the data of the
   selected pair. A different selection rule feeds the *same* optimization; to beat `0.2764`
   the selection must supply an *additional local constraint*, and by §3.2 coherence supplies
   none.

---

## 5. What would actually have to be true to buy something

For the record, the shape of a hypothesis that could improve `0.2764`:

- it must **fail for chains** (any hypothesis a chain satisfies cannot force `δ > 0`, since
  a chain has `δ = 0` — this is exactly what kills coherence);
- it must be **not implied by `δ(P) < 1/3`** (or it is circular, per §3.1);
- it must produce a **lower** bound on some balance, or couple **≥ 4** elements in a way that
  is not automatic — note that transitivity of the majority tournament is *entirely* a
  statement about triples, and triples are automatic (Fact 1), which is why coherence has
  no content at any scale.

Coherence fails all three tests. It is not merely inert against the current extremal
configuration; it is inert against *every* configuration, because it is a theorem rather
than a hypothesis.

---

## 6. Answer to the ticket's three-way question

The ticket offered: *(a)* the frozen constraint excludes the `0.2764`-achieving
configuration → report the improved constant; *(b)* the constraint is inert because the
extremal configuration is already frozen-coherent.

The answer is **(b)**, but by a stronger route than (b) anticipated. It is not that the
extremal configuration *happens* to be frozen-coherent. It is that **no configuration is
excluded by coherence**, because:

- on the `≤ 3` elements the optimization sees, coherence is a universally true fact (§3.2);
- as a global condition, its content is a homogeneous system of upper bounds on balances,
  satisfied by a chain (§3.3);
- and as a hypothesis it is logically implied by `δ(P) < 1/3`, so it does not restrict the
  class of posets at all (§3.1).

**This one fact buys exactly nothing over `0.2764`.**

---

## 7. Status labels

| claim | status |
|---|---|
| Fact 1 (triple inequality `≤ 2`) | **PROVEN** (§1), plus exhaustive check on 4000 random posets, `n = 3..6` |
| Fact 2 (coherence from `δ < 1/3`) | **PROVEN** (§1) |
| (KS-2) `F(1) = F(−1)` | **PROVEN** (§2.3) |
| (KS-1) log-concavity of `F` | **CITED** — [KS84, Thm 2.5], quoted verbatim in Chan–Pak–Panova |
| (BFT) cross-product at `k=ℓ=1` | **CITED** — [BFT95, Thm 3.2], via Ahlswede–Daykin |
| `(5−√5)/10 = 1/(φ+2)` | **VERIFIED** numerically |
| exact BFT final optimization | **NOT OBTAINED** — primary sources paywalled; see honesty ledger §2.3. The verdict does not depend on it (§3.2). |
| §3.1, §3.2, §3.3 (inertness) | **PROVEN**, given the cited locality of (KS-1)/(BFT) |
| §4 (`e`-consecutive selection door) | **ARGUED, not fully formalized** — item 1 is a proven non-implication, item 2 is a structural argument about the shape of the optimization |
| provenance table §2.2 | **CITED** |

## 8. Sources

- J. Kahn and M. Saks, *Balancing poset extensions*, Order 1 (1984), 113–126.
- G. R. Brightwell, S. Felsner, W. T. Trotter, *Balancing pairs and the cross product
  conjecture*, Order 12 (1995), 327–349. <https://link.springer.com/article/10.1007/BF01110378>
- S. H. Chan, I. Pak, G. Panova, *The cross-product conjecture for width two posets*
  (statements of KS-1 and CPC quoted verbatim): <https://www.math.ucla.edu/~pak/papers/CP-v57.pdf>
- M. Aires, J. Kahn, *Balancing extensions in posets of large width*:
  <https://arxiv.org/pdf/2509.11549>
- E. Chen, *A family of partially ordered sets with small balance constant*:
  <https://arxiv.org/pdf/1709.05753>
