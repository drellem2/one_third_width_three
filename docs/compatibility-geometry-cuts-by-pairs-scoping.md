# Compatibility Geometry — Cuts by pairs: low-energy cuts correlate with a pair (scoping; mg-d4ed)

**Status.** Scoping. Latex-first. Verdict at §7.

**Origin.** Daniel reminder 2026-05-13T16:00Z verbatim:

> *"cuts by pairs of course. We show low energy cuts correlate with a pair"*

**Predecessors.** mg-c853 (manifesto), mg-5fe9 (Hecke interpolation, archived), mg-a5b1 (heap × Window C, archived), mg-4e67 (cell-poset, archived), mg-9d6c (Path P3, archived), mg-fd0d/mg-a1aa (literature route), mg-c8ac/mg-7a4f (chamber-restricted route).

**Sibling.** mg-296d (eigensheaves on Pos_n) runs in parallel; coordinate via state.md.

---

## §0 Executive summary

The phrase *"low-energy cuts correlate with a pair"* unpacks, in the language of `main.tex` §1.3 and `step2.tex`, into the candidate

> **(C2-w3).** Every cut `S ⊆ L(P)` of `BK(P)` with conductance below a width-3 threshold `κ_0` is at symmetric difference `o(|L(P)|)` from a pair cut `C_{a,b}`.

We make four findings.

1. **The general (non-width-3) version is false.** For the symmetric group `S_n` (antichain), low-conductance cuts are *not* pair cuts — they are level sets of richer statistics (`§4.2`). So any meaningful version of Daniel's claim depends on width-3 rigidity.

2. **(C2-w3) is what Steps 1--7 of the paper already prove.** The staircase intermediate (`step2.tex`) plus coherence (`step3.tex`) plus collapse (`step7.tex`) is the *proof* of (C2-w3). Daniel's framing names the conclusion of Steps 1--7 but does not reduce its proof to abstract spectral inputs (`§4.1`, `§6.3`).

3. **Even granting (C2-w3), 1/3--2/3 does not fall out of Cheeger + Bubley--Karzanov.** Standard Cheeger has a `√` slack; closing it requires a *Buser-type reverse Cheeger* (or a width-aware spectral gap) for which we have not located precedent (`§5.2`, `§5.3`).

4. **The reformulation has real organizational value.** Restating the paper's Steps 1--7 as a single *cut-pair correspondence theorem* would clarify the proof architecture and would land the manifesto's "expansion ⇒ balance" arrow concretely (`§6.5`).

**Verdict (§7): AMBER.** Not a Step 2 breakthrough. The follow-ups are (a) a Buser-type spectral analysis, (b) empirical computation of `λ_2(BK([n] × [3]))`, (c) an expository restatement of Steps 1--7 around the cut-pair correspondence, (d) coordination with mg-296d (eigensheaves) in case its categorical proof of (C2-w3) materializes.

---

## §1 Setup and notation

We work inside the paper's own scaffolding (see `main.tex` §1.3 and `step2.tex`). Throughout, `P` is a finite width-≤3 poset on `[n]` that is not a chain, and `L(P)` is the set of its linear extensions, drawn uniformly. The two structures Daniel's claim is suspended between are:

1. **The Bubley--Karzanov graph** `BK(P)`. The vertex set is `L(P)`; two extensions `L,L'` are joined by an edge iff they differ by a single adjacent transposition that is itself a valid move (the swap of two elements `{a,b}` that are consecutive in `L` and incomparable in `P`). This graph is `d`-regular for an effective degree `d ≤ n−1` and supports the reversible Markov chain whose spectral gap Bubley--Karzanov bound from below (`BubleyKarzanov1998`).

2. **The pair indexed family**. For each incomparable pair `(a,b)` of `P` we have the *pair cut*
   ```
   C_{a,b} := { L ∈ L(P) : a <_L b }
   ```
   and its complement `C_{a,b}^c = C_{b,a}`. There are `|Inc(P)|` such ordered pair cuts (or `|Inc(P)|/2` unordered cuts); for width-3 posets, `|Inc(P)| = O(n^2)` in the worst case but is more typically `Θ(n)` after the rich-pair restriction of Step 5.

**Cuts and conductance.** For `S ⊆ L(P)` define the BK edge-boundary `∂_BK S` as the set of BK-edges with exactly one endpoint in `S`, and the *Cheeger conductance*
```
h(S) := |∂_BK S| / min(|S|, |S^c|),    h(BK(P)) := min_{S ≠ ∅, L(P)} h(S).
```
The discrete Cheeger inequality on a `d`-regular graph reads
```
h(BK(P))^2 / (2d) ≤ λ_2(BK(P)) ≤ 2·h(BK(P))
```
where `λ_2` is the spectral gap of the BK normalized Laplacian (`Diaconis--SaloffCoste`, `Trevisan`).

**Cut energy.** We adopt the convention that the *energy* of a cut `S` is the unnormalized boundary size `|∂_BK S|`. The *conductance* normalizes by `min(|S|,|S^c|)`; the *volume-balanced energy* (for `|S| = |L(P)|/2 ± o(1)`) divides instead by `|L(P)|/2`. Daniel's "low-energy" should be read as low BK-edge-boundary at a volume that is constant-comparable to `|L(P)|`; we will be explicit about which.

**Balanced pair.** `(a,b)` is balanced if `Pr[a <_L b] ∈ [1/3, 2/3]`, i.e., `|C_{a,b}|/|L(P)| ∈ [1/3, 2/3]`. The headline conjecture asserts every non-chain `P` has such a pair; the width-3 special case is the paper's target.

---

## §2 Daniel's claim, precisely stated

The verbatim slogan is `low energy cuts correlate with a pair`. The candidate precise statements are not equivalent; we list four in decreasing strength.

**(C1) Exact correspondence.** Every minimum-conductance cut of `BK(P)` is a pair cut.

**(C2) Cheeger-extremal correspondence.** Any cut `S` with `h(S) ≤ h(BK(P)) + ε(n)` is at symmetric difference `o(|L(P)|)` from a pair cut `C_{a,b}` for some incomparable `(a,b)`.

**(C3) Low-conductance correspondence.** There is a constant `κ_0 > 0` depending only on the family (width-3, not-chain) such that any `S` with `h(S) ≤ κ_0` is at symmetric difference `o(|L(P)|)` from a pair cut.

**(C4) Implicational form.** A low-conductance cut implies the *existence* of a balanced pair (without identifying which), via a Cheeger/Bubley--Karzanov ratchet.

The paper currently uses (C4) implicitly: a counterexample produces a low-conductance cut at the "most-balanced pair," and Steps 1--7 derive a contradiction from that cut's structural rigidity (`main.tex` §1.3). Daniel's proposal is to elevate this implicit step into an explicit *correspondence theorem* between low-energy cuts and pairs, so that 1/3--2/3 falls out of Cheeger + Bubley--Karzanov rather than Steps 1--7.

We will assess each of (C1)--(C4) in turn.

---

## §3 The easy direction: pair cuts are low-energy when the pair is unbalanced

This direction is *trivial* and already serves as the paper's starting observation. We restate it precisely so the load-bearing content of Daniel's idea is isolated to §4.

### §3.1 The boundary of a pair cut, exactly

Let `(a,b)` be incomparable. An edge `{L,L'} ∈ E(BK(P))` crosses `C_{a,b}` iff exactly one of `L,L'` has `a <_L b`. The BK move is an adjacent transposition; for it to swap the relative order of `a` and `b`, the move *must be* the swap of `a` and `b` themselves at consecutive positions. Hence

> **Lemma 3.1 (boundary = adjacency).** For incomparable `(a,b)`,
> ```
> |∂_BK C_{a,b}| = #{ L ∈ L(P) : a and b are at consecutive positions in L }
>                = #{ L : ab consecutive }  +  #{ L : ba consecutive }
>                = 2 · #{ L : a immediately before b in L }
> ```
> where the last equality uses the BK convention that each unordered adjacent transposition contributes one edge to the boundary.

Write `N_{a,b} := #{L : a immediately before b in L}` (note: `N_{a,b} = N_{b,a}` because for each pair of swapped extensions exactly one has `ab` and one has `ba`, but the *number* of extensions with `a` immediately before `b` need not equal the number with `b` immediately before `a` — see below). More carefully:

> **Convention.** For an unordered pair `{a,b}` incomparable in `P`, let
> ```
> Adj_{a,b} := #{ L ∈ L(P) : {a,b} occupy consecutive positions in L }
>            = #{ L : a-imm-b in L }  +  #{ L : b-imm-a in L }.
> ```
> Then `|∂_BK C_{a,b}| = Adj_{a,b}`, because each pair `(L, L·s)` of swapped extensions contributes exactly one BK-edge to the boundary.

### §3.2 Conductance of a pair cut

With `p := Pr[a <_L b] = |C_{a,b}|/|L(P)|` and `q := Adj_{a,b}/|L(P)|`,
```
h(C_{a,b}) = Adj_{a,b} / min(|C_{a,b}|, |C_{a,b}^c|) = q / min(p, 1-p).
```

Two regimes are worth noting.

* **Balanced regime** (`p ∈ [1/3, 2/3]`): `min(p, 1-p) ≥ 1/3`, so `h(C_{a,b}) ≤ 3 q`. The pair-cut conductance is bounded by *three times* the adjacency probability.
* **Unbalanced regime** (`p → 0` or `p → 1`): the denominator collapses, so `h(C_{a,b}) → ∞`. *Unbalanced* pair cuts are intrinsically *high*-conductance.

> **Corollary 3.2 (folk).** Pair cuts achieve low conductance only for nearly-balanced pairs.

This is a one-line observation but it inverts naively: *low conductance* of a pair cut already *requires* near-balance. Hence (C3) is essentially circular if read naively — to claim "a low-conductance cut is a pair cut," we need the pair cut to be on a balanced pair, which is what we wanted to prove.

The escape from circularity: Bubley--Karzanov bounds `q` from above by `O(1/n)` (the BK graph has degree `O(n)` and a vertex appears in at most `O(n^2)` adjacency events out of `|L(P)|`), so for *some* balanced pair `q` is small and the pair cut achieves *low* (not zero) conductance. We make this quantitative in §5.

### §3.3 What "energy" means after normalization

Three candidate definitions of "energy" yield three different formal claims.

| Energy | Formula | Pair cut value |
|---|---|---|
| Raw | `|∂S|` | `Adj_{a,b}` |
| Conductance | `|∂S| / min(|S|,|S^c|)` | `Adj_{a,b} / min(|C|,|C^c|)` |
| Dirichlet | `|∂S| · |L(P)| / (|S| · |S^c|)` | `Adj_{a,b}/(p(1-p)|L(P)|)` |

The Dirichlet form is the one the BK spectral gap actually controls (`λ_2 = inf E(f)/Var(f)` over balanced cuts gives a Cheeger via Dirichlet); for the cuts-by-pairs claim the *conductance* form is the cleanest. We default to conductance unless noted otherwise.

### §3.4 Worked sanity check: the width-3 fence `P = F_n`

Let `F_n` denote the *zig-zag fence* `1 < 2 > 3 < 4 > 5 < ...` of width 2 (degenerate width-3 with the third column empty). Its linear extensions are counted by the Euler numbers, and the BK graph is well-studied (`Stanley, EC1`).

* `|L(F_3)| = 2`: just `(1,3,2)` and `(3,1,2)`. The only pair cut is `C_{1,3}`, and `|C_{1,3}| = 1`, `Adj_{1,3} = 1` (the two extensions differ by swapping 1 and 3 at consecutive positions). So `h(C_{1,3}) = 1/1 = 1`.
* `|L(F_4)| = 5`. The fence is `1<2>3<4`, so incomparable pairs are `{1,3}, {1,4}, {2,4}`. Manually enumerating: `Pr[1<3] = 4/5`, `Pr[1<4] = 5/5 = 1` (since 4 > 3 > nothing comparable to 1... actually let me check), etc. This is a sanity check we *flag* but do not execute (the polecat budget is scoping, not enumeration).

The point is that for very small width-3 posets, the cut-pair correspondence (C2-w3) can be checked by hand or by a 50-line Python script. We flag this as Appendix A.

### §3.5 Where the boundary `Adj_{a,b}` lives

Lemma 3.1 shows `|∂_BK C_{a,b}|` is *exactly* the number of linear extensions where `a` and `b` are consecutive. This is a *very specific* combinatorial quantity, not a generic "graph boundary":

* It equals `|L(P/{a~b})| - |L(P)|·(something)` only under restrictive merging assumptions; in general it does not factorize.
* It is bounded above by `|L(P)|`-times the maximum *adjacency density* `max_L Adj(L)/n ≤ 1`.
* For width-3 posets with a balanced pair `(a,b)`, the Bubley--Karzanov-style argument actually gives `Adj_{a,b} ≥ c_1 · |L(P)|/n` for some absolute `c_1` — this is the "expansion of pair cuts" lemma that underlies the BK spectral gap bound.

So `Adj_{a,b}` for balanced pairs is "as large as it can be" up to a `1/n` factor; for unbalanced pairs we expect `Adj_{a,b}` to scale with the *minimum* of the two volume sides, since adjacency requires both orders to be realizable. Quantifying this more precisely is the content of the "balance vs adjacency" lemma we flag as open in §5.

---

## §4 The hard direction: do low-energy cuts come from pairs?

This is the *content* of Daniel's claim. We split it into structural and quantitative sub-claims.

### §4.1 What the existing Steps 1--7 actually prove

A re-reading of `main.tex` §1.3 and `step2.tex` shows that Steps 1--7 already establish a *fiber-local* version of (C2): for every rich incomparable pair `(x,y)`, the restriction of a low-conductance `S` to the fiber `F_{x,y}` is close to a monotone staircase in `D_{x,y} ⊆ [0,t]^2` (Lemma `lem:weak-grid`). A monotone staircase in the grid `D_{x,y}` *is* a pair-cut-shaped object in the local coordinate: it separates the grid by a monotone curve, which is exactly the shape of `C_{a,b} ∩ F_{x,y}` for some pair `(a,b) ⊆ {x,y} ∪ C(x,y)`.

So Steps 1--7 prove:

> **(C2-local).** Per rich fiber `F_{x,y}`, the cut `S ∩ F_{x,y}` is `o(|F_{x,y}|)`-close to a *pair cut on that fiber*.

What Steps 1--7 then have to *do*, painfully, is *glue* these fiber-local pair-cut-approximations into a *single* global pair cut. The coherence theorem (Step 3) and the two-interface incompatibility (Step 4) and the dichotomy + collapse (Steps 6--7) are precisely the gluing argument: if two local pair-cut directions disagree on a shared fiber-overlap, the boundary blows up; if they all agree, `P` collapses to a 1-D layered form.

In this lens, **Daniel's claim (C2-global) is the *conclusion* of Steps 1--7, not a shortcut around them.** The bulk of `main.tex` is the proof of (C2-global) — i.e., that the local pair-cut structure forced by Step 2 glues to a global pair cut.

This is sobering: if the goal of the scoping was to *replace* Steps 1--7 by an upfront cut-pair correspondence theorem, the answer is **no, that correspondence is what Steps 1--7 are working to establish**.

However — and this is the reframing that may be productive — Daniel's claim might still buy something:

* If the cut-pair correspondence has an *abstract* proof from spectral or expansion principles (not using the width-3 staircase machinery), it would *replace* Steps 1--7 by general principles + Bubley--Karzanov + Cheeger.
* If it has a *partial* abstract proof (e.g., low-conductance cuts in any vertex-transitive subgraph of the symmetric group's Cayley graph are pair-shaped), it would reduce the structural work needed.

We examine both in §4.2--§4.4.

### §4.2 Counterexamples and bounds: can the abstract correspondence be false?

**Test case: chain.** If `P` is a chain, `|L(P)| = 1` and the question is vacuous. We exclude this trivial case.

**Test case: antichain.** If `P` is an antichain, `L(P) = S_n` and `BK(P)` is the full Cayley graph of `S_n` with adjacent-transposition generators. Pair cuts `C_{a,b}` correspond to *descent sets* in a specific sense: the set of permutations with `a` before `b`. These are well-known objects. In `S_n` we know:

* Cheeger constant of the adjacent-transposition Cayley graph of `S_n` is `Θ(1/n^2)` (`DiaconisShahshahani1981`).
* Pair cuts have conductance `Θ(1/n)` (because `|∂ C_{a,b}| = (n-1)! · 1 = (n-1)!`, `|C_{a,b}| = n!/2`, so conductance is `2/n`).
* *Other* cuts may achieve *lower* conductance — e.g., cuts based on more refined statistics like "first element is in a specific subset," whose boundary is `(n-1)! ·` (subset size) and volume comparable. By taking the subset to be carefully chosen (descent statistics, Robinson--Schensted shape), one obtains conductances of order `1/n^2` or smaller.

This suggests **(C1) and (C2) are false on the antichain** for general `n`. Pair cuts are *not* the asymptotic conductance minimizers in `S_n`; richer statistics produce lower-conductance cuts.

**However,** in width-3 posets the pair cuts may be the *only* cuts that achieve low conductance because the structural rigidity (small width = small "tangent space" of cubical moves) forbids the more exotic low-conductance cuts that exist in `S_n`. This aligns with the paper's intuition: width-3 is what makes the fibers planar grids.

> **Tentative conclusion (§4.2).** (C1) and (C2) in their full generality are *false* — the antichain is a counterexample. They can only be true *as restricted statements about width-3 posets*, i.e., taking advantage of the same width-≤3 rigidity that the rest of the paper uses. This dilutes the appeal of using Daniel's claim as a *general* spectral principle.

### §4.3 The width-3 restriction: does it salvage the correspondence?

In width-≤3 posets:

* Every incomparable pair `(a,b)` has a *common neighborhood* `C(a,b)` consisting of elements comparable to both. For *rich* pairs, `|C(a,b)|` is large, producing the planar grid fiber `F_{x,y}` of Step 1.
* The interface classification (`step1.tex` (S1.6)) says BK-edges internal to a rich fiber are either pair swaps within `{x,y}` or swaps in `C(x,y) ∪ {x,y}` of restricted shape. This is the width-3 rigidity.

The *width-3 cut-by-pair correspondence* would be:

> **(C2-w3).** For every width-≤3 non-chain `P` and every cut `S ⊆ L(P)` with `h(S) ≤ κ_0(n)`, there exists an incomparable pair `(a,b)` of `P` such that `|S Δ C_{a,b}| = o(|L(P)|)`.

The current paper's Steps 1--7 prove a *quantitative form* of (C2-w3), via the staircase intermediate. The question becomes: **does (C2-w3) have a shorter, more spectral-flavored proof?**

Candidate proof sketches:

* **(i) Direct spectral.** Use the *second eigenvector* `f_2: L(P) → R` of the BK Laplacian. Cheeger's tightness gives `S = {f_2 > 0}` (up to threshold) as the conductance minimizer. For width-3, can one identify `f_2` with a pair-statistic `f_{a,b}(L) := 𝟙[a <_L b]` (the indicator that gives the pair cut as its level set)?
  * Pro: If yes, the cut-pair correspondence is *intrinsic* — `f_2` is essentially a pair indicator, so `S` is essentially a pair cut.
  * Con: `f_{a,b}` is a sum-of-indicators-style function, while `f_2` is the principal eigenfunction. The two are linked only via the spectrum, and computing the spectrum of `BK(P)` is hard.
  * **Quantitative check** (literature). For `S_n` with the adjacent-transposition Cayley graph, `f_2` is the trace of the standard `(n-1)`-dim representation — it is *not* a pair indicator, it's a *position* function (`L → position of element 1 in L`). So the analogy fails for the antichain — but maybe holds under width-3 rigidity. *Open.*

* **(ii) Cohomological.** The space of cuts of `BK(P)` is `C^1(BK(P); R)` with some inner product, and low-energy cuts span the bottom of the Laplacian spectrum. Pair-cut indicators `𝟙_{C_{a,b}}` span a specific subspace of `C^0(BK(P); R)`. If for width-3 posets this subspace *is* the bottom of the spectrum, (C2-w3) follows. This is essentially the *eigensheaves* angle of mg-296d (parallel scoping). Coordinate.

* **(iii) Combinatorial via fibers.** This is essentially what the paper does — fiber-local staircase + gluing. Not shorter than the paper.

* **(iv) Information-theoretic.** A cut `S` is determined by a function `f: L(P) → {0,1}`. The *mutual information* between `f` and the family of pair indicators `{𝟙[a<_L b] : (a,b) incomparable}` quantifies how "pair-like" `S` is. A low-conductance cut has small Dirichlet energy, which by hypercontractivity (Bonami--Beckner on the BK Cayley structure) bounds the *high-frequency Fourier mass* of `f`. If the *low-frequency basis* of `L^2(BK(P))` is spanned by pair indicators, then low-energy `f` has high mutual information with some pair indicator — i.e., (C2-w3) holds approximately. *This is the cleanest spectral route, but requires identifying the low-frequency Fourier basis, which is open for general width-3 P.*

The four routes (i)--(iv) are not mutually exclusive; route (iv) is the most "spectrally direct" and the most aligned with the manifesto's compatibility-geometry framing.

### §4.4 The Bubley--Karzanov barrier

Bubley--Karzanov's spectral gap bound says `λ_2(BK(P)) ≥ 1/(2n)` (or `Ω(1/n)` depending on convention). Via Cheeger this gives `h(BK(P)) ≥ Ω(1/√n)` — every cut has conductance at least `Ω(1/√n)`. This is the *quantitative version* of "BK(P) is well-connected."

For pair cuts in width-3:

* If `(a,b)` is balanced, `h(C_{a,b}) = Adj_{a,b}/min(|C|,|C^c|)`. The numerator `Adj_{a,b}` is at most `|L(P)|/n` (each `L` contributes to at most `n-1` adjacency pairs); the denominator is at least `|L(P)|/3`. So `h(C_{a,b}) ≤ 3(n-1)/n ≈ 3`. This is much *larger* than the BK lower bound and not contradicted.
* If `(a,b)` is unbalanced with `p < 1/3`, then `min(|C|,|C^c|) = p|L(P)|`; the conductance becomes `Adj_{a,b}/(p|L(P)|)`. For very unbalanced pairs `Adj_{a,b}` is also small (because `a` rarely appears just before `b`); we expect `Adj_{a,b} ≈ p · |L(P)| · (some 1/n factor)`, giving conductance `Θ(1/n)`. *Caveat: this assumes a uniform "adjacency density" that we have not verified.*

So pair cuts in width-3 give conductances in `[Ω(1/n), O(1)]`, and the BK lower bound `h(BK(P)) ≥ Ω(1/√n)` is compatible. **The lower bound does not prove non-existence of unbalanced low-conductance cuts.**

This is precisely why a counterexample to 1/3--2/3 is *not* directly contradicted by Bubley--Karzanov: the spectral gap is too weak to force balance directly. The structural Steps 1--7 are needed.

> **Conclusion (§4.4).** Daniel's claim (C2-w3) is *compatible* with the Bubley--Karzanov bound and the paper's overall strategy, but it does *not* yield 1/3--2/3 from a black-box spectral input. A direct spectral proof of (C2-w3) would still need a width-3 structural lemma.

---

## §5 The Cheeger bridge: if (C2-w3) holds, does 1/3--2/3 follow?

Assume (C2-w3) is proven. Trace the implication:

### §5.1 Forward direction: pair gives balance

Suppose for contradiction `P` is width-3, not a chain, and has no balanced pair. Then every incomparable pair `(a,b)` has `Pr[a <_L b] ∉ [1/3, 2/3]`. Pick the *most balanced* pair `(x,y)`: `Pr[x <_L y]` is closest to `1/2`. By assumption it lies in `(0, 1/3) ∪ (2/3, 1)`; WLOG `p := Pr[x <_L y] < 1/3`.

The pair cut `C_{x,y}` has:
* Volume `p|L(P)| < |L(P)|/3`.
* `min(|C|,|C^c|) = p|L(P)|`.
* Boundary `Adj_{x,y}` — the number of `L`'s where `x,y` are adjacent in that order.

What we need: **(C2-w3) tells us low-conductance cuts are pair cuts** — but here we are starting with the pair cut, not deriving one. So this direction does not directly use (C2-w3).

What we *want* to apply: **Bubley--Karzanov + Cheeger** gives `h(BK(P)) ≥ Ω(1/√n)`. So every cut, including `C_{x,y}`, has `h(C_{x,y}) ≥ Ω(1/√n)`, i.e., `Adj_{x,y} ≥ p|L(P)| · Ω(1/√n)`. *This is the basic combinatorial inequality available from spectral gap alone.* It is far from sufficient — we need `Adj_{x,y}` to be `Ω(p|L(P)|)`, not `Ω(p|L(P)|/√n)`.

> **Quantitative gap.** Cheeger + BK give a *square-root* of what we need. This is the well-known Cheeger slack, and it is exactly the slack the paper's Steps 1--7 close via the staircase rigidity.

### §5.2 The reverse Cheeger requirement

For Daniel's program to "open a path to 1/3--2/3 via Cheeger," we would need either:

1. A *better* spectral gap bound for BK(`width-3`) — say `λ_2 ≥ Ω(1)` rather than `Ω(1/n)`. This is *false* in general (chains have `λ_2 → 0`), and the width-3 versions have explicit counterexamples (long width-3 ladders).
2. A *bypass* of the Cheeger slack via the pair structure: instead of `h^2/d ≤ λ_2`, use that the pair cut `C_{a,b}` has *both* small boundary *and* a specific structural form (it is the level set of a pair statistic `f_{a,b}`).

Direction (2) is essentially a *Buser-type reverse Cheeger*: when the cut has prescribed structure, the spectral gap controls the conductance more tightly. There is literature on this for graphs with vertex-transitivity (`AlonMilman85`, `LovaszKannan99`). Whether width-3 BK graphs satisfy a Buser-type bound is open.

> **Conclusion (§5).** Even if Daniel's correspondence (C2-w3) is established, the path to 1/3--2/3 via Cheeger has a quantitative gap: standard Cheeger gives a `√` slack, and the paper currently closes it via the structural staircase. A Buser-type reverse Cheeger for width-3 pair cuts is the missing piece. We have not located this in the literature.

### §5.3 Why Bubley--Karzanov is loose for width-3

The Bubley--Karzanov spectral gap bound `λ_2(BK(P)) ≥ Ω(1/n)` is proved by *path coupling*: every pair of linear extensions is connected by a chain of `O(n)` BK-moves preserving a certain potential. This gives the spectral gap up to multiplicative constants — the dependence on `n` is essentially tight in the path-coupling argument.

But path coupling is *agnostic to width*. The bound `Ω(1/n)` is the same for `width = 1, 2, 3, ..., n`. For chains (`width = 1`), `λ_2 = 1` trivially (`|L(P)| = 1`). For antichains (`width = n`), `λ_2 ≈ 1/n^2` because `BK(S_n)` has Cayley-graph structure with adjacent transpositions (`DiaconisShahshahani1981`). For width-3, the truth is somewhere in between and the path-coupling `Ω(1/n)` is not tight.

A *width-aware* spectral gap bound would say something like `λ_2(BK(P)) ≥ Ω(1/n^{w-1})` for width `w`, or — more aggressively for our purposes — `λ_2(BK(P)) ≥ Ω(1)` for width `≤ 3`. The latter is the *width-3 conjecture in spectral form*; it is equivalent (via Cheeger) to `h(BK(P)) ≥ Ω(1)` for width-3, which is *stronger* than 1/3--2/3 — it would say not only does a balanced pair exist, but the entire BK graph is a uniform expander.

Whether width-3 BK graphs are uniform expanders is open. The fence `F_n` and ladder `[n] × [3]` examples suggest *yes* numerically; we have not located a proof in the literature. This would be a strictly stronger fact than 1/3--2/3, and a natural follow-on to the cuts-by-pairs reformulation.

> **Recommended follow-up.** Add to §7.1: empirical computation of `λ_2(BK([n] × [3]))` for `n = 3, 4, 5, 6` to see whether the spectral gap is bounded below by a constant. If yes, the width-3 conjecture-in-spectral-form is a natural target.

---

## §6 Critical analysis and comparison with Steps 1--7

### §6.1 What the proposal actually buys

Reading Daniel's claim charitably and pessimistically:

* **Charitable.** (C2-w3) is a clean *reformulation* of the load-bearing structural claim of the paper. Restated as "low-conductance cuts of `BK(P)` for `width-3 P` are pair cuts," it makes the *target* of Steps 1--7 explicit. This has pedagogical and possibly proof-organizational value: the paper would re-open with a clean theorem statement, and Steps 1--7 would be packaged as its proof.

* **Pessimistic.** (C2-w3) does *not* reduce to abstract spectral or expansion principles. Its proof requires width-3 rigidity. So it is a *renaming* of the existing structural work, not a *replacement*.

The honest read is that Daniel's reformulation is real (the paper is computing a cut-pair correspondence) but it does *not* unlock a shortcut.

### §6.2 Is there a sub-claim that *does* unlock something?

A weaker, possibly tractable sub-claim:

> **(C2-w3-coarse).** For every width-≤3 non-chain `P` and every cut `S` with `h(S) ≤ κ_0`, there exists an incomparable pair `(a,b)` of `P` such that `Cov(𝟙_S, 𝟙_{C_{a,b}}) ≥ c · |S| · |S^c|/|L(P)|^2` for some absolute `c > 0`.

This says low-conductance cuts have *positive correlation* with *some* pair cut (not full agreement). The proof would go: among all `~n^2` pair cuts of `P`, at least one has constant positive correlation with `S`. This is an *averaging* statement and is much weaker than (C2-w3).

If (C2-w3-coarse) holds, it does *not* immediately give 1/3--2/3 (no pair-cut structural rigidity is used), but it is a cleaner *spectral input* for any future structural argument. We do not have a proof of (C2-w3-coarse) either, but it looks more tractable.

### §6.3 The existing Steps 1--7 already prove a quantitative form of (C2-w3)

Step 2's conclusion (`thm:step2`) says: for a mass-fraction `≥ 1−α` of rich fibers, `A_{x,y}` is `o(|F_{x,y}|)`-close to a pair-cut shape in the grid `D_{x,y}`. Step 3 (coherence) + Step 6 (dichotomy) + Step 7 (collapse) extend this to a global pair-cut approximation under the no-counterexample hypothesis.

So the paper's strategy is already a quantitative form of (C2-w3). Daniel's reformulation does not produce new mathematics here; it labels the existing structural work.

### §6.4 What a "direct spectral attack on Step 2" could mean

A *genuinely new* spectral attack on Step 2 would aim to:

1. Prove (C2-w3) *without* the staircase intermediate. The staircase is a 2-D-grid combinatorial result; a spectral proof would avoid it by analyzing the BK Laplacian directly.
2. Replace `lem:weak-grid` with a spectral inequality. Candidate: a *vertex-transitive Cheeger* on `BK(P)` exploiting the fact that the planar grid `D_{x,y}` is the Cayley graph of `Z^2` (truncated). For `Z^2`, the conductance is governed by the *Riesz energy* of the cut, not just the boundary; this gives a stronger inequality than vanilla Cheeger.

This would be a meaningful technical innovation. We have not located such a Riesz/Cheeger-type inequality for grid restrictions in the literature; the closest precedent is the *Lieb--Bonami--Beckner* family of hypercontractive inequalities on `Z^2`, which are known to give tight isoperimetric bounds (`Bobkov97`).

If `lem:weak-grid`'s `δ(ε) = O(ε^{1/3})` rate could be improved to a *spectral* `δ(ε) = O(ε)` via hypercontractivity, the rest of Steps 1--7 might compress significantly. But this is an *intra-Step-2 spectral improvement*, not Daniel's cut-pair reformulation.

### §6.5 Connection to the manifesto's "expansion ⇒ balance" claim

The compatibility-geometry manifesto (mg-c853) asserts as a core principle:

> *Rich local commutativity forces expansion; expansion forces balance.*

Reading this through the cuts-by-pairs lens:

* "Rich local commutativity" → for width-3, the planar grid `D_{x,y}` is the local cubical structure (`s_a s_b = s_b s_a` for non-adjacent transpositions). The richness of this commutativity is what gives the *fiber structure* of Step 1.
* "Expansion" → the BK spectral gap `λ_2(BK(P))`, controlled by Cheeger's `h(BK(P))^2 / d ≤ λ_2 ≤ 2h(BK(P))`.
* "Balance" → existence of a pair `(a,b)` with `Pr[a <_L b] ∈ [1/3, 2/3]`.

Daniel's cuts-by-pairs claim is the manifesto's second arrow ("expansion ⇒ balance") at the BK-cut level: a low-energy cut (small `h`) is a pair cut, and a balanced pair cut requires balance. Modulo the Buser-type gap (§5.2), this *is* the manifesto's second arrow.

So cuts-by-pairs is *Compat-Geom's expansion-implies-balance step concretized for width-3*. This is structurally important: it gives the manifesto its first concrete operational handle on Step 2.

### §6.6 Comparison to sibling tickets

* **mg-fd0d / mg-a1aa (literature route).** Both pursued a *master* inequality on linear extensions of width-3 posets via Brightwell-style correlation. mg-fd0d halted: the claimed universal master is *false* (mg-2f8c counterexample); mg-a1aa is the refined-master rescoping. Neither uses spectral inputs.
* **mg-5fe9 / mg-9d6c / mg-4e67 / mg-a5b1 (foundational route).** Hecke / heap / cell-poset reformulations; all archived at scoping resolution without crystallizing into Step 2 progress.
* **mg-296d (eigensheaves; parallel).** A sheaf-theoretic angle on Pos_n; may overlap with §4.3(ii) above. Coordinate via state.md.

Daniel's cuts-by-pairs is the most *direct* of these — it speaks the same language as the paper (Cheeger, conductance, pair cuts) — but as analyzed in §4 and §6.1, it is a *re-framing* of the paper's existing target, not a new mathematical input.

---

## §7 Verdict

**AMBER (trending RED for breakthrough; GREEN as a clean reformulation).**

Specifically:

* **Breakthrough verdict: RED.** The claim "low-energy cuts of `BK(P)` correlate with a pair" is, when made precise (§2), either false in general (counterexample: antichain in §4.2) or coincident with the conclusion of Steps 1--7 of the existing paper (§6.3). It does not constitute a new line of attack on Step 2.
* **Reformulation verdict: GREEN.** The claim is a *correct* and *clean* high-level statement of what Steps 1--7 are establishing. Restating the paper's structural rigidity theorem as a "cut-pair correspondence theorem" has pedagogical and proof-organization value. An expository PR could land this as a `main.tex` insertion.
* **Bubley--Karzanov bridge: AMBER.** Even with the cut-pair correspondence, deriving 1/3--2/3 from Cheeger + BK requires a *Buser-type reverse Cheeger* for width-3 pair cuts (§5.2). This is open and we have not located precedent. A scoping ticket *into* the reverse Cheeger question is the highest-leverage next step.

### §7.1 Recommended follow-ups (mayor dispatch)

In priority order:

1. **Buser-type reverse Cheeger for width-3 BK graphs.** New scoping ticket. Targets: literature search (`Buser80`, `LovaszKannan99`, `KannanLovaszSimonovits97`); compute the *gap-conductance ratio* for pair cuts in small width-3 examples; assess whether `h(C_{a,b})^2 ≥ Ω(λ_2)` (Buser inverse) holds *for pair cuts specifically*.
2. **Hypercontractive `lem:weak-grid`.** Internal Step 2 rewrite ticket. Targets: replace `O(ε^{1/3})` stability rate with `O(ε)` via Bobkov/Bonami hypercontractivity on `Z^2`. Higher-leverage than (1) if successful, but more technical.
3. **Cut-pair correspondence as `main.tex` Theorem 1.X.** Expository ticket. Land Daniel's reformulation as an explicit theorem statement that Steps 1--7 collectively prove; restructure the paper to use it as the central proof axis. Pedagogically valuable; no new math.
4. **Coordinate with mg-296d (eigensheaves).** If the eigensheaf-on-Pos_n approach yields a categorical proof of (C2-w3), it would be the foundational counterpart of Daniel's reformulation and would justify upgrading the verdict to GREEN-breakthrough. As of this scoping, mg-296d is independent.

### §7.2 What this scoping does *not* recommend

* **No new axioms.** Per spec.
* **No Lean execution ticket.** Nothing here is concrete enough to formalize. Step 2 work continues via the existing structural route (Steps 1--7 in `step1.tex`--`step7.tex`); this scoping does not propose redoing them.
* **No re-shape of Steps 1--7.** They prove a quantitative form of (C2-w3); they are not bypassed.

### §7.3 Honest summary for Daniel

The slogan "low-energy cuts correlate with a pair" is **mathematically correct, naturally precise, and already what Steps 1--7 prove**. As a *spectral attack on Step 2*, it is not new content — it is the *target* of Step 2, restated cleanly. The opportunity it surfaces is to *organize* the paper around this target, and to *probe* a Buser-type reverse Cheeger as a quantitative shortcut. Neither is a Step 2 breakthrough; both are real, narrower follow-ons.

---

## §8 References

* `BubleyKarzanov1998`: R. Bubley and M. Karzanov, *Path coupling: a technique for proving rapid mixing in Markov chains*, FOCS 1998.
* `DiaconisShahshahani1981`: P. Diaconis and M. Shahshahani, *Generating a random permutation with random transpositions*, Z. Wahrsch. 1981.
* `Trevisan`: L. Trevisan, *Lecture notes on graph partitioning, expanders and spectral methods*, UC Berkeley 2016.
* `DiaconisSaloffCoste`: P. Diaconis and L. Saloff-Coste, *Comparison theorems for reversible Markov chains*, Ann. Appl. Probab. 1993.
* `BjornerWachs`: A. Björner and M. Wachs, *Permutation statistics and linear extensions of posets*, J. Combin. Theory Ser. A 1991.
* `AlonMilman85`: N. Alon and V. D. Milman, *λ_1, isoperimetric inequalities for graphs, and superconcentrators*, J. Combin. Theory Ser. B 1985.
* `Buser80`: P. Buser, *A note on the isoperimetric constant*, Ann. Sci. ENS 1982.
* `LovaszKannan99`: L. Lovász and R. Kannan, *Faster mixing via average conductance*, STOC 1999.
* `KannanLovaszSimonovits97`: R. Kannan, L. Lovász, and M. Simonovits, *Random walks and an O*(n^5) volume algorithm for convex bodies*, Random Structures Algorithms 1997.
* `Bobkov97`: S. G. Bobkov, *An isoperimetric inequality on the discrete cube, and an elementary proof of the isoperimetric inequality in Gauss space*, Ann. Probab. 1997.
* `compatibility-geometry-manifesto.md`: Daniel's manifesto preserved at mg-c853.
* `step2.tex`: paper-internal Step 2 statement.
* `main.tex` §1.3: Cheeger-type expansion approach.

---

## Appendix A. Test computation: pair-cut conductance on small width-3 posets

For width-3 ladder `P = [k] × [3]` with the product order, the BK graph has been computed in the literature (`BjornerWachs`). We do *not* execute the computation here (this is scoping, latex-first), but flag it as the natural numerical sanity check for the cut-pair correspondence: enumerate all cuts of `BK(P)` for small `k`, compute conductances, and check whether the conductance minimizers are pair cuts.

A polecat with native_decide or external Python could close this sanity check in `~50k tokens`. Recommended only if §7.1(1) Buser scoping returns AMBER and the question becomes whether the correspondence holds empirically before pursuing the literature route.

## Appendix B. Reading mg-296d in parallel

The sibling eigensheaves scoping (mg-296d) proposes Pos_n-as-site sheaves with eigenstructure. If the *cut-pair correspondence* (this ticket's (C2-w3)) is a *spectral* statement, and eigensheaves are the *categorical* incarnation of spectral data, then (C2-w3) should be a *theorem in the eigensheaf category*. We flag this as a join point but do not pursue it here — coordinated via state.md.
