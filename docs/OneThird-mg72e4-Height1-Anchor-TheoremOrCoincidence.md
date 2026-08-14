# Is `H̃_{n−2}(lk_{Δ_n} P) = 0` at height-1 vertices a THEOREM or a small-`n` coincidence? (mg-72e4)

*Answers the single follow-up `mg-e08a` named and `mg-1b3b` carried into
[`OneThird-mg52c4-PerPoset-Subposet-Question.md`](OneThird-mg52c4-PerPoset-Subposet-Question.md)
§5. Instrument: [`scripts/compat_geom_mg72e4_height1_anchor.py`](../scripts/compat_geom_mg72e4_height1_anchor.py),
output [`data/onethird-mg72e4-height1-anchor.json`](../data/onethird-mg72e4-height1-anchor.json).
Run: `/usr/bin/python3 scripts/compat_geom_mg72e4_height1_anchor.py` (stdlib only, `ALL_PASS = True`).*

> **The ticket, as filed:** *"every case is a one-degree near-miss and no dimension argument
> forces it"* — verified at `n = 3, 4, 5` only, and *"if it is a coincidence the closed direction
> REOPENS."*

---

## 0. Verdict

> ### The "one-degree near-miss" is an `n = 4` ARTIFACT. The margin is `n − 3` and it GROWS.
>
> ### The question is not settled as a theorem, but the reason to suspect a coincidence is gone, and the measurement now runs through `n = 7` — 163 iso classes and 227 850 of the 227 892 labelled height-1 vertices there, **0 violations**.

Four results, in descending order of how much they should change what anyone does.

1. **The evidence for "coincidence" was an `n = 4` artifact.** `mg-e08a` measured the anchor
   degree and its neighbours and found the nearest non-vanishing degree exactly one away — at
   `n = 4`. Measured over the *whole* homotopy type of the relevant complex (§4), the nearest
   non-vanishing degree is **`n − 3`**, and the needed degree is `n − c − 1`, so the margin is
   **`c − 2`**, minimum `n − 3` over the classes where anything is non-zero:

   | `n` | min margin | degrees where `Γ(P)` has homology |
   |---|---|---|
   | 4 | **1** | `{0, 1}` |
   | 5 | **2** | `{2}` |
   | 6 | **3** | `{3}` |
   | 7 | **4** (see §4.2) | `{4}` |

   A quantity that misses by one at `n = 4`, by two at `n = 5`, by three at `n = 6` and by four at
   `n = 7` is not behaving like arithmetic luck. **`n = 7` matters specifically**: it is where
   `mg-24eb`'s *"exactly the ordinal sums"* coincidence broke, which is the precedent `mg-52c4` §5
   cites as the reason to suspect this one.

2. **The measurement is no longer expensive, and it now reaches `n = 7`.** Björner's **crosscut
   theorem** replaces the order complex of the upper link — whose vertex set is most of `PPF_n`,
   which is what put `mg-e08a`'s three `n = 5` classes over its materialisation cap — by a complex
   `Γ(P)` on **at most `n(n−1) − 2c` vertices** (§3). At `n = 6` the largest `Γ(P)` has 20
   vertices; at `n = 7`, 30. The `n ≤ 6` sweep runs in about 20 seconds and `n = 7` in minutes,
   where the direct computation was infeasible. **`mg-e08a`'s three uncomputed `n = 5` classes are
   computed here** (§4): the `n = 5` evidence is 20/20 iso classes, not 58/61.

3. **A piece of it is now a theorem, not a measurement** (§5): for `c ≥ n` the vanishing follows
   from `U(P) ≠ ∅`, which is proven for every `n ≥ 6` with no measurement. That is 3 590 of the
   11 642 height-1 vertices at `n = 6` (30.8%) and 110 082 of the 227 892 at `n = 7` (48.3%) —
   a share that grows with `n`. The rest is still measurement.

4. **The structure the remaining conjecture needs is now explicit and small.** What is left to
   prove is a *connectivity* statement about one concrete complex — `Γ(P)` is `(n−4)`-connected —
   not a dimension count. **The naive dimension argument was always going to fail, and the reason
   is now visible:** `Γ(P)` really does carry homology, in degree `n − 3`, for a specific and
   identifiable family of `P` (§4.3). A dimension argument cannot see the difference between
   degree `n − 3` and degree `n − c − 1`; a connectivity argument can.

**What this does NOT do.** It does not prove the statement for all `n`. §7 says exactly what is
open and what would close it. And it does **not** reopen the F-series: see §8.

---

## 1. Controls first

Three, and the design follows `mg-e08a`'s: an instrument that cannot fail is not evidence.

**H1 — the homology routine against independently known answers.** `∂Δ^k ≃ S^{k−1}` for
`k = 1..5`; the standard 7-vertex `Z₇` torus `(β̃₀, β̃₁, β̃₂) = (0, 2, 1)`; the empty complex
`= S^{−1}`. All reproduce.

**H2 — the crosscut reduction against a DIRECT computation.** This is the load-bearing control,
because §3 is where an error would be invisible. For **every one of the 12 vertices of `Δ₃` and
all 194 of `Δ₄`** — not only the height-1 ones — the instrument computes the upper link
`Δ(↑P ∖ {P})` **directly from the poset** and compares its full reduced Betti vector with
`Γ(P)`'s. **206/206 agree.** It also computes `Δ(L̄(P))` and `lk_{Δ_n}(P)` directly and checks the
join formula `lk = Δ(L̄(P)) ∗ Δ(↑P ∖ {P})` at all 206: **206/206 agree.**

**H3 — the instrument reproduces `mg-e08a`'s published numbers without importing them.** Nothing
in this instrument is imported from the repo; poset enumeration, transitive closure, the order
complex and the two-prime Betti routine are written from scratch. It independently recovers:

| `mg-e08a` figure | reproduced here |
|---|---|
| 38 of 194 links non-contractible at `n = 4`, all height-1 | **38** |
| `β̃₃ = 1` at `c = 3`, `β̃₃ = 3` at `c = 4` | **`{1, 3}`** |
| 108/108 height-≥2 links contractible at `n = 4` | **108/108** |
| all 12 links at `n = 3` non-contractible | **12/12** |
| 0 vertices with non-zero `H̃_{n−2}(lk P)` at `n = 3, 4` | **0** |
| height-1 census 12 / 86 / 840 / 11 642 at `n = 3..6` | **12 / 86 / 840 / 11 642** |

A fourth control, added because `n = 7` is out of brute-force reach: the height-1 isomorphism
classes at `n = 7` are enumerated by **bipartition** (a height-1 poset is a bipartite graph between
its tail-set and its head-set, plus free elements), canonicalising under `S_a × S_b` instead of
`S_n`. That enumerator is checked against the brute-force one at `n = 3, 4, 5, 6` — same classes,
same class sizes — and only then used at `n = 7`.

**Negative controls.** (N1) The *swapped* claim — *"`β̃_{n−c}(Γ)` vanishes too"* — must be able to
go RED, and it does: it is **refuted on 3 of the 8 classes at `n = 4`**. So the instrument is
discriminating at the degree next to the one under test, which is exactly the degree the
"coincidence" story is about. (N2) At the 108 height-≥2 vertices of `Δ₄` the link is contractible,
a different mechanism, and the instrument reports it as such. (N3) The instrument demonstrably
**can** report a non-zero answer in the relevant range: it reports `β̃₃ ≠ 0` at 38 vertices of
`Δ₄`.

---

## 2. The reduction — restated, and re-derived rather than inherited

For height-1 `P ∈ PPF_n`, write `c := |Comp(P)| = |P|` and

    L̄(P) := {Q ∈ PPF_n : Q ⊊ P},      U(P) := {Q ∈ PPF_n : Q ⊋ P}.

- `lk_{Δ_n}(P) = Δ(L̄(P)) ∗ Δ(U(P))` — the link of a vertex of an order complex is the **join** of
  the two halves. (This is `mg-52c4` §3.2's correction to F28 §2.3; re-verified here at all 206
  vertices of `Δ₃` and `Δ₄`.)
- `Δ(L̄(P)) ≃ S^{c−2}` — `mg-52c4` Theorem A (A2), for height-1 `P`.
- Over a field, `H̃_k(X ∗ Y) = ⊕_{i+j=k−1} H̃_i(X) ⊗ H̃_j(Y)`.

Putting `i = c − 2` and `k = n − 2`:

> **Proposition 1.** For height-1 `P ∈ PPF_n`,
> `H̃_{n−2}(lk_{Δ_n}(P)) ≅ H̃_{n−c−1}(Δ(U(P)))`.

`mg-e08a` §7 already records this identity (as `H̃_{n−1−c}(U)`); it is re-derived here rather than
imported, and the join formula it rests on is re-verified at 206 vertices. **The naive dimension
argument dies here**, exactly as `mg-1b3b` warns: `dim Δ(U(P))` is of order `C(n,2)`, far above
`n − c − 1`, for every `n ≥ 4`. Any proof must bound the **bottom** of `U(P)`'s homology, not its
top — a connectivity statement, not a dimension count.

---

## 3. The new tool — the crosscut theorem makes `U(P)` small

`Δ(U(P))` is the object that put `mg-e08a` over its cap: for `c = 1` at `n = 5` it has 11 345 097
simplices, and at `n = 6` the vertex set alone is most of `PPF_6`'s 129 302 elements. It does not
have to be materialised.

> **Proposition 2 (crosscut reduction).** Fix `P ∈ PPF_n` and set
> `M := {P} ∪ U(P) ∪ {1̂}` ordered by inclusion of relation sets, `1̂` adjoined on top.
>
> 1. **`M` is a lattice.** The meet of `Q₁, Q₂ ∈ U(P)` is `Q₁ ∩ Q₂` — an intersection of partial
>    orders is a partial order, it contains `P`, and it is non-total, so it lies in `U(P) ∪ {P}`.
>    A finite meet-semilattice with `0̂` and an adjoined `1̂` is a lattice; the join of `Q₁, Q₂` is
>    `tc(Q₁ ∪ Q₂)` when that is acyclic and non-total, and `1̂` otherwise.
> 2. **The atoms of `M`** are the minimal elements of `U(P)`. Each is `tc(P ∪ {r})` for a single
>    ordered pair `r ∉ P`: if `Q ⊋ P` pick `r ∈ Q ∖ P`, then `P ⊊ tc(P ∪ {r}) ⊆ Q`.
>    So there are at most `n(n−1) − 2c` of them.
> 3. **Crosscut** (Björner, *Topological methods*, Thm 10.8 — the same citation `mg-52c4` §2.3
>    uses for the *lower* interval): the atoms are a crosscut of `M`, so
>
>        Δ(U(P))  ≃  Γ(P) := { A ⊆ Atoms(P) : tc(P ∪ ⋃A) is an acyclic, non-total relation }.
>
> 4. `Γ(P)` is a simplicial complex: if `tc(P ∪ ⋃A)` is acyclic and non-total then so is
>    `tc(P ∪ ⋃A′)` for `A′ ⊆ A`, since the latter is contained in the former.

**Sizes, measured.** The largest `Γ(P)` over all height-1 classes has **6 vertices at `n = 4`,
12 at `n = 5`, 20 at `n = 6`** — against upper links with tens of thousands of elements. The full
`n ≤ 6` sweep, including the complete homotopy type of every `Γ(P)`, runs in about 20 seconds.

**This is a homotopy equivalence, not a rational one.** It is not subject to the `Q`-acyclicity
trap `mg-e08a` §1 documents: what the crosscut theorem gives is `≃`, and the `Q` enters only when
this document then *measures* `Γ(P)` with rational Betti numbers. Every "contractible" verdict in
the tables below is therefore still **`Q`-acyclic**, for the ordinary reason, and is labelled so.

---

## 4. The measurement

### 4.1 `n = 6` complete, and `mg-e08a`'s `n = 5` gap closed

Height-1 isomorphism classes, all `n` from 3 to 6, with `d := n − c − 1` the needed degree:

| `n` | iso classes | labelled vertices | `β̃_d(Γ(P)) ≠ 0` | over cap |
|---|---|---|---|---|
| 3 | 3 | 12 | **0** | 0 |
| 4 | 8 | 86 | **0** | 0 |
| 5 | 20 | 840 | **0** | 0 |
| 6 | **55** | **11 642** | **0** | 0 |
| 7 | **163** | **227 892** | **0** | 0 — *see below* |

**The `n = 7` row was `162 of 163` classes / `227 850 of 227 892` vertices when this document was
written; `mg-bcd7` closed the remaining class and the row above is complete.** The single
over-cap class was the `c = 1` one (`Γ(P)` has 30 vertices and the needed degree is 5, so this
instrument's cap test rejected it), 42 of the 227 892 labelled height-1 vertices. It is now
measured: **`β̃₅(Γ(P); Q) = 0`** — rational Betti, as everywhere else in this table, not
contractibility. See `docs/OneThird-mgbcd7-n7c1-Beta5.md`, confirmed independently by `mg-9cd1`.

Two things about that cap are worth keeping, because they say the class was never out of reach.
The test used here is a binomial bound on the **ambient** simplex on the 30 atoms,
`C(30,8) = 5 852 925 > 3 000 000` — not a count of `Γ(P)`'s faces, of which there are `3 546 022`
through dimension 7 and only **`1 470 787` through dimension 6, which is all `β̃₅` needs**, well
inside this instrument's own cap. And `mg-bcd7` did not need that skeleton at all: `Γ(P) = X ∖ F`
with `X` a cone and `F` a filter generated by 120 six-element faces, so the answer comes from
matrices of 120/1 680/10 920 generators. (Observation and the `1 470 787` are `mg-9cd1`'s; the
f-vector and the reduction are `mg-bcd7`'s.)

The `n = 6` row is the ticket's step 2, complete: `mg-1b3b` sized that job at 11 642 of 129 302
vertices, and every one of them is covered by the 55 classes. The `n = 5` row is 20/20 classes,
which **closes the `58/61` gap** `mg-e08a` recorded — the three classes it could not materialise
(one `c = 1` at 11 345 097 simplices, two `c = 2` at 887 425) are three of these 20, and `Γ(P)`
has 12, 10 and 10 vertices respectively.

Breakdown at `n = 6` by number of relations (`d = n − c − 1`):

| `c` | needed degree `d` | classes | labelled | `β̃_d ≠ 0` |
|---|---|---|---|---|
| 1 | 4 | 1 | 30 | 0 |
| 2 | 3 | 3 | 300 | 0 |
| 3 | 2 | 6 | 1 320 | 0 |
| 4 | 1 | 13 | 2 910 | 0 |
| 5 | 0 | 13 | 3 492 | 0 |
| 6 | −1 | 10 | 2 400 | 0 |
| 7 | −2 | 5 | 960 | 0 |
| 8 | −3 | 3 | 210 | 0 |
| 9 | −4 | 1 | 20 | 0 |

### 4.2 The margin — this is the part that answers the ticket

Counting only whether the *needed* degree is empty is what produced the "one-degree near-miss"
reading. Because `Γ(P)` is small, its **whole** homotopy type is affordable, and that is a
different and much more informative measurement:

| `n` | classes with `Γ(P)` not `Q`-acyclic | degrees carrying homology | **min margin** `= firstnonzero − d` |
|---|---|---|---|
| 4 | 4 of 8 | `{0, 1}` | **1** |
| 5 | 4 of 20 | `{2}` | **2** |
| 6 | 5 of 55 | `{3}` | **3** |
| 7 | 2 of the 146 within cap | `{4}` | **10 measured / 4 including the star** |

**The `n = 7` margin row needs its caveat stated, not buried.** The full homotopy type of `Γ(P)` is
computed only where `Γ(P)` has at most 20 vertices, which is 146 of the 163 classes at `n = 7`; the
17 excluded include the star `K_{6,1}`. Over the 146, the minimum margin is **10** (attained at
`K_{3,4}` and `K_{4,3}`, `c = 12`, `β̃₄ = 1`). The star is excluded from that pool but its margin is
known without computing: `U(K_{n−1,1}) ≅ PPF_{n−1} ≃_Q S^{n−3}` by **F17+F18**, and `c = n − 1`
gives `d = 0`, so its margin is exactly `n − 3 = 4`. So `4` is the honest `n = 7` figure and `10`
is what was measured; both are ≥ the `n − 3` pattern and neither is `1`.

For `n ≥ 5` every non-`Q`-acyclic `Γ(P)` measured is a **rational `(n−3)`-sphere** — a single `1`
in degree `n − 3` and nothing else — and every other `Γ(P)` is `Q`-acyclic. Since the needed
degree is `n − c − 1`, the margin is `c − 2`, and the classes that carry homology all have
`c ≥ 4` at `n = 5` and `c ≥ 5` at `n = 6`.

**So the ticket's premise does not survive its own measurement.** *"Every case is a one-degree
near-miss"* is a true statement about `n = 4` and a false one about `n = 5` and `n = 6`. At `n = 4`
the classes carrying homology have `c = 3` and `c = 4`, giving margin 1; from `n = 5` on the
minimum margin is `n − 3`.

### 4.3 Where the homology actually lives

The five non-`Q`-acyclic classes at `n = 6` are `c = 5` (the star `K_{5,1}` and its dual),
`c = 8` (`K_{2,4}` and `K_{4,2}`) and `c = 9` (`K_{3,3}`) — complete bipartite height-1 posets; at
`n = 7`, the two within cap are `K_{3,4}` and `K_{4,3}`.
This is not an accident and it is checkable by hand: for `P = K_{a,b}` a refinement `Q ⊋ P` can
add relations only *within* the lower block and *within* the upper block, so

    U(K_{a,b})  ≅  (L_a × L_b) ∖ {(∅,∅)} ∖ {(total, total)}

with `L_a` the poset of partial orders on `a` elements. For `b = 1` this is exactly `PPF_{n−1}`,
which is `≃_Q S^{n−3}` by **F17+F18** — the programme's own sphere theorem reappearing one level
down. The instrument recovers `β̃_{n−3} = 1` for all of them without being told to. `K_{2,2}` at
`n = 4` is the one exception in the measured range (`β̃₀ = 3`, not `β̃₁ = 1`), because `PPF_2 = ∅`
makes the construction degenerate.

`n = 4` also has one non-bipartite class carrying homology (`c = 3`, class size 24, `K_{2,2}` minus
an edge), so the family is not exactly "the complete bipartite ones" and this document does not
claim it is.

---

## 5. What is now PROVEN rather than measured

> **Proposition 3.** Let `P ∈ PPF_n` be height-1 with `c = |P| ≥ n`, and let `n ≥ 6`. Then
> `H̃_{n−2}(lk_{Δ_n}(P)) = 0`.

*Proof.* By Proposition 1 the quantity is `H̃_{n−c−1}(Δ(U(P)))` and `n − c − 1 ≤ −1`. In degrees
below `−1` every reduced homology group vanishes, so the only case to rule out is `c = n`, where
the claim is `H̃_{−1}(Δ(U(P))) = 0`, i.e. **`U(P) ≠ ∅`**.

Pick a linear extension `t` of `P` (a total order with `P ⊆ t`; one exists, and `P ⊊ t` because
`P` is non-total). Choose `v ∈ Comp(t) ∖ (Cov(t) ∪ P)` — a comparable non-cover pair of the chain
`t` that `P` does not already contain. Such a `v` exists: `|Comp(t) ∖ Cov(t)| = C(n,2) − (n−1)`,
while a height-1 poset on `n` elements has at most `⌊n²/4⌋` relations by Mirsky (no 3-chain ⟹ two
antichains ⟹ the relations form a bipartite graph), and `C(n,2) − (n−1) > ⌊n²/4⌋` for `n ≥ 6`.
Set `Q := tc(P ∪ {v})`. Then `Q ⊆ t` so `Q` is acyclic, and `Q ⊋ P`. Finally `Q ≠ t`: every cover
relation of a chain is join-irreducible for `tc` (`mg-52c4` §2.3 step (i)), so `Q = t` would force
`Cov(t) ⊆ P ∪ {v}`, and `v ∉ Cov(t)`, hence `Cov(t) ⊆ P` and `P ⊇ tc(Cov(t)) = t` — contradicting
`P ⊊ t`. So `Q ⊆ t` with `Q ≠ t` is non-total, and `Q ∈ U(P)`. ∎

At `n = 6` this covers `c ∈ {6,...,9}`, i.e. **3 590 of the 11 642 height-1 vertices (30.8%)**, and
at `n = 7` it covers `c ∈ {7,...,12}`, i.e. **110 082 of 227 892 (48.3%)** — with no computation at
all, and a share that grows with `n`. The `n ≥ 6` hypothesis is only used for the counting step; at `n = 4, 5`
the same conclusion is measured rather than proven (§4.1), and `n = 5` is the boundary case where
`C(n,2) − (n−1) = ⌊n²/4⌋ = 6`.

**This is the honest size of the proven part.** It is not the whole question, and §7 says so.

---

## 6. What the correct proof has to look like — and why the obvious one fails

`mg-1b3b`'s sharpening was right and is now sharper still.

- **Dimension is the wrong invariant, permanently.** `dim Δ(U(P))` exceeds `n − c − 1` for every
  `n ≥ 4`, and no refinement of a dimension count can work, because `Γ(P)` **does** carry homology
  — in degree `n − 3` — for an identifiable family of `P` (§4.3). A bound that forces degree
  `n − c − 1` empty must distinguish it from degree `n − 3`, which a dimension bound cannot.
- **The right statement is a connectivity statement**, and it is now about one small explicit
  complex:

  > **Conjecture C (mg-72e4).** For every height-1 `P ∈ PPF_n`, `Γ(P)` has no reduced homology
  > below degree `n − 3`; equivalently `Δ(↑P ∖ {P})` is `(n−4)`-acyclic.

  Conjecture C settles the question for every `c ≥ 3` (since then `n − c − 1 ≤ n − 4 < n − 3`),
  which is 11 312 of the 11 642 height-1 vertices at `n = 6`. It leaves `c = 1` and `c = 2`,
  where the needed degree is at or above `n − 3` and something else is required — measured, both
  are `Q`-acyclic in the anchor degree at every `n ≤ 7`, **with no exception** since `mg-bcd7`
  closed the `n = 7` `c = 1` class. For `c = 1` alone the measurement now runs to `n = 9`
  (`mg-bcd7` §7), by a reduction that does not build `Γ(P)`. Still measurement, still not a
  theorem.
- **A cross-check that Conjecture C is the right shape:** `U(K_{n−1,1}) ≅ PPF_{n−1}`, whose order
  complex is `≃_Q S^{n−3}` by F17+F18. So the bound in Conjecture C is **tight** and is attained
  at the star — it cannot be improved to `(n−3)`-acyclic, and any proof must let that case
  through.

---

## 7. Verdict, and exactly what is still open

**Theorem or coincidence?** On this evidence: **not a coincidence, and not yet a theorem.**

Stated so that nobody over-reads it:

1. **Proven, all `n ≥ 6`, no measurement:** the vanishing at every height-1 vertex with `c ≥ n`
   (§5). 30.8% of the `n = 6` height-1 population.
2. **Measured exhaustively, `n ≤ 6`:** every height-1 iso class — 3 / 8 / 20 / 55 classes covering
   12 / 86 / 840 / 11 642 labelled vertices — **0 violations**, none over cap. This includes the
   three `n = 5` classes `mg-e08a` could not reach.
3. **Measured at `n = 7`, complete:** **163 of 163** iso classes, **227 892 of 227 892** labelled
   vertices, **0 violations**, none over cap. The one gap this document originally left — the
   `c = 1` class, 42 vertices, `162 of 163` and `227 850 of 227 892` as first written — was closed
   by `mg-bcd7` (`β̃₅ = 0` rationally) and confirmed independently by `mg-9cd1`.
   `n = 7` is the `n` at which the corpus's nearest precedent — `mg-24eb`'s *"exactly the ordinal
   sums"* — turned out to be false.
4. **Refuted:** the *"every case is a one-degree near-miss"* premise. True at `n = 4`; false at
   `n = 5, 6, 7`, where the margin is 2, 3 and (at least) 4.
5. **Open:** Conjecture C (§6), and the `c ≤ 2` cases it does not cover. **Nothing here proves the
   statement for any `n`** beyond the `c ≥ n` slice of Proposition 3 — everything else is
   measurement, and measurement stops at `n = 7` (`n = 9` for `c = 1` alone, via `mg-bcd7`).
   `mg-bcd7` removed the *hole* in the `c ≤ 2` evidence; it did not supply an argument, and that
   slice still has none.

**What would close it.** Conjecture C plus a `c ≤ 2` argument. Both are now statements about
`Γ(P)`, a complex on at most `n(n−1) − 2c` vertices with an explicit face rule, rather than about
an order complex with 10⁷ simplices. That is a materially easier target than the one the ticket
was filed against, and it is the concrete deliverable this ticket leaves behind.

**Two traps, honoured.**
- *"Contractible" means `Q`-acyclic.* Every `Γ(P)` verdict in §4 is a two-prime rational Betti
  computation and cannot distinguish `RP²` from a point. The **crosscut equivalence itself** (§3)
  is a genuine homotopy equivalence and is not affected; only the measurements on top of it are.
- *The Euler/Möbius predicate cannot see this.* No Euler characteristic is used anywhere in this
  instrument; every verdict is Betti-level in a named degree.
- *The Mayer–Vietoris connecting map is a different map.* `∂ : H̃_{n−2}(Δ_n) → H̃_{n−3}(lk P)` is
  genuinely non-zero (`mg-e08a` §7) and nothing here touches it. This document is about the
  anchor-degree component of the link and says nothing about `∂`.

---

## 8. Scope — what this does NOT do

- **It does not reopen the F-series.** `mg-e08a` confirmed *"do not open an F33"*, `mg-1b3b`
  carried that, and the result here moves in the direction that *strengthens* the closure, not
  against it. A negative answer would have reopened it; this is not a negative answer.
- It does not retract anything from `mg-52c4` or `mg-e08a`. Theorem A, Corollary B and the audit's
  scoping notes are used, not challenged; the one thing it corrects is a *characterisation of the
  evidence* — "one-degree near-miss" — not a claim about the mathematics.
- It does not compute anything at height ≥ 2 beyond the `n = 4` control, because Corollary B
  already covers those vertices.
- It does not establish Conjecture C, and it does not measure `n ≥ 8` at all. The `n = 7` sweep as
  originally landed left one `c = 1` class (42 of 227 892 vertices) over cap, and 17 of 163
  classes without a full homotopy type; both were named in §4, not rolled into a pass. **The
  over-cap class is now closed** (`mg-bcd7`; and `mg-bcd7` §7 measures the `c = 1` class alone out
  to `n = 9`). The 17 classes without a full homotopy type are **not** closed by this document —
  `mg-9cd1` reports having measured them, and those figures belong to it.

## 9. References

**In this repo:** `docs/OneThird-mgbcd7-n7c1-Beta5.md` (finishes the `n = 7` `c = 1` class this
document left over cap — `β̃₅ = 0` rationally — and extends `c = 1` to `n = 9`),
`docs/OneThird-mg52c4-PerPoset-Subposet-Question.md` (Theorem A, Corollary B,
§3.2's join-formula correction, §5's statement of this question),
`docs/OneThird-mge08a-TheoremA-IndependentAudit.md` (§6–§8: the 38 non-contractible links, the
anchor-degree measurement, the `58/61` cap, the `Q`-acyclicity and Euler-blindness traps),
`docs/compatibility-geometry-F17-equivariant-cofiber-morse.md` (Lemma L1),
`...-F18-ucc2-delta-injective.md`, `...-F28-sheaf-cohomology-on-POSET.md` (§2.3).

**Work items:** `mg-52c4` (Theorem A), `mg-e08a` (the audit that named this question),
`mg-1b3b` (carried it and sized the `n = 6` job at 11 642), `mg-72e4` (this).

**Literature:** A. Björner, *Topological methods*, Handbook of Combinatorics (1995) — Thm 10.8
(crosscut), §10.2 (closure/order-homotopy). L. Mirsky, *A dual of Dilworth's decomposition
theorem*, Amer. Math. Monthly 78 (1971).
