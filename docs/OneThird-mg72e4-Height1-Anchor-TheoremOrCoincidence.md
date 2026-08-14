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
> ### The question is not settled as a theorem, but the reason to suspect a coincidence is gone, and the measurement now runs through `n = 7` — all 163 iso classes and all 227 892 labelled height-1 vertices there, **0 violations**.

*(This line read "163 iso classes and 227 850 of the 227 892 labelled height-1 vertices" as first
landed — a mismatch `mg-9cd1` recorded as **D1**, because the class count was stated complete
while the vertex count was not. Both are complete now: `mg-bcd7` measured the one class this
document left over cap. Nothing else in §0 changes, and in particular the **min margin** row in
result 1 below is untouched — `mg-bcd7` did not compute a margin for that class, so `mg-9cd1`'s
finding **D2** about the min-margin denominator stands exactly as written.)*

Four results, in descending order of how much they should change what anyone does.

1. **The evidence for "coincidence" was an `n = 4` artifact.** `mg-e08a` measured the anchor
   degree and its neighbours and found the nearest non-vanishing degree exactly one away — at
   `n = 4`. Measured over the *whole* homotopy type of the relevant complex (§4), the nearest
   non-vanishing degree is **`n − 3`**, and the needed degree is `n − c − 1`, so the margin is
   **`c − 2`**, minimum `n − 3` over the classes where anything is non-zero:

   | `n` | min margin | over how many of the iso classes | degrees where `Γ(P)` has homology |
   |---|---|---|---|
   | 4 | **1** | 8 of 8 | `{0, 1}` |
   | 5 | **2** | 20 of 20 | `{2}` |
   | 6 | **3** | 55 of 55 | `{3}` |
   | 7 | **4** (see §4.2) | **163 of 163** | `{4}` |

   **The `n = 7` row's third column is here because it was missing**, and it is now complete: as
   first published the figure `4` stood on **148** of the 163 classes, and `mg-9cd1` **D2**
   recorded it as a fourth denominator stated nowhere. §4.2 derives all of them. `mg-0f24` took it
   to **160 of 163**, and `mg-dd84` closed the last three (`c ≤ 2`, 252 of the 227 892 labelled
   vertices) — so the population is now **163 of 163 iso classes and 227 892 of 227 892 labelled
   height-1 vertices**, the same as every other `n = 7` figure here, and the value is `= 4` rather
   than `≥ 4` because the minimum is *attained*, at the two stars. Those three classes do not
   attain it: `Γ(P)` carries **no homology in any degree** for all three
   (`docs/OneThird-mgdd84-n7-cLE2-Margin.md`), so they satisfy `margin ≥ 4` vacuously. They are
   still the `c ≤ 2` slice §6 names as the part Conjecture C would not reach — `mg-dd84` supplies
   an argument for those three *families*, not for the slice.

   A quantity that misses by one at `n = 4`, by two at `n = 5`, by three at `n = 6` and by at least
   four at `n = 7` is not behaving like arithmetic luck. **`n = 7` matters specifically**: it is where
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
go RED, and it does. **Its denominator and its scope, stated (`mg-9cd1` D5):** the control ran
**144 instances** over `n = 4..7` and is refuted on **3**, all three at `n = 4`. At `n = 4` the
testable population is **7 of the 8 classes**, not 8 — the `c = 4` class has `d = −1`, so the
swapped degree is never computed there. At `n = 5, 6, 7` it is **0 of 137** (`16 + 36 + 85`; the
86th testable class at `n = 7` is the one the over-cap gate declines, §4.1). So the instrument is
demonstrably discriminating at the degree next to the one under test — but **at `n = 4` only**, and
the three refuting classes are exactly the three `n = 4` classes with `β̃₁ ≠ 0` (`c = 3`, class
sizes 4 / 24 / 4), i.e. three of the four §4.2 counts as carrying homology. **N1 is therefore not
independent evidence: it is the headline `n = 4` finding wearing a control's label.**
*(One more thing the `d = −1` branch hides, noted at `mg-0f24`: the `c = 4` class at `n = 4` would
refute the swapped claim too — it is `K_{2,2}`, its swapped degree is `0`, and §4.3 records
`β̃₀ = 3` there — so 4 of the 8 classes refute it and only 3 of them are inside N1's loop.)*
(N2) At the 108 height-≥2 vertices of `Δ₄` the link is contractible,
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
this document then *measures* `Γ(P)` with rational Betti numbers.

> **Scope of that caveat: the WHOLE document, `§1` included, and in both directions.**
> As first written this read *"every 'contractible' verdict in **the tables below**"*, which left
> the four bare uses of "contractible" in §1 — the 38 of 194 and 108/108 links at `n = 4`, the
> 12 links at `n = 3`, and (N2) — outside it, although each is the same two-prime Betti verdict
> (`mg-9cd1` **D6**). They are not, and never were, exempt. Both directions matter, because only
> one of them is safe:
>
> - **A zero is stronger than it looks.** `β̃_p = 0` forces `β̃_Q = 0`, since `rank_{F_p} ≤ rank_Q`.
>   So every *vanishing* verdict here — which is every census verdict, and the whole of §4.1 — is a
>   genuine rational vanishing, and `mg-9cd1`'s mod-2 readings prove rational vanishing too.
> - **A non-zero is weaker than it looks.** `β̃_p = 1` gives only `β̃_Q ≤ 1`; it cannot exclude
>   `p`-torsion. So a non-zero reading in this document, or in `mg-9cd1`'s, is **not** a rational
>   value and must not be quoted as one. Where a rational value is asserted for a non-zero — the
>   stars' `β̃₄ = 1` in §4.2/§4.3 — it comes from **F17+F18**, not from the measurement.
>
> "Contractible" means `Q`-acyclic everywhere in this document, and cannot distinguish `RP²` from
> a point.

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
f-vector and the reduction are `mg-bcd7`'s. Both f-vectors are re-measured at `mg-0f24` by a third
enumeration — `30, 425, 3 760, 23 160, 105 032, 362 740, 975 640, 2 075 235` — agreeing on every
entry, including the dimension-7 count `mg-bcd7` *predicted* and `mg-9cd1` measured.)

> **The gate is now repaired, and the repair is not the one class** (`mg-9cd1` **D7**, landed at
> `mg-0f24`). `binom(#atoms, d + 3)` is the top layer of a simplex this instrument never builds; it
> is replaced by a count of `Γ(P)`'s **realised** faces, enumerated with early abort, and the count
> is recorded per class in the output. Three things came out of doing it against a measurement
> instead of against the known class
> ([`scripts/audit_mg0f24_cap_gap.py`](../scripts/audit_mg0f24_cap_gap.py),
> [`data/onethird-mg0f24-cap-gap.json`](../data/onethird-mg0f24-cap-gap.json)):
>
> 1. **Nothing else was wrongly excluded, and that is measured rather than assumed.** Over every
>    height-1 class at `n = 3..7` — 249 classes, the whole range this instrument has ever been run
>    over — the old gate excluded **exactly one** class, this one, and the realised-face gate
>    excludes **none**. The defect had a population of 1. It bites harder further out: at `n = 8`
>    the old gate would decline **6 classes / 1 792 labelled vertices** (`c = 1`, three `c = 2`,
>    two `c = 3`). **`mg-c99c` R1 has now measured what the realised gate says about those six,
>    and the `n ≤ 7` pattern does not repeat: it declines 3 of them (392 labelled) and admits 3
>    (1 400 labelled, `78 %`).** So the defect's population is 1 at `n ≤ 7` and 3 at `n = 8`, not
>    6 — but "the ambient gate's declines are always spurious" would have been wrong for half of
>    them. The measurement is complete over all 206 gated classes at `n = 8` and the realised gate
>    excludes **nothing** the ambient gate admitted, on either column, at any `n ≤ 8`
>    ([`scripts/audit_mgc99c_n8_realised_gate.py`](../scripts/audit_mgc99c_n8_realised_gate.py),
>    [`data/onethird-mgc99c-n8-realised-gate.json`](../data/onethird-mgc99c-n8-realised-gate.json);
>    `mg-0f24`'s `n ≤ 7` per-class verdicts are replayed there and reproduce identically). *`n = 8`
>    remains outside everything else here — this is a reading of a **gate**, not of any `β̃_d`.*
> 2. **A naive swap would still have excluded it.** The census reads the skeleton through dimension
>    `d + 1`, but the near-miss column `β̃_{d+1}` (control N1) needs one dimension more, and this
>    class is `1 470 787` faces at the first and `3 546 022` at the second — *over* the same
>    3 000 000 cap. The two skeletons are now gated separately, so a class over cap on the extra
>    dimension still resolves the census question instead of being dropped whole. The audit's
>    *"1 470 787 is all `β̃₅` needs"* is right, and only lands once the instrument stops asking for
>    the extra degree.
> 3. **The replacement gate is a proxy too, and is labelled as one.** Face count bounds
>    *materialisation*; what actually failed to return here was the *elimination*. So the
>    hand-off to the Betti routine has its own threshold, set at what this instrument has been
>    **observed to complete** — over `n = 3..7`, the largest skeleton it has finished is `574 559`
>    faces and the largest full `Γ(P)` it has materialised is `409 599`, both measured at
>    `mg-0f24` — and declared a budget, not a feasibility bound. Under it this class
>    is still declined, now for a stated and measured reason rather than a bound on the wrong
>    object, and its value is known from two other routes. The margin gate above (`#atoms ≤ 20`,
>    i.e. `2^20`) is the **same ambient proxy** and is deliberately left in place: it is what
>    produced the published `146 of 163`, and moving it would move a published population rather
>    than repair one. It is now recorded per class in the output so the population is readable.

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

| `n` | classes where `Γ(P)` **reads non-zero** | degrees carrying homology | **min margin** `= firstnonzero − d` | over what population |
|---|---|---|---|---|
| 4 | 4 of 8 | `{0, 1}` | **1** | 8 of 8 — complete |
| 5 | 4 of 20 | `{2}` | **2** | 20 of 20 — complete |
| 6 | 5 of 55 | `{3}` | **3** | 55 of 55 — complete |
| 7 | **= 6 of 163 over `Z/2`** (see §4.3) | `{4}` | **4**, attained at the stars | **163 of 163** — complete since `mg-dd84` |

*(Three things about that table, all of them scope. **(i) The first column is a field reading, not
a `Q`-acyclicity verdict** — it used to be headed *"not `Q`-acyclic"*, which is the direction §3's
caveat does not license: `β̃_p ≠ 0` gives only `β̃_Q ≤ β̃_p`, so a non-zero reading cannot by itself
promote a class out of `Q`-acyclic. The one place a rational non-vanishing is actually established
is the stars, and it comes from F17+F18. **(ii) The `n ≤ 6` denominators are complete** — the
largest `Γ(P)` there has 6 / 12 / 20 vertices and the full-homotopy-type gate admits everything up
to 20; at `n = 7` the largest has 30 and the gate bites, so the first three rows and the fourth are
not the same kind of number, which is what made the `n = 7` entry easy to misread. **(iii) `4` is
attained, not merely bounded** — it is `≥ 4` everywhere it was measured and `= 4` at the stars, so
the minimum over the whole population is `4`. *(Read as a lower bound until `mg-dd84` closed the
last three classes; the qualifier that came off is the denominator, not the value.)*)*

**The `n = 7` margin row needs its caveat stated, not buried — and the caveat has a denominator
that has to be derived rather than picked.** Three numbers are in circulation (`146`, `148`,
`14 of 17`) and they do not compose by addition. Deriving, at `n = 7`, out of **163 classes /
227 892 labelled vertices**:

| | classes | labelled | why |
|---|---|---|---|
| full homotopy type of `Γ(P)` computed | **146** | 225 540 | the gate is `#atoms ≤ 20`; these are the classes that clear it |
| no full homotopy type | 17 | 2 352 | `#atoms` between 21 and 30 |
|  — of those, the two stars `K_{6,1}`, `K_{1,6}` | 2 | 14 | margin `4` **inferred** from F17+F18, not computed |
|  — of those, the rest | 15 | 2 338 | **no margin information of any kind** — `mg-9cd1` **D2** |
| **population of "min margin 4" as first published** | **148** | **225 554** | `146 + 2 stars` |
| `mg-9cd1` §4.3 measured all 17 and reached `margin ≥ 4` on | **14** of the 17 | 2 100 | `c ∈ {3,4,5,6,10}`, `β̃` over `Z/2`. `mg-9cd1`'s §6 table calls this *"12 of the 15"* — same classes, counted out of the 15 that had **no** margin information rather than out of the 17 without a full type. `14 = 12 + the 2 stars`, `17 = 15 + the 2 stars` |
| population after `mg-0f24` | **160** | **227 640** | `146 + 14`, **not** `148 + 14` |
| the last 3 (`c = 1`, 42; the two `c = 2`, 105 each) | **3** | **252** | `mg-dd84`: `Γ(P)` carries **no homology in any degree**, so `margin ≥ 4` holds vacuously and is not attained |
| **population now** | **163** | **227 892** | `160 + 3` — complete |

**The trap in that table is the `population after mg-0f24` row.** `148 + 14 = 162` is wrong: the
two stars are counted in *both* the 148 and the 14 — they are exactly the classes that moved from
*inferred* to *measured* — so the union is `146 + 14 = 160` and the overlap is 2. Adding the two
published figures would have produced a **fifth** denominator, which is the defect this repair
exists to carry, reproduced inside its own repair. **`160 + 3 = 163` does compose**, and only
because the three classes `mg-dd84` closed are by construction the ones with *no* margin
information after `mg-0f24` — disjoint from the 160. `mg-dd84` checks that disjointness rather
than assuming it, for the reason the row above it exists.

Over the 146, the minimum margin is **10** (attained at `K_{3,4}` and `K_{4,3}`, `c = 12`,
`β̃₄ = 1`). The stars are outside that pool and their margin is known without computing it:
`U(K_{n−1,1}) ≅ PPF_{n−1} ≃_Q S^{n−3}` by **F17+F18**, and `c = n − 1` gives `d = 0`, so the margin
is exactly `n − 3 = 4` — and `mg-9cd1` has since measured `β̃₄(Γ(K_{6,1}); Z/2) = 1` with nothing
below, corroborating it. So **`4` is the honest `n = 7` figure, on 163 of 163 classes and 227 892
of 227 892 labelled vertices** (`mg-dd84`; it was `160 of 163` between `mg-0f24` and that), `10` is
the figure over the 146 the instrument computed in full, and the last three classes turned out to
carry no homology at all rather than to sit just above the bound. Neither figure is `1`, which is
what the ticket asked.

For `n ≥ 5` every non-`Q`-acyclic `Γ(P)` measured **reads as** a rational `(n−3)`-sphere — a single
`1` in degree `n − 3` and nothing else — and every other `Γ(P)` is `Q`-acyclic. *(With §3's caveat
applied in both directions: the zeros are rational vanishing outright, while the `1` in degree
`n − 3` bounds `β̃_Q ≤ 1` over the instrument's primes and does not on its own exclude torsion. At
the stars a rational value does follow — from F17+F18, not from this measurement.)* Since the needed
degree is `n − c − 1`, the margin is `c − 2`, and the classes that carry homology all have
`c ≥ 4` at `n = 5` and `c ≥ 5` at `n = 6`.

**So the ticket's premise does not survive its own measurement.** *"Every case is a one-degree
near-miss"* is a true statement about `n = 4` and a false one about `n = 5` and `n = 6`. At `n = 4`
the classes carrying homology have `c = 3` and `c = 4`, giving margin 1; from `n = 5` on the
minimum margin is `n − 3`.

### 4.3 Where the homology actually lives

The five non-`Q`-acyclic classes at `n = 6` are `c = 5` (the star `K_{5,1}` and its dual),
`c = 8` (`K_{2,4}` and `K_{4,2}`) and `c = 9` (`K_{3,3}`) — complete bipartite height-1 posets.

**At `n = 7` the list is `= 6` of the 163 over `Z/2`, not the 2 this section used to name**
(`mg-9cd1` **D3**, corrected to `≥ 6` at `mg-0f24`, closed to `= 6` at `mg-c99c`). The two this
instrument found are the two it looked at; four more sat among the 17 classes it never gave a full
homotopy type, and `mg-9cd1` §4.3 measured them. *(Read with §3's caveat: "carries homology" below
means **reads non-zero over the field named in the last column**, which is a rational statement
only where the last column says so.)*

| class | `c` | labelled | `β̃₄` | field, and what it establishes |
|---|---|---|---|---|
| `K_{3,4}`, `K_{4,3}` | 12 | 35 each | 1 | both instrument primes **and `Z/2`** (`mg-c99c`) — the two within cap |
| `K_{6,1}`, `K_{1,6}` (the stars) | 6 | 7 each | 1 | `Z/2` (`mg-9cd1`), **both instrument primes** (`mg-c99c`), **and rationally by F17+F18** |
| `K_{2,5}`, `K_{5,2}` | 10 | 21 each | 1 | `Z/2` (`mg-9cd1`) **and both instrument primes** (`mg-c99c`) — all three still only bound `β̃_Q ≤ 1`; **no rational value** |

All six are complete bipartite with homology in degree exactly `n − 3 = 4`, which *strengthens* the
reading below rather than weakening it; what was wrong was the count. The `n = 7` entry in §4.2's
first column is therefore `= 6 of 163 over Z/2` and the `2` that stood there was `2 of the 146`.

**Why this is now `= 6` and not `≥ 6` — the inequality was carrying one blind spot, and it is
closed** (`mg-c99c` **R2**). The two populations used to be read over **different fields** — the
146 over this instrument's two primes near `10⁶`, the 17 over `Z/2` — so a class among the 146
could have carried 2-torsion in degree 4 that its primes cannot see, and `≥` was the honest
symbol. All 146 have now been re-read over `Z/2`
([`scripts/audit_mgc99c_z2_reread.py`](../scripts/audit_mgc99c_z2_reread.py),
[`data/onethird-mgc99c-z2-reread.json`](../data/onethird-mgc99c-z2-reread.json)):

- `β̃₄` over `Z/2` **equals** `β̃₄` over both instrument primes on **every one of the 146**. By
  universal coefficients `dim_{F₂} H̃₄ = rank₄ + t₄(2) + t₃(2)`, so the agreement forces
  `t₄(2) = t₃(2) = 0` — both, since they are non-negative and sum to zero. There is no hidden
  seventh class and no 2-torsion in degree 3 or 4 anywhere in that population.
- The other **17** were re-read too, in the same run and independently of `mg-9cd1`, because
  their degree-4 skeletons turn out to sit **inside this instrument's own `ELIM_CAP`** (largest
  eliminated: `495 147` faces against the 600 000 budget). They were excluded from the census by
  the gate on the **full** homotopy type, not by any degree-4 cost. That re-derivation reproduces
  `mg-9cd1`'s four exactly — the two stars and `K_{2,5}`/`K_{5,2}` — so the `6` is now a figure
  one script derives over all 163 rather than `2` measured here plus `4` quoted from elsewhere.
- Reading the 17 over the instrument's primes as well (also new, also inside the cap) is what
  moved the last column above. It does **not** move `β̃_Q`: §3's caveat is unchanged, a mod-`p`
  ONE bounds `β̃_Q ≤ 1` in every field, so `K_{2,5}`/`K_{5,2}` still have no rational value.
- **Cross-check with `mg-dd84`, which landed the same night on a different branch.** Three of the
  17 are the `c ≤ 2` classes (`c = 1`, 42 labelled; two `c = 2`, 105 each) that `mg-dd84` found
  carry **no homology in any degree** — §4.2's last table row. This run reads all three as `β̃₄ = 0`
  over `Z/2` *and* over both instrument primes, by a different route and for a different purpose.
  Neither measurement was aware of the other.

**What `= 6` is not.** It is a count *over `Z/2`*, in degree 4, over all 163 — the field label
stays on the figure. Two blind spots remain and **neither is the one that was closed**: (a) **odd
torsion at a prime nobody read** — the three fields here are `Z/2` and the two primes near `10⁶`,
and a class could carry `q`-torsion at some other `q`; (b) "no 2-torsion" is read against those
primes standing in for the free rank, so torsion *at* `1 000 003` or `999 983` would be invisible
to the comparison. The two primes agreeing on all 163 is evidence for (b), not a proof. What the
`≥` was for is gone; what is left is different and is stated here rather than folded into it.

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

   > **Points 1 and 3 overlap; do not add them** (`mg-9cd1` O1). At `n = 7`, `110 082` of the
   > 227 892 vertices point 3 calls *measured* (48.3%) are this proven slice re-counted: for
   > `c ≥ 8` the needed degree is `≤ −2` and the instrument sets `β̃_d = 0` by arithmetic, and for
   > `c = 7` it checks only that `Γ(P)` is non-empty — which *is* Proposition 3's content. Both
   > statements are true; a reader adding them is double counting.
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
   `n = 5, 6, 7`, where the margin is 2, 3 and 4. All four figures are now minima over the
   **complete** class populations — the `n = 7` one over **163 of 163** classes and 227 892 of
   227 892 labelled vertices, since `mg-dd84` closed the last three (`c ≤ 2`, 252 vertices) by
   showing `Γ(P)` carries no homology in any degree there. §4.2 derives that denominator through
   all four of its values, and it is not the `148` the figure was first published on.
5. **Open:** Conjecture C (§6), and the `c ≤ 2` cases it does not cover. **Nothing here proves the
   statement for any `n`** beyond the `c ≥ n` slice of Proposition 3 — everything else is
   measurement, and measurement stops at `n = 7` (`n = 9` for `c = 1` alone, via `mg-bcd7`).
   `mg-bcd7` removed the *hole* in the `c ≤ 2` evidence; `mg-dd84` then supplied an **argument**
   for three named `c ≤ 2` families — `P = {(0,1)}` and the two `c = 2` shapes — good at every
   `n ≥ 4` and checked to `n = 8`. That is three families, **not** the `c ≤ 2` slice: the slice
   still has no general argument, and `mg-dd84` §6 pt 3 says so in the same terms.

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

**Repairs to this document:** `mg-9cd1`'s independent audit
(`docs/OneThird-mg9cd1-Height1Anchor-IndependentAudit.md`) returned pass-with-defects; `mg-bcd7`
discharged D1 by measurement and `mg-0f24` carried the rest — §0 result 1 and §4.2 (D2, the margin's
denominator, derived), §4.2/§4.3 (D3, the homology-carrying count), §1 (D5, N1's scope), §3 (D6,
the `Q`-acyclicity caveat, widened to the whole document and to both directions), §4.1 and
`scripts/compat_geom_mg72e4_height1_anchor.py` (D7, the over-cap gate), §7 pt 1 (O1). The gate
measurement is `scripts/audit_mg0f24_cap_gap.py` → `data/onethird-mg0f24-cap-gap.json`, whose
face counter is pinned against this instrument's own `gamma_faces()` builder per dimension on all
31 classes at `n ≤ 5` before any of its numbers are used.

**Work items:** `mg-52c4` (Theorem A), `mg-e08a` (the audit that named this question),
`mg-1b3b` (carried it and sized the `n = 6` job at 11 642), `mg-72e4` (this),
`mg-9cd1` (independent audit), `mg-bcd7` (the `n = 7` `c = 1` class), `mg-0f24` (the repairs).

**Literature:** A. Björner, *Topological methods*, Handbook of Combinatorics (1995) — Thm 10.8
(crosscut), §10.2 (closure/order-homotopy). L. Mirsky, *A dual of Dilworth's decomposition
theorem*, Amer. Math. Monthly 78 (1971).
