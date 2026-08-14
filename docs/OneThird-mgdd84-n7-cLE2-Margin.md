# `mg-dd84` — the last 3 classes: `Γ(P)` has **no homology in any degree**, and the `n = 7` min-margin denominator closes at **163 of 163 / 227 892 of 227 892**

**Status: CLOSED.** The three `c ≤ 2` height-1 classes at `n = 7` that `mg-72e4`, `mg-9cd1` and
`mg-0f24` each left at `margin ≥ 1` are measured, and the answer is stronger than the `≥ 4` the
ticket asked for: **`H̃_k(Γ(P)) = 0` for every `k`**, so there is no first non-zero degree at all.

- Instrument: [`scripts/compat_geom_mgdd84_n7_cle2_margin.py`](../scripts/compat_geom_mgdd84_n7_cle2_margin.py)
- Data: [`data/onethird-mgdd84-n7-cle2-margin.json`](../data/onethird-mgdd84-n7-cle2-margin.json)
- Run: `/usr/bin/python3 scripts/compat_geom_mgdd84_n7_cle2_margin.py` — `ALL_PASS = True`,
  **≈ 48 s wall, 277 MB peak RSS, one process, no pool.** *(Two measured runs on the 10-core fleet
  host: `47.8 s` by `/usr/bin/time -l` with `pogo host load` reporting PROCEED at 19% fleet share,
  and `160.5 s` for the same work with this repo's own `./presubmit.sh` running concurrently. The
  wall clock is contention-sensitive and the 48 s is the quiet-host figure; the memory is not, and
  the worker budget `$POGO_WORKER_CORES = 3` is never approached because nothing here
  parallelises. The `seconds` key in the JSON is whichever run last wrote it.)*
- Closes: `mg-9cd1` §7 pt 1 and §6.1's declined remainder; `mg-72e4` §0 result 1, §4.2 and §7 pt 4.
- Also settles, with a reason rather than a table: `mg-bcd7` §7's *"observed pattern … not proved
  here"*.

---

## 0. Verdict

> ### The margin for all three classes is **not a number**: `Γ(P)` carries no homology in any degree, so `margin ≥ 4` holds vacuously and `min margin = 4` at `n = 7` now stands on **163 of 163 iso classes and 227 892 of 227 892 labelled height-1 vertices** — the same population as every other `n = 7` figure in this lineage.
>
> ### The minimum `4` is still attained where it always was, at the two stars `K_{6,1}`, `K_{1,6}`. Nothing about the value moves; only its denominator does.

*(The stars' `= 4` is **not this document's measurement**: it is `mg-72e4` §4.2's inference from
F17+F18 (`U(K_{n−1,1}) ≅ PPF_{n−1} ≃_Q S^{n−3}`, `d = 0`, margin `n − 3`), corroborated by
`mg-9cd1` §4.3's `β̃₄(Γ(K_{6,1}); Z/2) = 1` with nothing below. Neither is re-derived here. What is
this document's is the denominator and the three classes that were missing from it.)*

| class | `c` | labelled | atoms | `d = n−c−1` | before | **now** |
|---|---|---|---|---|---|---|
| `P = {(0,1)}` | 1 | 42 | 30 | 5 | `margin ≥ 1` | **no non-zero degree**; `β̃_{−1..8} = 0` measured |
| `P = {(0,1),(0,2)}` ("V") | 2 | 105 | 26 | 4 | `margin ≥ 1` | **no non-zero degree**; `β̃_{−1..7} = 0` measured |
| `P = {(0,2),(1,2)}` ("Λ") | 2 | 105 | 26 | 4 | `margin ≥ 1` | **no non-zero degree**; `β̃_{−1..7} = 0` measured |

Three things about that, in the order they should change what anyone does.

1. **The route was the one `mg-bcd7` predicted, and it went further than four more degrees.**
   `p9cd1` named the cone/LES decomposition as the thing to look for before brute force, and it
   is the right instinct: the filter `F = X ∖ Γ` is not merely small, it is **exactly identified**
   — a direct sum, over the total orders it realises, of augmented chain complexes of simplices.
   Those are exact. So `H_k(X, Γ) = 0` in *every* degree at once, and computing `β̃₆, β̃₇, β̃₈`
   one at a time was never the shape of the answer. §2 is the argument; §3 is what was measured
   to check it.

2. **It was never a resource problem.** `p9cd1` declined this on a stated resource ground and
   that judgement was correct on the information it had — a brute-force `β̃` through degree 8 on
   a complex with ~10⁶ faces in degree 6 alone is exactly what it said it was. What the
   decomposition changes is the **object**: the largest matrix this instrument factors has
   **2 002 columns**, against the `Γ`-boundary matrices with `10⁵`–`10⁶` columns the declined
   route would have had to eliminate, and the whole run — three classes at `n = 7`, plus
   brute-force cross-checks at `n = 3..6`, plus the control steps `V0`–`V8` — costs **≈ 48 s and
   277 MB in a single process**. *(The 47.8 s and the 277 MB are measured; the cost of the
   declined computation is **not** — `mg-72e4` reports only that its rank computation "had not
   returned", so no ratio between the two is stated here and none should be quoted.)* The point
   the figure does support: what closed this was reading `mg-bcd7`, not more cores.

3. **The result is `Z`-acyclic, not contractible, and the two are not being conflated.** The
   exactness in §2 is at chain level over `Z`, so it gives `H̃_*(Γ(P); Z) = 0`. That is strictly
   stronger than the rational statement the margin needs and strictly weaker than
   contractibility, which is **not** claimed anywhere here and which this instrument cannot see.
   See §5.

**What this does NOT do.** It does not prove Conjecture C, it does not touch `n ≥ 8` beyond the
hypothesis check in §4.4, and it does not make the `c ≤ 2` slice a consequence of anything — it
supplies an argument for *three named families*, not for `c ≤ 2` in general. §6 is explicit.

---

## 1. What was open, and the three numbers that were in play

`mg-72e4` published *"min margin 4"* at `n = 7` with no denominator. `mg-9cd1` **D2** found the
denominator was **148 of 163** and that 15 classes had no margin information of any kind.
`mg-0f24` landed the repair and **derived** the population rather than adding the published
figures: `146` (full homotopy type computed) → `148` (as published, `146` + the 2 stars) →
**`160` of 163** (`146` + the 14 `mg-9cd1` measured), **not** `148 + 14 = 162`, because the two
stars are in both sets and the overlap is 2.

That left three classes / 252 labelled vertices at `margin ≥ 1`, which is what this document
closes. The arithmetic trap is worth restating because it recurs one level down: the new
population is **163**, and it is `160 + 3` only because these three classes are disjoint from the
160 — which is checkable and checked (`V0` in the instrument re-derives the `n = 7` class list and
confirms exactly these three `c ≤ 2` classes sit above the 20-atom margin gate; the fourth
`c = 2` class, `P = {(0,3),(1,2)}` with 420 labelled vertices, has **20** atoms and was inside the
gate all along, i.e. inside the 146).

---

## 2. The argument

Fix a height-1 `P ∈ PPF_n`, write `Atoms(P)` for the minimal elements of `U(P)` and

    Γ(P) = { S ⊆ Atoms(P) : tc(P ∪ ⋃S) is a NON-TOTAL partial order }        (mg-72e4 §3)
    X(P) = { S ⊆ Atoms(P) : tc(P ∪ ⋃S) is a          partial order }
    F    = X ∖ Γ = { S ∈ X : tc(P ∪ ⋃S) is TOTAL }.

`F` is upward closed in `X`: a total order is maximal among partial orders, so any face of `X`
above a face of `F` has the *same* transitive closure and is in `F` too.

### L1 — `X` is a cone, in one of two dual forms

Suppose some `s ∈ [n]` is carried by **no atom as a head**: no atom's relation set contains a
pair `(y, s)`. Every atom contains `P`, so `s` is then a source of `P` as well, and hence a source
of `tc(P ∪ ⋃S)` for every face `S` of `X`. Let `α₀ := tc(P ∪ {(s, x)})` for any `x` making `α₀` an
atom; the pairs `α₀` adds to `P` are `{(s, z) : z = x or x <_P z}`, all of which leave `s`, so
adjoining `α₀` to a face of `X` can close a cycle only through an in-arc at `s`, and there is
none. Hence `S ∪ {α₀} ∈ X` for every `S ∈ X`, `X` is a cone with apex `α₀`, and `H̃_*(X) = 0`.

Dually: if some `t` is carried by no atom as a **tail**, `α₀ := tc(P ∪ {(x, t)})` is an apex by
the same argument with the arrows reversed.

**Both forms are needed, and only writing the first is what the instrument caught.** The `V`
class `P = {(0,1),(0,2)}` has the source form (`0` is in no atom's head set — every candidate
`tc(P ∪ {(y,0)})` is either cyclic or contains the atom `tc(P ∪ {(y,1)})` properly and so is not
minimal). Its dual `P = {(0,2),(1,2)}` has the **sink** form and no source form at all. The first
version of the instrument searched only for a source and reported
`n7_c2_L: X not shown to be a cone` — a real refusal, on the class where the LES would otherwise
have been used without a warrant. It is recorded here rather than quietly fixed because the
failure mode it avoided is the one this lineage keeps paying for.

### L2 — `F` splits over the total orders it realises

Every `S ∈ F` determines the total order `L(S) := tc(P ∪ ⋃S)`. If `τ = S ∖ {α}` is still in `F`
then `L(τ) ⊆ L(S)` and both are total on `[n]`, so `L(τ) = L(S)`. Every boundary face therefore
either stays in `F` **with the same `L`** or leaves `F` and is zero in the relative complex
`C_*(X, Γ)`, which is free on `F`. So

    C_*(X, Γ)  =  ⊕_L  C_*(L)          over the total orders L ⊇ P that F realises.

### L3 — each summand is the augmented chain complex of a simplex

Fix such an `L`, and let `A_L := {α ∈ Atoms(P) : α ⊆ L}`. Write `cov(L)` for the cover pairs of
`L`.

> **A cover pair of `L` lies in exactly one atom of `A_L`.** If `(x,y) ∈ cov(L) ∖ P` lies in
> `α = tc(P ∪ {r}) ⊆ L` and `(x,y)` is *derived* rather than equal to `r`, there is an
> intermediate `z` with `x <_α z <_α y`, hence `x <_L z <_L y`, contradicting `(x,y)` being a
> cover of `L`. So `r = (x,y)` and `α = tc(P ∪ {(x,y)})`.

Set `Req(L) := {tc(P ∪ {(x,y)}) : (x,y) ∈ cov(L) ∖ P}` and `Opt(L) := A_L ∖ Req(L)`. A face `S` of
`F` with `L(S) = L` has `⋃S ⊆ L`, hence `S ⊆ A_L`; and for `S ⊆ A_L`, `tc(P ∪ ⋃S) = L` iff
`⋃S ∪ P ⊇ cov(L)`, which by the box above is iff `S ⊇ Req(L)`. So the faces of `F` with order `L`
are **exactly**

    { Req(L) ∪ T  :  T ⊆ Opt(L) },

of dimension `|Req(L)| + |T| − 1`. Deleting an element of `Req(L)` drops out of `F`; deleting an
element of `T` stays. That is precisely the **augmented** chain complex of the full simplex on
the vertex set `Opt(L)`, shifted up by `|Req(L)|` — with `T = ∅` playing the role of the empty
face.

*(If some cover of `L` is not carried by any atom, no `S` generates `L` and `L` contributes
nothing. That is why only 120 of the 2 520 total orders above `P = {(0,1)}` are realised, and 48
of the 1 680 above each `c = 2` class.)*

### L4 — `Opt(L)` is non-empty, and that is the whole hypothesis

The augmented chain complex of a simplex on a **non-empty** vertex set is exact. So if
`Opt(L) ≠ ∅` for every realised `L`,

    H_k(X, Γ) = 0   for every k,

and with `X` contractible the long exact sequence of the pair gives
`H̃_k(Γ) ≅ H_{k+1}(X, Γ) = 0` for every `k`. Over `Z`: the relative complex is free and each
summand is exact as a complex of free abelian groups.

**L4 is a real hypothesis and it does fail.** At `n = 3` the `c = 1` class has one realised total
order with `|Req| = 2` and `|Opt| = 0`; the summand is a single generator with zero boundary,
`H_1(X, Γ) = 1`, and `β̃₀(Γ) = 1` — `Γ` is `S⁰`, which is `mg-72e4`'s *"all 12 links at `n = 3`
non-contractible"*. The instrument computes that case and **requires** it to come out non-zero
(a `V7` failure is declared if `n = 3` reports acyclic). A hypothesis that is never false is not
doing any work.

For these three families `Opt(L)` is non-empty at every `n ≥ 4`, in closed form:

| family | realised `L` | `|Req(L)|` | `|Opt(L)|` |
|---|---|---|---|
| `c = 1`, `m := n − 2` | `m!` | `n − 1` | `C(m,2) + m − 1` |
| `c = 2` V and Λ, `f := n − 3` | `2 · f!` | `n − 1` | `C(f,2) + 2f − 1` |

Both are `≥ 1` for `m ≥ 2` resp. `f ≥ 1`, i.e. for `n ≥ 4`. At `n = 7`: `120` orders, `|Req| = 6`,
`|Opt| = 14` for `c = 1`; `48` orders, `|Req| = 6`, `|Opt| = 13` for each `c = 2` class. Every
entry in that table is reproduced by the instrument at `n = 3..8` (§4.4), not read off the
formula.

---

## 3. What was measured, not assumed

Each row is a key in the JSON and is re-run by the instrument.

| step | check | result |
|---|---|---|
| `V0` | this instrument's `tc`, atom routine and rank routine against **`mg-72e4`'s own** | atoms identical on all three classes; `tc` agrees on 2 000 random relations at `n = 5`; both rank routines agree on 200 random sparse matrices; the bitset `F₂` rank agrees with the sparse one |
| `V0` | the `n = 7` class census re-derived, and which `c ≤ 2` classes are over the 20-atom margin gate | 163 classes / 227 892 vertices; the three named classes are exactly the `c ≤ 2` ones over the gate |
| `V1` | homology reader against known answers: `∂Δ^k ≃ S^{k−1}` for `k = 1..5`, the 7-vertex `Z₇` torus, the 6-vertex `RP²` | `(0,0,2,1)` for the torus at both fields; `RP²` reads `(0,0,0,0)` rationally and `(0,0,1,1)` over `F₂` — the reader **can** distinguish rational vanishing from torsion-free vanishing |
| `L1` | the cone apex, plus exhaustive re-check that adjoining it keeps every face of `X` of size ≤ 4 (≤ 6 at small `n`) inside `X` | 23 586 faces checked at `n = 7`, `c = 1`; passes for all three, one by the source form and one by the **sink** form |
| `L3` | every cover of every realised `L` lies in exactly one atom of `A_L` | multiplicity set `= {1}` for all three |
| `L3` | every block, face by face, equals `{Req(L) ∪ T : T ⊆ Opt(L)}` | 0 blocks fail |
| `L2` | the relative boundary, computed on the enumerated faces, never crosses blocks | 0 crossings |
| `F` | the filter enumerated **directly from the raw predicate** (`tc(P ∪ ⋃S)` total), and compared with the closed form of §2 | agree at every dimension |
| `F` | the **minimal** faces of `F` found by brute-force DFS over subsets of the atoms | exactly the 120 (resp. 48) `Req(L)` — so the upward enumeration is complete |
| `V6` | the enumeration re-run with the "only try atoms inside `L`" shortcut **removed** | identical output at `n = 4, 5, 6` for all three families |
| `V8` | the mechanism run on three classes that **do** carry homology (`K_{6,1}`, `K_{1,6}`, `K_{3,4}`) — it must fail on them, and the step that fails must be named | fails at **L1** on all three; `L3` and `L4` hold. §6 pt 3 |
| ranks | every degree computed **blocked** (per `L`) and, where affordable, **globally** as one matrix | agree everywhere both were computed |
| ranks | 7 primes: `2, 3, 5, 7, 46337, 999983, 1000003` | agree at every degree computed |
| `V5` | `mg-bcd7`'s published `\|F\|` at dims 5/6/7 and its ranks `∂₆ = 120`, `∂₇ = 1 560` | **reproduced exactly**: `120, 1 680, 10 920` and `120, 1 560` |

### 3.1 The numbers

`c = 1`, `P = {(0,1)}` — 30 atoms, 120 realised total orders, `|Req| = 6`, `|Opt| = 14`:

| dim of `F` | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|
| faces | 120 | 1 680 | 10 920 | 43 680 | 120 120 | 240 240 |
| `rank ∂` | 0 | 120 | 1 560 | 9 360 | 34 320 | 85 800 |

`= 120 · C(14, k−5)` and `= 120 · C(13, k−6)` respectively, at all seven primes. Hence
`H_k(X, Γ) = 0` for `k ≤ 9`, i.e. **`β̃_{−1} … β̃₈(Γ) = 0`**, which is `margin ≥ 4` with three
degrees to spare — and §2 says every remaining degree is zero too.

Each `c = 2` class — 26 atoms, 48 realised orders, `|Req| = 6`, `|Opt| = 13`:

| dim of `F` | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|
| faces | 48 | 624 | 3 744 | 13 728 | 34 320 |

giving **`β̃_{−1} … β̃₇(Γ) = 0`**, again at all seven primes, which is `margin ≥ 4` with three
degrees to spare.

### 3.2 The negative control, and the version that does not discriminate

`V4` is `mg-bcd7`'s `V6` re-run for this instrument: inside the same `X` (at `n = 6`, where the
whole complex is affordable), replace the true filter by a **different** family of the same number
of generators of the same size, and read the relative homology. Three substitutions were tried for
each class:

| substitution | `c = 1` | `c = 2` V | `c = 2` Λ |
|---|---|---|---|
| lexicographically first non-filter faces of `X` (same count, same size) | **`H₄ = 1`** | **`H₄ = 1`** | **`H₄ = 1`** |
| lexicographically last | all zero | all zero | all zero |
| seeded random | all zero | all zero | all zero |

The two that came out zero are reported, not dropped. They are the shape of control `mg-bcd7`
already recorded as vacuous — plenty of filters in the same degree are also exact — and the one
that moves is what shows the measurement is reading the filter rather than the shape of the code.
A control that only ever fires is no better than one that never does.

### 3.3 Brute force, at every `n` where brute force is possible

`V3` computes `Γ(P)` **in full** by DFS on the face predicate — *this* instrument's, written from
scratch and checked against `mg-72e4`'s `tc` and atom routine in `V0` — and reads its reduced
Betti vector directly, with no decomposition anywhere in the path, then compares with the relative
route:

| class | `n` | atoms | `Γ` faces | degrees compared | direct `β̃` | relative `β̃` | |
|---|---|---|---|---|---|---|---|
| `c = 1` | 3 | 2 | 2 | `−1 … 0` | `(0, 1)` | `(0, 1)` | **agree — and non-zero**, the `L4` failure |
| `c = 1` | 4 | 6 | 39 | `−1 … 3` | all 0 | all 0 | agree |
| `c = 1` | 5 | 12 | 1 407 | `−1 … 5` | all 0 | all 0 | agree |
| `c = 1` | 6 | 20 | 126 719 | `−1 … 4` | all 0 | all 0 | agree |
| `c = 2` V, Λ | 4 | 5 | 19 | `−1 … 2` | all 0 | all 0 | agree |
| `c = 2` V, Λ | 5 | 10 | 511 | `−1 … 5` | all 0 | all 0 | agree |
| `c = 2` V, Λ | 6 | 17 | 35 327 | `−1 … 5` | all 0 | all 0 | agree |

The direct Betti vector is read only as deep as a 40 000-face budget allows — that is why the
`n = 6`, `c = 1` row stops at degree 4 despite `Γ` being fully enumerated — and the relative route
is read to degree 5 at `n ≤ 6`, so the compared range is the intersection. It is recorded per row
in the JSON under `agree_on_degrees`, and nothing outside that range is being claimed as
cross-checked.

---

## 4. Consequences at their destinations

### 4.1 The denominator

> **`min margin = 4` at `n = 7`, over 163 of 163 iso classes and 227 892 of 227 892 labelled
> height-1 vertices.** The minimum is attained at the two stars `K_{6,1}`, `K_{1,6}`, whose
> margin is `= 4` by F17+F18 and `≥ 4` by `mg-9cd1`'s mod-2 measurement.

The population walk, complete:

| | classes | labelled | |
|---|---|---|---|
| full homotopy type of `Γ(P)` computed (`#atoms ≤ 20`) | 146 | 225 540 | `mg-72e4` |
| as first published (`146` + the 2 stars, inferred) | 148 | 225 554 | `mg-72e4`, denominator unstated — `mg-9cd1` **D2** |
| `146` + the 14 `mg-9cd1` measured (overlap 2, **not** `148 + 14`) | 160 | 227 640 | `mg-0f24` |
| **+ the 3 `c ≤ 2` classes of this document** | **163** | **227 892** | **`mg-dd84`** |

`160 + 3 = 163` composes here — where `148 + 14` did not — because the three classes of this
document are disjoint from the 160 by construction: they are precisely the classes with **no**
margin information after `mg-0f24`. That disjointness is checked (`V0`), not assumed, for the
same reason the earlier sum was wrong.

### 4.2 `mg-bcd7` §7's observed pattern now has a reason

`mg-bcd7` measured the `c = 1` family at `n = 4 … 9` and recorded, explicitly as a pattern and
explicitly as unproved:

    rank ∂_{m+2} = |F_{m+1}|            rank ∂_{m+3} = |F_{m+2}| − |F_{m+1}|

Those are exactly the first two exactness identities of §2's direct-sum decomposition, and §2
gives them for every degree and every `n ≥ 4`: `|F_{m+1+t}| = m! · C(k, t)` with `k = |Opt|`, and
the ranks are the partial alternating sums of a simplex boundary. `mg-bcd7`'s `n = 8` and `n = 9`
rows are consistent with it; this document does not re-run them and does not claim to have
measured `n ≥ 8` homology.

### 4.3 What is unchanged

- **`≥ 6 of 163` classes carry homology in degree 4, still `≥` and not `=`.** These three carry
  none, so they do not add to the count; the reason it stays a lower bound is `mg-9cd1` **D3** —
  the 146 were read over two primes near `10⁶` and the 17 over `Z/2`, so 2-torsion in degree 4
  among the 146 is invisible to both. That remainder is `mg-c99c`'s R2, not this document's.
- **Conjecture C is not proved and is not touched.** §2 is an argument about three named
  families, not about `c ≤ 2`.
- **`n = 7` was already 163 of 163 / 227 892 of 227 892 with 0 violations** for the anchor-degree
  census (`mg-bcd7`, `mg-0f24`). What was partial was the *margin*, and only that.

### 4.4 The hypotheses across `n`, as far as this run goes

`V7` checks L1, L3's multiplicity condition and L4 at `n = 3 … 8` for all three families, from
the poset alone — no filter enumerated, no rank taken:

| `n` | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| `c = 1`: atoms / realised `L` / `\|Opt\|` | 2 / 1 / **0** | 6 / 2 / 2 | 12 / 6 / 5 | 20 / 24 / 9 | 30 / 120 / 14 | 42 / 720 / 20 |
| `c = 2` V and Λ: atoms / realised `L` / `\|Opt\|` | 0 / 0 / — | 5 / 2 / 1 | 10 / 4 / 4 | 17 / 12 / 8 | 26 / 48 / 13 | 37 / 240 / 19 |

L1 holds at every `n ≥ 4` (source form for `c = 1` and V, **sink** form for Λ), the cover
multiplicity is `1` throughout, and L4 holds at every `n ≥ 4`. So `Γ(P)` is acyclic for these
three families at `4 ≤ n ≤ 8`, by the argument, checked. `n ≥ 9` is not run here and nothing is
claimed there.

The `n = 3` column fails for two different reasons and they should not be run together: for
`c = 1` the hypothesis that fails is **L4** (`|Opt| = 0`, one realised order) and `Γ` is genuinely
`S⁰`; for the two `c = 2` shapes there are **no atoms at all** on three elements — every
`tc(P ∪ {r})` is total — so `Γ` is the empty complex and there is nothing for either hypothesis to
say. Only the first is the interesting failure.

---

## 5. Coefficients — read this before quoting the number

- **The vanishing is `Z`-acyclic**, and that comes from §2 being an exactness statement about a
  complex of free abelian groups, not from any prime. `H̃_k(Γ(P); Z) = 0` for all `k`, hence
  `H̃_k(Γ(P); Q) = 0`.
- **It is NOT contractibility.** `Z`-acyclic does not imply contractible, this document does not
  say it does, and the instrument computes no homotopy group. The `mg-e08a` trap is honoured in
  the same terms `mg-bcd7` §5 uses.
- **The mod-`p` measurements corroborate; they do not establish.** `rank_{F_p} ≤ rank_Q` gives
  `β_Q ≤ β_{F_p}`, so a single vanishing prime forces rational vanishing — the safe direction, and
  the one used. The reverse (reading a rational value off agreeing mod-`p` values) is not used
  anywhere here. Every rank in §3.1 was in fact computed at all seven primes and they agree, which
  says the relative homology carries no `p`-torsion for `p ∈ {2,3,5,7}` in the degrees read; that
  is a statement about the *pair* `(X, Γ)`, and the integral statement about `Γ` is §2's.
- **The margin, precisely.** "Margin" is `firstnonzero(β̃) − d`. These three classes have no
  non-zero degree, so they have no margin in that sense; they satisfy `margin ≥ 4` vacuously and
  they do **not** attain the minimum. Saying *"their margin is 4"* would be wrong in the
  direction that matters, and no table here says it.

---

## 6. What is still open

1. **Conjecture C**, unchanged. `c ≤ 2` is still not covered by it even if it were proved, and §2
   is not a substitute: it is an argument for `P = {(0,1)}` and the two `c = 2` shapes on any `n`,
   not for the slice.
2. **`n ≥ 8`** — §4.4 checks the *hypotheses* to `n = 8` and nothing beyond. `mg-c99c` carries the
   two "run the repaired instrument wider" remainders (`R1`, the realised-face gate unmeasured at
   `n = 8` for 6 classes; `R2`, `D3`'s `≥ 6` which cannot become `= 6` until the 146 are re-read
   over `Z/2`). Neither is touched here.
3. **Whether the §2 mechanism extends past these three families — and exactly which step stops
   it.** L2 and L3 are general: they use nothing about `c`. **The one that fails is L1**, and
   `V8` measures that rather than asserting it, on the three `n = 7` classes known to carry
   homology in degree 4:

   | class | `L1`: `X` a cone | `L3`: cover multiplicity | `L4`: `Opt(L) ≠ ∅` | fails at |
   |---|---|---|---|---|
   | `K_{6,1}` | **no** | `{1}` | yes (`|Opt| = 10`, 720 orders) | **L1** |
   | `K_{1,6}` | **no** | `{1}` | yes (`|Opt| = 10`, 720 orders) | **L1** |
   | `K_{3,4}` | **no** | `{1}` | yes (`|Opt| = 4`, 144 orders) | **L1** |

   At `K_{6,1}` the element `0` *is* carried by no atom as a head — but every pair `(0, x)` is
   already in `P`, so there is no **atom** `tc(P ∪ {(0,x)})` to serve as apex, and the cone
   collapses at exactly that point. So the mechanism is not a proof of the whole census and must
   not be quoted as one; what it needs is `X` contractible, and *"for which height-1 `P` is
   `X(P)` contractible"* is the well-posed question this document leaves open.

   *(This bullet said "both L1 and L4 fail" when it was first drafted. L4 holds at all three —
   `V8` exists because that assertion had not been measured.)*

---

## 7. References

`docs/OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md` (§0 result 1, §4.2, §7 — amended by
this work); `docs/OneThird-mg9cd1-Height1Anchor-IndependentAudit.md` (§4.3, §6.1, §7 — the
remainder this closes); `docs/OneThird-mgbcd7-n7c1-Beta5.md` (the cone/LES decomposition this
extends, and §7's pattern); `docs/OneThird-mg52c4-PerPoset-Subposet-Question.md` (Theorem A, the
crosscut reduction); `docs/OneThird-mge08a-TheoremA-IndependentAudit.md` (the `Q`-acyclicity
trap). `scripts/compat_geom_mg72e4_height1_anchor.py` (imported once, in `V0`, deliberately, as an
external control). Work items: `mg-dd84` (this), `mg-72e4`, `mg-9cd1`, `mg-0f24`, `mg-bcd7`,
`mg-c99c` (the sibling carrying `R1`/`R2`). Literature: Björner, *Topological methods*, Thm 10.8.
