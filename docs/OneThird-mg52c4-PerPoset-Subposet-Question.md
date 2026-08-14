# What is proven for INDIVIDUAL posets and their proper subposets (mg-52c4)

*Answers `mg-e768` PART B, asked by Daniel on 2026-08-06 and re-asked 2026-08-13. `mg-65f5` carried
R1/R2/R3 and explicitly did not carry PART B; this document carries it.*

> **Daniel, 2026-08-06 (`mg-e768`):** *"i remember that we proved the whole category pos_n is
> spherical, but i can't remember if we proved anything for individual posets, say for instance
> taking all their proper subposets"*

Verification harness: [`scripts/compat_geom_mg52c4_subposet_complexes.py`](../scripts/compat_geom_mg52c4_subposet_complexes.py),
output [`data/onethird-mg52c4-subposet-complexes.json`](../data/onethird-mg52c4-subposet-complexes.json).
Run: `/usr/bin/python3 scripts/compat_geom_mg52c4_subposet_complexes.py` (~2 min, stdlib only,
`ALL_PASS = True`).

---

## 0. The answer, in five lines

1. **YES — one thing was already proven for an individual poset's proper subposets, and it is the
   load-bearing lemma of the very theorem Daniel remembers.** F17's **Lemma L1**: for `P` a *chain*,
   the complex of nonempty proper subposets of `P` is **contractible**. It is the single genuine
   homotopy-equivalence input to F17, and hence sits underneath F17+F18's `Δ_n ≃_Q S^{n-2}`
   (§2.2). Nothing else per-poset is proven anywhere in the corpus (§2.6).
2. **This ticket settles the general case.** *(Theorem A, §2.3.)* For **any** finite poset `P` with at
   least one relation, the complex of its nonempty proper subposets is **contractible if `P` has a
   3-element chain**, and is `S^{c−2}` (`c = ` number of comparable pairs) **if `P` has height 1**.
   The proof is elementary and is L1's own closure-operator argument with one word changed.
3. **The category-level result does restrict to individual posets — to zero.** Restriction of
   `ω_bal^(n)` to the up-set `↑P` vanishes for *every* `P` and every `n`, because `Δ(↑P)` is a cone
   (§3.1); and by Theorem A the *link* `lk_{Δ_n}(P)` is contractible for every `P` with a 3-chain, so
   the class dies there too (§3.3). Every width-≤3 poset on `n ≥ 7` elements has a 3-chain (Mirsky),
   so in the target regime the fibrewise anchor is **identically trivial**, not merely unproven.

   > **SCOPED 2026-08-14 (`mg-e08a` audit, carried by `mg-1b3b`).** *"Identically trivial"* is
   > proven for less than the sentence above implies, and the rest is true by measurement.
   > The honest statement, in four clauses:
   >
   > - **Proven at height ≥ 2.** The link is contractible at every height-≥2 vertex — Corollary B,
   >   all `n`, no width bound (§3.3). That is 108 of the 194 vertices at `n = 4`.
   > - **VACUOUS at `n = 3`.** `PPF_3` has **no** height-≥2 element (the census in §2.4 says `0`), so
   >   Corollary B's population there is empty; and **all 12 links at `n = 3` are non-contractible**
   >   (each is `S⁰`).
   > - **Measurement only elsewhere.** At the height-1 vertices — which Mirsky removes from the
   >   *width-≤3 family* but **not** from the *vertex set of `Δ_n`*, which is all of `PPF_n` — the
   >   link is often **not** contractible: 38 of 194 at `n = 4` (32 with `β̃₃ = 1`, 6 with `β̃₃ = 3`).
   >   What survives there is the weaker fact that the anchor-degree component
   >   `H̃_{n−2}(lk_{Δ_n}(P))` is zero, established by **exhaustive measurement at `n ≤ 5`**
   >   (`mg-e08a` §7) and by no argument: every case lands on zero by exactly one degree and no
   >   dimension argument forces it.
   > - **Not established for `n ≥ 6`.** The height-1 population does not vanish there
   >   (11 642 of 129 302 at `n = 6`), and at `n ≥ 7` those vertices are all of width ≥ 4, so Mirsky
   >   says nothing about them either.
   >
   >   > **UPDATED 2026-08-14 (`mg-72e4`).** `n = 6` **is** now established: all 55 height-1
   >   > isomorphism classes, covering every one of the 11 642 labelled vertices, **0 violations**,
   >   > none over cap. The `n = 5` evidence is now 20/20 classes rather than 58/61 — the three
   >   > over `mg-e08a`'s materialisation cap are computed. **And the "exactly one degree" wording
   >   > in the clause above is an `n = 4` artifact:** measured over the whole homotopy type rather
   >   > than the anchor degree alone, the margin to the nearest non-vanishing degree is `1` at
   >   > `n = 4`, `2` at `n = 5`, `3` at `n = 6`. Still **not proven** for all `n`; what is proven
   >   > is the `c ≥ n` slice. See
   >   > [`OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md`](OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md).
   >   >
   >   > **EXTENDED to `n = 7` 2026-08-14 (`mg-9cd1` D4, carried by `mg-0f24`).** The record above
   >   > stopped at `n = 6` three commits after it was written. `n = 7` is measured **complete** —
   >   > **163 of 163** iso classes, **227 892 of 227 892** labelled height-1 vertices, **0
   >   > violations** (`mg-72e4`, its last class closed by `mg-bcd7` and replicated independently by
   >   > `mg-9cd1`) — and the margin there is **`≥ 4`**, on 160 of the 163 classes, the remaining
   >   > three (`c ≤ 2`, 252 vertices) bounded only at `≥ 1`. Nothing above is retracted and nothing
   >   > is proven that was not: `n = 7` is still measurement.
   >
   > **This scopes the claim; it does not retract it.** The recommendation *"do not open an F33"*
   > (§5) survives the audit unchanged, and a reader who takes this note as licence to reopen the
   > arc has misread it. See `docs/OneThird-mge08a-TheoremA-IndependentAudit.md` §0, §6, §7, §9.
4. **Two F28 statements are wrong and are struck at their destination** (§3.1–§3.2): (F-5)
   *"restriction maps carry local-to-global content"* is **vacuous**, and §2.3's identification
   `Δ(↑P ∖ {P}) = lk_{Δ_n}(P)` **drops the lower factor** — the very factor Theorem A computes.
5. **Sub-question 3 (what would a fibrewise sphere theorem buy?): nothing** (§4). It would replace a
   rank-1 sgn-isotype anchor by a rank-0 one; and in the one case where a sphere *does* appear
   (height 1) the dimension of **`Δ(L̄(P))`, the lower join factor**, depends only on `|Comp(P)|`, so
   it cannot separate a bad-cut poset from a good one — and no height-1 poset of width ≤ 3 has more
   than 6 elements. (The blindness is a property of that *lower factor* and does **not** transfer to
   `lk_{Δ_n}(P)` itself — §4 point 4, as corrected.) **Recommendation: do not open an F33.** §5.

---

## 1. What the question is, stated precisely

**Settled, and not re-derived here (ticket mandate).** F17 (`mg-4d3a`) + F18 (`mg-d039`), both GREEN
and unconditional:

    H̃^k(Δ_n; Q) = 0            for 0 < k < n−2
                 = sgn_{S_n}    for k = n−2,          all n ≥ 3,

`Δ_n := Δ(PPF_n)`, `PPF_n` = the poset of *proper* partial orders on `[n]` (non-empty relation,
non-total) ordered by refinement `P ≤ Q ⟺ P ⊆ Q` as relation sets (F13 §1 notation). The obstruction
class is `ω_bal^(n) ∈ H̃^{n-2}(Δ_n, Q)^{sgn}`, unique up to scalar.

That is a statement about the **whole category**. The per-poset object is, for a fixed
`P ∈ PPF_n`, the **open lower interval**

    L̄(P) := { Q ∈ PPF_n : Q ⊊ P }  =  { Q transitively closed : ∅ ≠ Q ⊊ P },

the second equality because every sub-relation of a non-total `P` is non-total, so `PPF_n`'s side
conditions are automatic below `P`. `Δ(L̄(P))` **is** "the complex of all proper subposets of `P`".

### 1.1 Three readings of "subposet", and which one is which

| reading | object | used by |
|---|---|---|
| **(S1) sub-relation** — weaken the order, same ground set: `Q ⊆ P` | `L̄(P)`, the *down*-direction in `PPF_n` | **F17 Lemma L1**; this document |
| **(S2) refinement** — `P ⊆ Q`, so `L(Q) ⊆ L(P)` and `G_BK(Q)` is an induced subgraph of `G_BK(P)` | `↑P`, the *up*-direction | F28 §1.5/§3, F29 §1.2, F30, F31 |
| **(S3) induced subposet on a proper subset `S ⊊ [n]`** | the Boolean lattice `B_n` minus its top | nobody |

The F28/F29/F30/F31 line committed to **(S2)** because that is the reading under which BK graphs
restrict to induced subgraphs (F28 §1.2 (ii)). Daniel's wording — *"taking all their proper
subposets"* — is most naturally **(S1)**, which is also the reading under which F17's L1 is stated.
**All three are answered below**: (S1) in §2.3, (S2) in §3, (S3) in §2.5.

---

## 2. Sub-question 1 — is there a per-poset complex with a computed homotopy type?

### 2.1 Answer

Yes. One case was already proven (§2.2); the general case is settled here (§2.3); and the answer is
that in the regime the 1/3–2/3 program cares about, the complex is **contractible** — so the honest
headline is *"yes, and it is trivial"*, not *"nothing is known"*.

### 2.2 What was already proven — F17 Lemma L1, verbatim

`docs/compatibility-geometry-F17-equivariant-cofiber-morse.md` §3:

> **Lemma L1.** *Let `Q_0` be a total order (chain) on `[n]`, `n ≥ 3`. The poset*
> `L̄(Q_0) := {Q : ∅ ≠ Q ⊊ Q_0, Q transitively closed}`
> *of nonempty proper sub-partial-orders of the chain (ordered by inclusion) has* **contractible**
> *order complex.*

Its proof takes `r_* := (a_1, a_n)` (bottom-to-top relation of the chain) and shows
`c(Q) := tc(Q ∪ {r_*})` is a closure operator on `L̄(Q_0)` whose image has global minimum `{r_*}`;
Björner's order-homotopy lemma then gives `Δ(L̄(Q_0)) ≃ Δ(c(L̄(Q_0)))`, a cone.

**This is exactly a per-poset proper-subposet statement for an individual poset.** F17 §3 Remark (b)
records that L1 is *"the **single** topological input that is not 'a cone' or 'an interior
operator'"* in the whole F17 reduction — i.e. the answer to Daniel's question is not a footnote, it
is the one genuine homotopy-theoretic lemma sitting under the category-level sphere theorem he
remembers.

What L1 does **not** do: it covers only `P = ` a chain, and it produces *contractible*, not
*spherical*.

### 2.3 Theorem A — the general case (new here)

> **Theorem A (mg-52c4).** Let `P` be a finite poset with at least one strict relation. Write
> `Comp(P)` for its set of comparable pairs, `c := |Comp(P)|`, and `Cov(P)` for its cover relations.
> Let `L̄(P) = {Q : ∅ ≠ Q ⊊ P, Q transitively closed}` be the poset of proper subposets of `P`. Then
>
> - **(A1)** if `P` has a 3-element chain `a < b < c` (equivalently `Cov(P) ≠ Comp(P)`, equivalently
>   `height(P) ≥ 2`), then `Δ(L̄(P))` is **contractible**;
> - **(A2)** if `P` has height 1 (`Cov(P) = Comp(P)`, i.e. no 3-chain), then
>   `Δ(L̄(P)) ≅ sd(∂Δ^{c-1}) ≃ S^{c-2}` — a sphere, with the convention `S^{-1} = ∅` when `c = 1`.
>
> In particular the homotopy type depends on `P` **only** through the pair
> `(height(P) ≥ 2?, |Comp(P)|)`.

*Proof of (A2).* If `P` has no 3-chain then no two relations of `P` compose: a composable pair
`(a,b), (b,c) ∈ P` would exhibit `a < b < c`. Hence **every** subset of `Comp(P)` is transitively
closed, so `L(P) := {Q ⊆ P transitively closed}` is the full Boolean lattice `2^{Comp(P)}` and
`L̄(P)` is its proper part. The order complex of the proper part of a Boolean lattice on `c` atoms is
the barycentric subdivision of `∂Δ^{c-1}`, i.e. `S^{c-2}`; for `c = 1` the proper part is empty. ∎

*Proof of (A1).* Pick `v := (a,c) ∈ Comp(P) ∖ Cov(P)` (it exists: `a < b < c` makes `(a,c)`
comparable and not a cover). Define `κ(Q) := tc(Q ∪ {v})` on `L̄(P)`.

- *`κ` lands in `L̄(P)`.* `Q ∪ {v} ⊆ P` and `P` is transitively closed, so `κ(Q) ⊆ P`; and
  `κ(Q) ⊇ {v} ≠ ∅`. It remains to show `κ(Q) ≠ P`. Suppose `tc(Q ∪ {v}) = P`. Every cover relation
  of `P` is join-irreducible for `tc`: if `(x,y) ∈ tc(S)` with `(x,y)` a cover, then `(x,y) ∈ S`
  (any strictly shorter derivation would produce an element strictly between `x` and `y`). Hence
  `Cov(P) ⊆ Q ∪ {v}`, and `v ∉ Cov(P)`, so `Cov(P) ⊆ Q`; but `tc(Cov(P)) = P`, so `Q = P`,
  contradicting `Q ⊊ P`.
- *`κ` is a closure operator.* Extensive (`Q ⊆ κ(Q)`), monotone (`tc` is monotone), idempotent
  (`v ∈ κ(Q)`, so `κ(κ(Q)) = tc(κ(Q) ∪ {v}) = κ(Q)`).
- *The image is a cone.* `κ(L̄(P)) = {Q ∈ L̄(P) : v ∈ Q}` has global minimum `{v}` — a singleton
  relation is transitively closed, is nonempty, and is proper because `Cov(P) ≠ ∅` and `v ∉ Cov(P)`
  give `|Comp(P)| ≥ 2`.

A closure operator induces `Δ(L̄(P)) ≃ Δ(κ(L̄(P)))` (Björner, *Topological methods*, §10.2 —
the same citation F17 §3 uses), and a poset with a global minimum has contractible order complex. ∎

**Relation to L1.** Take `P = ` a chain on `[n]`, `n ≥ 3`, and `v = (a_1, a_n)`: (A1)'s proof *is*
L1's proof. L1 is the special case; Theorem A is L1 with "bottom-to-top relation of a chain"
replaced by "any comparable non-cover pair", plus the height-1 case L1 never had to consider.

**An equivalent route, for cross-checking.** `L(P)` is a finite lattice (meet = intersection, join =
`tc` of union, `0̂ = ∅`, `1̂ = P`) whose atoms are the singletons `{e}`, `e ∈ Comp(P)`. Björner's
crosscut theorem gives `Δ(L̄(P)) ≃ Γ = {A ⊆ Comp(P) : tc(A) ≠ P} = {A ⊆ Comp(P) : Cov(P) ⊄ A}`.
If some `v ∈ Comp(P) ∖ Cov(P)` exists then `Γ` is a cone with apex `v` (adjoining `v` cannot supply a
missing cover) — contractible; otherwise `Γ = ∂Δ^{c-1}`. Same dichotomy, no closure operator.

### 2.4 Machine verification

`scripts/compat_geom_mg52c4_subposet_complexes.py`, `ALL_PASS = True`:

| check | scope | result |
|---|---|---|
| **T1** Möbius number `μ(∅, P)` = predicted reduced Euler characteristic (`0` / `(−1)^c`) | **every** `P ∈ PPF_3` (12), `PPF_4` (194), `PPF_5` (4110); a `PPF_6` sample of 14813 that **includes every height-1 poset of `PPF_6`** | 0 failures |
| **T2** full reduced Betti vector of `Δ(L̄(P))` = predicted (all-zero, or a single 1 in degree `c−2`) | every `P ∈ PPF_3`, `PPF_4` (206 complexes) | 0 failures |
| **T3** full reduced Betti vector of the **link** `lk_{Δ_n}(P)` | every `P ∈ PPF_3` (12), `PPF_4` (194) | 108/108 height-≥2 links contractible; 0 failures. **This row is silent on the other 86 vertices at `n = 4` and on all 12 at `n = 3` — see the completed table below** |
| **T4** F17 Lemma L1 recovered as the chain case | `n = 3, 4` full Betti; `n = 5` Möbius | contractible, as F17 §3 Remark (c) also reports |
| **CONTROL** the *swapped* prediction (sphere ↔ contractible) must go RED | every `P ∈ PPF_4`, `PPF_5` | fails on 108/108 + 86/86 (`n=4`) and 3270/3270 + 840/840 (`n=5`) — **discriminating in both directions**, so T1's pass is not vacuous |

**Census of the two classes** (from the same run — the spherical class is the *minority* and shrinks):

| `n` | `\|PPF_n\|` | height ≥ 2 → contractible | height 1 → `S^{c-2}` |
|---|---|---|---|
| 3 | 12 | 0 | 12 (100%) |
| 4 | 194 | 108 | 86 (44%) |
| 5 | 4110 | 3270 | 840 (20%) |
| 6 | 129302 | 117660 | 11642 (9.0%) |

and at width ≤ 3 with `n ≥ 7` the height-1 column is **empty** (§3.3). **The height-1 column is not
empty in `Δ_n`, whose vertex set is all of `PPF_n`** — that is the distinction the scoping note in
§0 point 3 turns on.

**T3 completed (`mg-e08a`, independently measured — every vertex of `Δ_4`, not only the 108).** The
T3 row above reports the height-≥2 rows and stops; here are all seven:

| height | `c` | link contractible | link `β̃` | count |
|---|---|---|---|---|
| ≥ 2 | 3 | ✅ | all zero | 24 |
| ≥ 2 | 4 | ✅ | all zero | 48 |
| ≥ 2 | 5 | ✅ | all zero | 36 |
| 1 | 1 | ✅ | all zero | 12 |
| 1 | 2 | ✅ | all zero | 36 |
| **1** | **3** | **❌** | **`β̃₃ = 1`** | **32** |
| **1** | **4** | **❌** | **`β̃₃ = 3`** | **6** |

**38 of 194 vertices — 19.6% — have a link that is not contractible**, and all 38 are height-1. At
`n = 3` all 12 links are non-contractible (each `S⁰`) and the height-≥2 population is empty, so the
height-≥2 roll-up there is an `all()` over an empty set; `mg-e08a`'s roll-up refuses that as a pass
rather than counting it. This is a reporting omission of the T3 row, not an uncomputed case — the
same test computes it.

Betti numbers use the two-prime rank routine of `scripts/compat_geom_F17_equivariant_morse.py`
(imported, not re-implemented, so there is exactly one `reduced_betti` in the tree).

**What the verification does and does not establish.** T2/T3/T4 pin the homotopy type only through
rational Betti numbers, and only for `n ≤ 4` (`n = 5` chain: `355`-element poset, 6.5M simplices, over
the materialisation cap — Möbius only). Theorem A's proof, not the harness, is what covers all `n`.
Its two halves are three paragraphs each and `§2.3` gives both routes; an auditor should check (i)
the join-irreducibility of cover relations under `tc`, and (ii) that `κ`'s image is nonempty *and*
proper.

> **"Contractible" here means `Q`-acyclic (`mg-e08a` §1, carried by `mg-1b3b`).** Rational Betti
> numbers are the verification currency of this harness *and* of the audit's independent one, and
> they cannot distinguish `RP²` from a point: the minimal 6-vertex `RP²` measures all-zero over `Q`
> and is not contractible. So **every "contractible" verdict produced by a Betti computation in
> either harness is really "`Q`-acyclic"**. Genuine contractibility comes from Theorem A (A1)'s
> **proof** — a closure operator onto a cone, `n`-uniform and computation-free — not from any Betti
> number. The prose in this document says "contractible" because the theorem says so; the tables say
> "contractible" when they mean `Q`-acyclic, and where the two could differ it is the proof that
> carries the claim.

> **AUDITED 2026-08-14 (`mg-e08a`, commit `191af85`).** Theorem A and Corollary B **passed** an
> independent audit that imported nothing from this tree: both named proof steps were run as
> exhaustive machine predicates (297 416 and 285 156 instances, 0 failures), steps (iii)/(iv) too,
> and the conclusion was re-verified by **full reduced Betti over all 4110 elements of `PPF_5`** —
> closing the `n = 5` gap this paragraph admits. 25 predictions were pre-registered at `a752fd0`
> before any audit code existed; 24 confirmed, 1 partially, none refuted. The audit's findings that
> bear on this document are carried at §0 point 3, §3.3, §3.5 and §4 point 4 (by `mg-1b3b`). See
> `docs/OneThird-mge08a-TheoremA-IndependentAudit.md`.

### 2.5 The (S3) reading, for completeness

If "proper subposets of `P`" means *induced subposets `P|_S` on proper nonempty subsets `S ⊊ [n]`*,
the indexing poset is the proper part of the Boolean lattice `B_n`, whose order complex is
`sd(∂Δ^{n-1}) ≃ S^{n-2}` — a sphere of the same dimension as `Δ_n`, **for every `P`, independent of
`P` entirely**. It is a sphere for a reason that has nothing to do with `P`, and carries no
information about `P`. (If one instead takes the *image* poset of distinct induced subposets,
collapsing occurs and the type is no longer `P`-independent; nothing in the corpus uses that object
and this document does not compute it.)

### 2.6 Nothing else per-poset exists in the corpus

Searched `docs/` for `subposet`, `per-poset`, `fibrewise/fiberwise`, `link`, `crosscut`,
`contractib`, `homotopy type`, `wedge of spheres`, `order complex of`. Every per-poset hit is one of:

- **F17 §3 Lemma L1** and its two re-uses (Prop. 2.1, §4.2) — the one real answer (§2.2);
- **F14 §1.1** MoveA/MoveB/PEEL fibre hypotheses — *cone-or-empty* checks on down-sets `Q_{<x}`, i.e.
  conditions verified en route, not homotopy-type computations of a named poset's subposet complex;
- **F27 §4.1** — names `lk_{Δ(PPF_n)}(P)` as a per-`P` object and describes it **correctly** (*"the
  order complex of the open interval `(P, P_top) ∪ (P_bot, P)` […] partial orders `Q` with `Q ⊊ P` or
  `P ⊊ Q`"*), but **computes no homotopy type** — its finding is that the link and `G_BK(P)` are
  different combinatorial objects with no map between them (RED-mechanism-mismatch);
- **F28 §2.3** — the explicit statement that the link computation *"is not in hand for general `P`"*
  (quoted in §3.2), with the identification error §3.2 corrects;
- the unrelated *statistical* "per-poset" of the L1b / Reverse-Cheeger line (`per-poset lower bound on
  λ_std`), which is not topology.

There is no fibrewise sphere theorem, no wedge-of-spheres computation, and no partial one.

---

## 3. Sub-question 2 — does the category-level result restrict?

### 3.1 It restricts to zero, for every `P`, for a one-line reason — and F28 (F-5) is vacuous

F28 §1.6 lists as a *structural fact* of its framework:

> (F-5) **Sub-site framework.** Up-sets `↑P` parametrise BK-subposet families; restriction maps carry
> local-to-global content.

and §1.5 proposes `res : H^{n-2}(PPF_n, Q) → H^{n-2}(↑P, Q)`, `ω_bal^(n) ↦ ω_bal^(n)|_{↑P}`, whose
*"vanishing or non-vanishing is a local-to-global constraint"*.

**`ω_bal^(n)|_{↑P} = 0` for every `P ∈ PPF_n` and every `n ≥ 3`, unconditionally.** `↑P` has `P` as a
global *minimum*, so `Δ(↑P)` is a cone with apex `P`, so `H̃^k(↑P, Q) = 0` for all `k`. The
restriction is the zero map. There is no constraint, for any `P`, ever. F28 half-noticed this — §2.3
writes *"`Δ(↑P)` is the cone of this over `P`"* — but the observation is not carried back to (F-5),
which is stated as though the restriction could be non-zero.

**(F-5) is therefore struck as a load-bearing framework fact.** It is not *wrong* that `↑P`
parametrises BK-subposet families (that part stands); it is wrong that its restriction map carries
content.

### 3.2 F28 §2.3's link identification drops exactly the factor that matters

F28 §2.3 says:

> `↑P` is rationally the link of `P` in `Δ_n` (more precisely: `Δ(↑P ∖ {P}) = lk_{Δ_n}(P)`, since
> `↑P` includes `P` as its minimum but `Δ(↑P)` is the cone of this over `P`).

**The parenthetical is false.** For an order complex, the link of a vertex is the **join of both
halves**:

    lk_{Δ(Q)}(P) = Δ(Q_{<P}) * Δ(Q_{>P}),

so `lk_{Δ_n}(P) = Δ(L̄(P)) * Δ(↑P ∖ {P})`. F28 dropped `Δ(L̄(P))` — the lower factor, which is
precisely the object of Daniel's question and of Theorem A. Everything F28 §2.3 then says about "the
link" is really about the *upper* half only.

**And it is a regression, not a first draft.** F27 §4.1 — the immediately preceding ticket in the
same line — states the link *correctly*, with both halves: *"the order complex of the open interval
`(P, P_top) ∪ (P_bot, P)` […] vertices: partial orders `Q ∈ PPF_n` with `Q ⊊ P` **or** `P ⊊ Q`"*. F28
was written after F27 and lost the first disjunct.

The corrected version of F28 §2.3's honest observation still stands, and is worth repeating because
it is the closest the corpus came to answering PART B before this ticket:

> **This is not in hand for general `P`** — F17+F18 control `Δ_n` globally, not its links. […] the
> F17+F18 unconditional `Δ_n ≃_Q S^{n-2}` *rational sphere* statement does NOT immediately give
> `lk(P)` is a rational sphere […] So this is an open question.

F28 was right that it was open, and right that rational sphericity does not descend to links. §3.3
now closes it — in the negative.

### 3.3 Corollary B — the link is contractible for every `P` with a 3-chain

> **Corollary B (mg-52c4).** For every `n ≥ 3` and every `P ∈ PPF_n` of height ≥ 2,
> `lk_{Δ_n}(P) = Δ(L̄(P)) * Δ(↑P ∖ {P})` is **contractible**, so `H̃^*(lk_{Δ_n}(P); Q) = 0` and no
> restriction of `ω_bal^(n)` to the local structure at `P` is non-zero.

*Proof.* Theorem A (A1) makes the first join factor contractible; a join with a contractible factor
is contractible (`X * Y ≃ pt * Y = Cone(Y) ≃ pt`). ∎

Verified directly, without the join formula, for every `P ∈ PPF_4` of height ≥ 2 (T3: 108/108
contractible links, computed from the actual link poset `{Q ∈ PPF_4 : Q ⊊ P or Q ⊋ P}`).

**Why this settles the target regime, not just a corner of it.** By Mirsky's theorem a poset with no
3-chain is a union of 2 antichains, so a height-1 poset of width ≤ 3 has **at most 6 elements**.
Every width-≤3 poset on `n ≥ 7` elements therefore has a 3-chain and falls under (A1)/Corollary B.
The spherical case (A2) is empty in the regime the 1/3–2/3 program is about.

**So the fibrewise anchor is not "unproven", it is identically trivial.** This is a strictly stronger
and more useful finding than "nothing is known": a fibrewise route cannot be rescued by working
harder, because there is no non-zero class to work with.

> **SCOPED 2026-08-14 (`mg-e08a` §6–§7, carried by `mg-1b3b`) — the two sentences above merge a
> theorem with a measurement, and only one of them is a theorem.**
>
> - **Corollary B is proven and non-vacuous where its hypothesis has instances**: 108/108 height-≥2
>   links contractible at `n = 4`, verified directly from the link poset. No `n` bound, no width
>   bound. Nothing here is retracted.
> - **At `n = 3` Corollary B is VACUOUS.** `PPF_3` has no height-≥2 element at all (§2.4's own
>   census says `0`), so its population is empty; and all 12 links at `n = 3` are **non-contractible**
>   (each `S⁰`). An `all()` over an empty set is not a pass and is not reported as one.
> - **Mirsky does not remove the height-1 vertices from `Δ_n`.** It removes them from the
>   *width-≤3 family*. The vertices of `Δ_n` are all of `PPF_n`, and the height-1 fraction is
>   86/194 at `n = 4`, 840/4110 at `n = 5` and 11 642/129 302 at `n = 6`. At `n ≥ 7` they are all of
>   width ≥ 4, so Mirsky says nothing about them; they are still vertices and Corollary B still does
>   not cover them. **38 of the 194 links at `n = 4` are not contractible** (§2.4's completed T3
>   table).
> - **What holds at those vertices is weaker and is a measurement.** The quantity the "identically
>   trivial" headline needs is the anchor-degree component `H̃_{n−2}(lk_{Δ_n}(P))`, and it is zero at
>   every one of the 12 vertices at `n = 3`, all 194 at `n = 4` and every height-1 class within cap
>   at `n = 5` — *including* the 38 whose links are not contractible. That is a **degree
>   coincidence**: every case lands on zero by exactly one degree, `dim U` exceeds the needed degree
>   for all `n ≥ 4`, and no proof of it is known. **It is not established for `n ≥ 6`.**
>
>   > **AMENDED 2026-08-14 (`mg-72e4`).** Three of the sentences above are now wrong, and the
>   > conclusion is unchanged. (i) **"every case lands on zero by exactly one degree" is an `n = 4`
>   > artifact** — the margin is `1` at `n = 4`, `2` at `n = 5`, `3` at `n = 6`, so the "near miss"
>   > that motivated the follow-up ticket widens rather than persisting. (ii) **`n = 6` IS now
>   > established**, all 55 height-1 classes / 11 642 labelled vertices, 0 violations, via
>   > Björner's crosscut theorem, which replaces `Δ(↑P ∖ {P})` by a complex on at most
>   > `n(n−1) − 2c` vertices. (iii) **`n = 5` is 20/20 classes**, not 58/61. What survives: it is
>   > still not proven for all `n`, and *"`dim U` exceeds the needed degree"* is still true and is
>   > still the reason a dimension argument cannot work — the correct target is a *connectivity*
>   > statement. `mg-72e4` proves the `c ≥ n` slice outright. See
>   > [`OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md`](OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md).
>   >
>   > **EXTENDED to `n = 7` 2026-08-14 (`mg-9cd1` D4, carried by `mg-0f24`).** (i) and (ii) above
>   > now reach one further: the margin is **`≥ 4` at `n = 7`** — on 160 of the 163 iso classes,
>   > with three (`c ≤ 2`, 252 labelled vertices) bounded only at `≥ 1` — so the near-miss widens
>   > again rather than stalling at `n = 6`; and **`n = 7` is established complete**, 163 of 163
>   > classes / 227 892 of 227 892 labelled vertices, 0 violations. `n = 7` is the `n` at which
>   > `mg-24eb`'s *"exactly the ordinal sums"* coincidence broke, which is why this row and not
>   > another is the one worth carrying here. Still not proven for all `n`.
> - **One nearby map is genuinely non-zero.** Restrictions are not the only maps to the local
>   structure at `P`: the Mayer–Vietoris connecting map
>   `∂ : H̃_{n−2}(Δ_n) → H̃_{n−3}(lk_{Δ_n}(P))` is not a restriction and is not covered by the cone
>   argument. At `n = 3`, deleting **any one** of the 12 vertices makes `Δ_3 ∖ {P}` contractible — so
>   *"no restriction of `ω_bal^(n)` to the local structure at `P` is non-zero"* is true **for
>   restrictions** and false for the local structure in general.
>
> **Net effect on the recommendation: none.** The conclusion holds where it is proven and holds
> elsewhere at `n ≤ 5` because it was exhaustively counted; §5's *"do not open an F33"* stands
> (`mg-e08a` §0, §9). Scoping a claim is not retracting it.

### 3.4 F31 §3.6 (R-B) is the same wall from another side

F31 §3.6 rescue **(R-B)** (stabiliser-orbit refinement) records: *"F17+F18 constrains the
full-`S_n`-sgn-isotype of `H^{n-2}(Δ_n, Q)`, not the `Stab_{S_n}{x,y}`-sgn-isotype. […] **The F17+F18
anchor breaks.**"* That is the same phenomenon in the equivariant direction: any move that localises
— to a stabiliser, or to a single `P` — leaves the object F17+F18 computes. §3.1/§3.3 say what
happens on the other side of that move for the *geometric* localisation: the target group is not
merely uncomputed, it is zero.

### 3.5 The one fibrewise object still uncomputed

`Δ(↑P ∖ {P})` — the **upper** link, the proper part of the interval `[P, 1̂]` of proper extensions of
`P` — is *not* computed by Theorem A and is *not* trivially a cone. Two things to say about it:

1. It is the object F28 §2.3 was actually talking about (once its identification is corrected).
2. **It is not something `ω_bal^(n)` restricts to.** The natural maps out of `H^*(Δ_n)` land on `↑P`
   (zero, §3.1) or on the full link (zero for height ≥ 2, §3.3). Computing `Δ(↑P ∖ {P})` would be a
   new theorem about a new object, not a restriction of an existing one — so it inherits no anchor,
   which is precisely the F28 (N-2) gap in a new place.

> **STRENGTHENED and MEASURED 2026-08-14 (`mg-e08a` §7–§8, carried by `mg-1b3b`).** Two amendments,
> both of which make this section's conclusion rest on less.
>
> **(a) Point 2 needs no height hypothesis.** Since `Δ(↑P ∖ {P}) ⊆ Δ(↑P) ⊆ Δ_n` and `Δ(↑P)` is a
> cone (§3.1), the restriction of `ω_bal^(n)` to the **upper link** factors through a cone and is
> therefore zero for **every** `P`, at every height, for every `n`. This section inherits a height-≥2
> hypothesis from §3.3 that this half does not need — so §3.5's conclusion survives the scoping note
> at §3.3 untouched, and for a better reason than the one given above.
>
> **(b) It is no longer uncomputed at `n ≤ 5`, and it is not always contractible.** `Δ(↑P ∖ {P})` was
> computed for 14/14 isomorphism classes at `n = 4` and 58/61 at `n = 5` (three over cap, named in
> the audit's JSON). At `n = 4` it has `β̃₁ = 1` at the `c = 3` height-1 classes, `β̃₀ ∈ {1, 3}` at
> `c = 4`, and is **empty** at the maximal vertices; at `n = 5` it ranges over `β̃₂ = 1`,
> `β̃₁ ∈ {1, 2}`, `β̃₀ ∈ {1, 3}`, and empty. §3.5's instinct — *not trivially a cone* — is right.
> The finding does not change the conclusion: by (a) the object still carries no anchor, so computing
> it produced exactly the fact-with-no-consumer this section predicts.

---

## 4. Sub-question 3 — what would a per-poset sphere theorem buy?

**Nothing that is currently blocked, and it would make the anchor weaker rather than stronger.**
Stated as the ticket asks — *before* anyone proves one.

The intended use of any sphere theorem in this line (F28 §6, F29, F30, F31) is the implication chain

    bad cut in P  ⟶  a non-trivial local class  ⟶  contradiction with the sphere anchor.

The chain has two live walls, and a fibrewise sphere theorem is on neither of them.

1. **F28 (AMBER, `mg-d0fa`) — the sheaf wall.** No BK-derived sheaf is both functorial under
   refinement and admits a morphism to `Q̲` that F17+F18 can constrain (§3.2–§3.4, §5.1). This is a
   statement about *coefficients*, not about which complex is spherical. Replacing `Δ_n` by a
   per-poset complex changes the base, not the coefficient problem — the same four candidate sheaves
   fail on `L̄(P)` for the same reasons.
2. **F31 (RED, `mg-01ce`) — the kernel wall.** `K_chain-loc ⊆ ker(Φ_*)`, and the bad-cut class's
   *defining* feature (construction from sgn-orbit-summed relabel-invariant bias values) is exactly
   what places it in the kernel; F30's `c_BC(P) = 0` is generic, not a contradiction. A different
   anchor on a different complex does not move a class out of the kernel of the comparison map.

And three positive reasons it would be worse than the ambient statement:

3. **The class is zero, not merely unknown** (§3.1, §3.3). A fibrewise route trades a rank-1
   sgn-isotype anchor (`H^{n-2}(Δ_n) = sgn`) for a rank-0 one.
4. **Where a sphere does appear it is blind — in `Δ(L̄(P))`, the lower join factor.** In the
   height-1 case (A2) the homotopy type **of `Δ(L̄(P))`** is `S^{c-2}` with `c = |Comp(P)|` — a
   function of the *number of relations only*. Two height-1 posets with the same number of comparable
   pairs, one with a bad cut and one without, have identical **subposet complexes**. That invariant
   cannot see the property the program needs it to see.

   > **CORRECTED 2026-08-14 (`mg-e08a` §6.4, carried by `mg-1b3b`) — the blindness is a property of
   > the lower factor and does NOT transfer to the link.** The object F28 §2.3 and F29-B ask about is
   > `lk_{Δ_n}(P) = Δ(L̄(P)) * Δ(↑P ∖ {P})`, whose type at a height-1 vertex is
   > `Σ^{c−1} Δ(↑P ∖ {P})` — **not** a function of `c` alone. Measured at `n = 4`: height-1 vertices
   > with `c = 3` give `β̃₃ = 1` and with `c = 4` give `β̃₃ = 3`, while `c = 1, 2` give contractible
   > links. So `lk_{Δ_n}(P)` is *not* blind in the way `Δ(L̄(P))` is, and the argument above must be
   > read as being about the lower factor only. **Point 4 is still a correct reason not to want a
   > fibrewise sphere theorem** — the invariant it names really is blind — but it is a statement about
   > `Δ(L̄(P))`, and quoting it about "the link" is the conflation this note removes.
5. **The height-1 case is empty in-regime anyway** (§3.3, Mirsky): width ≤ 3 and `n ≥ 7` forces a
   3-chain.

**One thing Corollary B does *not* buy, stated so nobody claims it later.** F27 §4.1 runs Garland's
method in reverse: `H̃^{n-2}(Δ_n) ≠ 0` (F17+F18) forces *some* vertex link of `Δ_n` to have spectral
gap below the Garland threshold. It is tempting to combine this with Corollary B and conclude that
the forced local spectral defect must sit on the height-1 vertices. **That inference is invalid.**
Garland's hypothesis is a *spectral gap* condition on the link's 1-skeleton, and contractibility does
not imply a spectral gap (a long path is contractible and has a tiny gap). Corollary B therefore
localises nothing on the Garland side. F27's own verdict on that route (RED-mechanism-mismatch: no
map between `lk_{Δ(PPF_n)}(P)` and `G_BK(P)`) is untouched.

**Therefore:** the honest answer to sub-question 3 is the one the ticket named as legitimate —
*"nothing the F-series wall does not already block"* — with the sharpening that the fibrewise object
is not merely blocked but trivial.

---

## 5. Recommendation

- **Do not open an F33.** There is no fibrewise sphere theorem to prove: Theorem A settles (S1), and
  what it settles is contractibility. The only uncomputed fibrewise object is the upper link `↑P ∖
  {P}` (§3.5), and it carries no anchor, so computing it would produce a fact with no consumer.
  > **The recommendation survives the `mg-e08a` audit unchanged (2026-08-14).** The scoping notes at
  > §0 point 3, §2.4, §3.3, §3.5 and §4 point 4 narrow *what is proven where*; none of them supplies
  > a non-zero fibrewise class, and the audit's own verdict is that the recommendation stands
  > (`mg-e08a` §0, §9). **Do not read the scoping as licence to reopen the arc.**

- **If anything is worth a separate ticket**, it is a **one-session independent audit of Theorem A
  and Corollary B** (§2.4 names the two steps to check), because they are the load-bearing new claims
  here and they are being used to *close* a direction rather than open one. That is cheap and is the
  right shape of follow-up. — **DONE: `mg-e08a`, commit `191af85`. Verdict: both CORRECT** (§2.4).
  The audit leaves **exactly one** follow-up worth a ticket: whether `H̃_{n−2}(lk_{Δ_n}(P)) = 0` at
  height-1 vertices is a **theorem** or a small-`n` coincidence. It is the load-bearing fact under
  "identically trivial" at the vertices Corollary B does not reach, it holds at `n = 3, 4, 5` by
  measurement only, every case is a one-degree near-miss, and no dimension argument forces it. This
  corpus has been bitten by exactly this shape twice — `mg-24eb` re-scoped *"exactly the ordinal
  sums"* as a coincidence false from `n = 7`, and `mg-d1be` closed the width-2 caveat only at
  `n = 8`.
  > **ANSWERED: `mg-72e4`.** *"Not a coincidence, and not yet a theorem."* The
  > *"every case is a one-degree near-miss"* premise is **refuted** — it is true at `n = 4` and
  > false at `n = 5` and `n = 6`, where the margin is 2 and 3. `n = 6` is measured complete
  > (55 classes, 11 642 vertices, 0 violations) and `n = 5` is 20/20 rather than 58/61, both via
  > the crosscut reduction. The `c ≥ n` slice is proven for all `n ≥ 6`. What is left is a
  > *connectivity* conjecture about a complex on `≤ n(n−1) − 2c` vertices, plus the `c ≤ 2` cases.
  > **Nothing reopens.** See
  > [`OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md`](OneThird-mg72e4-Height1-Anchor-TheoremOrCoincidence.md).
  >
  > **EXTENDED to `n = 7` 2026-08-14 (`mg-9cd1` D4, carried by `mg-0f24`).** The premise is false
  > at `n = 7` as well, where the margin is **`≥ 4`** (on 160 of the 163 iso classes; three at
  > `c ≤ 2`, 252 labelled vertices, are bounded only at `≥ 1`). `n = 7` is measured **complete** —
  > 163 of 163 classes, 227 892 of 227 892 labelled vertices, 0 violations — via the same crosscut
  > reduction. Nothing reopens here either.
- **The F28 corrections in §3.1–§3.2 are landed at their destination** in this same commit (a dated
  note at F28 §1.6 (F-5) and §2.3), so a future reader of F28 cannot re-inherit the vacuous (F-5) or
  the wrong link identity. F17 §3 gets a forward pointer recording that L1 is the special case of
  Theorem A. Nothing else in F17/F18/F28/F29/F30/F31 is touched.

## 6. Scope — what this document does not do

- It does **not** re-derive the F-series (ticket mandate) and **retracts nothing** from F17/F18: they
  are GREEN, unconditional, and untouched. F31 stays RED, F28 stays AMBER; §3.1–§3.2 strike two
  *framework* statements inside F28, not its verdict.
- It does **not** compute `Δ(↑P ∖ {P})` (§3.5 — `mg-e08a` since has, for `n ≤ 5`; see the note
  there), the (S3) image poset (§2.5), or any twisted-coefficient
  or equivariant refinement of Theorem A (`Aut(P)` acts on `L̄(P)`; the equivariant homotopy type is
  not computed here and is not needed for §3–§4, since contractible is contractible equivariantly for
  the cone in (A1) but that is not verified).
- Theorem A / Corollary B are **new in this document**. ~~and not independently audited~~ —
  **superseded 2026-08-14:** both were independently audited by `mg-e08a` (commit `191af85`) and
  both **passed**; the audit's scoping findings are carried into this document by `mg-1b3b` at
  §0 point 3, §2.4, §3.3, §3.5, §4 point 4 and §5. What remains not established is the *unproven*
  half named in §5: `H̃_{n−2}(lk_{Δ_n}(P)) = 0` at height-1 vertices for `n ≥ 6`.
- Every "contractible" verdict this document's **tables** report is `Q`-acyclicity (§2.4); genuine
  contractibility comes from Theorem A's proof.

## 7. References

**F-series (in `docs/`, last F-series commit `a464f1f`, 2026-05-16):**
`compatibility-geometry-F17-equivariant-cofiber-morse.md` (§3 Lemma L1; Prop. 2.1; §4.2),
`...-F18-ucc2-delta-injective.md` (§0.3), `...-F13-shift-aware-functoriality.md` (§1, `PPF_n`
notation and Lemma 1.4), `...-F28-sheaf-cohomology-on-POSET.md` (§1.5, §1.6 (F-5), §2.3, §3, §5.1,
§7.6), `...-F27-spectral-to-cohomology-scoping.md` (§4.1 — the link stated correctly, and the Garland
reverse-direction argument), `...-F29-cech-bias-cohomology.md`, `...-F30-chain-level-phi.md`,
`...-F31-phi-star-injectivity.md` (§3.2, §3.6 (R-B), §3.7).

**Audit:** `docs/OneThird-mge08a-TheoremA-IndependentAudit.md` (`mg-e08a`, commit `191af85`), its
pre-registered predictions `docs/OneThird-mge08a-TheoremA-AUDIT-PREDICTIONS.md` (`a752fd0`),
instrument `scripts/compat_geom_mge08a_theoremA_audit.py`, output
`data/onethird-mge08a-theoremA-audit.json`.

**Work items:** `mg-e768` (PART A/B, archived), `mg-65f5` (R1/R2/R3 — did not carry PART B),
`mg-4d3a` (F17), `mg-d039` (F18), `mg-d0fa` (F28), `mg-01ce` (F31), `mg-52c4` (this),
`mg-e08a` (the audit), `mg-1b3b` (carried the audit's three scoping repairs into this document,
F28 §2.3 and §4 point 4).

**Literature:** A. Björner, *Topological methods*, in Handbook of Combinatorics (1995) — §10.2
closure/order-homotopy lemma (used by F17 §3 and by §2.3 (A1)); Thm 10.8 crosscut theorem (§2.3
alternative route). L. Mirsky, *A dual of Dilworth's decomposition theorem*, Amer. Math. Monthly 78
(1971) (§3.3).
