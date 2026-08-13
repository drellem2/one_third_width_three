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
4. **Two F28 statements are wrong and are struck at their destination** (§3.1–§3.2): (F-5)
   *"restriction maps carry local-to-global content"* is **vacuous**, and §2.3's identification
   `Δ(↑P ∖ {P}) = lk_{Δ_n}(P)` **drops the lower factor** — the very factor Theorem A computes.
5. **Sub-question 3 (what would a fibrewise sphere theorem buy?): nothing** (§4). It would replace a
   rank-1 sgn-isotype anchor by a rank-0 one; and in the one case where a sphere *does* appear
   (height 1) its dimension depends only on `|Comp(P)|`, so it cannot separate a bad-cut poset from a
   good one — and no height-1 poset of width ≤ 3 has more than 6 elements. **Recommendation: do not
   open an F33.** §5.

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
| **T3** full reduced Betti vector of the **link** `lk_{Δ_n}(P)` | every `P ∈ PPF_3` (12), `PPF_4` (194) | 108/108 height-≥2 links contractible; 0 failures |
| **T4** F17 Lemma L1 recovered as the chain case | `n = 3, 4` full Betti; `n = 5` Möbius | contractible, as F17 §3 Remark (c) also reports |
| **CONTROL** the *swapped* prediction (sphere ↔ contractible) must go RED | every `P ∈ PPF_4`, `PPF_5` | fails on 108/108 + 86/86 (`n=4`) and 3270/3270 + 840/840 (`n=5`) — **discriminating in both directions**, so T1's pass is not vacuous |

**Census of the two classes** (from the same run — the spherical class is the *minority* and shrinks):

| `n` | `\|PPF_n\|` | height ≥ 2 → contractible | height 1 → `S^{c-2}` |
|---|---|---|---|
| 3 | 12 | 0 | 12 (100%) |
| 4 | 194 | 108 | 86 (44%) |
| 5 | 4110 | 3270 | 840 (20%) |
| 6 | 129302 | 117660 | 11642 (9.0%) |

and at width ≤ 3 with `n ≥ 7` the height-1 column is **empty** (§3.3).

Betti numbers use the two-prime rank routine of `scripts/compat_geom_F17_equivariant_morse.py`
(imported, not re-implemented, so there is exactly one `reduced_betti` in the tree).

**What the verification does and does not establish.** T2/T3/T4 pin the homotopy type only through
rational Betti numbers, and only for `n ≤ 4` (`n = 5` chain: `355`-element poset, 6.5M simplices, over
the materialisation cap — Möbius only). Theorem A's proof, not the harness, is what covers all `n`.
**Theorem A has not been independently audited.** Its two halves are three paragraphs each and
`§2.3` gives both routes; an auditor should check (i) the join-irreducibility of cover relations under
`tc`, and (ii) that `κ`'s image is nonempty *and* proper.

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
4. **Where a sphere does appear it is blind.** In the height-1 case (A2) the homotopy type is
   `S^{c-2}` with `c = |Comp(P)|` — a function of the *number of relations only*. Two height-1 posets
   with the same number of comparable pairs, one with a bad cut and one without, have identical
   subposet complexes. The invariant cannot see the property the program needs it to see.
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
- **If anything is worth a separate ticket**, it is a **one-session independent audit of Theorem A
  and Corollary B** (§2.4 names the two steps to check), because they are the load-bearing new claims
  here and they are being used to *close* a direction rather than open one. That is cheap and is the
  right shape of follow-up.
- **The F28 corrections in §3.1–§3.2 are landed at their destination** in this same commit (a dated
  note at F28 §1.6 (F-5) and §2.3), so a future reader of F28 cannot re-inherit the vacuous (F-5) or
  the wrong link identity. F17 §3 gets a forward pointer recording that L1 is the special case of
  Theorem A. Nothing else in F17/F18/F28/F29/F30/F31 is touched.

## 6. Scope — what this document does not do

- It does **not** re-derive the F-series (ticket mandate) and **retracts nothing** from F17/F18: they
  are GREEN, unconditional, and untouched. F31 stays RED, F28 stays AMBER; §3.1–§3.2 strike two
  *framework* statements inside F28, not its verdict.
- It does **not** compute `Δ(↑P ∖ {P})` (§3.5), the (S3) image poset (§2.5), or any twisted-coefficient
  or equivariant refinement of Theorem A (`Aut(P)` acts on `L̄(P)`; the equivariant homotopy type is
  not computed here and is not needed for §3–§4, since contractible is contractible equivariantly for
  the cone in (A1) but that is not verified).
- Theorem A / Corollary B are **new in this document and not independently audited** (§2.4).

## 7. References

**F-series (in `docs/`, last F-series commit `a464f1f`, 2026-05-16):**
`compatibility-geometry-F17-equivariant-cofiber-morse.md` (§3 Lemma L1; Prop. 2.1; §4.2),
`...-F18-ucc2-delta-injective.md` (§0.3), `...-F13-shift-aware-functoriality.md` (§1, `PPF_n`
notation and Lemma 1.4), `...-F28-sheaf-cohomology-on-POSET.md` (§1.5, §1.6 (F-5), §2.3, §3, §5.1,
§7.6), `...-F27-spectral-to-cohomology-scoping.md` (§4.1 — the link stated correctly, and the Garland
reverse-direction argument), `...-F29-cech-bias-cohomology.md`, `...-F30-chain-level-phi.md`,
`...-F31-phi-star-injectivity.md` (§3.2, §3.6 (R-B), §3.7).

**Work items:** `mg-e768` (PART A/B, archived), `mg-65f5` (R1/R2/R3 — did not carry PART B),
`mg-4d3a` (F17), `mg-d039` (F18), `mg-d0fa` (F28), `mg-01ce` (F31), `mg-52c4` (this).

**Literature:** A. Björner, *Topological methods*, in Handbook of Combinatorics (1995) — §10.2
closure/order-homotopy lemma (used by F17 §3 and by §2.3 (A1)); Thm 10.8 crosscut theorem (§2.3
alternative route). L. Mirsky, *A dual of Dilworth's decomposition theorem*, Amer. Math. Monthly 78
(1971) (§3.3).
