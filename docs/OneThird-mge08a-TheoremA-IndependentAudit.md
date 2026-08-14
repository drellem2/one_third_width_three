# INDEPENDENT AUDIT of mg-52c4's Theorem A and Corollary B (mg-e08a)

*Audits `docs/OneThird-mg52c4-PerPoset-Subposet-Question.md` at commit `cf63bb3`, together with
the two edits that commit landed at F17 §3 and F28 §1.6/§2.3.*

**Predictions pre-registered before any audit code existed:**
[`docs/OneThird-mge08a-TheoremA-AUDIT-PREDICTIONS.md`](OneThird-mge08a-TheoremA-AUDIT-PREDICTIONS.md)
(commit `a752fd0`). Instrument: [`scripts/compat_geom_mge08a_theoremA_audit.py`](../scripts/compat_geom_mge08a_theoremA_audit.py),
output [`data/onethird-mge08a-theoremA-audit.json`](../data/onethird-mge08a-theoremA-audit.json).
Run: `/usr/bin/python3 scripts/compat_geom_mge08a_theoremA_audit.py` (~6.5 min, stdlib only,
`ALL_PASS = True`).

**Independence.** The audited harness imports `reduced_betti` from
`scripts/compat_geom_F17_equivariant_morse.py`. This instrument imports **nothing** from the repo:
poset enumeration, transitive closure, the order complex, and the boundary-rank / reduced-Betti
routine (two primes, persistence-style reduction) are re-implemented from scratch. The audited
script was deliberately not opened until after this instrument produced its numbers. **This is not
a re-run of the audited harness** — every figure below is re-derived.

---

## 0. Verdict

> ### Theorem A is CORRECT. Corollary B is CORRECT. The recommendation *"do not open an F33"* STANDS.
>
> ### But the headline sentence — *"the fibrewise `F17+F18` anchor is identically zero"* — is proven for **less than the document implies**, and the part it does not prove is true only by measurement, not by argument.

Four results, in descending order of how much they should change what anyone does:

1. **Theorem A survives audit intact.** Both proof steps §2.4 names, plus two it does not name,
   were checked as exhaustive machine predicates (§2), and the theorem's conclusion was
   re-verified by **full reduced Betti** over every isomorphism class of poset on `n ≤ 5`
   elements — which covers **all 4110 elements of `PPF_5`**, closing the verification gap §2.4
   admits (§3). I found no error. *(Predictions A1–A6, B1–B4, C1–C4: all confirmed.)*
2. **The admitted Euler-blindness is real, and now demonstrated rather than asserted** — §4
   exhibits an explicit poset the Möbius/Euler check calls contractible and Betti does not.
   **But it is not load-bearing**, because Theorem A's proof is `n`-independent and this audit
   supplies full Betti at `n = 5` anyway. *(D1, D2 confirmed.)*
3. **Corollary B does not cover every vertex of `Δ_n`, and the gap is large.** At `n = 4`,
   **38 of 194 vertices have a NON-contractible link** (§6). At `n = 3` the Corollary is
   **vacuous** — there are no height-≥2 vertices at all, and all 12 links are non-contractible.
   Mirsky removes the height-1 posets only from the *width-≤3 family*; it does not remove them
   from the *vertex set of `Δ_n`*, which is all of `PPF_n`. *(E3 confirmed; E4 confirmed.)*
4. **The conclusion nonetheless survives at every vertex I can reach — for a reason the document
   never gives.** The anchor-degree component `H̃_{n−2}(lk_{Δ_n}(P))` is **zero at every one of
   the 12 vertices at `n = 3`, every one of the 194 at `n = 4`, and every height-1 class at
   `n = 5`** (§7) — including the 38 whose links are not contractible. That is a *degree*
   coincidence, not contractibility, and I find no proof that it persists. **The negative
   conclusion is right; the stated reason covers 108/194 of it at `n = 4` and 0/12 at `n = 3`.**

Nothing here asks for a retraction. It asks for **one scoping sentence** in two places (§9).

---

## 1. Controls first — this audit can fail, and did

The ticket requires establishing the method can fail *before* reporting a verdict. Three separate
controls, and one of them caught me.

**H1 — the instrument against independently known answers.** `∂Δ^k ≃ S^{k−1}` for `k = 1..5`; the
Möbius–Kantor 7-vertex torus `(β̃₁, β̃₂) = (2, 1)`; the empty complex `= S^{−1}`; two disjoint
circles `(β̃₀, β̃₁) = (1, 2)`. **All reproduce.**

> **H1 caught a real defect in this audit's first draft.** My initial hand-written "torus" and
> "Klein bottle" facet lists were both wrong — the first was not a surface at all (it measured
> `(0,0,1)`), and the second was in fact a torus (it measured `(0,2,1)`, the answer I had labelled
> for the first). The control went RED and the run reported `ALL_PASS = False` before any verdict
> was written. Both were replaced with the standard `Z_7` construction, which verifies. **A control
> that has never failed is not evidence; this one has.**

**H2 — swapped predictions.** Asserting (A1)'s answer for height-1 posets and (A2)'s for height-≥2
posets must go RED everywhere the two differ. Result over `PPF_4`: **108/108 and 86/86 fail —
100% in both directions.** (This matches the audited run's own control, independently.)

**H3 — perturbation, the control this ticket specifically demands.** H2 can be passed by an
instrument that merely computes the right thing on the cases it was handed. H3 additionally
requires the answer to *move*:

| perturbation | `P` | height ≥ 2 | measured `β̃` | predicted | matches |
|---|---|---|---|---|---|
| before add | `{(0,1),(2,3)}`, `c=2` | no | `β̃₀ = 1` (`S⁰`) | `S^{c−2}` | ✅ |
| **after add** `(1,2)` | `0<1<2<3`, `c=6` | **yes** | all zero | contractible | ✅ |
| before delete | `0<1<2`, `c=3` | yes | all zero | contractible | ✅ |
| **after delete** | `{(0,1),(3,4),(5,6)}`, `c=3` | **no** | `β̃₁ = 1` (`S¹`) | `S^{c−2}` | ✅ |

**Both flips detected; the measured answer moved in both directions.** The instrument tracks a
moving target, not a fixed one.

**A limitation of this audit that is also a limitation of the audited one.** Rational Betti numbers
are the verification currency of both instruments, and they cannot distinguish `RP²` from a point:
the minimal 6-vertex `RP²` measures **all-zero over `Q`** and is not contractible. So every
"contractible" verdict in both harnesses is really **"`Q`-acyclic"**. Theorem A (A1) claims genuine
contractibility, and it is the **proof** — a closure operator onto a cone — that supplies that, not
any Betti computation. This is recorded in the JSON as an explicit `LIMITATION`, not hidden.

---

## 2. The two named proof steps (§2.4) — checked as predicates, not as conclusions

§2.4 says: *"an auditor should check (i) the join-irreducibility of cover relations under `tc`, and
(ii) that `κ`'s image is nonempty and proper."* Checking the theorem's *conclusion* would not check
these; each was turned into a machine predicate and run exhaustively over **every** poset on `≤ 5`
elements.

| step | statement | tests | failures |
|---|---|---|---|
| **(i)** | for every `S ⊆ P`, every cover of `P` lying in `tc(S)` already lies in `S` | **297,416** `(P, S)` pairs | **0** |
| **(ii)** | `κ(Q) = tc(Q ∪ {v})` is nonempty, proper, and lands in `L̄(P)` | **285,156** | **0** |
| **(iii)** | `κ` is extensive, monotone, idempotent | **285,156** | **0** |
| **(iv)** | `κ`'s image = `{Q : v ∈ Q}`, with global minimum `{v}` | **3,528** posets | **0** |

**Reading the proof rather than the summary, both steps are correct.** Two remarks an auditor
should record:

- **Step (i) has an unstated side condition, and it is satisfied.** The argument — *"any strictly
  shorter derivation would produce an element strictly between `x` and `y`"* — needs `S ⊆ P`, so
  that the intermediate elements of a `tc`-derivation are genuinely between `x` and `y` **in `P`**.
  Without it the claim is false (a derivation through elements outside `P` would not contradict
  covering in `P`). At the only use site `S = Q ∪ {v} ⊆ P`, so the condition holds. **Not a defect
  — but it is the step's actual hinge, and the document does not say so.** The predicate above
  tests exactly the `S ⊆ P` form.
- **Step (ii)'s properness argument is the delicate half and it is right.** `tc(Q ∪ {v}) = P` would
  force `Cov(P) ⊆ Q ∪ {v}` by (i), hence `Cov(P) ⊆ Q` since `v ∉ Cov(P)`, hence `Q ⊇ tc(Cov(P)) = P`
  — contradiction. Every link in that chain checks.

**Steps (iii) and (iv) are not named by §2.4 but are equally load-bearing**, since Björner's
order-homotopy lemma needs a genuine closure operator and the cone needs a genuine global minimum.
Both verify.

**The crosscut cross-check (§2.3's alternative route) is genuinely independent and also correct.**
`Γ = {A ⊆ Comp(P) : tc(A) ≠ P} = {A : Cov(P) ⊄ A}` — the second equality is step (i) again — is a
cone with apex `v` when `v` exists, and `∂Δ^{c−1}` when it does not. Same dichotomy, no closure
operator. Two routes agreeing is worth more than one route checked twice.

### 2.1 The height-1 half, and the boundary between the cases

(A2)'s argument — no 3-chain ⟹ no composable pair in `Comp(P)` ⟹ every subset of `Comp(P)` is
transitively closed ⟹ `L(P) = 2^{Comp(P)}` — is correct, and the order complex of the proper part
of a Boolean lattice on `c` atoms is `sd(∂Δ^{c−1}) ≃ S^{c−2}`.

**The dichotomy is exhaustive and the degenerate cases land on the right side** *(predictions
B1–B4, all confirmed)*:

- **Exhaustive.** Given the hypothesis "at least one strict relation", `height(P) ≥ 1` always, so
  (A1) ∪ (A2) is everything. There is no third case.
- **`c = 1`** → `L̄(P) = ∅ = S^{−1}`, measured `β̃₋₁ = 1`. This is *not* a vacuous corner: the
  single-relation posets are genuine minimal vertices of `PPF_n` (12 of them at `n = 4`).
- **`c = 2`** → `S⁰`, measured. **`c ≤ 2` is fine.**
- **Antichains and isolated elements are not a gap.** `L̄(P)` depends on `P` only through
  `Comp(P)`, so isolated elements are invisible to the theorem; the pure antichain has
  `Comp(P) = ∅`, is excluded by hypothesis, and is not an element of `PPF_n` anyway.
- **The three stated equivalences** (3-chain ⟺ `Cov(P) ≠ Comp(P)` ⟺ `height(P) ≥ 2`) hold under
  the edge-count height convention, which the document uses consistently.

---

## 3. Closing the verification gap the document admits

§2.4 records: *"T2/T3/T4 pin the homotopy type only through rational Betti numbers, and only for
`n ≤ 4` … Theorem A's proof, not the harness, is what covers all `n`."* This audit pushes the
Betti verification to `n = 5`.

| `n` | iso classes with a relation | **full Betti verified** | over cap | largest complex verified |
|---|---|---|---|---|
| 2 | 1 | 1 | 0 | — |
| 3 | 4 | 4 | 0 | 9 simplices |
| 4 | 15 | 15 | 0 | 1,511 simplices |
| **5** | 62 | **61** | **1** | **1,104,707 simplices** |

The single over-cap class at `n = 5` is the **5-chain** (`c = 10`, `|L̄| = 355`, 6,566,003
simplices) — the object F17 §3 Remark (c) also skips. **It is a total order, so it is not an element
of `PPF_5` at all.** Every one of the 61 remaining classes is verified, and since
`Δ(L̄(P)) ≅ Δ(L̄(σP))` for any relabelling `σ`, **that covers all 4110 elements of `PPF_5` by full
reduced Betti, not by Möbius.** The `n = 5` gap is closed.

**And (A2) is verified well past anything `PPF_4` can reach.** Theorem A is a statement about an
*arbitrary* finite poset, so `c` — not `n` — is the real parameter. Disjoint unions of `c` 2-chains
(height 1, `c` comparable pairs):

| `c` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| `\|L̄(P)\|` | 0 | 2 | 6 | 14 | 30 | 62 | 126 | 254 |
| simplices | 0 | 2 | 12 | 74 | 540 | 4,682 | 47,292 | 545,834 |
| measured | `S^{−1}` | `S⁰` | `S¹` | `S²` | `S³` | `S⁴` | `S⁵` | `S⁶` |
| predicted `S^{c−2}` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |

The largest `c` inside `PPF_4` is 5. **(A2) is confirmed to `c = 8`.**

---

## 4. The Euler blindness, demonstrated

§2.4's gap is exactly the shape in which a wrong contractibility claim would hide, so it deserves a
witness rather than an assertion. Here is one.

Take the wedge `S¹ ∨ S²`, form its face poset, and take that poset's order complex — a genuine
**order complex of a poset**, which is the class of object T1/T2 range over. It has 19 poset
elements and:

| | value |
|---|---|
| reduced Betti | `β̃₁ = 1, β̃₂ = 1` |
| **reduced Euler characteristic** | **0** |
| Möbius/Euler predicate says | **contractible** ❌ |
| full Betti predicate says | **not contractible** ✅ |

**So the blindness is real and exhibited, not merely conceded.** A Möbius check over a population
containing this poset would report zero failures while the poset is a wedge of two spheres.

**But it is not where the risk was.** Theorem A's proof never mentions `n`: it is a statement about
an arbitrary finite poset, proved by a closure operator. The corpus is therefore **not** relying on
the check that cannot see — and after §3 it does not need to at `n = 5` either. *(D1 and D2 both
confirmed, and they are not in tension: D1 says the instrument is blind, D2 says the instrument is
not what carries the claim.)*

---

## 5. The link identity, verified independently

mg-52c4 corrected F28 §2.3, which had identified `lk_{Δ_n}(P)` with the *upper* half alone. The
correction is `lk_{Δ_n}(P) = Δ(L̄(P)) * Δ(↑P ∖ {P})`. **Confirmed at all 194 vertices of `Δ_4`,
in two independent ways:**

- the link poset `{Q : Q ⊊ P or Q ⊋ P}` **is** the ordinal sum of the two halves (every element of
  the lower half is below every element of the upper half) — so its order complex is the join;
- the join Betti formula `H̃_k(X * Y) = ⊕_{i+j=k−1} H̃_i(X) ⊗ H̃_j(Y)` **reproduces the measured
  homology of every one of the 194 links** from the two halves computed separately.

**mg-52c4's correction to F28 is right, and the regression it identifies (F27 §4.1 states it
correctly, F28 lost the first disjunct) is real.**

---

## 6. Where the document over-reaches: the height-1 vertices

Corollary B is stated correctly — *"for every `P ∈ PPF_n` of height ≥ 2"*. The over-reach is in
what the document then does with it.

### 6.1 `n = 4` — 38 of 194 vertices have a non-contractible link

Every vertex of `Δ_4`, reported by `(height, c)`. **The audited run's T3 table reports only the
first three of these seven rows** (*"108/108 height-≥2 links contractible"*) and is silent on the
other 86 vertices:

| height | `c` | link contractible | link `β̃` | count |
|---|---|---|---|---|
| ≥ 2 | 3 | ✅ | all zero | 24 |
| ≥ 2 | 4 | ✅ | all zero | 48 |
| ≥ 2 | 5 | ✅ | all zero | 36 |
| 1 | 1 | ✅ | all zero | 12 |
| 1 | 2 | ✅ | all zero | 36 |
| **1** | **3** | **❌** | **`β̃₃ = 1`** | **32** |
| **1** | **4** | **❌** | **`β̃₃ = 3`** | **6** |

**Corollary B is confirmed, non-vacuously, on all 108 height-≥2 vertices.** *(Prediction E1
confirmed: it is a theorem, with no `n` bound and no width bound, for the class it names.)*

**And 38 of 194 vertices — 19.6% — have a link that is not contractible.** Thirty-two of them are
rational `S³`; six are rational wedges of **three** `S³`s. *(Prediction E3 confirmed. E4 confirmed:
these were computable by the same test — this is a reporting omission, not an uncomputed case.)*

### 6.2 `n = 3` — Corollary B is vacuous, and every link is non-contractible

`PPF_3` has **no height-≥2 elements at all** (the document's own census table says `0`). So at
`n = 3`:

- Corollary B's height-≥2 population is **empty**, and `all(...)` over it is vacuously true —
  this audit's roll-up explicitly refuses that as a pass;
- **all 12 links are non-contractible** (each is `S⁰`).

### 6.3 Why Mirsky does not close this

§3.3's Mirsky step is **correct**: a height-1 poset of width ≤ 3 is a union of 2 antichains of size
≤ 3, so it has at most 6 elements, so every width-≤3 poset on `n ≥ 7` elements has a 3-chain.
Verified exhaustively — the height-1-and-width-≤3 population is 2, 12, 86, 710, 4940 at
`n = 2..6`, and the bound is **tight at 6** (witnesses exist).

**But that removes the height-1 posets from the width-≤3 family, not from the vertex set of `Δ_n`.**
The vertices of `Δ_n` are all of `PPF_n`, and height-1 vertices are a positive fraction of it at
every `n` — 86/194 at `n = 4`, 840/4110 at `n = 5`, **11,642/129,302 at `n = 6`**, by mg-52c4's own
census. At `n ≥ 7` those vertices are all of width ≥ 4, so Mirsky says nothing about them; they are
still there, and Corollary B still does not cover them.

This matters most **inside F28**, where the mg-52c4 edit landed:

> *"**ANSWERED 2026-08-14 (mg-52c4): NO.** For every `P` of height ≥ 2 the link is contractible,
> not spherical of any dimension; the height-1 exceptions have ≤ 6 elements at width ≤ 3. This does
> not refine F17+F18 to the link level — **it shows there is nothing at the link level to refine
> to.**"*

F28 §2.3's `P` **ranges over all of `PPF_n`**. Under that quantifier the final clause is refuted by
measurement: at `n = 4` there are 38 vertices whose links are rational spheres or wedges of them.
The honest answer to F29-B (*"are the links rationally spherical?"*) is **"no at height ≥ 2, and
yes at 32 of the 194 vertices at `n = 4`"** — not *"nothing at the link level"*.

### 6.4 §4 point 4 conflates two objects

§4's *"where a sphere does appear it is blind — `S^{c−2}` depends only on `|Comp(P)|`"* is a
statement about `Δ(L̄(P))`, the **lower factor**. The object F28 §2.3 and F29-B ask about is
`lk_{Δ_n}(P)`, whose type at a height-1 vertex is `Σ^{c−1} Δ(↑P ∖ {P})` — **not** a function of `c`
alone. The `n = 4` table above shows it directly: `c = 3` and `c = 4` height-1 vertices give
`β̃₃ = 1` and `β̃₃ = 3`, and the `c = 1, 2` ones give contractible links. **The blindness argument
is correct for the lower factor and does not transfer to the link.** *(Prediction G1 confirmed.)*

---

## 7. Does the conclusion survive anyway? Yes — measured, not proven

This is the part that decides whether §6 is a scoping note or a refutation. It is a scoping note.

**The restriction maps are all zero, and mg-52c4's argument for that is correct and can be
strengthened.** `Δ(↑P)` has `P` as a global minimum, so it is a cone, so
`res_{↑P}(ω_bal) = 0` for every `P` and every `n`. F28's (F-5) really is vacuous, and the strike is
right. **Strengthening:** since `Δ(↑P ∖ {P}) ⊆ Δ(↑P) ⊆ Δ_n`, the restriction to the **upper link**
factors through a cone and is therefore zero **for every `P`, with no height hypothesis at all** —
§3.5 inherits a height-≥2 hypothesis from §3.3 that this half does not need. *(Prediction F1
confirmed.)*

**The anchor-degree component of the link vanishes at every vertex reached.** The quantity the
headline needs is `H̃_{n−2}(lk_{Δ_n}(P))`. Measured:

| `n` | vertices | vertices with **non-zero** `H̃_{n−2}(lk P)` |
|---|---|---|
| 3 | 12 (all height 1, all links non-contractible) | **0** |
| 4 | 194 (38 links non-contractible) | **0** |
| 5 | all height-1 classes within cap | **0** (via the join formula and (A2)) |

At `n = 5` this is computed through `H̃_{n−2}(lk P) = H̃_{n−1−c}(U)`, `U := Δ(↑P ∖ {P})`, which
follows from (A2) plus the join formula verified in §5.

**So the conclusion holds — but by a degree coincidence, and every case is a near-miss.** At
`n = 4`: `c = 1` needs `H̃₂(U) = 0` and `U` is contractible; `c = 2` needs `H̃₁(U) = 0` and `U` is
contractible; `c = 3` needs `H̃₀(U) = 0` and `U ≃ S¹`; `c = 4` needs `H̃₋₁(U) = 0` and `U` has 4
components. **Every one lands on zero by one degree.** There is no dimension argument forcing this
(`dim U` exceeds the needed degree for all `n ≥ 4`), and I found no proof of it. **It is an
empirical fact at `n = 3, 4, 5`, not a theorem.**

**And one map in the neighbourhood is genuinely non-zero.** The restriction maps are not the only
maps from the anchor to the local structure at `P`: Mayer–Vietoris supplies
`∂ : H̃_{n−2}(Δ_n) → H̃_{n−3}(lk_{Δ_n}(P))`, which is not a restriction and is not covered by the
cone argument. Probed theorem-free by deleting each vertex:

| `n` | deletions that **change** `H̃_*(Δ_n)` | unchanged | all changed are height-1? |
|---|---|---|---|
| 3 | **12 of 12** — `Δ_3 ∖ {P}` becomes **contractible** | 0 | yes (all vertices are) |
| 4 | **38 of 194** — `(β̃₂) = (1)` → `(β̃₂, β̃₃) = (1, 1)` | 156 | **yes** |

**At `n = 3` the connecting map is non-zero at every single vertex** — deleting any one vertex
destroys the `F17+F18` class outright. So *"no restriction of `ω_bal` to the local structure at `P`
is non-zero"* (§3.3) is true **for restrictions** and false for the local structure in general.
At `n = 4` the anchor class survives every deletion (`β̃₂` is preserved at all 194); what the 38
deletions change is a *new* `β̃₃`. *(Predictions F2 and F3 both confirmed — F3 was recorded as the
lower-confidence one and it held.)*

---

## 8. §3.5's "one fibrewise object still uncomputed" — now computed for `n ≤ 5`

§3.5 names `Δ(↑P ∖ {P})` as *not computed* and *not trivially a cone*. Both true. It is computed
here for **14/14 isomorphism classes at `n = 4` and 58/61 at `n = 5`**, and the finding is that
§3.5's instinct is right to be cautious:

- **The upper link is NOT always contractible.** At `n = 4`: `β̃₁ = 1` at the `c = 3` height-1
  classes, `β̃₀ = 1` and `β̃₀ = 3` at `c = 4`, and it is **empty** at the maximal vertices (`c = 5`).
  At `n = 5` it ranges over `β̃₂ = 1`, `β̃₁ ∈ {1, 2}`, `β̃₀ ∈ {1, 3}`, and empty.
- **A structural cross-check falls out.** For `P = {(i, 4) : i < 4}` at `n = 5`, `↑P ∖ {P}` has 194
  elements and measures `β̃₂ = 1` — it is `PPF_4`, and `Δ_4 ≃_Q S²`. The instrument recovers
  `Δ_4` inside `Δ_5`'s upper link without being told to.
- **§3.5's conclusion is nevertheless correct**, and for a better reason than it gives (§7): the
  restriction to the upper link is zero for *every* `P` because it factors through the cone
  `Δ(↑P)`. Computing `Δ(↑P ∖ {P})` produces a fact with no consumer, exactly as §3.5 says.

---

## 9. Recommendations

**Do not open an F33.** The audited recommendation stands. Theorem A settles the (S1) reading and
what it settles is contractibility; the anchor's restriction to the local structure at `P` is
measured zero at every vertex reachable at `n = 3, 4, 5`; and §4's two walls (the F28 sheaf wall,
the F31 kernel wall) are correctly identified as untouched by a change of base complex. §4's final
paragraph — that Corollary B does **not** localise the Garland spectral defect, because
contractible does not imply a spectral gap — is the document's most careful moment and is right.

**Three scoping repairs, all one sentence each. I have not made them** — mg-52c4 owns these
documents and a second worker editing them is how a correct fix gets reverted by another correct
fix.

1. **`docs/OneThird-mg52c4-PerPoset-Subposet-Question.md` §0 point 3 and §3.3.** Replace
   *"the fibrewise anchor is identically trivial"* with a statement scoped to what is proven:
   *"the link is contractible at every height-≥2 vertex, which is every width-≤3 poset on `n ≥ 7`;
   at the height-1 vertices of `Δ_n` — which are not width-≤3 and are not removed by Mirsky — the
   link is often not contractible (38 of 194 at `n = 4`), and the anchor-degree component vanishes
   there by measurement (`n ≤ 5`, mg-e08a) rather than by argument."*
2. **F28 §2.3, the mg-52c4 edit.** *"it shows there is nothing at the link level to refine to"* is
   refuted under F28's own quantifier (`P` ranges over all of `PPF_n`). Recommend: *"…nothing at
   the link level to refine to **at the height-≥2 vertices**; at height-1 vertices the links are
   rationally spherical or wedges (32 × `S³` and 6 × `3·S³` at `n = 4`)."*
3. **§4 point 4.** Say `Δ(L̄(P))` where it currently says the sphere is blind — the blindness is a
   property of the lower factor, not of `lk_{Δ_n}(P)` (§6.4).

**One thing worth a follow-up ticket, and only one.** Whether `H̃_{n−2}(lk_{Δ_n}(P)) = 0` at
height-1 vertices is a **theorem** or a small-`n` coincidence. It is currently the load-bearing
fact under "identically zero" at the vertices Corollary B does not reach, it holds at
`n = 3, 4, 5` by measurement only, every case is a one-degree near-miss, and no dimension argument
forces it. This corpus has been bitten by exactly this shape before — `mg-24eb` re-scoped
*"exactly the ordinal sums"* as a small-`n` coincidence false from `n = 7`, and `mg-d1be` found the
width-2 caveat closed only at `n = 8`. **A negative that closes a direction should not rest on a
pattern that has only been checked to `n = 5`.**

## 10. Scope — what this audit does not do

- It does **not** edit `docs/compatibility-geometry-F17*.md`, `F28*.md`, or mg-52c4's own document.
  Findings are reported; repairs are recommended and left to their owner.
- It does **not** re-run `scripts/compat_geom_mg52c4_subposet_complexes.py`. Re-running an
  instrument that already reports `ALL_PASS = True` is a reproduction, not an audit.
- It does **not** verify contractibility in the strong sense anywhere — rational Betti cannot (see
  the `RP²` control, §1). The proof supplies that; the computation supplies `Q`-acyclicity.
- It does **not** reach the 5-chain's full Betti (6.5M simplices, over cap; not an element of
  `PPF_5`), nor three height-1 upper-link classes at `n = 5` (`c = 1` at 11.3M simplices and two
  `c = 2` at 887k). These are named in the JSON under `over_cap`, not silently dropped.
- Nothing in F17/F18 is touched or doubted; they remain GREEN and unconditional. F28 stays AMBER,
  F31 stays RED.

## 11. Prediction scorecard

All 25 pre-registered predictions resolved; **24 confirmed, 1 partially confirmed**, none refuted.

| group | outcome |
|---|---|
| **A1–A6** (the two named proof steps, both routes, "I will find no error") | **confirmed** — no error found |
| **B1–B4** (dichotomy exhaustive, `c ≤ 2`, antichains, height convention) | **confirmed** |
| **C1–C4** (independent re-implementation, census, past `n = 4`, high `c`) | **confirmed** — C3 predicted ≥ 3500 of 4110 within cap; actual is **all 4110** |
| **D1, D2** (Euler blind; but not load-bearing) | **confirmed**, with an explicit witness |
| **E1, E2** (Corollary B is a theorem; Mirsky correct) | **confirmed** |
| **E3** (a height-1 `P ∈ PPF_4` with non-contractible link) | **confirmed** — 38 of them |
| **E4** (the 86 height-1 links are a reporting omission) | **confirmed** |
| **F1** (upper-link restriction argument correct, strengthenable) | **confirmed** |
| **F2** (the MV connecting map is unaddressed) | **confirmed** |
| **F3** (some `P` with `H̃_*(Δ_4 ∖ P) ≠ H̃_*(Δ_4)`) — *recorded as lower confidence* | **confirmed** — 38 at `n = 4`, 12/12 at `n = 3` |
| **G1** (§4 point 4 conflates `Δ(L̄(P))` with `lk(P)`) | **confirmed** |
| **G2, G3** (the two walls; the Garland paragraph) | **confirmed** |
| **G4** (overall: sound, recommendation right, headline over-reaches) | **confirmed** |
| **H1–H3** (my controls reproduce / discriminate) | **confirmed** — H1 caught a real defect in this audit's first draft |
| **H4** (shared-ingredient enumeration finds exactly `tc`) | **partially confirmed** — `tc` was one shared ingredient, but the enumeration found a **second** I had not predicted: rational Betti as the verification currency, which is blind to `RP²` in both instruments (§1) |

**H4 is the one that did not fully hold, and it is the one worth keeping.** I predicted my
instrument would share exactly one non-independent ingredient with the audited one. It shares two,
and the second — that "contractible" means "`Q`-acyclic" in both harnesses — is the more consequential
of the pair. An audit's own defect-enumeration is subject to the defect it enumerates.

---

## 12. References

- **Audited:** `docs/OneThird-mg52c4-PerPoset-Subposet-Question.md` (mg-52c4, commit `cf63bb3`);
  its edits at `docs/compatibility-geometry-F17-equivariant-cofiber-morse.md` §3 and
  `docs/compatibility-geometry-F28-sheaf-cohomology-on-POSET.md` §1.6 (F-5), §2.3.
- **Context:** F17 §0.2/§2.1–§2.3 and Lemma L1 (`mg-4d3a`); F18 (`mg-d039`); F27 §4.1 (the link
  stated correctly); F31 §3.6 (`mg-01ce`).
- **This audit:** `docs/OneThird-mge08a-TheoremA-AUDIT-PREDICTIONS.md` (`a752fd0`),
  `scripts/compat_geom_mge08a_theoremA_audit.py`, `data/onethird-mge08a-theoremA-audit.json`.
- **Literature:** A. Björner, *Topological methods*, Handbook of Combinatorics (1995), §10.2
  (closure/order-homotopy) and Thm 10.8 (crosscut); L. Mirsky, *A dual of Dilworth's decomposition
  theorem*, Amer. Math. Monthly 78 (1971).
- **Work items:** `mg-e08a` (this), `mg-52c4` (audited), `mg-e768` PART B (the question),
  `mg-24eb` / `mg-d1be` (prior small-`n`-coincidence findings cited in §9).
