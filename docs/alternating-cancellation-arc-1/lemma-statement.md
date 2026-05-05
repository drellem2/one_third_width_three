# Alternating-Cancellation Lemma — precise statement

> **EXPLORATORY ONLY — NOT a live program.**
>
> Deliverable A for `mg-acc8` (alternating-cancellation arc 1.0
> kickoff, 2026-05-05, branch `alternating-cancellation-arc-1`,
> polecat `pacc8`). It is the answer to the precision points
> PM flagged in mg-344a `## Daniel's proposed direction` (the
> two-component "saturation lemma" sketch). Daniel's
> in-session sketch (verbatim, mg-acc8 §Origin):
>
> > *Possible lemma shape — Alternating-Cancellation Lemma.
> > Let `L(P) ⊆ S_n` be Bruhat-convex. If `L(P)` contains
> > many independent adjacent-swap directions, then
> > `|Σ(P)| ≪ |L(P)|`. Therefore sign saturation implies
> > the adjacent-swap graph of `L(P)` locally thin. Then
> > combine with layering: local thinness + bounded
> > interaction width ⇒ quotient-to-chain collapse.*
>
> The deliverable is a **lemma formalisation**, not a proof
> commitment. The headline `OneThird.width3_one_third_two_thirds`
> retains `hC3 : Step8.Case3Witness` (intentionally) under
> pm-onethird's option (δ) park (2026-04-27); this arc neither
> overturns nor confirms that retention. See `verdict.md` for
> the aggregate scoping verdict.

---

## 0. Provenance and outcome class

* **Filed under** `mg-acc8` (alternating-cancellation arc 1.0
  kickoff, polecat `pacc8`).
* **Sibling arcs (closed).**
  * `mg-3e53` / `mg-3d9d` / `mg-805c` — arc 1.0
    (recommendation A; A1 RED-fallback; B1 ship).
  * `mg-80ab` — arc 2.0 scoping. Zero GREEN of 4 framings.
  * `mg-65e1` — arc 3.0 scoping. Zero GREEN of 8 ε-close
    × 12 strategy alternatives.
  * `mg-0bc8` — arc 4.0 scoping. **RED on K=2 N-poset**
    (`|Σ|/|L| = 1/3` saturating, fix-point bound `2/9 < 1/3`,
    inverting strategy premise). F4-a / F4-b / F5
    introduced.
  * `mg-8baf` — conceptual arc 1.0 cross-field literature
    audit. No USABLE finding; SUGGESTIVE cluster
    (Caputo / DSC / Bubley–Dyer / Wilson) addresses the F5
    prerequisite, not the terminal F4-a.
  * `mg-cda8` — F1/F2/F3 synthesis-as-deliverable
    (`docs/why-hC3-is-structural.md`).
* **Sibling arcs (active).**
  * `mg-344a` — Daniel's parallel conceptual-development
    workspace (the three-component "bespoke
    finite/rigid combinatorics" package; this arc scopes one
    component).
  * `mg-e112` — proof-approaches catalog (parallel polecat;
    if landed it provides §A K=2 obstruction-family
    enumeration up to isomorphism, broader than this arc's
    7-config sample).
* **Outcome class.** Substantive scoping / verification chunk;
  no parallel cleanup. Per
  `feedback_distinguish_arc_chunk_outcomes`: this doc + the
  two siblings IS the deliverable. Headline / axiom
  inventory / `hC3` retention / sorry-count all unchanged
  by this ticket.
* **Branch.** `alternating-cancellation-arc-1`, parallel to
  `main` (parent commit `a74067a`). All artefacts under
  `docs/alternating-cancellation-arc-1/`.

---

## 1. Setup

### 1.1 Notation

Let `α` be a finite poset of cardinality `n`, and write `L(α)`
for the set of linear extensions of `α`. Each `L ∈ L(α)` is an
ordered list of the elements of `α` respecting `≤_α`. Fix a
reference linear extension `L_0 ∈ L(α)` and identify `L(α)`
with a subset of `S_n` via the labeling `i ↦ L_0[i]`: each
`L ∈ L(α)` becomes the permutation `σ_L ∈ S_n` with
`σ_L(i) = pos_L(label_i)` (the position of element `label_i`
in `L`).

Under this identification:

* `L(α) ⊆ S_n`.
* `sign(L) := (-1)^{number of inversions in σ_L}`. Equivalent
  to the parity of the unique product of adjacent transpositions
  taking `L_0` to `L`.
* `Σ(α) := Σ_{L ∈ L(α)} sign(L)` is the **sign-imbalance** of
  `α`.

### 1.2 Adjacent-swap directions

For each `i ∈ {1, …, n−1}`, write `τ_i = (i, i+1) ∈ S_n` for
the simple transposition swapping positions `i` and `i+1`.
Define

```
D_i(α)  :=  { L ∈ L(α)  :  τ_i · L ∈ L(α) }                      (1.2.a)
```

— the set of LEs on which the adjacent-swap direction `τ_i`
**fires** (produces another LE). Equivalently:

```
D_i(α)  =  { L ∈ L(α)  :  L[i], L[i+1] are α-incomparable }.    (1.2.b)
```

Two basic facts:

* **`τ_i`-closure.** `D_i(α)` is closed under `τ_i`: if
  `L ∈ D_i`, then `τ_i · L ∈ D_i` (since the elements at
  positions `i`, `i+1` are still `α`-incomparable after the
  swap, just exchanged). So `τ_i` restricts to an involution
  `D_i → D_i`.
* **Fixed-point freeness.** `τ_i · L ≠ L` for any `L`
  (positions `i, i+1` differ). So the involution is
  fixed-point free.
* **Sign-flipping.** `sign(τ_i · L) = −sign(L)` (one
  additional adjacent transposition flips parity).

Hence `(D_i, τ_i)` is a **fixed-point-free, sign-flipping,
order-2 action**. Pair every `L ∈ D_i` with `τ_i · L ∈ D_i`;
each pair contributes `+1 + (−1) = 0` to the signed sum over
`D_i`. Therefore:

```
Σ_{L ∈ D_i(α)} sign(L)  =  0,    for every i ∈ {1, …, n−1}.    (1.2.c)
```

### 1.3 The BK graph

`BK(L(α))` has vertex set `L(α)` and an edge `{L, L'}`
whenever `L' = τ_i · L` for some `i`. By construction, the
edge set has the canonical decomposition

```
E(BK(L(α)))  =  ⊔_{i = 1}^{n−1}  E_i,    E_i := { {L, τ_i L} : L ∈ D_i }.
```

Each `E_i` is a perfect matching on `D_i` ⊆ `L(α)`. Note that
`|E_i| = |D_i| / 2` (since `D_i` is paired by `τ_i` into
disjoint 2-element orbits).

The graph `BK(L(α))` is bipartite with bipartition
`L(α) = L_+(α) ⊔ L_−(α)` by parity of `sign`: every edge flips
parity. Then

```
Σ(α)  =  |L_+(α)|  −  |L_−(α)|.                                  (1.3.a)
```

---

## 2. The single-direction lemma

### 2.1 Statement

**Lemma 2.1 (single-direction alternating cancellation).**
For any finite poset `α` and any `i ∈ {1, …, n−1}`,

```
|Σ(α)|  ≤  |L(α)|  −  |D_i(α)|.                                  (2.1.a)
```

Hence

```
|Σ(α)|  ≤  |L(α)|  −  max_i |D_i(α)|.                            (2.1.b)
```

### 2.2 Proof

By (1.2.c), `Σ_{L ∈ D_i} sign(L) = 0`. So
`Σ(α) = Σ_{L ∈ L(α) ∖ D_i} sign(L)`. Since each summand is
`±1`, `|Σ(α)| ≤ |L(α) ∖ D_i| = |L(α)| − |D_i(α)|`. ∎

### 2.3 Tightness on the K=2 N-poset

(See `verification.md` §1 for the full enumeration.) The K=2
N-poset has `|L| = 6`, `|Σ| = 2`, `max_i |D_i| = 4`. The
bound (2.1.b) gives `|Σ| ≤ 2`, attained as equality. Same
behaviour on the F1 3-element minimal counterexample
`{a, a', y}` with `a' < y`: `|L| = 3`, `|Σ| = 1`,
`max_i |D_i| = 2`, bound `|Σ| ≤ 1` attained.

So the bound (2.1.a) is **tight** on the K=2 obstruction
family base case. This is the first non-trivial content the
lemma supplies.

---

## 3. The multi-direction extension

### 3.1 Pairwise non-adjacent index sets

For `S ⊆ {1, …, n−1}`, write `S` is **pairwise non-adjacent**
if `|i − j| ≥ 2` for all distinct `i, j ∈ S`. Equivalently,
`{τ_i : i ∈ S}` are pairwise commuting transpositions, and
`⟨τ_i : i ∈ S⟩ ≅ (Z/2)^{|S|}` (Coxeter relations: commuting
non-adjacent simple transpositions).

For non-adjacent `S`, define

```
D_S(α)  :=  ∩_{i ∈ S}  D_i(α).                                   (3.1.a)
```

Note an important compatibility: if `L ∈ D_i ∩ D_j` with
`|i − j| ≥ 2`, then `τ_j · L ∈ D_i` (because swapping
positions `j, j+1` does not disturb positions `i, i+1`, and
the elements at `i, i+1` remain `α`-incomparable). Hence the
abelian subgroup `⟨τ_i : i ∈ S⟩` acts on `D_S(α)` (not just
on the larger `L(α)`).

### 3.2 Statement

**Lemma 3.2 (multi-direction alternating cancellation).**
Let `S ⊆ {1, …, n−1}` be pairwise non-adjacent. The action
of `⟨τ_i : i ∈ S⟩ ≅ (Z/2)^{|S|}` on `D_S(α)` is
fixed-point free, sign-flipping, and produces orbits of size
`2^{|S|}` whose summed signs vanish. Hence

```
Σ_{L ∈ D_S(α)} sign(L)  =  0.                                    (3.2.a)
```

In particular,

```
|Σ(α)|  ≤  |L(α)|  −  |D_S(α)|.                                  (3.2.b)
```

Optimising over non-adjacent `S`:

```
|Σ(α)|  ≤  |L(α)|  −  max_{S non-adj} |D_S(α)|.                  (3.2.c)
```

### 3.3 Proof

The action is fixed-point free: each `τ_i` is fixed-point
free on `D_i ⊇ D_S`. Distinct group elements `g, g' ∈
⟨τ_i : i ∈ S⟩` give `g · L ≠ g' · L` because
`g^{−1} g' ∈ ⟨τ_i : i ∈ S⟩ \ {e}` is a non-identity product
of distinct commuting transpositions, which is fixed-point
free on `S_n` (it permutes at least one position non-trivially).

Sign-flipping: each `τ_i` flips sign; products of `k`
commuting transpositions multiply sign by `(−1)^k`. So the
sum over an orbit of size `2^{|S|}` is

```
Σ_{ε ∈ {0,1}^S} (−1)^{Σ_i ε_i} · sign(L)  =
  sign(L) · ∏_{i ∈ S} (1 + (−1))  =  0.
```

Hence (3.2.a). The bound (3.2.b) follows by the same residual-sum
argument as Lemma 2.1. ∎

### 3.4 Why "non-adjacent" is forced

For `i, j` adjacent (`|i − j| = 1`), `τ_i τ_j ≠ τ_j τ_i`
(braid relation: `τ_i τ_{i+1} τ_i = τ_{i+1} τ_i τ_{i+1}`,
not commuting). The orbit of `L` under
`⟨τ_i, τ_{i+1}⟩` has size 6 (the symmetric group `S_3` on
positions `{i, i+1, i+2}`); the signs no longer cancel by
abelian-orbit counting. **The lemma fails for adjacent
directions** because the orbit structure includes 3-cycles
(sign `+1`) that are not paired with sign-flipping
involutions.

This is a structural feature, not a bookkeeping artefact:
adjacent directions correspond to overlapping triple
configurations on positions `i, i+1, i+2`, where the
combinatorics is not (Z/2)^k.

---

## 4. Bipartite / matching reformulation

### 4.1 Bipartite structure

Recall `BK(L(α))` is bipartite by parity (every edge flips
sign). Let `M ⊆ E(BK(L(α)))` be a **matching** (a set of
pairwise vertex-disjoint edges). Each edge in `M` connects
one `L ∈ L_+` to one `L' ∈ L_−`, contributing
`sign(L) + sign(L') = 0` to the signed sum over the matched
pair.

### 4.2 Matching deficiency bound

If `M` is a maximum matching in `BK(L(α))`, the unmatched
vertices `L(α) \ V(M)` have signed sum bounded by their
count:

```
|Σ(α)|  ≤  |L(α)|  −  2 · |M|  =  ν(L(α)),                       (4.2.a)
```

where `ν(L(α))` is the **matching deficiency** of
`BK(L(α))`. This refines (3.2.c), since any non-adjacent
`S` produces a matching of size `|D_S|/2` × small factor;
specifically, choosing `M = E_i` (the single-direction
matching from §1.3) gives `2|M| = |D_i|`, recovering (2.1).

### 4.3 König–Hall sharpening

Since the bipartite graph `BK(L(α))` is signed by parity, by
König's theorem,

```
|M_max|  =  min(|L_+|, |L_−|)    ⇔    Hall's condition holds
                                      on the smaller side.        (4.3.a)
```

`|Σ(α)| = ||L_+| − |L_−||`. When `|M_max| = min(|L_+|, |L_−|)`,
deficiency `ν(L(α)) = |L| − 2 · min(|L_+|, |L_−|) = ||L_+| − |L_−|| =
|Σ(α)|`, so (4.2.a) is **tight**.

When Hall fails, deficiency exceeds `|Σ|`, and (4.2.a) is
strict.

---

## 5. Choosing the precision points

PM's review of Daniel's sketch (mg-acc8 §Polecat-task §A
"Make the lemma statement precise") flagged three precision
questions. We resolve each below.

### 5.1 What is "many independent adjacent-swap directions"?

PM's candidates:
* **(a) disjoint position pairs** — pairwise non-adjacent
  index sets `S ⊆ [n−1]`. **Adopted.**
* **(b) generating disjoint sub-Sym groups** — same as (a)
  for adjacent-transposition generators.
* **(c) Bruhat-graph spanning** — too strong; would require
  the entire BK graph to be connected by arc-swap moves,
  which is true generically (BK graphs are connected) but
  doesn't admit a quantitative grading.
* **(d) some other notion** — e.g., min-degree of `BK(L(α))`
  bounded below. Useful but not sharper than (a) for the
  cancellation argument.

**Verdict:** (a). Pairwise non-adjacent gives the cleanest
mathematical content because the abelian-orbit cancellation
argument requires commutativity, which holds iff the
indices are non-adjacent (§3.4). **No other notion gives a
strictly stronger bound** under the cancellation argument
alone, because adjacent-direction triples don't cancel
(they generate `S_3` on a 3-element position window,
including a sign-`+1` 3-cycle that doesn't pair).

The natural quantitative version: define
`m(α) := max_{S non-adj} |D_S(α)|` (maximum **fire-set
size** under non-adjacent direction choice). Then the
single bound (3.2.c) gives `|Σ(α)| ≤ |L(α)| − m(α)`.

**Sharper available form** (matching-based): define
`ν(α) := |L(α)| − 2 · ν^*(BK(L(α)))` where `ν^*` is maximum
matching size. Then `|Σ(α)| ≤ ν(α) ≤ |L(α)| − m(α)`. The
matching form is sharper but harder to evaluate
combinatorially; the non-adjacent-set form is easier to
read and is what the cancellation argument literally
provides.

### 5.2 What is "≪"?

PM's candidates:
* Asymptotic in `|L(α)|`.
* Constant ratio bounded below `1/3`.
* Bounded by `1/3 − ε` for explicit `ε`.

**Verdict.** The cancellation argument supplies the **exact
identity**

```
|Σ(α)| / |L(α)|  ≤  1  −  m(α)/|L(α)|.                           (5.2.a)
```

There is no asymptotic looseness; (5.2.a) holds as a
finite-`n` inequality with rationals on both sides.

The **contrapositive** is what's wanted for the saturation
case (`|Σ(α)| / |L(α)| = 1/3` exactly):

```
|Σ(α)| / |L(α)|  =  1/3      ⟹      m(α) / |L(α)|  ≤  2/3.       (5.2.b)
```

So "sign saturation ⇒ at most 2/3 of the LEs are
simultaneously fired by some non-adjacent direction set."

Equivalently, "at least 1/3 of the LEs fail every
non-adjacent direction choice" — i.e., for at least 1/3 of
LEs, every fixed pairwise-non-adjacent `S` has at least one
`i ∈ S` with `τ_i · L ∉ L(α)`.

**This is the rigorous "≪" form.** It is a finite-`n`
inequality with explicit rational constant. **No asymptotic
machinery, no ε.** This is the form most useful for the
contrapositive saturation argument.

### 5.3 What does "quotient-to-chain collapse" produce concretely?

PM's candidates (§Polecat-task §A.3):
* **"Layered with bounded K"** — already where we are.
  Vacuous.
* **"Is a literal chain"** — too strong; the K=2 N-poset
  isn't a chain; refuted by the obstruction family.
* **"Band size = 1, OR band size 2 with at most one
  cross-band non-edge, OR specific small-finite list of
  classes"** — usable.
* The polecat's job is to find the right intermediate
  sharpness.

**This is the precision question on which the lemma either
earns its keep or is vacuous. The polecat's answer is:** the
rigorous content (Lemma 3.2) does **not by itself** produce
a "quotient-to-chain collapse" statement of the
intermediate-sharpness form. It produces **only** (5.2.b):
the `1 − m/|L|` lower bound on `|Σ|/|L|`.

To upgrade (5.2.b) to a structural conclusion, one of the
following **additional inputs** is required:

* **(α) a bespoke combinatorial structure theorem** of the
  form: *"For a layered width-3 poset `α` with K = 2 (or
  bounded K), if at least 1/3 of `L(α)` LEs fail every
  pairwise-non-adjacent direction set, then `α` has one of
  the following structural properties: (i) N-poset core,
  (ii) reducible (admits a B1-style ordinal cut), or (iii)
  contains a balanced pair directly."*

  This is the trichotomy. It is **not derivable** from the
  cancellation argument alone; it would be a separate
  combinatorial result on the K=2 obstruction family. The
  polecat could not locate such a theorem in published
  literature (Brightwell, Felsner–Trotter, Bubley–Karzanov,
  Kahn–Linial), and verifying it on the obstruction family
  (next deliverable) is exactly the job of a structure
  theorem, not a lemma.

* **(β) BK-walk eigenvalue / spectral comparison** — i.e.,
  use the fact that `Σ(α)/|L(α)|` is the sign-isotypic
  component of `1_{L(α)} ∈ L^2(S_n)` to bound BK-walk
  eigenvalues, then apply Cheeger + Theorem E
  to extract a balanced pair. This is the **F5 prerequisite**
  flagged in arc 4.0 §6 (mg-0bc8), known to be paper-level
  math outside polecat authority and currently unsolved in
  cited published literature. Substantively new (paper-tier)
  spectral comparison work would be required.

* **(γ) Steps 5–7 invocation** — appeal to the in-tree
  fiber-coherence / globalisation machinery to convert
  "many low-fire LEs" into structural rigidity. This is
  the **F4-b trap** flagged in arc 4.0 §4 (mg-0bc8),
  triggered by the ticket's stop-loss condition (mg-acc8
  §Stop-loss): "the lemma's 'locally thin' notion conflates
  with Steps 5-7 content." STOP-and-report condition fires.

**Verdict.** The polecat adopts the **honest intermediate
sharpness**: the lemma's *direct* conclusion is the
inequality (5.2.b) — nothing structural. Promotion to a
trichotomy-driver requires (α), (β), or (γ), none of which
the polecat can supply within scope. See `verdict.md` for
the aggregate verdict.

---

## 6. The "Bruhat-convex" hypothesis

Daniel's sketch reads "Let `L(P) ⊆ S_n` be Bruhat-convex."
The polecat investigated and reports:

### 6.1 `L(α)` is generally NOT Bruhat-convex

Direct counterexample on the K=2 N-poset (`α = {x_1, x_2,
y_1, y_2}` with `x_1 < y_1`, `x_2 < y_2`, reference LE
`L_0 = (x_1, x_2, y_1, y_2)`, identification with `S_4`):

* `L_1 = e ∈ L(α)`.
* `L_6 = (1 3 4 2) = s_1 s_3 s_2 ∈ L(α)`, `ℓ(L_6) = 3`.
* The Bruhat interval `[L_1, L_6]` has 8 elements (subwords
  of `s_1 s_3 s_2`): `e, s_1, s_2, s_3, s_1 s_3, s_1 s_2,
  s_3 s_2, s_1 s_3 s_2`.
* Of these, `s_1 s_2` corresponds to the one-line `3124` —
  i.e., `(x_2, y_1, x_1, y_2)`, which violates `x_1 < y_1`
  (`x_1` appears at position 3 after `y_1` at position 2).
  **Not in `L(α)`.**
* Similarly `s_3 s_2 = 1342` is `(x_1, y_2, x_2, y_1)`,
  violating `x_2 < y_2`. **Not in `L(α)`.**

So `[L_1, L_6]_{Bruhat} \ L(α) ≠ ∅`. Hence `L(α)` is **not
Bruhat-convex** for the K=2 N-poset.

### 6.2 What `L(α)` is

Standard fact (Björner–Wachs 1991, Edelman): `L(α)` is the
**weak-order interval** `[L_min, L_max]` where `L_min` is
the lexicographically-least extension and `L_max` is the
greatest under any compatible reference. Weak order is
strictly weaker than Bruhat order (`w ≤_{weak} w'` ⇒
`w ≤_{Bruhat} w'`, but not conversely on length-jumping
elements like `s_1 s_2` jumping over `e`).

### 6.3 Reading of Daniel's sketch

The polecat reads "Bruhat-convex" as **loose terminology for
"L(α) is closed under adjacent-swap moves into-and-out-of"**
— i.e., the BK graph is well-defined on `L(α)`, which is
trivially true. Under that reading, the lemma's setup is
fine and no convexity hypothesis is operative.

**An alternative reading** — "weak-order convex" — does
hold (`L(α)` is a weak-order interval). But it's not used
in the cancellation argument either; the argument relies on
`τ_i`-closure of `D_i(α)`, which is direct from the
definition (§1.2).

**Net effect.** The "Bruhat-convex" hypothesis is **not
needed** for Lemmas 2.1 and 3.2 as stated. They hold for
arbitrary finite posets `α`. The polecat drops the
hypothesis and notes the discrepancy in the lemma
statement.

---

## 7. Summary — the lemma in final form

**Lemma (Alternating-Cancellation, single-direction).** For
any finite poset `α` and any `i ∈ {1, …, n−1}`,

```
|Σ(α)|  ≤  |L(α)|  −  |D_i(α)|.
```

**Lemma (Alternating-Cancellation, multi-direction).** For
any finite poset `α` and any pairwise-non-adjacent
`S ⊆ {1, …, n−1}`,

```
|Σ(α)|  ≤  |L(α)|  −  |D_S(α)|,    where  D_S(α) := ∩_{i ∈ S} D_i(α).
```

In particular, optimising over `S`,

```
|Σ(α)|  ≤  |L(α)|  −  m(α),    where  m(α) := max_{S non-adj} |D_S(α)|.
```

**Corollary (saturation contrapositive).** If
`|Σ(α)|/|L(α)| = 1/3`, then `m(α)/|L(α)| ≤ 2/3` — at
least `1/3` of the LEs fail every pairwise-non-adjacent
direction choice.

These are the **rigorous statements**. They are tight on
the K=2 N-poset (`verification.md` §1) and on the F1
3-element minimal counterexample (`verification.md` §2).

**The polecat does not assert a structural classifier
beyond (5.2.b).** Promoting the corollary to a trichotomy
(N-poset core / reducible / balanced-pair) requires
substantively new work beyond polecat scope; see `verdict.md`.

---

## 8. References and memory anchors

### Internal documents

* `notes/bk-walk-irrep-eigenvalue-bounds.md` (mg-7e24) —
  Daniel's irrep / character table; sign-irrep entry is the
  starting point for the cancellation argument.
* `docs/math-simp-arc-4.0/scoping.md` (mg-0bc8) — arc 4.0
  computations; Σ values on K=2 obstruction family
  configurations are from this audit.
* `docs/conceptual-arc-1/lit-audit.md` (mg-8baf) —
  cross-field literature audit; SUGGESTIVE cluster around
  Caputo / DSC / Bubley–Dyer / Wilson is the F5 prerequisite
  reference.
* `docs/why-hC3-is-structural.md` (mg-cda8) — F1/F2/F3
  framing; this lemma navigates around F1 (no Aut-based
  reduction) and F2 (no per-element Brightwell), but bumps
  into F4-a / F4-b / F5 from arc 4.0.
* `docs/path-c-track-1-status-1.md` §2 (mg-b666) — F1
  cardinality obstruction; F1 minimal counterexample
  `{a, a', y}` is a verification target.

### Memory anchors applied

* `feedback_latex_first_for_math_simp` — applied (no Lean
  changes).
* `feedback_audit_bar_for_axioms` — applied (no axiom
  candidates surfaced).
* `feedback_signature_regressions` — applied (no
  replacement of `hC3`).
* `feedback_n_poset_is_not_ordinal_sum` — applied (K=2
  N-poset is the canonical first verification target).
* `feedback_distinguish_arc_chunk_outcomes` — applied at
  close (verdict in `verdict.md`).

### Daniel directives

* In-session ~2026-05-05T~12Z: "Possible lemma shape —
  Alternating-Cancellation Lemma. … if you think this is
  worth exploring have a polecat see if they can make it
  useful. this may have to be part of a larger effort to
  explore this part of the proof."
* PM agreement: worth exploring; this arc is the first
  focused investigation.

---

*This file is Deliverable A for `mg-acc8`, filed
2026-05-05 by polecat `pacc8` on branch
`alternating-cancellation-arc-1`. It is doc-only (no Lean
source changes). See `verification.md` (Deliverable B) and
`verdict.md` (Deliverable C) for the full deliverable
package.*
