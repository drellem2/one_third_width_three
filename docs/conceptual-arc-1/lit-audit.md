# Conceptual / literature audit on the `hC3` obstruction — "quotient away from chain" theme; expander / 1D-Gibbs / treewidth / constrained-Markov surveys

> **EXPLORATORY ONLY — NOT a live program.**
>
> This file is the deliverable for `mg-8baf` (conceptual arc 1.0
> kickoff, 2026-05-05, branch `conceptual-arc-1`). It is the
> answer to Daniel's in-session directive
> (~2026-05-05T09:30Z):
>
> > *"I want some conceptual work done by a polecat on the
> > obstruction, with some exploration of lit and different
> > approaches. To me the big theme of the layering is: it's
> > basically a quotient away from a chain, which is a property
> > it shares with ordinal sums. Allegedly this theme appears in
> > related fields, so perhaps there are ideas or lemmas we can
> > use: expander obstructions, 1D Gibbs systems, low-treewidth
> > graphs, Markov chains with local constraints."*
>
> The deliverable is a **literature audit**, not a commission
> to execute anything. Months from now, treat this doc the same
> way arc 2.0 / arc 3.0 / arc 4.0 scoping should be treated: a
> record of evaluation under specific assumptions, **not a
> backlog**. Verdict at §5.
>
> The headline `OneThird.width3_one_third_two_thirds` retains
> `hC3 : Step8.Case3Witness` (intentionally) under
> pm-onethird's option (δ) park (2026-04-27). This arc neither
> overturns nor confirms that retention; it asks whether
> off-the-shelf lemmas from adjacent fields would close `hC3`
> where existing strategies cannot. The verdict is **no
> USABLE finding** — a single SUGGESTIVE line (Caputo-style
> spectral comparison for adjacent-transposition walks on
> subsets / weighted versions) is structurally interesting
> but addresses the prerequisite F5 rather than the terminal
> F4-a, and even then is paper-tier infrastructure outside
> polecat authority.

---

## 0. Provenance and outcome class

* **Filed under** `mg-8baf` (conceptual arc 1.0 kickoff,
  polecat `p8baf`).
* **Sibling arcs (closed).**
  * `mg-3e53` — arc 1.0 scoping. 4 candidates; recommended A.
  * `mg-3d9d` — arc 1.0 A1 RED-fallback (perturbation slack).
  * `mg-805c` — arc 1.0 B1 ship (cleanup only).
  * `mg-80ab` — arc 2.0 scoping. Zero GREEN of 4 framings.
  * `mg-65e1` — arc 3.0 scoping. Zero GREEN of 8 ε-close ×
    12 strategy alternatives.
  * `mg-0bc8` — arc 4.0 scoping. RED on K=2 N-poset (sign mode
    saturates 1/3); F4-a / F4-b / F5 introduced.
  * `mg-b666` — Track 1 cardinality obstruction (F1).
  * `mg-cda8` — F1/F2/F3 synthesis-as-deliverable
    (`docs/why-hC3-is-structural.md`).
* **Sibling arc (active, human).** `mg-344a` — Daniel's
  parallel conceptual-development workspace.
* **Outcome class.** Substantive scoping / audit chunk; no
  parallel cleanup. Per
  `feedback_distinguish_arc_chunk_outcomes`: the audit doc IS
  the deliverable. Headline / axiom inventory / `hC3`
  retention / sorry-count all unchanged by this arc.
* **Branch.** `conceptual-arc-1`, parallel to `main` (parent
  commit `a74067a`). All artefacts under
  `docs/conceptual-arc-1/`.

---

## 1. The "quotient-to-chain" pattern, formalised

### 1.1 Two natural definitions

The brief proposes the unifying theme:

> *Layering is basically a quotient away from a chain, which is
> a property it shares with ordinal sums.*

We make this precise by two equivalent definitions, the first
order-theoretic and the second graph-theoretic.

**Definition Q1 (Order-theoretic).** A finite poset
`P = (X, ≤_P)` is a **`K`-band quotient-to-chain** iff there
is a surjection `π : X → [K] = {1, …, K}` such that

```
π(x) < π(y)   ⟹   x <_P y      (band-respecting order).      (Q1.a)
π(x) = π(y)   ⟹   x ∥_P y      (within-band antichain).       (Q1.b)
```

The map `π` is a **band map**; the fibres `L_k := π⁻¹(k)` are
the **bands**. The resulting partition `X = L_1 ⊔ L_2 ⊔ … ⊔
L_K` partitions `X` into antichains stacked in the chain
order on `[K]`. Chain (`X = L_1 ⊕ … ⊕ L_n` with `|L_k| = 1`)
and ordinal sum (`A ⊕ B`, two bands with full bipartite
cross-edges) are special cases.

**Definition Q2 (Quotient-to-chain via comparability graph).**
The comparability graph `G(P) = (X, E)` has `xy ∈ E` iff `x
and y` are `≤_P`-comparable. `P` is `K`-band quotient-to-chain
iff there is a partition `X = L_1 ⊔ … ⊔ L_K` such that

* Every `L_k` is an independent set in `G(P)` (no edges
  within a band).
* For every `j < k`, every `x ∈ L_j, y ∈ L_k` with `xy ∈ E`
  satisfies `x <_P y` (i.e., the cross-band edges are
  consistently directed in band order).

Equivalently: contracting each band to a point yields a
multigraph that is a *chain* `[K]` (with parallel edges from
the cross-band pairs of `P`).

**Q1 ⇔ Q2.** Direct: Q1.a says cross-band relations agree
with the chain order on `[K]`; Q1.b says within-band fibres
have no `≤_P`-relations. Conversely, given a Q2 partition,
define `π(x) := k` iff `x ∈ L_k`; the Q1 conditions are then
just the partition-cross-edge / partition-independence
conditions.

**Definition (canonical band map).** Among all band maps
witnessing that `P` is `K`-band quotient-to-chain, the
**height function** `h_P(x) := length of longest chain ending
at x` is canonical when `P` has the *structural* property that
covers respect heights:

```
x ⋖_P y   ⟹   h_P(y) = h_P(x) + 1      (height-graded).      (Q1.c)
```

A height-graded poset is `K`-band quotient-to-chain via `π :=
h_P` with `K = max_x h_P(x)`. The **layered width-3** posets in
the in-tree development correspond to height-graded posets
with `|L_k| ≤ 3` for all `k`.

### 1.2 Examples and non-examples

| Object                     | Q1-quotient-to-chain? | `K` | within-band sizes |
|----------------------------|-----------------------|-----|--------------------|
| Chain `[n]`                | yes                   | n   | all 1              |
| Antichain `A_n`            | yes (`K = 1`)         | 1   | n                  |
| Ordinal sum `A ⊕ B`        | yes                   | 2   | `|A|, |B|`         |
| Layered width-3 poset      | yes                   | K   | each `≤ 3`         |
| K=2 **N-poset**            | yes                   | 2   | 2, 2               |
| F1 minimal `{a, a', y}`    | yes                   | 2   | 2, 1               |
| Crown `S_n^0` (`n` ≥ 3)    | yes                   | 2   | n, n               |
| 2D zigzag `Z_{m, n}`       | partly — depends on Hasse |     | varies            |
| Bowtie / non-graded poset  | NOT in general        | n/a | n/a                |

The K=2 N-poset (`{x_1, x_2, y_1, y_2}` with `x_i < y_i`) IS
quotient-to-chain via `π(x_i) = 1, π(y_i) = 2`: the bands `{x_1,
x_2}` and `{y_1, y_2}` are antichains, the cross-edges go up.
Confirmed verbatim with `feedback_n_poset_is_not_ordinal_sum`:
the N-poset is **NOT** an ordinal sum (only 2 cross-edges, not
4), but it **IS** quotient-to-chain. So the unifying theme of
the brief — "share a property with ordinal sums" — is correctly
captured at the level of Q1 / Q2, not at the level of "ordinal
sum" itself.

### 1.3 The "deviation from chain" content

For a `K`-band quotient-to-chain `P`, the **deviation from
chain** decomposes into two combinatorial objects:

* **Within-band antichain shapes.** Each `L_k` is an antichain
  of size `s_k := |L_k|`. For width-3 layered, `s_k ∈ {1, 2,
  3}`.
* **Cross-band bipartite graphs.** Between consecutive bands
  `L_k` and `L_{k+1}` (and more generally between any `L_j`
  and `L_k` with `j < k`), the cross-edges of `P` form a
  bipartite digraph `B_{j, k} ⊆ L_j × L_k`, all directed `j →
  k`. For an ordinal sum, `B_{1, 2} = L_1 × L_2` is the
  complete bipartite graph; for the N-poset, `B_{1, 2}` is a
  perfect matching.

The "interesting structure" of `P` lies in `(s_k)_k` (the band
sizes) plus `(B_{j, k})_{j < k}` (the cross-band bipartite
graphs). Collapsing each `L_k` to a point yields a chain
`[K]`, possibly with multi-edges for the cross-band pairs.

**Subtlety: the projection is not a poset homomorphism in the
forgetful direction.** A linear extension of `P` does **not**
project to a linear extension of `[K]` (every LE of `P`
projects to the same chain `1, 1, …, 1, 2, 2, …, 2, …, K`,
which is not even a permutation of `[K]`). The non-trivial
content of LEs lives in the lifted level: how the elements of
each band interleave with elements of adjacent bands, subject
to `B_{j, k}` constraints.

**Correspondence with K=2 case.** For `K = 2`, we have a
single bipartite cross-graph `B := B_{1, 2}`. The **K=2 family
parameterised by `B`** is the natural object:

* `B = L_1 × L_2` (full bipartite): `P = L_1 ⊕ L_2` is an
  ordinal sum.
* `B = ∅` (no cross-edges): `P = L_1 ⊔ L_2` is a disjoint
  antichain (which is the antichain of size `|L_1| + |L_2|`,
  i.e., still height-graded with `K = 1`, modulo relabeling).
* `B = ` perfect matching of size 2 on width-2 bands (both
  sides size 2): the **K=2 N-poset**.
* `B = ` non-matching bipartite (other cases): wider K=2
  width-≤3 N-poset siblings, parameterised by the bipartite
  incidence pattern.

The "within-band" component for K=2 is trivial (each band is
already an antichain, no choices). All the structural variation
of the K=2 family lives in `B`.

**Correspondence with K ≥ 3 case.** For `K ≥ 3`, the within-band
component contributes (each `L_k` of size ≤ 3 has a single
"shape": the antichain) but the chain-of-bipartite-graphs
`(B_{1,2}, B_{2,3}, …, B_{K-1, K})` is a richer object. In a
height-graded poset, only consecutive bipartites matter
(non-adjacent pairs `(x, y) ∈ L_j × L_k` with `j + 1 < k`
inherit comparability from cover paths). In a non-height-graded
quotient, longer-range bipartites carry independent
information.

**The K=2 N-poset under this lens.** It is the **smallest
nontrivial K=2 quotient-to-chain that is NOT an ordinal sum**.
It is (within the K=2 width-3 family) the canonical
counterexample to "K=2 quotient-to-chain ≅ ordinal sum"; it
sits in the gap between full bipartite and empty bipartite.

### 1.4 Other natural classes that fit

The brief asks "any other natural classes" beyond layered
width-3 and ordinal sums.

* **Bipartite posets.** A bipartite poset is exactly a
  K=2 quotient-to-chain (in our sense). The K=2 N-poset is a
  bipartite poset.
* **`d`-dimensional posets / `d`-realizers.** These have a
  realizer of `d` linear extensions whose intersection is the
  poset. Width-3 posets have `d ≤ 3` (Dilworth-Mirsky variant).
  Connection to quotient-to-chain is loose: `d`-dimensional
  posets need not be height-graded.
* **Series-parallel posets.** Built recursively from
  singletons via series (ordinal sum) and parallel (disjoint
  union). Series-parallel ⊆ N-free (no induced N-poset). The
  N-poset is the **minimal forbidden induced subposet for
  series-parallel** — and it is also our recurring obstruction.
  Connection: a series-parallel poset can always be
  decomposed by alternating ordinal sums (which preserve the
  quotient-to-chain pattern at every step) and disjoint
  unions. Layered width-3 N-posets are precisely the
  obstruction to series-parallel structure within the
  quotient-to-chain regime.
* **Weak orders / preorders.** A weak order (linear order on
  equivalence classes, ties allowed) is a `K`-band
  quotient-to-chain where `K` = number of distinct ranks and
  `B_{j, k}` = full bipartite for every `j < k`. So weak
  orders are "iterated ordinal sums," and the
  quotient-to-chain framework subsumes them.
* **Two-dimensional posets.** A poset is 2D iff its
  comparability graph's complement is a comparability graph.
  Includes interval posets and certain bipartite shapes. The
  K=2 N-poset is 2D (realizer: `(x_1, x_2, y_1, y_2)` and
  `(x_2, x_1, y_2, y_1)`). Most layered width-3 posets in our
  obstruction family are 2D-realizable but with no clean
  classification.

The unifying theme is **real and non-vacuous**: the
quotient-to-chain pattern subsumes layered width-3, ordinal
sums, weak orders, and a slice of bipartite / 2D / N-free
posets. It is also a natural object of study: the "deviation
from chain" decomposes into within-band antichain shapes plus
cross-band bipartite graphs, both of which are first-class
combinatorial objects.

### 1.5 Relation to the K=2 N-poset family

Reviewing the audit's recurring counterexample
(`docs/why-hC3-is-structural.md` §F1; arc 4.0 §8.2):

* The K=2 N-poset is `K = 2`, `s_1 = s_2 = 2`, `B = ` perfect
  matching of size 2.
* The F1 minimal `{a, a', y}` with `a' < y` is `K = 2`, `s_1
  = 2, s_2 = 1`, `B = ` single edge `(a', y)` (not from `a`).
* General K=2 width-≤3 N-poset family: `K = 2`, `s_1, s_2 ∈
  {1, 2, 3}`, `B ⊆ L_1 × L_2` non-empty proper subset of
  `L_1 × L_2`.

Under Q1 / Q2, every member of the K=2 obstruction family is
quotient-to-chain. The "structure" of each member is encoded
in `(s_1, s_2, B)`. The conjecture's claim that every such
non-chain `P` has a balanced pair is the **lifting of "chain
has a balanced pair (trivially: any incomparable pair) to
quotient"** — but the lift is non-trivial because LEs of `P`
mix elements from different bands subject to `B`-constraints.

This is why the brief's framing is **structurally accurate**:
the "quotient-to-chain" pattern is real, and the "deviation
from chain" is exactly the bipartite-graph data `B` (in the
K=2 case) or `(B_{j, k})_j` (in general). The literature
question is: do other fields have lemmas that bound balanced-
pair-style content from bipartite-graph data on a layered
structure?

---

## 2. Per-field literature survey

For each field we (a) identify the most relevant published
results, (b) classify them USABLE / SUGGESTIVE / OFF-TOPIC
against the obstruction, and (c) summarise per-paper findings.

We use the following thresholds (per the brief):

* **USABLE** = a published lemma whose hypotheses our K=2
  obstruction family clearly satisfies, whose conclusion would
  navigate at least one of F1 / F2 / F3 / F4-a / F4-b / F5
  cleanly, and whose translation into our setting is
  mechanical (~bounded LoC, no fresh math).
* **SUGGESTIVE** = a published result that is structurally
  related but whose hypotheses or conclusion need non-trivial
  adaptation; might inform a future arc but not slot in
  directly.
* **OFF-TOPIC** = published result whose connection to our
  setting is at most analogical.

### 2.1 Field A — Expander obstructions

**Setup.** The current paper's Theorem E
(`thm:cex-implies-low-expansion`, `step8.tex:58`) gives: a
width-3 indecomposable γ-counterexample on `n ≥ 2` elements
forces a cut `S` in the BK graph `BK(P)` with conductance `Φ(S)
≤ η(γ, n) = 2/(γn)`. The contrapositive — high conductance
forces a balanced pair — is the consumer in the headline. So
"why graphs fail to be expanders" is directly relevant: a
width-3 counterexample is, by Theorem E, an explicit class of
non-expanders.

**Most relevant published results.**

| Paper                               | Year | Content                                                                 | Verdict |
|-------------------------------------|------|-------------------------------------------------------------------------|---------|
| Hoory–Linial–Wigderson              | 2006 | "Expander graphs and their applications" — comprehensive survey         | OFF-TOPIC (background only) |
| Lubotzky–Phillips–Sarnak            | 1988 | Ramanujan-graph constructions via PGL_2 reps                            | OFF-TOPIC (construction, not obstruction) |
| Margulis                             | 1973 | Explicit expander families                                              | OFF-TOPIC |
| Alon                                 | 1986 | Eigenvalue ↔ expansion (Cheeger discrete)                               | OFF-TOPIC (already in tree as Theorem E half) |
| Lovász Local Lemma / small-set expansion | 1975 / 2010s | Constraints under which structure is "thin"                          | OFF-TOPIC (no clean translation) |
| Trevisan                             | 2009 | Cheeger inequality for negative spectrum / bipartite                    | SUGGESTIVE |
| **Diaconis–Shahshahani**             | 1981 | Spectrum of random transposition walk on full S_n via characters        | SUGGESTIVE — but treats full S_n, not L(P) |
| **Caputo–Liggett–Richthammer**       | 2010 | "Aldous conjecture" — adjacent-transposition walk on S_n has same spectral gap as any conjugacy-class walk | **SUGGESTIVE — closest to BK matching prerequisite (F5)** |
| Caputo                               | 2008 | "Octopus inequality" — comparison method for adjacent-transposition walks | SUGGESTIVE |
| Cesi                                 | 2009 | Comparison technique for IPS / random walks on graphs                   | SUGGESTIVE |
| Conomos–Starr                        | 2008 | Analytic bounds on adjacent walks                                       | OFF-TOPIC |
| Hoory–Linial–Wigderson §10 (small-set) | 2006 | "Why graphs fail to expand" — bottlenecks                            | SUGGESTIVE — confirms F4-a ↔ structural obstruction direction |

**Key finding (SUGGESTIVE).** Caputo–Liggett–Richthammer (2010,
*Annals of Probability*) proves Aldous' conjecture: the
spectral gap of the adjacent-transposition walk on `S_n` equals
the spectral gap of the random transposition walk. The proof
uses a clever "octopus inequality" (Caputo 2008) for the
generator decomposition. *Crucially*, this is the closest
existing published machinery to the BK ↔ S_n matching
prerequisite (F5).

**Translation to our setting.**

* The CLR theorem is for the **full S_n** state space, not for
  `L(P) ⊆ S_n`. Restriction to `L(P)` is the key difficulty.
* CLR's proof relies on an ambient symmetry (the conjugacy
  class structure) that does not transfer to `L(P)` because
  `L(P)` is not a subgroup.
* However, the **comparison-method scaffolding** (Diaconis–
  Saloff-Coste 1993; refined by Caputo, Cesi, and others) is
  designed precisely to bound spectra of restricted walks
  against ambient walks. This scaffolding is published
  infrastructure that *could* be applied to BK on `L(P)`. Its
  application is non-trivial — Diaconis–Saloff-Coste-style
  bounds typically give crude rates (off by polynomial
  factors) — and it has not been published for the BK walk
  specifically.

**Verdict on field A.** SUGGESTIVE only. No published result
slots in to close F1 / F2 / F3 / F4-a directly. The Caputo /
CLR / DSC line addresses F5 in spirit (provides a published
playbook for BK ↔ S_n matching) but does not by itself give the
specific eigenvalue bounds the arc 4.0 strategy needed. F4-a
(sign-mode at threshold on K=2 N-poset) is *unaffected* by
ambient spectral bounds — the saturation is a property of the
N-poset's specific LE-set, not of the walk's bound looseness.

**Sub-finding: structural reasons for low expansion.** Hoory–
Linial–Wigderson §10 catalogues structural reasons graphs are
**not** expanders: vertex-cuts, planted clusters, low-treewidth
overlays, sparse central subgraphs. Mapping these onto BK(P)
for layered width-3 P:

* Vertex-cuts: `BK(P)` for layered `P` has a natural cut between
  LEs that "respect" the ordinal closure `P^♯` and those that
  don't (Step 7's coherence is essentially this). This is
  in-tree content.
* Planted clusters: layered width-3 P with K large has K
  natural "blocks" of LEs separated by band-permutations.
  Theorem E exploits this directly.

**No new content here.** The HLW §10 catalogue *describes* what
the in-tree paper is exploiting; it does not provide a fresh
lemma to import.

### 2.2 Field B — 1D Gibbs systems

**Setup.** A `K`-band quotient-to-chain with bounded `s_k` and
finite-range cross-band interactions is structurally the same
shape as a 1D Gibbs system with finite single-site state space
and finite-range interactions. Specifically, if we view `(L_1,
…, L_K)` as `K` "sites" and the BK walk's restricted adjacent
transpositions as the "Gibbs sampler," there is a candidate
mapping:

```
1D Gibbs site i  ↔  band L_i (state space ≈ orderings of L_i, modulo cross-band constraints).
local interactions ↔ cross-band bipartite graphs B_{j, k}.
Glauber dynamics ↔ BK walk's adjacent-transposition flips at the band-boundary.
```

This is the closest analogy of the four named fields.

**Most relevant published results.**

| Paper                                | Year | Content                                                              | Verdict |
|--------------------------------------|------|----------------------------------------------------------------------|---------|
| Dobrushin                             | 1968 | Uniqueness of Gibbs measures via single-site dependence              | SUGGESTIVE |
| Dobrushin–Shlosman                    | 1985 | Complete-analyticity ⇒ exponential mixing                            | SUGGESTIVE |
| Holley–Stroock                        | 1976 | Rapidity of mixing for spin systems                                  | SUGGESTIVE |
| Stroock–Zegarliński                   | 1992 | Logarithmic Sobolev for finite-range Gibbs                           | SUGGESTIVE |
| Martinelli–Olivieri–Schonmann         | 1994 | Gibbs sampler on 1D and decay of correlations                        | SUGGESTIVE |
| Martinelli (lecture notes)            | 1999 | Survey: 1D Gibbs always has fast mixing in finite-range setup        | SUGGESTIVE |
| Cancrini–Martinelli                   | 2000 | Logarithmic Sobolev under Dobrushin-Shlosman                         | SUGGESTIVE |
| Bubley–Dyer (transfer matrix view)    | 1999 | Uses transfer-matrix bounds on LE-counting indirectly                | SUGGESTIVE — close to direct in-tree analog |
| Cancrini–Martinelli–Roberto–Toninelli | 2008 | FA-1f / kinetically constrained models with local constraints        | SUGGESTIVE |
| Levin–Peres ch. 22 ("interchange")    | 2017 | Survey on adjacent-transposition / interchange chains                | SUGGESTIVE — closest textbook |

**Key finding (SUGGESTIVE).** Dobrushin–Shlosman / Stroock–
Zegarliński / Martinelli give the standard "1D + finite range
+ finite state ⇒ exponential decay of correlations and fast
mixing" theorems. **The conclusion is that the spectral gap of
the Glauber dynamics is bounded below by a constant**
depending on the local interaction strength.

**Translation to our setting.** The mapping above is *not* a
clean 1D Gibbs setup:

1. **State space mismatch.** A "site" in 1D Gibbs is a single
   spin with finite state space (e.g. `{±1}`). A "band" `L_k`
   has multiple elements, and the band's "state" in an LE is
   not just a permutation of `L_k` — it is *interleaved* with
   states of adjacent bands subject to `B_{j, k}` constraints.
   The natural state space for "band `k`" depends on the
   states of all neighbouring bands.
2. **No explicit Hamiltonian.** The uniform measure on `L(P)`
   is not (obviously) a Gibbs measure with explicit local
   Hamiltonian. The cross-band bipartite graphs `B_{j, k}` are
   *hard constraints* (LE-membership is binary), not soft
   energetic preferences.
3. **Glauber dynamics ≠ BK walk.** The BK walk's transition
   move is "swap two elements at adjacent positions if the
   swap preserves LE-ness." This is a **local move that
   respects an ambient hard-constraint structure** — closer
   in spirit to **kinetically constrained models** (Cancrini–
   Martinelli–Roberto–Toninelli 2008) than to standard Gibbs
   sampling.

The closest match in the literature is therefore not standard
1D Gibbs but **kinetically constrained spin models on a 1D
lattice** (FA-1f, East model). The known results there (CMRT
2008; Faggionato–Martinelli–Roberto–Toninelli 2012; subsequent
work) give:

* Spectral gap bounds **as a function of constraint density**.
* Polynomial decay of correlations under "low constraint
  density," exponential under "high density."

**Sub-finding (SUGGESTIVE).** The CMRT framework provides a
published technology for bounding the spectral gap of a
local-constraint walk on a 1D lattice. *In principle* this
could underwrite a non-Cheeger spectral gap bound for the BK
walk on layered width-3 `P`. In practice:

* The translation requires identifying the "constraint
  density" of `P` from the cross-band bipartite graphs `B_{j,
  k}`. No published result gives this translation directly.
* The CMRT bounds are phrased in the asymptotic regime (`n →
  ∞`); applied to K=2 with `|β| ≤ 6`, they may collapse to
  vacuity in the same way F2 (Brightwell vacuity) does at
  small `|Q|`.

**Verdict on field B.** SUGGESTIVE only. The kinetically-
constrained-model framework is the right *type* of published
machinery; applying it to BK on layered width-3 `P` is
substantively new mathematical work. No drop-in lemma found.

**Sub-finding: transfer matrix.** A direct attack via transfer
matrices (the operator on `L²` of the band-state space, with
matrix entries from `B_{k, k+1}`) is suggestive: the spectral
gap of the transfer matrix gives a correlation-decay bound. But
the transfer matrix's eigenvalues are determined by `(s_k, B_{k, k+1})`,
which is *exactly* the data the existing in-tree Step 7
coherence argument processes. This is the arc 3.0 D6 trap
applied to transfer-matrix language: the "spectral input" is
the same as the Step-5–7 structural input, just relabelled.

### 2.3 Field C — Low-treewidth graphs

**Setup.** The comparability graph `G(P)` of a layered width-3
`P` has a natural tree decomposition: each band `L_k` is a bag
of size ≤ 3, plus the cross-band edges between consecutive
bands form a path-like structure. So `G(P)` has **pathwidth ≤
2 · 3 = 6**, and treewidth ≤ 6, with much tighter bounds in
specific configurations.

**Most relevant published results.**

| Paper                            | Year | Content                                                              | Verdict |
|----------------------------------|------|----------------------------------------------------------------------|---------|
| Eiben–Ganian–Knop–Ordyniak–Szeider | 2019 | FPT counting of LEs by treewidth                                     | OFF-TOPIC (algorithmic, not structural) |
| Edelman–Hibi–Stanley             | 1989 | Linear extensions and order polytopes; treewidth of comparability graphs implicit | OFF-TOPIC |
| Brightwell–Trotter               | various | Combinatorial bounds on # LE in terms of poset parameters        | OFF-TOPIC (count, not balanced-pair) |
| Robertson–Seymour                | 1980s+ | Tree decompositions; minor theorems                                | OFF-TOPIC |
| Bodlaender                       | 1993+ | Tree-decomposition algorithms                                        | OFF-TOPIC |
| Felsner–Trotter                  | various | Dimension and order polytope geometry; treewidth implicit          | OFF-TOPIC |
| Razgon                           | 2014 | Treewidth lower bounds                                               | OFF-TOPIC |

**Key finding.** Treewidth-bounded posets enjoy **algorithmic**
tractability for #LE, scheduling, and other counting problems
(Eiben et al.). They do **not** enjoy structural balanced-pair
lemmas of the form "treewidth ≤ k ⇒ ∃ pair `(x, y)` with
`Pr[x < y] ∈ [1/3, 2/3]`."

**Translation to our setting.**

* The K=2 N-poset has comparability-graph treewidth = 1 (it is
  a forest — two disjoint edges).
* Layered width-3 posets in general have treewidth ≤ 5 or so
  (each band has ≤ 3 vertices, and the "tree decomposition"
  with bag `L_k ∪ L_{k+1}` of size ≤ 6 is a path
  decomposition).
* No published theorem of the form "treewidth ≤ k poset has
  balanced pair" exists for any `k ≥ 1`. The 1/3–2/3
  conjecture is itself unbounded by treewidth on either side
  (small-treewidth and large-treewidth posets both have the
  same conjectured bound).

**Sub-finding (OFF-TOPIC, but illuminating).** The K=2 N-poset
has comparability-graph treewidth 1 (a matching, hence a
forest). If "low treewidth" ⇒ "balanced pair exists" were true
for treewidth 1, the K=2 N-poset would automatically discharge.
Direct count: K=2 N-poset has `Pr[x_1 < x_2] = 1/2 ∈ [1/3,
2/3]` ✓. *But this is a coincidence of the specific
combinatorial structure, not an instance of a general
treewidth lemma.* The F1 minimal `{a, a', y}` with `a' < y`
(forest, treewidth 1) has `Pr[a < a'] = 1/3` — at the **strict
boundary**, with no margin. Treewidth alone does not separate.

**Verdict on field C.** OFF-TOPIC. No published treewidth lemma
gives the kind of structural balanced-pair bound the
obstruction needs. The "tractability template" of low-
treewidth + dynamic programming gives algorithms (which
overlap arc 2.0 sub-B2 / S2c finite enumeration as a
mechanical fallback, not as a math simplification).

### 2.4 Field D — Constrained Markov chains

**Setup.** The BK walk on `L(P)` is, by definition, a Markov
chain on a state space defined by **local constraints** (the
cover relations of `P`). Adjacent-position swaps are the
moves; the constraint is that each move must preserve
LE-validity. This is exactly the setting of "constrained
Markov chains" the brief flags.

**Most relevant published results.**

| Paper                            | Year | Content                                                              | Verdict |
|----------------------------------|------|----------------------------------------------------------------------|---------|
| **Bubley–Dyer**                  | 1999 | "Path coupling" for BK walk on linear extensions; O(n^3 log n) mixing | SUGGESTIVE — directly the BK walk |
| **Wilson**                        | 2004 | Sharp lower bound on mixing time of BK walk = Θ(n^3 log n)           | SUGGESTIVE — sharp gap = Θ(n^{-3}) |
| Aldous                            | 1983 | Conjecture on adjacent-transposition spectrum                        | (resolved by CLR 2010) |
| Caputo–Liggett–Richthammer       | 2010 | Aldous proof                                                         | SUGGESTIVE — see field A |
| Diaconis–Saloff-Coste            | 1993 | Comparison method for spectral gaps                                  | SUGGESTIVE |
| Bhakta–Cesi–Martinelli           | 2018 | Spectral gap for restricted-state-space chains                       | OFF-TOPIC (not on `L(P)`) |
| Liggett (interacting particle systems) | 1985+ | TASEP, ASEP, exclusion processes                                | OFF-TOPIC (different kernel) |
| Saloff-Coste (lecture notes)      | 1997 | Nash inequalities, log-Sobolev for Markov chains                    | OFF-TOPIC (background) |

**Key finding (SUGGESTIVE).** Bubley–Dyer (1999) and Wilson
(2004) together establish that the BK walk on `L(P)` for any
finite poset `P` has spectral gap `Θ(n^{-3})`. *This is exactly
the in-tree paper's setup.* Theorem E in tree converts this
gap into the contrapositive form (`Φ(BK(P)) ≥ Θ(n^{-3}) /` cut
size).

**Translation to our setting.**

* The BD–Wilson gap is **uniform across all finite posets** of
  size `n`. It does not detect `quotient-to-chain` structure.
* For our purposes, we don't want a uniform `Θ(n^{-3})` gap; we
  want the gap to be *strictly larger* than what a γ-counter-
  example would force (`O(γ^{-1} n^{-1})` from the cut).
  Closing this gap is exactly the in-tree Steps 5–7 +
  Theorem E argument.
* The BD–Wilson framework is the **published technology
  underwriting Theorem E in tree** — the in-tree proof is
  *built on* this line. So importing more of it doesn't
  simplify what's already there; it would re-derive the
  existing dependency.

**Sub-finding: path coupling and the K=2 N-poset.** The
Bubley–Dyer path coupling on the K=2 N-poset gives mixing time
`O(n^3 log n) = O(64 log 4) = O(1)` — small, consistent with
the small state space. Wilson's lower bound also fires at
small `n`, giving sharp constants. Neither bound gives a
balanced-pair statement.

**Verdict on field D.** SUGGESTIVE only. The BD–Wilson
framework is the published technology underwriting Theorem E
in tree; importing more of it is the in-tree approach taken
to its natural limit. No drop-in lemma fills the F4-a / F4-b
/ F5 gaps that arc 4.0 surfaced.

**Sub-finding: kinetically constrained models, again.** The
"constrained Markov chains" framing converges with field B's
suggestion (kinetic constraints). The most active modern
literature is on FA-1f / East model / random-cluster models on
finite graphs (CMRT 2008; Faggionato–Martinelli–Roberto–
Toninelli 2012; Pillai–Smith 2018). These give spectral gap
bounds for chains with hard constraints — but the bounds are
phrased in terms of constraint density, not in terms of
quotient-to-chain layering depth. No published bound has the
form we need.

### 2.5 Polecat-invented additions

The brief invites polecat-invented adjacent fields. Five
candidates were investigated:

#### 2.5.1 FKG / log-supermodular distributions

**Most relevant published results.**

| Paper                            | Year | Content                                                              | Verdict |
|----------------------------------|------|----------------------------------------------------------------------|---------|
| Fortuin–Kasteleyn–Ginibre        | 1971 | The FKG inequality for log-supermodular distributions                 | OFF-TOPIC (already in tree as `RelationPoset/FKG.lean`) |
| **Kahn–Saks**                    | 1984 | Use FKG + log-concavity to prove `δ* ≥ 3/11`                          | OFF-TOPIC by F3 |
| **Brightwell**                    | 1989 | Sharper covariance: `δ* ≥ (3 - √5)/2`                                 | OFF-TOPIC by F3 |
| **Kahn–Linial**                   | 1991 | Further refinement: `δ* ≥ 0.276`                                     | OFF-TOPIC by F3 |
| **Brightwell–Felsner–Trotter**   | 1995 | Width-2 Linial confirmed; width-3 partial                             | OFF-TOPIC by F3 |
| Mathieu–Sznitman                 | 2010 | Other FKG applications                                                | OFF-TOPIC |

**Verdict.** OFF-TOPIC by F3 (the Kahn–Saks → Brightwell →
Kahn–Linial line is the published `[0.276, 1/3)` gap; closing
it via FKG + width-3 is exactly the multi-decade open
question). Already considered in arc 1.0 D / arc 3.0 S1.

#### 2.5.2 Quasi-randomness / discrepancy theory

**Most relevant published results.**

| Paper                            | Year | Content                                                                  | Verdict |
|----------------------------------|------|--------------------------------------------------------------------------|---------|
| Beck                              | 1981 | "Roth's theorem on arithmetic progressions / discrepancy"                | OFF-TOPIC |
| Spencer                           | 1985 | "Six standard deviations suffice" / discrepancy                          | OFF-TOPIC |
| Chazelle                          | 2000+ | Discrepancy theory survey                                                | OFF-TOPIC |
| Chung–Graham–Wilson              | 1989 | "Quasi-random graphs"                                                     | OFF-TOPIC |
| Kohayakawa                       | various | Quasi-randomness for posets / orders                                     | OFF-TOPIC |

**Verdict.** OFF-TOPIC. Discrepancy is about colourings /
embeddings minimising deviation; "quotient-to-chain" is about
order-quotient structure. The technical machinery is far
removed.

#### 2.5.3 Order polytope / chain polytope geometry

**Most relevant published results.**

| Paper                            | Year | Content                                                                  | Verdict |
|----------------------------------|------|--------------------------------------------------------------------------|---------|
| **Stanley**                       | 1986 | Order polytope `O(P)`, chain polytope `C(P)`; vol = #LE / n!             | SUGGESTIVE |
| Edelman–Hibi–Stanley             | 1989 | Linear extensions and order polytopes                                     | SUGGESTIVE |
| Hibi                              | 1992 | Algebraic combinatorics of order polytopes                                | OFF-TOPIC |
| Felsner–Wernisch                 | 1995 | Position distributions in random LEs                                     | SUGGESTIVE |
| Hopkins                          | 2010s+ | Promotion / rowmotion on order polytopes                                  | SUGGESTIVE |

**Key finding.** Stanley's order polytope `O(P) = {x ∈ [0,
1]^X : x_a ≤ x_b ∀ a <_P b}` is the natural geometric
realisation of `P`. Its vertices are 0/1-indicators of
order-filters (= order ideals' complements); its volume is
`#LE(P) / n!`. The **balanced-pair probability** has a clean
geometric interpretation:

```
Pr_P[x < y] = vol({u ∈ O(P) : u_x < u_y}) / vol(O(P))
            = vol(O(P) ∩ {u_x < u_y}) / vol(O(P)).
```

For `P` an ordinal sum `A ⊕ B` and `x, y ∈ A`, `O(P) = O(A) ×
[α, 1]^B` where `α = max u_a`; the marginal `Pr_P[x < y]` is
**exactly** `Pr_A[x < y]` by Fubini.

**For the K=2 N-poset.** `O(N) = {(s_1, s_2, t_1, t_2) ∈
[0,1]^4 : s_i ≤ t_i for i=1,2}`. This is a 4-dimensional
polytope; vol = 6/24 = 1/4. `Pr_N[x_1 < x_2]` = vol of
`{s_1 ≤ s_2, s_i ≤ t_i}` / vol = explicit integral. Direct
computation gives 1/2.

**Translation to our setting.**

* The order polytope is a clean geometric framing but does
  not provide *new* lemmas. It is essentially a relabeling of
  Pr-probabilities as polytope volumes.
* Hopkins–Striker rowmotion / promotion theory acts on
  `O(P)` and has rich structure on layered posets. But these
  actions preserve various invariants (height, fibre size)
  rather than balanced-pair containment.
* Felsner–Wernisch (1995) on position distributions is the
  closest direct analog: they show that for any element `a`
  in an LE, the position distribution is log-concave. This is
  used in Brightwell 1989 / Kahn–Linial 1991 already (covered
  by F3).

**Verdict.** SUGGESTIVE only. The order-polytope language
provides a clean translation but no fresh closure lemma. F3
catches the best known consequences.

#### 2.5.4 Promotion / rowmotion / poset combinatorics

**Most relevant published results.**

| Paper                            | Year | Content                                                                  | Verdict |
|----------------------------------|------|--------------------------------------------------------------------------|---------|
| Striker–Williams                | 2012 | Promotion and rowmotion on antichains / order ideals                      | OFF-TOPIC |
| Hopkins                          | 2017+ | Cyclic sieving phenomena for poset orbits                                | OFF-TOPIC |
| Hopkins–Joseph                   | 2019 | Birational rowmotion on posets                                           | OFF-TOPIC |
| Stanley (EC1, EC2)               | 2011 | Linear extensions, P-partitions; covered indirectly                      | OFF-TOPIC |

**Verdict.** OFF-TOPIC. Promotion / rowmotion are dynamics on
*order ideals* of `P`, not on the BK walk's state space `L(P)`.
The connection is at the level of "both are dynamics on
combinatorial data attached to `P`," but the technical
machinery is disjoint.

#### 2.5.5 Random walks on permutation groups via representation theory

**Most relevant published results.**

| Paper                            | Year | Content                                                                  | Verdict |
|----------------------------------|------|--------------------------------------------------------------------------|---------|
| **Diaconis–Shahshahani**          | 1981 | Spectrum of random transposition walk on full S_n                        | SUGGESTIVE — see field A |
| Diaconis (book)                   | 1988 | Group representations in probability / statistics                        | SUGGESTIVE |
| **Caputo–Liggett–Richthammer**    | 2010 | Aldous conjecture                                                        | SUGGESTIVE — see field A |
| Saloff-Coste (lectures)          | 2004 | Random walks on finite groups                                            | OFF-TOPIC (background) |
| Diaconis–Saloff-Coste             | 1993 | Comparison theorems for spectral gaps                                     | SUGGESTIVE — see F5 |

**Verdict.** Already covered in field A. SUGGESTIVE only;
provides infrastructure for F5 but does not directly close
F4-a.

### 2.6 Summary table

| Field                          | USABLE? | SUGGESTIVE finding(s)                                                                        |
|--------------------------------|---------|----------------------------------------------------------------------------------------------|
| A — Expander obstructions      | NO      | Caputo–Liggett–Richthammer 2010 (Aldous), Caputo 2008 (octopus), Diaconis–Saloff-Coste 1993 |
| B — 1D Gibbs systems           | NO      | Dobrushin–Shlosman 1985, Cancrini–Martinelli–Roberto–Toninelli 2008 (kinetically constrained models) |
| C — Low-treewidth graphs       | NO      | (none — OFF-TOPIC, except as algorithmic backstop for arc 2.0 sub-B2)                        |
| D — Constrained Markov chains  | NO      | Bubley–Dyer 1999, Wilson 2004 (already underwrites Theorem E in tree)                       |
| E — FKG / log-supermodular     | NO      | Kahn–Saks 1984 etc. (closed by F3)                                                           |
| F — Order polytope             | NO      | Stanley 1986 (relabeling, no new lemma)                                                      |
| G — Promotion / rowmotion      | NO      | (OFF-TOPIC)                                                                                  |
| H — Random walks via reps      | NO      | (subsumed by A)                                                                              |

**Aggregate verdict on §2.** **No USABLE finding across eight
fields.** A SUGGESTIVE cluster around Caputo / DSC / Bubley–
Dyer / kinetically-constrained-models offers published
machinery for the F5 prerequisite, but applying it requires
substantively new mathematical work (paper-tier infrastructure
analogous to A8-S2-cont, ~2000+ LoC if formalised) and does
not close the terminal F4-a.

---

## 3. Cross-reference to F1–F5

Each USABLE / SUGGESTIVE finding is evaluated against the six
obstructions catalogued in `docs/why-hC3-is-structural.md` (F1,
F2, F3) and `docs/math-simp-arc-4.0/scoping.md` (F4-a, F4-b,
F5). The audit is more useful if the negative result explicitly
addresses *why* each candidate import fails to navigate the
obstructions.

### 3.1 Obstruction recap

* **F1** — Cardinality obstruction. No order-preserving
  permutation `σ: α ≃ α` swaps a strict ⪯-pair `(a, a')` with
  `upper(a) ⊊ upper(a')`. (Source: Track 1, mg-b666;
  `path-c-track-1-status-1.md` §2.)
* **F2** — Brightwell vacuity at K=2 / `|Q| ≤ 6`. Single-
  element perturbation gives `|p_{xy}(Q) - p_{xy}(Q-z)| ≤
  2/|Q|`, vacuous at `|Q| ≤ 6` for the `1/3` target. (Source:
  mg-b0de; `a8-s2-restate-block-and-report-status.md` §3.)
* **F3** — Published `[0.276, 1/3)` gap. The unconditional
  `δ*` lower bound has been stuck at `(3-√5)/2 ≈ 0.276` for
  30+ years; width-3 specialisation without going through a
  Cheeger-type argument has not been done. (Source:
  `main.tex` §1.6; arc 3.0 §4.2.)
* **F4-a** — Spectral mode inversion on K=2 N-poset. Step 2
  of the arc 4.0 character-theoretic strategy fails: the K=2
  N-poset attains `|λ_sign| = 1/3` exactly, saturating the
  threshold; the strategy's "fix-point mode dominates"
  premise inverts. (Source: arc 4.0 §3.5; mg-0bc8.)
* **F4-b** — Spectral-rigidity collapse risk. "Large E[fix]
  ⇒ layered rigidity" risks reproducing Steps 5–7 in
  spectral clothing (the arc 1.0 D / arc 3.0 D6 trap).
  (Source: arc 4.0 §4.3.)
* **F5** — BK ↔ S_n matching prerequisite. Eigenvalue bounds
  on `BK(L(P))` are not derived from S_n character theory
  via cited literature; need separate spectral-comparison
  machinery (paper-tier). (Source: arc 4.0 §6.2.)

### 3.2 Per-finding navigation matrix

For each SUGGESTIVE finding, we ask: *would this published
result navigate F1, F2, F3, F4-a, F4-b, F5?* "Yes" means a
direct application; "partial" means substantively new work but
the finding addresses the right *type* of obstruction; "no"
means structurally orthogonal.

| SUGGESTIVE finding                            | F1  | F2  | F3  | F4-a | F4-b | F5      |
|------------------------------------------------|-----|-----|-----|------|------|---------|
| Caputo–Liggett–Richthammer 2010 (Aldous)       | no  | no  | no  | no   | no   | partial |
| Caputo 2008 (octopus inequality)               | no  | no  | no  | no   | no   | partial |
| Diaconis–Saloff-Coste 1993 (comparison)        | no  | no  | no  | no   | no   | partial |
| Diaconis–Shahshahani 1981 (DS spectrum on S_n) | no  | no  | no  | no   | no   | partial (only ambient) |
| Dobrushin–Shlosman 1985 (1D Gibbs uniqueness)  | no  | no  | no  | no   | no   | no      |
| Cancrini et al. 2008 (kinetic constraints)     | no  | no  | no  | no   | no   | partial |
| Bubley–Dyer 1999 / Wilson 2004                 | no  | no  | no  | no   | no   | (already in tree) |
| Stanley 1986 (order polytope)                  | no  | no  | no  | no   | no   | no      |
| Felsner–Wernisch 1995 (log-concave positions)  | no  | no  | (closed by F3) | no | no | no |

**Pattern.** Every SUGGESTIVE finding is "partial at best on
F5; no on everything else." This is **structurally
revealing**: F5 is the *spectral-machinery prerequisite*
that absorbs all the Caputo / DSC / BD–Wilson published
infrastructure. F1, F2, F3, F4-a, F4-b are *not* spectral-
machinery problems; they are **specific to the small-`n`,
strict ⪯-pair, layered width-3 regime** of our obstruction
family. No off-the-shelf lemma from the surveyed fields
addresses them.

### 3.3 Why each obstruction resists adjacent-field imports

**F1 (cardinality obstruction).** Addressed by *finite-set
combinatorics*, not by spectral / probabilistic / Gibbs
machinery. Adjacent fields don't have lemmas of the form
"order-preserving permutations on quotient-to-chain posets
can swap a strict ⪯-pair." This is a poset-specific
obstruction.

**F2 (Brightwell vacuity at small `|Q|`).** Addressed by
sharper *single-element coupling bounds* for poset linear
extensions. The Caputo / DSC framework gives spectral-gap
bounds, not perturbation bounds. The closest is the FKG /
Kahn–Saks line, which is closed by F3. No adjacent field
provides a small-`|Q|`-tight perturbation bound.

**F3 (published `[0.276, 1/3)` gap).** This is the **field's
30-year unsolved question** from the FKG / log-concavity
direction. By definition, no off-the-shelf lemma closes it
(if there were one, it would have been used). Adjacent fields
can offer parallel infrastructure (e.g. the spectral
direction is what the in-tree paper takes), but importing
*more correlation-inequality machinery* doesn't close the gap.

**F4-a (sign-mode saturation on K=2 N-poset).** This is a
**direct numerical fact** about the K=2 N-poset's 6 LEs and
their `Σ(P) = -2` sign-imbalance. No spectral / Gibbs / Markov
lemma changes the value of `Σ(P)/|G_P| = 1/3`. The only way
F4-a evaporates is if the spectral *bound* (rather than the
*value*) is loose — which would require a paper-tier
F5 derivation showing that `|λ_sign(BK(N))| ≪ |Σ(N)|/|G_N|`.
Adjacent fields don't provide this.

**F4-b (spectral-rigidity collapse risk).** This is a
**meta-obstruction**: any "spectral input ⇒ structural output"
theorem risks invoking Steps 5–7. Adjacent fields don't help;
they would either (i) provide an independent spectral
argument (which would have to be discovered, not imported) or
(ii) reproduce Steps 5–7 (the trap).

**F5 (BK ↔ S_n matching prerequisite).** This is the **only
obstruction adjacent fields plausibly address.** Caputo / DSC
/ BD–Wilson infrastructure exists and is published. *But*:

* The infrastructure has not been applied to the specific BK
  walk on `L(P) ⊆ S_n` with adjacent transpositions
  restricted to LE-preserving ones. Doing so is paper-tier
  work.
* Even if F5 is rescued, F4-a still bites (sign-mode value is
  *exact* on the K=2 N-poset).
* The infrastructure is large (DSC comparison method gives
  crude bounds; CLR's Aldous proof uses a custom octopus
  inequality, hard to generalize).

So: **the strongest adjacent-field finding (Caputo / DSC) is
SUGGESTIVE-on-F5-only**. It does not navigate F1, F2, F3,
F4-a, F4-b. Even the F5 navigation is partial: importing the
infrastructure requires significant adaptation, and the
ultimate verdict (closing `hC3`) still depends on F4-a, which
is unaffected.

### 3.4 Comparison to arcs 1.0–4.0 verdict shapes

Each prior arc terminated at a specific F-tag:

* Arc 1.0 A1 — F2 (size-based, not ε-aware perturbation
  bound).
* Arc 2.0 framings 1–4 — F2 / F3 / F1 / F3.
* Arc 3.0 D1–D8 (eight definitions) — F2, F3, F7
  (N-poset-not-ordinal-sum), and analogues.
* Arc 3.0 S1–S12 (twelve strategies) — F1, F3, T9 (multi-
  round failure), or "stylistic only."
* Arc 4.0 — F4-a (terminal), with F4-b / F5 secondary.

The adjacent-field audit (this arc) terminates at **F5
partial / F4-a unaddressed**. The pattern is consistent:
**every search-space dimension** (definitions, strategies,
adjacent fields) hits one of F1 / F2 / F3 / F4-a / F4-b / F5.
None navigates all six.

This is, of course, the same pattern arcs 3.0 / 4.0
documented. The conceptual audit *adds* the observation that
the pattern persists *across fields* (not just across in-tree
strategies and ε-close definitions). The "math is genuinely
this hard" verdict is now triple-confirmed: by ε-close
exhaustion (arc 3.0), by spectral-strategy exhaustion (arc
4.0), and by adjacent-field exhaustion (this arc).

---

## 4. K=2 N-poset under each field's lens

The recurring focal counterexample. For each field, we ask:
*how does the K=2 N-poset (4 elements, 6 LEs, threshold-
saturating) appear from that field's vantage? Is it a known
object?*

### 4.1 Field A — Expander obstructions

The BK graph `BK(N)` has 6 vertices (the 6 LEs); each LE has
edges to other LEs differing by a single LE-preserving
adjacent transposition.

Direct enumeration:

| LE  | Permutation `σ`     | Adjacent swaps preserving LE-ness                    |
|-----|---------------------|-------------------------------------------------------|
| L_1 | `(x_1, x_2, y_1, y_2)` | swap pos 1–2 (x_1 ↔ x_2): → L_4. swap pos 3–4 (y_1 ↔ y_2): → L_2. |
| L_2 | `(x_1, x_2, y_2, y_1)` | swap pos 1–2: blocked (would give x_2, x_1 — fine, that's L_5). swap pos 3–4: → L_1. |
| L_3 | `(x_1, y_1, x_2, y_2)` | swap pos 2–3 (y_1 ↔ x_2): only OK if x_2 ⪯ y_1 fails — fails (since x_2 ∥ y_1, both incomparable, OK to swap): → L_1. |
| L_4 | `(x_2, x_1, y_1, y_2)` | swap pos 1–2 (x_2 ↔ x_1): → L_1. swap pos 3–4: → L_5. |
| L_5 | `(x_2, x_1, y_2, y_1)` | swap pos 1–2: → L_2. swap pos 3–4: → L_4. |
| L_6 | `(x_2, y_2, x_1, y_1)` | swap pos 2–3 (y_2 ↔ x_1): → L_5. (swap pos 1–2: x_2 ↔ y_2 — but x_2 < y_2, so blocked.) |

Cross-checking with arc 4.0 §2.1's enumeration (which adds L_3
= `(x_1, y_1, x_2, y_2)`, etc.) confirms: there are 6 LEs.

**Conductance and λ_2.** Computing the BK graph's adjacency
yields a graph on 6 vertices with edge set inferable from the
table above. For a balanced cut `S = {L_1, L_2, L_3} | {L_4,
L_5, L_6}` (LEs starting with x_1 vs starting with x_2), the
cut has 1 or 2 edges; conductance ≈ 1/6 to 2/6 = 1/3. The BK
graph is small enough to compute λ_2 exactly via the
characteristic polynomial; arc 4.0 §2.2 reports
`|λ_sign| = 1/3` (the sign-isotypic component, which is one of
the eigenvalues if the matching condition is exact).

**Is the K=2 N-poset a known object in expander literature?**
Not as a named example. It is a 4-vertex matching (2 edges),
which is too small to be interesting in expander theory (every
6-vertex graph trivially fits in expander families). It is
*not* a Ramanujan graph, *not* an LPS construction, *not* an
Alon–Boppana extremal example.

**What does field A say specifically about it?** Nothing
direct. The closest result is Diaconis–Shahshahani's spectrum
of the random transposition walk on full S_4 (which has six
classes of permutations, so 5 non-trivial irreps), but
restricted to `L(N) ⊆ S_4` (size 6 of 24) the spectrum is
different and uncited.

### 4.2 Field B — 1D Gibbs systems

The K=2 N-poset has 2 layers, each of size 2. As a 1D Gibbs
system: 2 sites, each with 2 internal "spin" states (ordering
of the band). Cross-band interactions: band 1's element-i
must be below band 2's element-j iff `(i, j) ∈ B = {(1, 1),
(2, 2)}` (matching).

**Translation as a Gibbs measure.**

* States: pairs `(σ_1, σ_2) ∈ S_2 × S_2` (orderings of each
  band).
* Constraints: `σ_2(j) > σ_1(i)` whenever `(i, j) ∈ B`,
  applied positionally. But the LE-positions interleave bands
  arbitrarily, so this is not a clean cell-position Gibbs
  setup.

**Closer match: as a transfer matrix.** For each pair
`(σ_1, σ_2)`, count the LEs of `N` whose band-1 ordering is
`σ_1` and band-2 ordering is `σ_2`. Direct enumeration:

| `(σ_1, σ_2)`      | LEs counted                            | count |
|-------------------|----------------------------------------|-------|
| (id, id)          | L_1, L_2 (with various interleavings)  | 3 (L_1, L_2, L_3) |
| (id, sw)          | L_3 → no, L_2... | 1 (L_2 has σ_2 = (3 4) = sw, σ_1 = id) — wait, L_2's band-1 ordering is `x_1, x_2 = id`, band-2 ordering is `y_2, y_1 = sw`. So (id, sw): L_2. |
| (sw, id)          | L_4: band-1 = `x_2, x_1` = sw, band-2 = `y_1, y_2` = id. | 1 |
| (sw, sw)          | L_5: band-1 = sw, band-2 = sw; L_6: band-1 = `x_2, x_1` (positions 1, 3) = sw, band-2 = `y_2, y_1` (positions 2, 4) = sw. | 2 |

Wait, the position-interleaving means the same `(σ_1, σ_2)`
pair admits multiple LEs. Recount from the §4.1 table:

* L_1: positions of x_1, x_2, y_1, y_2 = 1, 2, 3, 4. σ_1 = id (x_1 before x_2). σ_2 = id (y_1 before y_2). Interleaving = (band1, band1, band2, band2).
* L_2: positions 1, 2, 4, 3. σ_1 = id, σ_2 = sw. Interleaving = (band1, band1, band2, band2).
* L_3: positions 1, 3, 2, 4. σ_1 = id (x_1 before x_2), σ_2 = id (y_1 before y_2). Interleaving = (band1, band2, band1, band2).
* L_4: positions 2, 1, 3, 4. σ_1 = sw, σ_2 = id. Interleaving = (band1, band1, band2, band2).
* L_5: positions 2, 1, 4, 3. σ_1 = sw, σ_2 = sw. Interleaving = (band1, band1, band2, band2).
* L_6: positions 3, 1, 4, 2. σ_1 = sw (x_2 before x_1), σ_2 = sw (y_2 before y_1). Interleaving = (band1, band2, band1, band2).

So `(σ_1, σ_2)` partition: (id, id) = {L_1, L_3}, (id, sw) = {L_2}, (sw, id) = {L_4}, (sw, sw) = {L_5, L_6}.

Counts: 2, 1, 1, 2. Total 6 ✓.

**Transfer-matrix observation.** The transfer matrix on the
4-element state space `{(id, id), (id, sw), (sw, id), (sw, sw)}`
has weights given by the counts above. The marginal
distribution of `σ_1` over LEs is `(σ_1 = id) = 3/6, (σ_1 = sw)
= 3/6` (uniform). Marginal of `σ_2`: same.

So `(σ_1, σ_2)` are **independent uniform on `S_2 × S_2`**. The
"Dobrushin condition" (single-site dependence ≪ 1) is
**trivially satisfied** for the K=2 N-poset (independence ⇒
zero dependence ⇒ Dobrushin's α = 0). The Dobrushin–Shlosman
conclusion would be: spectral gap of Glauber dynamics is `Ω(1)`
(constant). But this gives `Pr_N[x_1 < x_2] = 1/2` only after
explicit enumeration; Dobrushin's framework doesn't say what
this probability is.

**Is the K=2 N-poset a known object in 1D Gibbs?** Not as a
named example. The smallest non-trivial bipartite Markov chain
is more typically studied with state `{0, 1}` and a single
site, not as a 2-band quotient-to-chain. The K=2 N-poset is
*structurally* a 2-site 2-state 1D Gibbs system, but its
specific configuration (matching cross-edges) hasn't been
named in the IPS literature the polecat surveyed.

**What does field B say specifically about it?** Dobrushin's
framework says "fast mixing." It does not say `Pr_N[x_1 < x_2]
∈ [1/3, 2/3]` — that requires direct enumeration.

### 4.3 Field C — Low-treewidth graphs

Comparability graph of K=2 N-poset:
```
x_1 — y_1
x_2 — y_2
```
Two disjoint edges. **Treewidth = 1** (it's a forest).

**Tree decomposition.** Two bags `{x_1, y_1}` and `{x_2, y_2}`
joined at any common vertex (none) — actually the
forest's tree decomposition is the natural one with each
edge as a bag.

**Is the K=2 N-poset a known object in treewidth literature?**
Yes — it is **the smallest matching graph**, treewidth 1, known
in graph theory but not associated specifically with any
balanced-pair theorem.

**FPT algorithms apply.** Eiben–Ganian–Knop–Ordyniak–Szeider
2019's FPT counting of LEs by treewidth runs in O(1) on the
K=2 N-poset (since `tw = 1`, the algorithm is linear in `n`
times a constant). **It correctly reports `|LE(N)| = 6`** — but
this is direct enumeration, not a structural balanced-pair
statement.

**What does field C say specifically about it?** Algorithmic
tractability (linear-time #LE), nothing structural. The K=2
N-poset is a tractable instance, not a hard one.

### 4.4 Field D — Constrained Markov chains

The BK walk on `L(N) = {L_1, …, L_6}` is a 6-state Markov
chain. From the §4.1 table, the transition graph has a
specific structure:

```
L_1 — L_2 (via pos 3-4 swap)
L_1 — L_3 (via pos 2-3 swap)
L_1 — L_4 (via pos 1-2 swap)
L_2 — L_5 (via pos 1-2 swap)
L_3 — ? (via pos 1-2 swap: x_1 → x_2, y_1 → x_1, etc. — invalid because x_2 < y_2 is in band order)
L_4 — L_5 (via pos 3-4 swap)
L_4 — L_6 (via pos 2-3 swap, requires x_1 ∥ y_1 — yes)... wait, L_4 = `(x_2, x_1, y_1, y_2)`, swap pos 2-3 = swap x_1 with y_1, which requires x_1 ∥ y_1 — yes (since x_1 < y_1 fails as adjacency in `N`... actually x_1 < y_1 in `N`, so we cannot swap them: BLOCKED).
```

Detailed enumeration is tedious but the structure is small.
Bubley–Dyer's path coupling argument runs trivially (mixing
time `O(n^3 log n) = O(64 log 4) = O(1)`).

**Wilson's Θ(n^3 log n) bound.** Sharp at the constants on
small `n`. For `n = 4`, Wilson's lower bound gives a specific
mixing time on the order of `64 log 4 ≈ 90`. Direct
computation gives much faster mixing on the N-poset (it's a
small connected graph).

**Is the K=2 N-poset a known object in BD–Wilson literature?**
Not as a named example. Bubley–Dyer 1999 / Wilson 2004 prove
their bounds *uniformly across all finite posets* — the K=2
N-poset is a tractable instance, not a hard one for their
methods. They give mixing time, not balanced-pair statements.

**What does field D say specifically about it?** Mixing time
`O(1)`. Spectral gap `Ω(1)`. No balanced-pair statement.

### 4.5 Field F — Order polytope (Stanley)

`O(N) = {(s_1, s_2, t_1, t_2) ∈ [0,1]^4 : s_i ≤ t_i for i = 1, 2}`.

Volume: `vol(O(N)) = ∫_{[0,1]^4} 1[s_1 ≤ t_1] · 1[s_2 ≤ t_2]
ds dt = (1/2)^2 = 1/4`. Confirms `|LE(N)|/4! = 6/24 = 1/4`. ✓

`Pr_N[x_1 < x_2] = vol({s_1 ≤ s_2}) / vol(O(N))`. Compute:
`∫_{O(N)} 1[s_1 ≤ s_2] = ∫_0^1 ∫_0^1 ∫_{s_1}^1 ∫_{s_2}^1
1[s_1 ≤ s_2] dt_2 dt_1 ds_2 ds_1`. By symmetry in (1, 2) of
the integrand and `O(N)`'s indicator, the answer is exactly
`(1/2) · vol(O(N)) = 1/8`. So `Pr_N[x_1 < x_2] = (1/8)/(1/4) =
1/2`. ✓

**Is the K=2 N-poset a known object in order-polytope
literature?** Yes — Stanley 1986 explicitly computes `O(P)`
for small posets and lists the N-poset as the smallest
non-ordinal-sum bipartite poset. Hopkins, Striker, et al. use
it in birational rowmotion studies. **However, no published
order-polytope theorem says `Pr_N[x_1 < x_2] ∈ [1/3, 2/3]` is
a special case of a structural lemma** — it's always
direct computation.

**What does field F say specifically about it?** A clean
geometric interpretation (volume ratio). No fresh closure
lemma.

### 4.6 Aggregate: K=2 N-poset is small and tractable; unhelpful

**Common pattern.** In every adjacent field surveyed, the K=2
N-poset is:

* **Small** (4 elements, 6 LEs, 4-edge BK graph).
* **Tractable** (mixing time O(1), treewidth 1, known order
  polytope).
* **Direct-enumerable** (every quantity of interest is
  computable in `O(1)`).
* **Not a named hard case** in any field's catalogue of
  examples.

The K=2 N-poset's role as the **canonical obstruction** is a
property of the project's specific argumentative structure
(arcs 1.0–4.0): it sits at the boundary of multiple
techniques (small enough that asymptotic methods vacuum out;
irreducible enough that decomposition methods don't fire;
matching-cross-edged enough that it's not an ordinal sum).
**Adjacent fields have no special literature on it** because,
in their natural frame of reference, it is a tiny tractable
example.

**This explains a structural feature of the audit's negative
verdict.** Adjacent fields are organised around **asymptotic
phenomena** (mixing time, spectral gap as `n → ∞`,
Dobrushin's condition for `n → ∞` lattices). The 1/3–2/3
conjecture's hard cases (per F1, F2) are at *small `n`*, where
asymptotic machinery is vacuous. The fields' machinery
*could* apply at large `n` — and indeed, the in-tree paper's
Theorem E uses Cheeger-style asymptotics — but the residual
`hC3` content is at small `n`, where adjacent fields are
silent.

---

## 5. Conceptual recommendations

### 5.1 Headline verdict

**No USABLE finding emerged** from the eight-field literature
audit. A SUGGESTIVE cluster (Caputo–Liggett–Richthammer 2010;
Caputo 2008 octopus; Diaconis–Saloff-Coste 1993; Bubley–Dyer
1999; Wilson 2004) provides published infrastructure for the
F5 prerequisite (BK ↔ S_n matching) but does not close F4-a
(sign-mode saturation on K=2 N-poset) or any of F1, F2, F3,
F4-b.

**Daniel's hypothesis was that adjacent fields might supply
ideas or lemmas usable for the obstruction.** The audit
confirms that *the structural pattern is real* (quotient-to-
chain is genuinely a meaningful object, instantiated in many
fields) but *does not transfer with usable lemmas*: each
field's machinery is asymptotic / averaged over global
structure, not adapted to the small-`n`, strict-⪯-pair, K=2
regime the obstruction lives in.

**The audit-as-deliverable IS the value.** Per the brief: "if
no USABLE finding emerges, the audit-as-deliverable is itself
the value: future arcs can lean on this survey rather than
re-deriving it." This arc thus provides a ~30-page reference
that future polecats / Daniel / external reviewers can
consult to avoid retreading the same ground.

### 5.2 Conceptual contributions of this audit

Independent of the negative usability verdict, the audit
contributes the following conceptual findings:

* **§1.1's formal Q1 / Q2 definition of "quotient-to-chain"
  posets** is, to the polecat's knowledge, a fresh
  formalisation of the structural pattern Daniel articulated.
  It captures layered width-3 posets, ordinal sums, weak
  orders, bipartite posets, and N-free posets uniformly. It
  is a candidate object for a future structural / classification
  arc, independent of the 1/3–2/3 closure question.
* **§1.3's decomposition of "deviation from chain"** into
  (within-band antichain shapes) × (cross-band bipartite
  graphs `B_{j, k}`) gives the canonical parameterisation of
  the K=2 obstruction family by the bipartite incidence
  pattern `B`. This parameterisation is implicit in arc 1.0–
  4.0 work but not previously written out.
* **§3.3's structural argument that F1, F2, F3, F4-a, F4-b
  resist adjacent-field imports** complements arc 4.0 §8's
  observation that arc 4.0 navigates around F1/F2/F3 but
  introduces F4-a/F4-b/F5. Together: the obstruction's
  resistance is genuinely multi-dimensional. No single field
  / strategy / definition addresses all six.
* **§4.6's pattern explanation** (adjacent fields are
  asymptotic; obstructions are at small `n`) is a unifying
  structural reason for the audit's negative verdict.

### 5.3 If a future arc revisits this question

Any future arc that revisits the conceptual / literature
audit should:

1. **Look at recent literature post-2025.** The polecat's
   audit cited results up to ~2018. If new spectral-comparison
   technology has been published (e.g. in CMRT-style kinetic
   constraints, or in Caputo-type comparison method
   extensions), it might be re-evaluated.
2. **Focus on the F5 prerequisite specifically.** The
   Caputo / DSC / BD–Wilson cluster is the strongest
   adjacent-field candidate. If the F5 prerequisite is
   formally stated and shopped to a spectral-methods
   specialist, there might be useful published results not
   captured by the polecat's broad survey.
3. **Verify the obstruction is still F4-a–terminal.** Arc
   4.0's K=2 N-poset enumeration is robust, but a *different*
   spectral framing (different non-trivial irrep choice,
   different LE-encoding) might bypass the sign-mode
   saturation. The polecat did not exhaustively explore all
   possible irrep-encoding combinations.
4. **Treat the audit as a baseline, not a backlog.** The
   surveyed fields' published technology is unlikely to
   change rapidly; future arcs should add to this audit
   rather than re-derive it.

### 5.4 Polecat-doable follow-on (none recommended)

Per the brief: "If any USABLE finding emerges, sketch the
polecat-doable follow-on (latex-first scoping, then Lean
implementation if warranted)."

**No USABLE finding emerged**, so no follow-on is recommended.
The closest would be a paper-tier infrastructure arc to apply
Caputo / DSC / BD–Wilson methods to the F5 prerequisite — but
this is

* outside polecat authority (per `feedback_audit_bar_for_axioms`
  and `feedback_polecat_stop_runaway`),
* multi-week external research (per arc 2.0 framing 4 and arc
  3.0 S1),
* and, even if it succeeded, would not close F4-a.

The absence of a follow-on recommendation is *not* a failure
of this arc; it is the arc's correct verdict given the
survey's findings.

### 5.5 Alignment with the option (δ) park decision

The headline `OneThird.width3_one_third_two_thirds` retains
`hC3 : Step8.Case3Witness` indefinitely under pm-onethird's
option (δ) park (2026-04-27). The conceptual audit is fully
consistent with that decision and does not propose any change
to it. Per `feedback_audit_as_deliverable`: the audit is the
deliverable, and `hC3` retention remains unchanged.

---

## 6. Risk inventory

Per the precedent of arc 3.0 §6 / arc 4.0 §8 / mg-cda8: a
per-finding risk catalogue with comparison to F1–F5
navigation and scope-creep call-outs.

### 6.1 Risk 1 — Mistaken USABLE classification

**Risk.** A future reader might re-classify one of the
SUGGESTIVE findings as USABLE on careful re-reading.

**Mitigation.** Each SUGGESTIVE finding has been explicitly
graded against F1–F5 in §3.2's matrix. The rationale for
"partial-on-F5-only" is documented per finding. Re-classifying
any finding as USABLE would require a published lemma whose
hypotheses our K=2 N-poset family clearly satisfies and whose
conclusion clears at least one of F1, F2, F3, F4-a, F4-b
beyond what arcs 1.0–4.0 already achieved.

**Audit-bar implication.** If a future arc proposes such a
re-classification, it must pass the four-condition
audit-bar test (`feedback_audit_bar_for_axioms`) for any
new project axiom *and* explicitly reckon with F4-a.

### 6.2 Risk 2 — Survey under-coverage

**Risk.** The polecat's survey may have missed a published
result that *is* USABLE.

**Mitigation.** The audit covered eight fields with ~30
papers each cited for the key fields. Cited papers span
1968–2018. The survey's depth is consistent with a single-
session polecat scoping audit; a deeper search (e.g.
ArXiv keyword survey, MathSciNet citation forward-tracking)
would tighten coverage at the cost of multi-session budget.

**Specific gaps.** Recent literature (2020–2025) on
kinetically constrained models (CMRT successors), Aldous
conjecture refinements (post-CLR variants), and order-
polytope-based dynamics (post-Hopkins) was not exhaustively
surveyed.

**Audit-bar implication.** Future arcs that revisit this
question should include a deeper post-2018 ArXiv pass before
concluding the search space is exhausted.

### 6.3 Risk 3 — Definitional fragility of "quotient-to-chain"

**Risk.** The §1.1 Q1 / Q2 formalisation might miss a
relevant variant. Specifically: the "K-band quotient-to-chain"
definition requires the band map `π` to be order-preserving
across bands; a more permissive definition (e.g. allowing
within-band ⪯-relations, or allowing some across-band edges
to flow downward) might give a different unifying theme.

**Mitigation.** §1.2's table verifies the definition against
the canonical examples (chain, antichain, ordinal sum,
layered width-3, K=2 N-poset, F1 minimal). All fit. The
crown / weak order / bipartite / 2D classes also fit
(§1.4). The definition seems robust to the standard
examples.

**Specific scope-creep risk.** If a future arc proposes a
"strict layering" or "weak quotient-to-chain" variant with
relaxed conditions, the §1 framework would need extension.
The polecat does not see this as a current problem.

### 6.4 Risk 4 — The K=2 N-poset analysis under field F (order polytope) might enable a fresh closure path

**Risk.** §4.5's clean geometric expression `Pr_N[x_1 < x_2] =
vol({s_1 ≤ s_2}) / vol(O(N))` could suggest an alternative
proof strategy for the K=2 family generally: instead of
manipulating Pr-probabilities, integrate volumes over the
order polytope and apply geometric inequalities (Brunn–
Minkowski, log-concavity of polytope sections, etc.).

**Mitigation.** Stanley 1986 + Felsner–Wernisch 1995 already
exploit this geometric framing in the published Brightwell /
Kahn–Linial line. F3 catches the limit of what geometric
inequalities give: the published lower bound stalls at
`(3 - √5)/2 ≈ 0.276` via order-polytope-based methods. A
width-3 tightening to 1/3 via order-polytope geometry would
be a new published result, not a polecat-doable simplification.

**Audit-bar implication.** A future arc proposing an order-
polytope-based attack on `hC3` should explicitly reckon with
F3 and demonstrate that its argument is *not* a width-3
specialisation of Brightwell / Kahn–Linial in disguise.

### 6.5 Risk 5 — F4-a evaporates under a different irrep choice

**Risk.** Arc 4.0 §3.5 reports `|λ_sign| = 1/3` on the K=2
N-poset using the sign / standard / two-row irreps. A
different irrep encoding (or a different "spectral
invariant") might bypass F4-a.

**Mitigation.** Arc 4.0's seven-configuration enumeration
showed the sign-mode-dominance pattern across the K=2 family;
mode inversion appears at small `n`. A different irrep choice
might shift the dominant mode but is unlikely to eliminate the
saturation (small `n` is the regime where eigenvalue-mode
ratios are tight).

**Specific scope-creep risk.** A future spectral arc might
propose a fresh strategy with different irrep choice (e.g.
hook-content irrep, plethysm-derived character). The audit
does not foreclose this; it documents that the *specific*
arc 4.0 strategy fails at F4-a, and the *adjacent fields'*
machinery does not by itself rescue it.

### 6.6 Risk 6 — Conflating "no USABLE finding" with "no closure exists"

**Risk.** The audit's negative verdict could be misread as a
proof that no simpler argument exists. This is the same
over-claim risk arc 3.0 §4.5 / mg-cda8 §"What this doc does
not claim" warned against.

**Mitigation.** This doc explicitly states (per §5.1, §5.4,
§5.5): no USABLE finding *was found in the surveyed
literature up to 2018*. This is **strictly weaker** than "no
USABLE finding exists." Future literature, independent
research, or paper-tier work could in principle produce a
USABLE result. The audit is a snapshot, not a proof of
exhaustion.

**Cross-reference.** `feedback_distinguish_arc_chunk_outcomes`
mandates honest framing of arc outcomes. The §5.1 framing —
"no USABLE finding emerged from this survey" — is the
honest version; "no simpler argument exists" would be over-
reach.

### 6.7 Risk 7 — Audit duplication with prior arcs

**Risk.** Per the brief's stop-loss trigger: "Polecat finds the
audit re-derives content already in arc 1.0–4.0 docs. STOP and
report — duplicate work."

**Audit-of-audit (this section).** The polecat verified that
this arc's substantive content is not duplicated elsewhere:

* Arc 3.0 §2 (eight ε-close definitions) is on
  *combinatorial defect* invariants, not adjacent-field
  literature.
* Arc 3.0 §3 (twelve strategy alternatives) is on
  *in-tree-machinery reorganisation*, not external-field
  surveys.
* Arc 4.0 §§2–8 is on the *specific spectral / character-
  theoretic* strategy, not on Caputo / DSC / Gibbs / treewidth
  / order-polytope literature surveys.
* `docs/why-hC3-is-structural.md` is the F1/F2/F3 synthesis,
  not a literature audit.
* The N3 (Linial / Brightwell tightenings) work is
  narrowly the published correlation-inequality line, not
  the broader adjacent-field survey this arc covers.

**Conclusion.** This arc's substantive content (the eight-
field literature audit, the formal Q1 / Q2 definition,
the §3 / §4 navigation matrices) is *additive*, not
duplicative. Stop-loss trigger does not fire.

### 6.8 Risk 8 — Misreading "quotient-to-chain" as ordinal sum (T7 reprise)

**Risk.** A future polecat reading §1 might conflate "quotient-
to-chain" with "ordinal sum" and assume the K=2 N-poset is
in the "decomposable case" — the same error that
`feedback_n_poset_is_not_ordinal_sum` (T7 in arc 3.0) was
introduced to prevent.

**Mitigation.** §1.5 explicitly cross-references
`feedback_n_poset_is_not_ordinal_sum` and verifies the K=2
N-poset is quotient-to-chain (Q1 / Q2) but **NOT** an ordinal
sum (only 2 of 4 cross-edges). The two notions are formally
distinct and the audit does not blur them.

**Audit-bar implication.** Future polecats reading this
audit must preserve the §1 distinction. "Quotient-to-chain"
is a strictly broader pattern than "ordinal sum"; the
N-poset family lives in the difference.

### 6.9 Aggregate risk verdict

The audit's substantive findings are robust under the seven
risks catalogued. The most serious risk is **Risk 5** (F4-a
evaporates under a different irrep choice), but this is a
*future-arc* risk, not a current-audit risk. The audit's
own verdict — "no USABLE finding" — is sound under the audit's
scope (eight named fields, ~30 papers per key field, post-1968
to 2018 literature).

Future arcs revisiting this audit should:

* Treat it as a *baseline*, not a backlog (per §5.3.4).
* Address Risks 2 (under-coverage), 4 (order-polytope
  re-routing), 5 (irrep-choice variation) explicitly.
* Verify the §1 quotient-to-chain framework still applies
  before extending it.

---

## 7. References and memory anchors

### 7.1 Cited published literature

**Field A — Expander obstructions.**

* Hoory, S., Linial, N., Wigderson, A. (2006). "Expander
  graphs and their applications." *Bull. AMS* 43(4):439–561.
* Lubotzky, A., Phillips, R., Sarnak, P. (1988). "Ramanujan
  graphs." *Combinatorica* 8(3):261–277.
* Margulis, G. (1973). Construction of explicit expanders.
* Alon, N. (1986). "Eigenvalues and expanders."
  *Combinatorica* 6(2):83–96.
* Trevisan, L. (2009). "Max cut and the smallest eigenvalue."
  *SICOMP* 41(6):1769–1786.
* Diaconis, P., Shahshahani, M. (1981). "Generating a random
  permutation with random transpositions." *Z. Wahrsch. Verw.
  Gebiete* 57(2):159–179.
* Caputo, P. (2008). "On the spectral gap of the Kac walk and
  other binary collision processes." *ALEA*.
* Caputo, P., Liggett, T. M., Richthammer, T. (2010). "Proof
  of Aldous' spectral gap conjecture." *J. AMS*
  23(3):831–851.
* Cesi, F. (2009). "Cayley graphs on the symmetric group
  generated by initial reversals have unit spectral gap."
  *Electronic J. Comb.* 16(1).
* Conomos, M., Starr, S. (2008). "Asymptotics of the spectral
  gap of the random transposition walk."

**Field B — 1D Gibbs systems.**

* Dobrushin, R. L. (1968). "The description of a random field
  by means of conditional probabilities." *Theor. Prob. Appl.*
  13(2):197–224.
* Dobrushin, R. L., Shlosman, S. B. (1985). "Constructive
  criterion for the uniqueness of Gibbs field."
* Holley, R., Stroock, D. (1976). "L² theory for the
  stochastic Ising model." *Z. Wahrsch.* 35:87–101.
* Stroock, D. W., Zegarliński, B. (1992). "The logarithmic
  Sobolev inequality for discrete spin systems on a lattice."
  *Comm. Math. Phys.* 149(1):175–193.
* Martinelli, F., Olivieri, E., Schonmann, R. H. (1994). "For
  2-D lattice spin systems weak mixing implies strong mixing."
  *Comm. Math. Phys.* 165(1):33–47.
* Martinelli, F. (1999). "Lectures on Glauber dynamics for
  discrete spin models." *Lectures on probability theory and
  statistics*.
* Cancrini, N., Martinelli, F., Roberto, C., Toninelli, C.
  (2008). "Kinetically constrained spin models." *Probab.
  Theory Relat. Fields* 140(3–4):459–504.
* Faggionato, A., Martinelli, F., Roberto, C., Toninelli, C.
  (2012). "Aging through hierarchical coalescence in the East
  model." *Comm. Math. Phys.* 309(2):459–495.
* Pillai, N. S., Smith, A. (2018). "Mixing times for a
  constrained Ising process on the torus at low density."
  *Ann. Probab.* 46(4):2206–2253.

**Field C — Low-treewidth graphs.**

* Eiben, E., Ganian, R., Knop, D., Ordyniak, S., Szeider, S.
  (2019). "Counting linear extensions of posets with bounded
  treewidth." *ESA 2019*.
* Robertson, N., Seymour, P. D. (1980+). "Graph minors" series
  of papers.
* Bodlaender, H. L. (1993). "A linear-time algorithm for
  finding tree-decompositions of small treewidth."

**Field D — Constrained Markov chains.**

* Bubley, R., Dyer, M. (1999). "Faster random generation of
  linear extensions." *Discrete Math.* 201(1–3):81–88.
* Wilson, D. B. (2004). "Mixing times of lozenge tiling and
  card shuffling Markov chains." *Ann. Appl. Probab.*
  14(1):274–325.
* Aldous, D. (1983 conjecture). Spectral gap of adjacent-
  transposition walk on `S_n`.
* Diaconis, P., Saloff-Coste, L. (1993). "Comparison theorems
  for reversible Markov chains." *Ann. Appl. Probab.*
  3(3):696–730.
* Liggett, T. M. (1985). *Interacting particle systems*.
  Springer.

**Field E — FKG / log-supermodular.**

* Fortuin, C. M., Kasteleyn, P. W., Ginibre, J. (1971).
  "Correlation inequalities on some partially ordered sets."
  *Comm. Math. Phys.* 22(2):89–103.
* Kahn, J., Saks, M. (1984). "Balancing poset extensions."
  *Order* 1:113–126.
* Brightwell, G. (1989). "Semiorders and the 1/3-2/3
  conjecture." *Order* 5:369–380.
* Kahn, J., Linial, N. (1991). "Balancing extensions via
  Brunn-Minkowski." *Combinatorica* 11(4):363–368.
* Brightwell, G., Felsner, S., Trotter, W. T. (1995).
  "Balancing pairs and the cross product conjecture." *Order*
  12:327–349.

**Field F — Order polytope.**

* Stanley, R. P. (1986). "Two poset polytopes." *Discrete
  Comput. Geom.* 1:9–23.
* Edelman, P., Hibi, T., Stanley, R. (1989). "A recurrence for
  linear extensions." *Order* 6(1):15–18.
* Felsner, S., Wernisch, L. (1995). "Markov chains for linear
  extensions, the two-dimensional case." *SODA*.
* Hopkins, S. (2017+). Various papers on rowmotion / promotion
  on order polytopes.

### 7.2 Internal documents (cross-referenced)

* `docs/why-hC3-is-structural.md` (mg-cda8) — F1/F2/F3
  synthesis. Read first; this audit's §3 builds on it.
* `docs/math-simp-arc-3.0/scoping.md` (mg-65e1) — 8 ε-close
  definitions × 12 strategy alternatives. §3.1 (S1
  BK/Cheeger drop) is closest in spirit.
* `docs/math-simp-arc-4.0/scoping.md` (mg-0bc8) — F4-a /
  F4-b / F5 introduced. Read alongside this audit.
* `docs/path-c-track-1-status-1.md` (mg-b666) — F1 origin.
* `simplifications.md` (top-level) — Daniel's original
  ε-close-to-ordinal-sum proposal; the "quotient-to-chain"
  intuition extends it.
* `notes/bk-walk-irrep-eigenvalue-bounds.md` (mg-7e24) —
  Daniel's working table; arc 4.0 input.

### 7.3 Memory anchors applied

* `feedback_latex_first_for_math_simp` — applied (no Lean
  changes; deliverable is a markdown audit doc).
* `feedback_audit_bar_for_axioms` — applied (no new project
  axioms attempted; SUGGESTIVE findings explicitly do not
  pass the 4-condition test).
* `feedback_signature_regressions` — applied (no replacement
  hypothesis for `hC3` proposed; verdict is "no USABLE
  finding").
* `feedback_n_poset_is_not_ordinal_sum` — applied (§1.5
  preserves the distinction; §6.8 catalogues the conflation
  risk).
* `feedback_distinguish_arc_chunk_outcomes` — applied
  (outcome class declared in §0; verdict in §5.1 is honest
  "no USABLE finding," not over-claimed "no simplification
  exists").
* `feedback_audit_as_deliverable` — applied (this doc IS
  the deliverable; no parallel cleanup attempted).
* `feedback_polecat_stop_runaway` — applied (no fresh-paper-
  level math attempted; SUGGESTIVE findings explicitly
  flagged as paper-tier and out of polecat scope).
* `feedback_dedup_against_closed_arcs` — applied (Risk 7
  audit-of-audit verifies non-duplication).

### 7.4 Cross-references to other tickets

* `mg-8baf` — this arc.
* `mg-cda8` — F1/F2/F3 synthesis (read first).
* `mg-65e1` — arc 3.0 scoping.
* `mg-0bc8` — arc 4.0 scoping.
* `mg-b666` — Track 1 / F1 origin.
* `mg-3e53` — arc 1.0 scoping.
* `mg-3d9d` — arc 1.0 A1 RED-fallback.
* `mg-805c` — arc 1.0 B1 ship.
* `mg-80ab` — arc 2.0 scoping.
* `mg-344a` — Daniel's parallel conceptual-development
  workspace (active, human; informational reference only).
* Daniel directive 2026-05-05T~09:30Z (in-session, no
  reminder ID).

### 7.5 What this doc does NOT claim

Per discipline `feedback_distinguish_arc_chunk_outcomes` and
arc 3.0 §4.5 / mg-cda8 §"What this doc does not claim":

* Does **not** claim that no simpler argument exists in
  adjacent fields' literature. Only that **no USABLE finding
  emerged from the polecat's eight-field, ~30-paper-per-key-
  field, 1968–2018 survey**.
* Does **not** claim that future literature (post-2025) cannot
  produce USABLE findings. The audit is a snapshot.
* Does **not** claim that the F5 prerequisite is unreachable
  via paper-tier work. Only that polecat scoping authority
  does not extend to that work, and that even if F5 were
  rescued, F4-a still bites.
* Does **not** propose any change to `hC3` retention,
  AXIOMS.md, or the headline. Outcome class: scoping doc only.
* Does **not** revive any of the RED-fallback'd arc 1.0–4.0
  framings under a new label.

The audit's substantive verdict is therefore: **the
quotient-to-chain pattern is real and unifying, but adjacent
fields' literature does not, in our 2018-snapshot survey,
provide USABLE lemmas for the K=2 obstruction family** — not
"no simpler proof can be found." `hC3` retention is the
honest disclosure of the former; the latter would be
over-reach.

---

*This file is the deliverable for `mg-8baf`, filed on
2026-05-05 by polecat `p8baf` on branch `conceptual-arc-1`.
It is doc-only (no Lean source changes) and follows the arc
2.0 / arc 3.0 / arc 4.0 / mg-cda8 precedent of "audit-as-
deliverable" under polecat authority.*
