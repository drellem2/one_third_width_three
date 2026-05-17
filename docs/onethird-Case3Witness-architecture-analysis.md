# Case3Witness lemma — architecture analysis: the missing interaction-radius bound

**Work item:** `mg-e2e9` (architecture analysis polecat,
single-session, paper-and-pencil, no Lean code changes).

**Trigger:** Daniel directive 2026-05-17T12:55Z (verbatim):

> "the case 3 witness lemma you provided … still doesn't make sense to
> me in the context of the architecture of the proof. The interaction
> radius for instance is not bounded, and so we don't actually know
> that there is a meaningful layered structure and not just a trivial
> one. If the coherence-collapse case upstream is doing real work, imo
> there should be another bound here."

**Verdict (top-of-page):** **AMBER-missing-bound-fix-proposed.**
Daniel's diagnosis is *correct*. The four caps that
`Step8.Case3Witness.{u}` (`LayeredBalanced.lean:433-443`) carries
do **not** bound the layered decomposition's interaction width
`LB.w` from above. Caps 2 and 3 are *ratio* bounds
(`K ≤ 2w+2`, `|β| ≤ 6w+6`) that become **vacuous** when `w` is
unconstrained, and the operational call site
(`lem_layered_balanced` K ≥ 2 branch,
`LayeredBalanced.lean:668`) explicitly substitutes
`canonicalLayered α` with `K = w = |α|` — making the (L2-forced)
axiom of the layered structure literally vacuous. As a
consequence, the universal `Case3Witness β` Prop instantiated at
`L := canonicalLayered β` is **mathematically equivalent to the
headline theorem itself** (`width3_one_third_two_thirds`). The
upstream coherence-collapse case (paper Steps 1-7, which is
*supposed* to deliver a layered decomposition with bounded `w`)
is structurally bypassed.

The proposed fix is straightforward at the lemma level: add a
fifth cap `LB.w ≤ W₀` for an absolute constant `W₀` (concretely
`W₀ = 4`, matching `InCase3Scope.w_mem`). With cap 5 the four
existing caps become *honest* finite-domain restrictions
(`|β| ≤ 30`, `K ≤ 10`, `w ∈ {1, 2, 3, 4}`), so `Case3Witness`
genuinely is a finitely-decidable claim over a bounded family of
finite posets. The downstream architectural rewrite required to
*supply* a cap-5-satisfying `LB` on the operational call path
(rather than `canonicalLayered`) is the substantive follow-on
work; that work intersects the K = 2 case-2-strict residual
already parked under option (δ) per `why-hC3-is-structural.md`,
so this analysis does not unlock new ground there.

The verdict is **AMBER not RED**: the missing bound is named
concretely (cap 5), the fix has a precise stated form, and the
downstream blockers are the *already-disclosed* residuals — not
fresh structural surprises.

---

## 1. Definitions

### 1a. "Interaction radius" = `LayeredDecomposition.w`

`LayeredDecomposition α` (`Step8.LayeredReduction.lean:115-149`)
carries:

* `K : ℕ` — depth of the layering;
* **`w : ℕ` — interaction width** (paper: "interaction width",
  `step8.tex:1905`);
* `band : α → ℕ` — band-index map in `[1, K]`;
* `(L1a)` `band_size`: each band has `≤ 3` elements;
* `(L1b)` `band_antichain`: each band is an antichain;
* `(L2-forced)` `forced_lt`: `band x + w < band y ⇒ x < y`;
* `(L2-upward)` `cross_band_lt_upward`: `x < y ⇒ band x ≤ band y`
  (added in mg-53ce).

The "interaction radius" Daniel names is the field `w`. Its
operational meaning is *the band-distance below which
incomparability is permitted*: pairs with `|band x − band y| > w`
are *forced comparable* by (L2-forced); pairs with
`|band x − band y| ≤ w` may be incomparable.

`w` is the dial that distinguishes a *meaningful* layered
structure from a *trivial* one:

* `w = 0`: every cross-band pair is forced comparable. This is
  the bipartite / Case 2 regime; the layered structure is
  maximally informative.
* `w = O_T(1)` (a constant in `|α|`): the band-distance window is
  small, so `lem:cut` (`LayeredReduction.lean:373`) cuts at
  `k ∈ (w, K−w)` with a window of size `6w` — this is the
  paper's setting where layered axioms do real work.
* `w ≥ K`: (L2-forced) becomes vacuous (no `x, y` satisfy
  `band x + w < band y`). The layered structure degenerates to a
  band assignment plus (L2-upward), i.e., essentially a
  *Szpilrajn linear extension* (under cap 1, every band singleton).

`canonicalLayered α` (`LayeredBalanced.lean:469`) is the
maximally trivial instance: `K = w = |α|`, every band a singleton
under a chosen Szpilrajn extension. By construction
`band x + |α| < band y` is impossible (both sides are in
`[1, |α|]`), so (L2-forced) of `canonicalLayered` is **vacuous**.

### 1b. `Case3Witness.{u}` — the four caps

```lean
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    Function.Injective LB.band →           -- cap 1
    LB.K ≤ 2 * LB.w + 2 →                  -- cap 2
    Fintype.card β ≤ 6 * LB.w + 6 →        -- cap 3
    (∀ k : ℕ, 1 ≤ k → k ≤ LB.K →
      (LB.bandSet k).Nonempty) →           -- cap 4
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    HasBalancedPair β
```

Caps in plain terms:

| Cap | Statement                                | Meaning                                                            |
|-----|------------------------------------------|--------------------------------------------------------------------|
| 1   | `Function.Injective LB.band`             | Each band has *exactly one* element (under (L1a) which caps at 3). |
| 2   | `LB.K ≤ 2 * LB.w + 2`                    | Ratio bound: depth ≤ 2 × interaction-width + 2.                    |
| 3   | `Fintype.card β ≤ 6 * LB.w + 6`          | Ratio bound: |β| ≤ 6 × interaction-width + 6.                      |
| 4   | `∀ k ∈ [1, LB.K], (LB.bandSet k).Nonempty` | No empty bands (compactified).                                   |

Observation: **caps 2 and 3 bound `K` and `|β|` only in terms of
`w`**. With `w` permitted to scale with `|β|`, the caps say
nothing absolute about `K` or `|β|`. Specifically, the
*canonical* instantiation `LB = canonicalLayered α` with
`K = w = |α|` satisfies caps 2 and 3 vacuously:

* Cap 2: `|α| ≤ 2|α| + 2` ✓
* Cap 3: `|α| ≤ 6|α| + 6` ✓

So caps 2 and 3 — which look like genuine size restrictions —
are operationally **inert** against the canonical substitution.
Cap 1 is satisfied by Szpilrajn injectivity; cap 4 holds because
each band is a singleton.

### 1c. The downstream consumer profile

`bounded_irreducible_balanced_hybrid`
(`BoundedIrreducibleBalanced.lean:1681`) takes precisely the
hypothesis profile of `Case3Witness`'s caps 2-3 (plus
`3 ≤ L.K`, `1 ≤ L.w`):

```lean
theorem bounded_irreducible_balanced_hybrid
    (L : LayeredDecomposition α)
    (_hWidth3 : HasWidthAtMost α 3)
    (_hIrr : LayerOrdinalIrreducible L)
    (_hK3 : 3 ≤ L.K)
    (_hw : 1 ≤ L.w)
    (_hCard : Fintype.card α ≤ 6 * L.w + 6)    -- = cap 3
    (_hDepth : L.K ≤ 2 * L.w + 2)               -- = cap 2
    (hCert : InCase3Scope L.w (...) L.K → HasBalancedPair α)
    (hStruct : ¬ InCase3Scope L.w (...) L.K → HasBalancedPair α) :
    HasBalancedPair α
```

`InCase3Scope w card K` (`BoundedIrreducibleBalanced.lean:1498`)
is the **only** place an absolute upper bound on `w` appears:

```lean
def InCase3Scope (w card K : ℕ) : Prop :=
  (K = 3 ∧ 1 ≤ w ∧ w ≤ 4 ∧
    (w = 1 → card ≤ 9) ∧ (2 ≤ w → card ≤ 7)) ∨
  (K = 4 ∧ w = 1 ∧ card ≤ 8)
```

So `w ≤ 4` is the absolute bound the F5a `case3_certificate` is
willing to certify. Outside this scope (`¬ InCase3Scope`) the
residual axiom `case3Witness_hasBalancedPair_outOfScope`
(`Case3Residual.lean:208`) takes the same `K ≤ 2w + 2` and
`|α| ≤ 6w + 6` caps **but does not constrain `w` from above
either**. Thus the residual axiom, as stated, asserts the
balanced-pair conclusion for *arbitrarily large `w`* and
consequently *arbitrarily large `|α|`* (since the cap
`|α| ≤ 6w + 6` permits any `|α|` once `w` is permitted to scale).

## 2. The trace: coherence-collapse → Case3Witness → headline

### 2a. The headline call path

```
OneThird.width3_one_third_two_thirds                  (MainTheorem.lean:52)
  ↓  (threads hC3 : Case3Witness)
width3_one_third_two_thirds_assembled                 (MainAssembly.lean:320-339)
  ↓
mainAssembly / mainTheoremInputsOf                    (MainAssembly.lean:238-247)
  ↓
lem_layered_balanced                                  (LayeredBalanced.lean:597)
  ↓  K = 1 branch:  bipartite_balanced_enum (closes inline)
  ↓  K ≥ 2 branch:  hC3 α (canonicalLayered α) <caps proved in-place>
                                                      (LayeredBalanced.lean:668)
Case3Witness.{u}                                      (LayeredBalanced.lean:433)
  ↓  applied to β = α, LB = canonicalLayered α
HasBalancedPair α
```

The K ≥ 2 branch (LayeredBalanced.lean:652-688) is the *sole*
operational consumer of `hC3`. It does **not** thread the input
`L : LayeredDecomposition α` — instead it constructs a fresh
`L' := canonicalLayered α` and applies `hC3 α L' ...`.

### 2b. What the coherence-collapse upstream *is supposed* to do

The paper's Steps 1-7 (`step{1..7}.tex`) are the BK-Cheeger /
fiber-coherence / staircase / collapse machinery:

* **Step 1-2** (staircase / fiber pair-cut): per-fiber pair-cut
  approximation under arithmetic richness.
* **Step 3** (interface coherence): glue fiber-local
  approximations to a near-monotone global form.
* **Step 4** (two-interface incompatibility): incoherent
  interfaces force large BK conductance, contradicting density.
* **Step 6** (coherence dichotomy): forces all rich fibers into a
  globally coherent state.
* **Step 7** (layered globalisation): the coherent global state
  *is* a layered decomposition with **bounded interaction width
  `w ≤ w₀(γ)`** (constant in `|α|`).
* **Step 8** (this file): consume the bounded-`w` layered
  decomposition to extract a balanced pair via cut + window
  perturbation (`lem:cut` + `lem:layered-reduction`).

**The "real work" of Steps 1-7 is delivering the bound `w ≤ w₀(γ)`.**
Without that bound, the layered decomposition is meaningless and
Step 8's cut argument has nothing to cut against.

The Lean formalisation has Steps 1-7 axiomatised behind
`Step7.LayeredWidth3` (`ChainPotentials.lean`), and
`layeredFromBridges` (`LayeredBridges.lean:181`) is the
extractor that pulls out the Step 7 witness. The Step 7
bandwidth field is `Lwidth3.bandwidth`, which gets threaded as
`L.w` of the resulting `LayeredDecomposition` (per the doc
header at `LayeredBridges.lean:48-58`):

```
w = Step7's bandwidth,  not  w = |α| + Step7's bandwidth.
```

In the paper, `Lwidth3.bandwidth = w₀(γ)` is a small constant.
In the current Lean, it is set as `Fintype.card α + 1` in the
chain-potentials extractor (`ChainPotentials.lean` cleared-
denominator audit), because Steps 1-7 are *not yet truly proved*
in the formalisation — they are extracted from an existential
without the genuine `w₀(γ)` content.

### 2c. The architectural disconnect

`lem_layered_balanced`'s K ≥ 2 branch (LayeredBalanced.lean:668)
**does not use the upstream-supplied `L`** at all. It
constructs a *fresh* `L' := canonicalLayered α` with
`K = w = |α|` and applies `hC3` to that. The upstream
`layeredFromBridges`/`Lwidth3.bandwidth` carrier of the
Step 7 content is *bypassed* at the K ≥ 2 dispatch.

So the architecture has:

* **Upstream**: Steps 1-7 produce `Lwidth3 : Step7.LayeredWidth3`
  with the *intended* bound `bandwidth ≤ w₀(γ)`. Threaded
  through `layeredFromBridges` to `L : LayeredDecomposition α`
  with `L.w = Lwidth3.bandwidth`.
* **Downstream**: `lem_layered_balanced` *discards* `L` for the
  K ≥ 2 dispatch and uses `canonicalLayered α` instead, whose
  `w = |α|` is *unbounded* in `|α|`.

This is the precise architectural point Daniel names: "the
interaction radius is not bounded, so we don't actually know
that there is a meaningful layered structure and not just a
trivial one."

The structural answer: the meaningful layered structure
*delivered by* Steps 1-7 is not the one *consumed by*
`lem_layered_balanced`. The consumer accepts (and dispatches
on) a trivial Szpilrajn-derived layered structure.

### 2d. The circular reading

Composing the K ≥ 2 dispatch with `canonicalLayered α`, the
`hC3 : Case3Witness` hypothesis instantiates as:

> For every width-3 non-chain finite `β` with `|β| ≥ 2`, taking
> `L := canonicalLayered β` (Szpilrajn-derived; satisfies caps
> 1-4 trivially): `β` has a balanced pair.

The four caps are vacuously satisfied by `canonicalLayered β`
for **every** finite `β`. So the universal `∀ β` ranges over
exactly the headline's domain (width-3 non-chain finite posets
with `|β| ≥ 2`), and the conclusion is exactly the headline's
conclusion (`HasBalancedPair β`).

**`hC3 : Case3Witness` ⇔ headline theorem** (modulo the K = 1
branch, which is independently discharged by
`bipartite_balanced_enum`).

So the K ≥ 2 branch of `lem_layered_balanced` is *not* a proof
that "if the input has a layered decomposition, balanced pairs
exist" — it is a re-statement of the headline, with the
layered hypothesis ignored and the conclusion supplied by
`hC3`. The layered structure does *no* mathematical work in the
K ≥ 2 dispatch.

(This is consistent with — and a structural refinement of —
the K-quantifier-scope finding in
`docs/case3witness-operational-audit.md` §2 (mg-e0b8): the
universal `Case3Witness β` is invoked at `K = |α|` rather than
at any bounded `K`. The present analysis adds the further
observation that *the same is true of `w`*, and that the
canonicalLayered substitution makes (L2-forced) literally
vacuous.)

## 3. What bound *should* be there — the missing cap 5

### 3a. The fix at the lemma level

Add a fifth antecedent to `Case3Witness.{u}` bounding
`LB.w` from above by an absolute constant `W₀`:

```lean
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    Function.Injective LB.band →                           -- cap 1
    LB.K ≤ 2 * LB.w + 2 →                                  -- cap 2
    Fintype.card β ≤ 6 * LB.w + 6 →                        -- cap 3
    (∀ k : ℕ, 1 ≤ k → k ≤ LB.K → (LB.bandSet k).Nonempty) → -- cap 4
    LB.w ≤ 4 →                                             -- cap 5 (NEW)
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    HasBalancedPair β
```

With `W₀ = 4`:

* Cap 5 + cap 2 ⇒ `LB.K ≤ 2·4 + 2 = 10`.
* Cap 5 + cap 3 ⇒ `Fintype.card β ≤ 6·4 + 6 = 30`.

So under cap 5, the universal `∀ β` ranges over **finite posets
of cardinality ≤ 30** with `K ≤ 10`, `w ∈ {1, 2, 3, 4}`. This is
genuinely a finitely-decidable claim over a bounded family.

Why `W₀ = 4`?

* It is the **maximum `w` admitted by `InCase3Scope`** (per
  `InCase3Scope.w_mem`: `w ∈ {1, 2, 3, 4}`).
* It is the **paper's actual scope for F5a's Case-3 finite
  enumeration** (`step8.tex:3050-3067 lem:enum`); the case3
  certificate covers `w ≤ 4` exhaustively, and the residual axiom
  covers the (now-bounded) `w = 5, …, 4` complement — which is
  *empty* once cap 5 is in place.
* Alternative bounds (`W₀ = K₀(γ) − const`, derived from the
  paper's Steps 1-7) would be larger but still constant in `|α|`;
  `W₀ = 4` is the *minimum* tight bound matching what the F5a
  certificate already covers.

A more conservative choice — `W₀` left as an abstract constant
parameter (e.g. `LB.w ≤ W₀ γ`) — would future-proof the bound
against changes in the F5a scope. For the present analysis the
concrete `W₀ = 4` is the operative choice.

### 3b. Why the existing axiom is silent on `w`

`case3Witness_hasBalancedPair_outOfScope`
(`Case3Residual.lean:208`) carries `1 ≤ L.w` and
`L.K ≤ 2 * L.w + 2` and `Fintype.card α ≤ 6 * L.w + 6` — but
*no* upper bound on `L.w`. Consequently, the axiom as stated
asserts: for every layered width-3 irreducible non-chain `α` with
any `w ≥ 1` satisfying `K ≤ 2w + 2`, `|α| ≤ 6w + 6`,
`¬ InCase3Scope (w, |α|, K)`, `α` has a balanced pair.

For `w = |α|/6 − 1` (so cap 3 saturates), the axiom asserts the
existence of a balanced pair in a width-3 non-chain `α` of
*any* cardinality. Combined with cap 1 (Szpilrajn-derivable on
every finite poset), this includes nearly all width-3 inputs —
the axiom claim is *almost* as strong as the headline.

Cap 5 in `Case3Witness` would NOT directly tighten the axiom
signature (the axiom is a separate object), but the axiom is
*operationally* only ever invoked through
`bounded_irreducible_balanced_hybrid`'s `hStruct` slot via the
dispatch in `Case3Witness_proof`'s K ≥ 3 branch. If
`Case3Witness` requires cap 5 from its caller, then the axiom is
only ever invoked on inputs with `LB.w ≤ 4` — at which point the
axiom is *redundant* (because `InCase3Scope` covers
`w ∈ {1, …, 4}` entirely for `K ∈ {3, 4}`; the genuinely-residual
cases are exactly `K ∈ {5, …, 10}` with `w ∈ {1, …, 4}`).

So adding cap 5 has the secondary effect of **narrowing the
residual axiom's effective domain** to the small finite set
`{(K, w, |α|) : 5 ≤ K ≤ 10, 1 ≤ w ≤ 4, |α| ≤ 30}` — a much
sharper target for a direct enumeration certificate.

### 3c. Downstream impact — the operational call site

`lem_layered_balanced`'s K ≥ 2 branch
(`LayeredBalanced.lean:668-688`) currently substitutes
`L' := canonicalLayered α` with `K = w = |α|`. This **fails cap 5
for any `|α| ≥ 5`**. So the branch must be rewritten.

Three options (mapped to the existing roadmap):

* **Option A — upstream-driven `w`-bound.** Use the *actual*
  `layeredFromBridges`-derived `L : LayeredDecomposition α` (with
  `L.w = Lwidth3.bandwidth ≤ w₀(γ) = 4`, *once Steps 1-7 deliver
  the genuine `w₀(γ)` bound*). The current `ChainPotentials`
  extractor returns `bandwidth = |α| + 1`, which is not
  cap-5-compatible; this option requires either (i) genuinely
  proving Steps 1-7 in Lean (multi-month scope) or (ii)
  axiomatising the bound `bandwidth ≤ 4` as a separate hypothesis
  threaded through `layeredFromBridges`. Path C / Steps 1-7
  full-proof scope (`docs/lean-forum-publication-readiness.md`
  context).

* **Option B — F3 strong-induction with bounded-`w` leaves.**
  Use the F3 framework
  `hasBalancedPair_of_layered_strongInduction_width3`
  (`LayerOrdinal.lean:472`, mg-a735) with an `hStep` argument
  constructed by reducibility-dispatch on the input `L`. The
  induction descends on `|α|`; reducible cuts shrink the
  cardinality, and irreducible leaves are bounded-`w` by the
  reducibility profile. The K = 2 case-2-strict residual blocks
  this option per `docs/path-c-track-1-status-1.md` (mg-b666).

* **Option C — drop `Case3Witness` as a hypothesis.** Rewrite the
  headline to invoke `lem:layered-reduction` directly (the
  paper's actual flow). Deepest architectural change; same
  blockers as Option A (Steps 1-7 needed to deliver `w₀(γ)`).

All three options intersect the previously-disclosed obstructions
catalogued in `docs/why-hC3-is-structural.md` (F1 cardinality, F2
Brightwell vacuity, F3 published gap). Adding cap 5 does not
unlock any of these obstructions; it merely re-localises them to
the operational-call dispatch (where they were always going to
fire eventually under any non-circular reading of the headline
discharge).

## 4. Verdict: AMBER-missing-bound-fix-proposed

### 4a. Why not GREEN-non-issue

The four existing caps are demonstrably insufficient. Concrete
proof: `Case3Witness` instantiated at any width-3 non-chain
finite `β` with `|β| ≥ 2`, via `L := canonicalLayered β`,
satisfies caps 1-4 vacuously (caps 2, 3 are
`|β| ≤ 2|β| + 2` and `|β| ≤ 6|β| + 6`; cap 1 is Szpilrajn
injectivity; cap 4 is singleton bands). Therefore
`Case3Witness` (as currently stated) is mathematically
equivalent to the headline theorem on the K ≥ 2 input domain.

This is not a *subtle* claim — it is mechanically verifiable
from the definition of `canonicalLayered` and the substitution at
`LayeredBalanced.lean:668`. Daniel's concern is well-founded.

### 4b. Why not RED-structural

The fix is **named precisely and is non-trivial to dismiss**:
add cap 5 `LB.w ≤ 4`. This is not a hypothetical patch — it has
a literature anchor (the F5a `case3_certificate` already covers
`w ≤ 4` exhaustively per `InCase3Scope`), it makes
`Case3Witness` a finite claim (`|β| ≤ 30`), and it sharpens the
residual axiom's effective domain to a small finite set.

The downstream architectural rewrite needed to *supply* a
cap-5-satisfying `LB` on the operational path is blocked by the
*already-known* K = 2 case-2-strict residual (mg-b666 obstruction)
and the not-yet-delivered Steps 1-7 `w₀(γ)` bound. These are
**previously disclosed structural facts**, not fresh discoveries.
The verdict is AMBER because the *lemma-level* fix is clear and
the *execution-level* blockers are already on the roadmap.

A RED verdict would require that no fix is possible — e.g., if
the K = 2 case-2-strict residual were *unsolvable in principle*
(which `why-hC3-is-structural.md` explicitly does not claim: F1
+ F2 + F3 are documented to *make the residual hard*, but the
BK-Cheeger / fiber-coherence approach is documented to *be a
path through*). The fix exists; the execution path through it is
the one already documented.

### 4c. Why this is genuinely actionable

This analysis converts an *aesthetic* objection ("the layered
structure is meaningless") into a *concrete* objection ("cap 5 is
missing"). The downstream consequences:

* The *naming* of cap 5 (`LB.w ≤ W₀`) provides a clean diff
  target for a future signature-restatement PR. The cap is a
  pure addition; the four existing caps remain unchanged.
* The *value* `W₀ = 4` is the F5a-certified scope and aligns
  the upper bound of `Case3Witness` with the upper bound the
  in-tree Bool certificate is willing to discharge. The residual
  axiom would become genuinely residual (covers `K ∈ {5, …, 10}`,
  `w ∈ {1, …, 4}`, `|α| ≤ 30`) and decidable.
* The *consequence at the call site* (failure of `canonicalLayered`
  to satisfy cap 5) names the precise operational gap that the
  current `lem_layered_balanced` K ≥ 2 dispatch is silently
  papering over via the canonicalLayered substitution.

The fix would not, by itself, close the K = 2 case-2-strict
residual or deliver Steps 1-7. It would, however, *expose* the
operational dependency on those items as a type error (cap 5 not
discharged at the call site), forcing a principled re-engagement
with the option-(δ) park decision rather than allowing the
universal-quantifier proxy to absorb the gap silently.

## 5. Recommended forward action

Per ticket Phase D mandate: a fix is *proposed* at the lemma
level (cap 5). The execution is **not** in scope for this
analysis ticket. Recommended follow-on tickets, in priority
order:

1. **(LEAN, signature-restatement)** File a ticket to add cap 5
   to `Case3Witness.{u}` and propagate the type signature change
   through `Case3Residual.lean`, `lem_layered_balanced`, and the
   headline assembly. Expected impact: the K ≥ 2 dispatch in
   `lem_layered_balanced` will fail to type-check (canonicalLayered
   does not satisfy cap 5 for `|α| ≥ 5`); this is the *intended*
   outcome — it surfaces the operational gap as a hard error.
   Estimated effort: ~50-100 LoC for the signature change plus
   the dispatch failure; ~weeks if the K ≥ 2 dispatch is to be
   rewritten in the same ticket. Recommended split: signature
   change in its own ticket, dispatch rewrite as a follow-on.

2. **(LEAN, residual-axiom-tightening)** Once cap 5 lands,
   restate `case3Witness_hasBalancedPair_outOfScope` to add the
   `LB.w ≤ 4` hypothesis. The residual claim then becomes a
   *finite* enumeration over the small set
   `{(K, w, |α|) : 5 ≤ K ≤ 10, 1 ≤ w ≤ 4, |α| ≤ 30}` and is a
   candidate for a direct `case3_certificate_extension`
   discharge (no `native_decide` extension if the extension can
   be done by-hand for the small finite count of tuples).
   Estimated effort: ~200-400 LoC.

3. **(LEAN, operational-dispatch rewrite)** Replace the
   `canonicalLayered α` substitution at `LayeredBalanced.lean:668`
   with either Option A (use upstream `layeredFromBridges` with
   bandwidth bound), Option B (F3 strong-induction descent on
   `|α|`), or Option C (drop `hC3` entirely). All three are
   substantial work intersecting the K = 2 case-2-strict residual
   already parked under option (δ). Estimated effort:
   multi-polecat, blocked on `path-c-cleanup-roadmap.md` items.

4. **(MATH, paper-level)** Audit the paper for the *upstream*
   `w ≤ w₀(γ)` bound delivery. The Steps 1-7 chain is the
   intended source of this bound; the constant `w₀(γ)` should be
   pinned (the analysis above assumes `W₀ = 4` based on
   `InCase3Scope.w_mem`, but the paper-derived constant may
   differ). This is the math-paper polecat scope, not a Lean
   polecat scope. Estimated effort: 100-200k single-session
   paper-and-pencil.

## 6. Cross-references and load-bearing claims

* **`lean/OneThird/Step8/LayeredReduction.lean:115-149`** —
  `LayeredDecomposition α` structure: `K`, `w`, `band`, axioms
  L1, L1b, L2-forced, L2-upward (`cross_band_lt_upward`).
* **`lean/OneThird/Step8/LayeredReduction.lean:373`** — `lem_cut`:
  for `K ≥ 2w + 2`, the cut at `k ∈ (w, K − w)` produces a
  window of size `6w`. Meaningful only when `w` is bounded
  relative to `K`.
* **`lean/OneThird/Step8/LayeredReduction.lean:514`** —
  `K₀(γ_n, γ_d, w) := max(2w + 2, ⌈2 γ_d / γ_n⌉ + 6w + 4)`. The
  threshold scales linearly in `w`; bounded `w` is required for
  this to be a useful absolute threshold.
* **`lean/OneThird/Step8/LayeredBalanced.lean:433-443`** —
  `Case3Witness.{u}` definition; the four caps (Injective,
  `K ≤ 2w+2`, `|β| ≤ 6w+6`, bands non-empty).
* **`lean/OneThird/Step8/LayeredBalanced.lean:469-506`** —
  `canonicalLayered α`: `K = w = |α|`, every band singleton,
  (L2-forced) vacuous.
* **`lean/OneThird/Step8/LayeredBalanced.lean:668`** — the
  operational substitution `let L' := canonicalLayered α` in the
  K ≥ 2 branch of `lem_layered_balanced`. **The architectural
  disconnect Daniel names.**
* **`lean/OneThird/Step8/LayeredBridges.lean:181-261`** —
  `layeredFromBridges`: the upstream-supplied `L` with
  `L.w = Lwidth3.bandwidth`. *Currently bypassed at the K ≥ 2
  dispatch.*
* **`lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1498-1501`** —
  `InCase3Scope`: the *only* place an absolute `w ≤ 4` bound
  appears.
* **`lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1681`** —
  `bounded_irreducible_balanced_hybrid`: consumer of caps 2, 3
  (plus `3 ≤ K`, `1 ≤ w`).
* **`lean/OneThird/Step8/Case3Residual.lean:208-217`** —
  `case3Witness_hasBalancedPair_outOfScope` axiom: takes
  `1 ≤ L.w`, `K ≤ 2w + 2`, `|α| ≤ 6w + 6` but *no* upper bound
  on `w`.
* **`docs/case3witness-operational-audit.md`** (mg-e0b8,
  2026-05-04) — the prior K-quantifier-scope audit. The present
  analysis extends that finding to the `w`-quantifier scope and
  identifies the canonicalLayered substitution as the precise
  vacuity vector.
* **`docs/why-hC3-is-structural.md`** (2026-05-04) — the option
  (δ) park rationale: F1 (cardinality), F2 (Brightwell vacuity at
  `|Q| ≤ 6`), F3 (published `[0.276, 1/3)` gap). The present
  analysis confirms that the *concrete* form of the obstruction
  is the missing `w ≤ W₀` bound; the F1/F2/F3 facts are the
  reasons that *closing the resulting cap-5-tightened gap* is
  hard.
* **`docs/path-c-track-1-status-1.md`** (mg-b666, 2026-05-04) —
  the K = 2 case-2-strict cardinality obstruction. Blocks
  Options A and B of §3c.
* **`docs/path-c-cleanup-roadmap.md`** (mg-7261, 2026-04-27) —
  the route taxonomy; cap 5 fits cleanly under Option (α) /
  Option (γ) variants.

## 7. Summary

The four existing caps on `Case3Witness.{u}` (Injective band,
`K ≤ 2w+2`, `|β| ≤ 6w+6`, bands non-empty) do **not** bound the
interaction width `w` from above. Caps 2 and 3 are *ratio*
bounds — they are vacuous when `w` is allowed to scale with
`|β|`. The operational call site uses `canonicalLayered α`
with `K = w = |α|`, satisfying all four caps vacuously and
collapsing the universal `Case3Witness β` to the headline
theorem itself.

The missing bound is `LB.w ≤ W₀` (cap 5), with `W₀ = 4` the
natural F5a-aligned constant. Adding cap 5 makes `Case3Witness`
a *finite* claim (`|β| ≤ 30`) and exposes the operational
canonicalLayered substitution as a type error, forcing a
principled engagement with the downstream architecture rather
than the current silent absorption.

Daniel's framing — "the interaction radius is not bounded, so
the layered structure is trivial; if the coherence-collapse case
upstream is doing real work, there should be another bound here"
— is exactly correct. The "real work" of Steps 1-7 is delivering
`w ≤ w₀(γ)`; the current Lean dispatch bypasses that work by
substituting `canonicalLayered`. The fix is to add cap 5 and
re-engineer the K ≥ 2 dispatch to consume the upstream `L` (or
descend by F3) rather than fabricate a fresh trivial `L'`.

Verdict: **AMBER-missing-bound-fix-proposed**. No new
mathematical obstructions; the fix is named; the downstream
blockers are the previously-disclosed K = 2 case-2-strict
residual and the not-yet-delivered Steps 1-7 `w₀(γ)`. File the
signature-restatement ticket; expect the K ≥ 2 dispatch to
require follow-on rework intersecting the option-(δ) park.
