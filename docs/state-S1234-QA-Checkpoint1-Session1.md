# State — OneThird S1234-QA: Checkpoint 1 audit (mg-8b95)

**Ticket:** mg-8b95 — OneThird-S1234-QA: Checkpoint 1 audit — does the
S1 `thm:interface` port carry a paper-side rigor gap.
**Phase:** FULL REFACTOR Phase 2, Checkpoint 1 — the hold-the-line
go/no-go gate on Wave-4 (Step 6), per
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §3.3.
**Depends:** mg-7592 (S4-A — landed).
**Session:** 1.

---

## §0. Verdict — **AMBER** (gap surfaced; re-scope before sinking Wave-4 Step 6 budget)

> **GREEN is not defensible; RED is too strong.** The S1 `thm:interface`
> Lean port **did surface a paper-side rigor gap not caught in the
> mg-6ab8 §2.1 pre-filing audit** — the paper's part-(iv) `|I(z)| ≤ 2`
> length claim is **false** (independently re-confirmed below, §3, with
> a worked width-3 non-chain counterexample). The interface theorem's
> four parts are nonetheless individually **true** (with the
> order-convexity correction the port already applied) and the cascade
> is **not broken** — so this is not RED. But the **operative content
> of part (iv) — the bad-set bound `|Bad_{x,y}| ≪ |F_{x,y}|` — and the
> corollary density bounds are NOT delivered** by the landed port: they
> sit as explicitly-vacuous `≤ |𝓛(P)|` scaffolds (§4). Downstream
> S4-B / S4-C and Step 7 consume exactly those. Calling this GREEN
> would be precisely the type-checks-clean verdict the audit charter
> forbids — the four parts type-check and ship non-vacuity witnesses,
> but the witnesses are degenerate (`t = 1`, singleton good fibers)
> and the operative satisfiability content is absent (§5).

**Three findings (detail in §3–§5; downstream map §6; satisfiability
assessment §7):**

1. **CONFIRMED paper-side imprecision** — `step1.tex:308–311`'s
   `|I(z)| ≤ 2` is false for width-3 posets. mg-6ab8 §2.1 explicitly
   claimed "No vacuity-discovery surfaced ... bad-set bound" and
   stated the combinatorial bound as `O(n·t)` "always valid" — both
   are wrong. The S1-B port (mg-2e24) caught it; the pre-filing audit
   did not. The corrected combinatorial bound is `O(n·t²)`.

2. **Part-(iv) bad-set bound UNDELIVERED.** The landed
   `InterfaceConclusion` part (iv) ships the order-convexity
   *structural backbone* (iv.a–d) but **no `|Bad_{x,y}|` cardinality
   bound and no strip decomposition.** The corollary-level
   quantitative bounds (`lem:bounded-interaction`, `cor:overlap` (b)
   density, `cor:triple-overlap` (d) bad mass) are vacuous scaffolds:
   `bounded_interaction` is the content-free `|Int| ≤ |𝓛(P)|`.

3. **`goodFiberSet` non-emptiness / bulk-ness UNESTABLISHED.** Part (ii)
   as landed is a *tautological* partition (`badSet := univ \
   goodFiberSet`). Whether `goodFiberSet x y` is even non-empty — let
   alone `(1−o(1))·|𝓛(P)|` — is not proven. The whole point of
   `thm:interface` as a *tool* is "the good fibers are the bulk"; that
   is exactly the missing part-(iv) content. Downstream Steps 2/3/4
   dodge this by taking `IsGoodFiber` as a hypothesis and witnessing
   non-vacuity on hand-built singleton fibers.

**Severity = AMBER, not RED.** No theorem is false, no signature
unsatisfiable, no dead end. The interface theorem is sound, and
`|Bad| ≪ |F|` is true in the rich regime the corollaries explicitly
assume (§7). The re-scope is **bounded** — one S1 follow-on ticket to
assemble the deferred part-(iv) quantitative content in the corrected
exponent and to replace the vacuous corollary scaffolds. It is **not**
a re-architecture.

**Recommendation (§8):** **Do not start Wave-4 Step 6 assembly.** File
an S1-E follow-on first (§8.1). Step 6 individual grounded lemmas may
be ported in the hypothesis-taking style S4-A used, but the cascade
*assembly* (`thm:step4 → thm:step6` wiring) is blocked until the S1
part-(iv) quantitative delivery lands, because S4-B/S4-C consume it.

---

## §1. Scope and method

**Charter (ticket mg-8b95).** Audit whether the landed S1
`thm:interface` Lean port (S1-A mg-30e3 / S1-B mg-2e24 / S1-C mg-bcf2 /
S1-D mg-794c) surfaced a paper-side rigor gap not caught in the mg-6ab8
§2.1 pre-filing audit — specifically, whether the four parts of the
grounded `thm:interface` deliver the hypotheses Steps 2–6 consume.
**Mandate: probe satisfiability, not just type-compatibility** — a
type-checks-clean verdict is explicitly insufficient (the 8th vacuity,
mg-faf8, came from a type-only check).

**Method.** Paper-and-code reading. Read `step1.tex` `thm:interface`
(`:144–195`), its proof (`:197–388`), `lem:bounded-interaction`
(`:397–427`), `cor:overlap` / `cor:triple-overlap` (`:429–688`), and
the "Output interface for subsequent steps" section (`:690–731`).
Read every landed S1 Lean file (`Interface.lean`, `GroundSet.lean`,
`LocalCoords.lean`, `BadSet.lean`, `BKMoves.lean`, `Corollaries.lean`)
and the S1-A/B/C/D state docs. Traced the actual import-and-consume
edges from S1 into the landed Step 2/3/4/5/6 grounded ports.
Constructed a worked width-3 non-chain instantiation (§3, §5).

**Build state.** Working tree clean at `87ddbab` (S4-A). `grep` confirms
**no `sorry`, no `axiom`** in `lean/OneThird/Step1/` (the only textual
hits are inside an `Interface.lean` docstring). The S1-A/B/C/D state
docs attest `lake build` clean and `#print axioms` = the three standard
mathlib axioms. A full mathlib rebuild was not re-run — this is a
paper+code audit, docs-only deliverable; the attestations cover it.

---

## §2. What the landed S1 port delivers

`thm_interface` (`Step1/Interface.lean:167`) — for `hP :
HasWidthAtMost α 3`, a threshold `T`, and a rich pair `hxy : IsRich T x
y` — produces `InterfaceConclusion x y`, a conjunction of four parts:

* **Part (i) — coordinate map.** `IsChain (·≤·) (commonNbhd x y)` and
  `∀ L, localCoord x y L ∈ range(t+1) ×ˢ range(t+1)`. ✔ genuine,
  width-3 load-bearing.
* **Part (ii) — raw-fiber decomposition.** Raw fibers cover `univ`;
  `goodFiberSet x y ∪ badSet x y = univ`; `Disjoint goodFiberSet
  badSet`. **All three clauses are definitionally tautological**:
  `badSet := univ \ goodFiberSet` (`LocalCoords.lean:305`), and every
  `L` is in its own raw fiber. The substantive paper content of
  part (ii) — that `F_{x,y}` is a disjoint union of *good* raw fibers —
  is folded into the *definition* of `goodFiberSet` (the filter "∃ L₀,
  `IsGoodFiber (rawFiber …)`", `LocalCoords.lean:297`).
* **Part (iii) — BK-move classification.** The 4-way trichotomy on
  every BK move. ✔ genuine, fully proved (`bkMove_classification`).
* **Part (iv) — bad-set structural backbone.** Four clauses:
  (a) common neighbours pairwise comparable; (b) `incompLocus`
  order-convex; (c) external count `= n − t − 2`;
  (d) collinear-fiber card `≤ t + 1`. ✔ each genuine and proved.

Two corollaries: `cor_overlap` / `cor_triple_overlap`
(`Interface.lean:332,358`) deliver **only** the commuting-`2×2`-square
/ commuting-`2×2×2`-cube *existence* on `regularOverlap` /
`regularTripleOverlap` membership.

**Crucial gap at the level of §2 itself.** The ticket charter names
part (iv) "**bad-set bound**". The landed part (iv) is **not a
bad-set bound** — it carries no `|Bad_{x,y}|` cardinality statement
and no strip decomposition `Bad = ⋃_{k=1}^{K} S_k`, `K = O(1)`. It is
the *ingredients* of the bound, not the bound. See §4.

---

## §3. Finding 1 — the `|I(z)| ≤ 2` paper-side imprecision (CONFIRMED)

`step1.tex:307–311` (inside the proof of part (iv)) asserts:

> the set `I(z) := {k : z ∥ c_k}` is a contiguous interval of length
> `≤ 2`; otherwise `{z, c_{k₁}, c_{k₂}, c_{k₃}}` together with `{x, y}`
> would contain a width-4 antichain.

`lem:bounded-interaction` (`step1.tex:417–418`) re-cites this as
"any external element `z` … is incomparable to a contiguous interval
of `C_{x,y}` of length `≤ 2`".

**The length bound is false.** The S1-B port (mg-2e24,
`docs/state-S1-B-bkmoves-badset-Session1.md`) flagged it; this audit
re-derives the refutation independently and exhibits an explicit
worked width-3 non-chain counterexample.

### §3.1. Worked counterexample `P₆` (a natural width-3 non-chain poset)

* **Ground set** `X = {x, y, c₁, c₂, c₃, z}`, `n = 6`.
* **Order** (cover relations, all else incomparable): `c₁ < c₂ < c₃`
  and `z < x`.
* **Width 3.** Every antichain picks ≤ 1 of the chain `{c₁,c₂,c₃}`,
  ≤ 1 of the comparable pair `{z, x}`, plus possibly `y` — so
  `width(P₆) = 3` (witness `{x, y, c₂}`). **Non-chain** (`x ∥ y`).
* `commonNbhd x y = {w : w ∥ x ∧ w ∥ y} = {c₁, c₂, c₃}` — a chain;
  `t(x,y) = 3`. So `(x,y)` is **rich** at any `T ≤ 3`
  (`IsRich T x y` holds).
* `z` is **external**: `z < x` ⇒ `z ∦ x` ⇒ `z ∉ commonNbhd x y`, and
  `z ∉ {x, y}`. So `externalFinset x y = {z}`, `|Z| = 1 = n − t − 2`. ✔
* `incompLocus x y z = {c ∈ {c₁,c₂,c₃} : z ∥ c} = {c₁, c₂, c₃}`, since
  `z` is incomparable to all three (`z < x`, but `z` has no relation to
  any `c_k`). Hence **`|I(z)| = 3 > 2`** — the paper's length bound
  fails.

The paper's stated mechanism cannot fire: a width-4 antichain inside
`{x, y, z} ∪ {c_{k}}` would have to be `{x, y, z, c_k}` (the `c`'s are
pairwise comparable, so an antichain uses ≤ 1 of them), which needs
`z ∥ x` **and** `z ∥ y` — i.e. `z ∈ commonNbhd x y`, contradicting
`z` external. So **no such width-4 antichain exists for external `z`**,
and width 3 yields only **order-convexity** of `I(z)`, not a length
bound.

### §3.2. The failure persists into the rich regime

`P₆` has `t = 3`; scale it: take `C_{x,y} = c₁ < … < c_t` for any `t`,
with `z < x` and `z ∥ c_k` for all `k`. Then `(x,y)` is rich at
threshold `t`, and `I(z) = {1,…,t}` with `|I(z)| = t = Θ(n)`. The
incomparability locus of a single external element can span the
**entire** common chain. The order-convex form is the only correct
one — exactly what the S1-B/S1-D port landed
(`incompLocus_ordConvex`, `BadSet.lean:121`).

### §3.3. Consequence for the bad-set bound

The paper's part-(iv) strip count uses `|I(z)| ≤ 2` to bound the bad
raw fibers per strip by `Σ_z |I(z)| ≤ 2|Z| = O(n)`, giving
`|Bad| = O(n·t)`. With the corrected `|I(z)| ≤ t`, the per-strip count
is `Σ_z |I(z)| ≤ t·|Z| = O(n·t)`, and (× per-fiber size `≤ t+1`)
`|Bad_{x,y}| = O(n·t²)` — one factor of `t` worse than the paper's
`O(n·t)`. The S1-D port adopted option (b) (accept `O(n·t²)`); this
audit endorses that as faithful — but see §4 for what was *not* then
delivered.

**mg-6ab8 §2.1 missed this.** It stated "Paper-side rigour. Rigorous …
**No vacuity-discovery surfaced** under skeptical re-read of the
bad-set bound" and "the combinatorial bound `O(n·t)` (always valid)".
The S1 port refutes both. The Checkpoint-1 question — *"paper-side gap
in S1 `thm:interface` port not caught by the pre-filing audit?"* — has
a factual **YES**. Verdict cannot be GREEN.

---

## §4. Finding 2 — the operative part-(iv) bad-set bound is UNDELIVERED

The paper's "Output interface for subsequent steps" (`step1.tex:690–
714`) lists **four** deliverables; #4 is:

> **Bad set bound.** `|Bad_{x,y}| ≪ |F_{x,y}|`, contained in `O(1)`
> strips of width `O(t)`.

and the scoping doc §2.1 (line 590) lists S1's deliverable as
"`thm:interface` (4 parts) + 2 corollaries + **bad-set bound**".

**The landed S1 port delivers none of the quantitative content:**

* `InterfaceConclusion` part (iv) carries the order-convexity
  *backbone* (a–d) but **no `|Bad|` cardinality bound, no strip
  decomposition.** "Bad-set bound" is delivered as ingredients only.
* `Corollaries.lean` `bounded_interaction` (`:182`) is the **vacuous**
  `|interactionLocus x y u v| ≤ Fintype.card (LinearExt α)` — i.e.
  `|Int| ≤ |𝓛(P)|`, a content-free bound. The paper bound is
  `|Int| = O((t_{xy}+t_{uv})²)`.
* `regularOverlap_density` (`:284`) / `regularTripleOverlap_density`
  (`:394`) are **genuine set-theoretic containments**
  (`Ω∖Ω° ⊆ Int`, `Ω³∖Ω³° ⊆ Σ Int`) — true and useful *as
  containments*, but chained with the vacuous `bounded_interaction`
  they yield only `|Ω∖Ω°| ≤ |𝓛(P)|` — vacuous as a density statement.
* `cor_overlap` / `cor_triple_overlap` deliver the commuting
  square/cube only; **`cor:overlap` part (b) (positive density) and
  `cor:triple-overlap` part (d) (bad mass `O(t·√|Ω³|)`) are not
  delivered.**

This is **disclosed** in the port: `Corollaries.lean` §"Scaffold vs.
paper strength" and S1-D state doc §5 ("Scope boundary (honest)")
explicitly de-scope the quantitative bounds — "They are
Step-4/Step-7 consumption-time concerns, not Step 1 assembly", "No
current consumer needs it."

**But "no current consumer needs it" is a *local* truth that masks a
*cascade-level* gap.** It holds only because the landed downstream
ports (S2, S3, S4-A) are themselves partial and defer their own
assembly (§6). The composite obligation — "S1 delivers what
Steps 2–7 consume" — is **not** satisfied. The bad-set bound and the
density bounds are consumed at **S4-B / S4-C** (the per-block
incompatibility `lem:rect-stable-area` and the global counting
`prop:G5` — `step1.tex:725`: "the bad-set bound ensures lower-order
loss when summing over overlap blocks") and at **Step 7 G4**
(`cor:triple-overlap` (d)). Neither S4-B nor S4-C is landed yet; when
they are attempted they will hit this wall.

This is the **mismatch a hold-the-line checkpoint exists to catch**:
the landed S1 port quietly narrowed its scope below what the scoping
doc specified and what the downstream cascade assumes, with each
individual landed theorem honest about its own narrowed scope.

---

## §5. Finding 3 — satisfiability probe: `goodFiberSet` non-emptiness / bulk-ness

Per the audit charter ("verify the delivered hypotheses are
**satisfiable** on natural width-3 non-chain inputs, with a worked
instantiation"):

**The four parts of `InterfaceConclusion` are each delivered, type-
clean, and individually satisfiable** — every clause is witnessed at
`Antichain3` (`thm_interface_nonvacuous`) and would hold at `P₆` of
§3.1 (`thm_interface` is universally quantified over width-3 rich
pairs; its hypotheses `HasWidthAtMost α 3` + `IsRich T x y` are
satisfiable, non-vacuously, at both). **There is no unsatisfiable
delivered signature** — this is why the verdict is AMBER, not RED.

**But the operative hypothesis the cascade needs is not among the
delivered ones.** Trace the S1 → S2 edge concretely:

* Step 2's grounded transport (`per_fiber_weak_grid`,
  `fiberBKBdy_card_eq_gridBdy_card`, `Step2/PerFiberGrounded.lean`)
  consumes `IsGoodFiber x y F` as an **explicit hypothesis** on a
  fiber `F`. It never calls `thm_interface` to *obtain* `F`.
* `thm_interface` part (ii) hands over `goodFiberSet x y` (a `Finset`)
  with the tautological partition. It does **not** hand over an
  `IsGoodFiber` witness, nor a proof that `goodFiberSet x y ≠ ∅`.
* By the *definition* of `goodFiberSet` (union of good raw fibers),
  `goodFiberSet x y ≠ ∅ ⟺ ∃ a good raw fiber`. So "a usable good
  fiber exists" **is exactly** `goodFiberSet x y ≠ ∅` — and the S1
  port proves no lower bound on `|goodFiberSet x y|`, not even
  non-emptiness.
* Step 2's own non-vacuity witness (`per_fiber_grounded_nonvacuous`)
  sidesteps this: it builds its good fiber as a **hand-made singleton**
  `{L}` via `isGoodFiber_singleton` (G1/G2/G3 hold trivially on one
  point). That singleton is **not** a `rawFiber` produced by Step 1.

**Worked instantiation of the gap.** On `P₆` (§3.1): `thm_interface x
y` fires and delivers `InterfaceConclusion x y` — all four parts,
type-clean, each satisfiable. Yet:

* the part-(iv) clause the cascade actually needs — `|Bad_{x,y}| ≪
  |F_{x,y}|`, equivalently `goodFiberSet x y` is the bulk of `𝓛(P₆)` —
  is **not in `InterfaceConclusion` at all**, so it cannot be
  instantiated;
* consequently Step 2's `per_fiber_weak_grid` **cannot be fired on an
  S1-produced good fiber of `P₆`** — only on an artificial singleton.

This is the satisfiability failure the charter demands be surfaced:
**not** "a delivered hypothesis is unsatisfiable" (that would be RED,
the 8th-vacuity pattern) but "**the delivered hypotheses are a strict,
type-clean subset of what downstream consumes, and the omitted one —
bad-set negligibility / good-fiber bulk-ness — is the operative
one.**" A pure type-compatibility check passes; a satisfiability check
of *the cascade* does not.

---

## §6. Downstream consumption map — what S2/S3/S4/S5/S6 actually consume from S1

| Step | Imports S1? | What it consumes | Bad-set / density bound consumed? |
|---|---|---|---|
| **S2** `PerFiberGrounded.lean` | `Step1.Interface`, `Step1.GroundSet` | `IsGoodFiber x y F` as an **explicit hypothesis** (clauses G1/G2/G3). Never invokes `thm_interface`. | No — takes good fibers as given. |
| **S3** `LocalSignGrounded.lean` | **No** (imports `Step2.PerFiberGrounded2`) | Step 2's staircase output `IsStaircasePlus`. Explicitly "needs *no* order-convexity of `D`". | No. |
| **S4-A** `WitnessGrounded.lean` | `Step1.Overlap`, `Step1.BKMoves` | `BKCommSquare` / `bkCommSquare_of_disjoint` (the commuting-square output). The witness lower bound `hWitLB` is **deferred to S4-B/C as a hypothesis**. | No — deferred. |
| **S5** `GroundSet.lean` | `Step1.GroundSet` | Only the `Antichain3` witness poset (re-use). Not a substantive `thm_interface` consumer. | No. |
| **S6** `CommutingSquare.lean` | `Step1.Corollaries` | `regularOverlap` / `badSet` / `interactionLocus`; proves the set-theoretic `|Ω| − |Ω°| ≤ |Int|`. Docstring claims `o(|Ω|)` "in the rich regime" — **unbacked** (depends on the deferred `bounded_interaction`). | Set-theoretic containment only; the `o(|Ω|)` negligibility is **asserted in prose, not proved**. |

**Reading.** Every landed consumer takes the *structural* outputs
(`IsGoodFiber` predicate, `BKCommSquare`, set-theoretic
containments) — never the quantitative bad-set / interaction-locus /
density bounds. So no landed step *currently fails*. The quantitative
bounds are first genuinely needed at **S4-B/S4-C** (not landed) and
**Step 7 G4**. Step 6's grounded lemmas are portable in the
hypothesis-taking style, but Step 6's docstring already over-claims
the `o(|Ω|)` it cannot yet prove.

---

## §7. Satisfiability of the paper claim `|Bad_{x,y}| ≪ |F_{x,y}|`

Is the paper's part-(iv) negligibility *itself* sound? Examined,
because if it were false the verdict would be RED.

* The combinatorial bound is, corrected, `|Bad_{x,y}| = O(|Z|·t²)`
  (the strip count carries a `|Z|` factor — `Bad = ∅` when `Z = ∅`).
* Negligibility `|Bad| ≪ |F_{x,y}|` needs `|F_{x,y}| ≫ |Z|·t²`.
* The paper supplies this via the **quantitative richness**
  `|F_{x,y}| ≥ c·n²` — and `cor:overlap` (b) / `cor:triple-overlap`
  (d) **explicitly assume the rich regime** `t_{xy}, t_{uv} = Θ(n)`,
  `|Ω| ≫ n²`. In that regime `|F_{x,y}|` is factorial-scale (free
  orderings of `Z`) and dominates `O(|Z|·t²) = poly(n)`. So
  **`|Bad| ≪ |F_{x,y}|` is TRUE in the rich regime** the corollaries
  use — the cascade is sound, and the `O(n·t) → O(n·t²)` weakening
  does not break it (poly vs. factorial).
* **Disclosed soft spot.** The paper's justification that
  `|F_{x,y}| ≥ c·n²` is "automatic in the main application"
  (`step1.tex:380–387`) is a *sketch*: it asserts "≥ `|Z|!/t^{O(1)}`
  good external classes" without bounding the count of *bad* external
  classes. The negligibility is therefore a **rich-regime
  conditional**, not an unconditional structural fact. The paper does
  state the conditional ("Outside this regime the combinatorial bound
  is the operative one") — so it is a *disclosed* conditional, not a
  hidden rigor gap. mg-6ab8 §2.1 did note the two-form structure of
  the bound (its "Hidden constraints" item 1) but mis-stated the
  combinatorial form as `O(n·t)` and as "always valid" for
  negligibility, which it is not.

**Conclusion of §7.** The paper math is sound; `|Bad| ≪ |F|` holds in
the operative regime. The gap is *delivery* (Finding 2) plus a
*disclosed conditional* that the Lean port must thread explicitly
rather than silently — not broken mathematics. This is what keeps the
verdict at AMBER and off RED.

---

## §8. Verdict and recommendation

**Verdict: AMBER.** The S1 `thm:interface` port surfaced a paper-side
rigor gap not caught pre-filing (the `|I(z)| ≤ 2` imprecision, §3) and,
more consequentially, the landed port does **not** deliver the
operative part-(iv) bad-set bound or the corollary density bounds
(§4) — they sit as vacuous `≤ |𝓛(P)|` scaffolds. The four parts as
landed deliver structural backbones plus a tautological partition;
the satisfiability content the cascade needs ("good fibers are the
bulk") is absent (§5). This is a **bounded re-scope**, not a
re-architecture (§7): the math is sound and `|Bad| ≪ |F|` holds in
the rich regime.

### §8.1. Required before Wave-4 Step 6 — file an S1-E follow-on

A single S1 follow-on ticket (suggested id **S1-E**), scope ~1
polecat / ~300–500k tokens:

1. **Assemble the part-(iv) bad-set cardinality bound** in the
   **corrected** `|Bad_{x,y}| = O(|Z|·t²)` form (the `|I(z)| ≤ 2 →
   order-convexity` correction is already in tree as
   `incompLocus_ordConvex`; the strip count + `collinear_fiber_card_le`
   are in tree — what is missing is the *assembly* into a cardinality
   statement).
2. **Replace the vacuous `Corollaries.lean` scaffolds.** Upgrade
   `bounded_interaction` from `|Int| ≤ |𝓛(P)|` to the genuine
   `O((t_{xy}+t_{uv})²)` bound, and thereby make
   `regularOverlap_density` / `regularTripleOverlap_density`
   informative. Deliver `cor:overlap` (b) and `cor:triple-overlap`
   (d).
3. **Thread the rich-regime richness hypothesis explicitly.** The
   negligibility `|Bad| = o(|𝓛(P)|)` / `goodFiberSet` bulk-ness is a
   *rich-regime conditional* (§7). Carry `|F_{x,y}| ≥ c·n²` (or the
   underlying `|Z|!`-class lower bound) as a **documented hypothesis**
   threaded from Step 5(R) richness — *not* as a free-standing
   universal theorem — analogous to how the cascade threads other
   Step 5 outputs. Proving the `|Z|!` lower bound outright is optional
   and can be a sub-item.
4. **Decide the `goodFiberSet`-non-emptiness wiring.** Either expose a
   lemma `goodFiberSet_nonempty_of_…` so downstream can extract a
   genuine `IsGoodFiber` raw fiber from `thm_interface`, or document
   that downstream must `unfold goodFiberSet` — but make the
   non-emptiness itself a *proved* consequence of (3).

### §8.2. Doc corrections (done in this commit where low-risk)

* `OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.1 / §3.3 — record
  the Checkpoint-1 AMBER outcome and the corrected exponent.
* `OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) §2.1 — the
  "no vacuity-discovery surfaced" / "`O(n·t)` always valid" claims are
  refuted; an amendment banner is added.

### §8.3. Step 6 gating

Wave-4 **Step 6 must not enter cascade assembly** until S1-E lands:
S4-B / S4-C consume the part-(iv) quantitative bounds, and Step 6
consumes a *completed* Step 4. Step 6's individual grounded lemmas
(G6–G10) may be ported in the hypothesis-taking style S4-A used —
that work is not blocked — but `thm:step6` assembly is. Step 6's
`CommutingSquare.lean` docstring claim of `o(|Ω|)` density should be
softened to "set-theoretic containment; the `o(|Ω|)` negligibility is
supplied by S1-E" until S1-E lands.

---

## §9. Skeptical re-audit of this audit (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2 checklist)

1. **Satisfiability.** The verdict does not rest on a type check. The
   `|I(z)| ≤ 2` refutation is a concrete poset `P₆` (§3.1). The
   delivery gap is demonstrated by tracing the S1→S2 edge to an
   `IsGoodFiber`-as-hypothesis with no S1-side producer, and by the
   `bounded_interaction : |Int| ≤ |𝓛(P)|` vacuous body.
2. **Discharge-coverage.** No artefact is over-credited: the audit
   reads the *bodies* of `bounded_interaction`, `regularOverlap_
   density`, `InterfaceConclusion`, `per_fiber_weak_grid`,
   `isGoodFiber_singleton` — not their names or docstrings.
3. **Universal-quantifier truthfulness.** The audit's own central
   negative claim ("`|I(z)| ≤ 2` is false") is backed by an explicit
   counterexample, not asserted. The positive claim ("`|Bad| ≪ |F|`
   holds in the rich regime") is qualified to the regime the
   corollaries assume, and the soft spot (§7) is disclosed, not
   hidden.

---

## §10. Files

* `docs/state-S1234-QA-Checkpoint1-Session1.md` — this file (NEW).
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` — §3.3 Checkpoint 1
  outcome recorded; §2.1 exponent corrected.
* `docs/OneThird-Steps-1-7-Lean-port-scoping.md` — §2.1 amendment
  banner (the `|I(z)| ≤ 2` refutation).

No Lean source changed — this is an audit.
