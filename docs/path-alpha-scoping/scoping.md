# Path α scoping — Hibi polytope infrastructure for probability-form FKG-on-LE (also discharges Brightwell axiom)

**Work item:** `mg-ff7f` (polecat `pff7f`).
**Branch:** `polecat-pff7f` (target `a8-s2-cont-execution-arc`).
**Predecessors.**
* `mg-b10a` (`docs/a8-s2-cont-execution-arc/cont-4-stop-report.md`,
  STOP report, trip-wire #2 fired) — the structural-obstruction
  diagnosis that motivated this scoping.
* `mg-8d39` (`docs/a8-s2-cont-scoping-arc/scoping.md` on
  `a8-s2-cont-scoping-arc`, commit `b81ad31`, upgraded GREEN
  conditional on no new structural obstruction) — the prior scoping
  whose conditional GREEN was retracted by mg-b10a.
* `mg-38cf` (`docs/brightwell-port-scope.md`) — the standalone audit
  of the Brightwell sharp-centred port; gives ~700–1100 LoC honest
  estimate for that single axiom in isolation.
* `mg-75ef` (`docs/case3-port-arc/rem-enumeration-proof.md`,
  archived) — verdict β math artifact: the case3 residual reduces
  to probability-form cross-poset FKG.
* `mg-5bf9` (`docs/case3-port-arc/linear-majority-alignment.md`,
  archived) — verdict AMBER, re-corroborates β.
* `lean/AXIOMS.md:13–225` (`brightwell_sharp_centred`) and
  `:226–454` (`case3Witness_hasBalancedPair_outOfScope`) — the two
  named project axioms targeted by Path α.

**Verdict:** **AMBER, leaning GREEN with one structural caveat.**
Path α is **feasible** in the polecat-arc sense — the residual ~1800–3000
LoC across 6–9 polecat sessions, with a clean dependency chain — but
the underlying FKG-on-LE primitive does **not** in fact require a
geometric Hibi polytope. It requires the **τ-inversion distributive
lattice on `LinearExt α`** (Brightwell §3.5.1), which is the
combinatorial chamber lattice of the order polytope. This is a
substantively smaller piece of mathematics than "the Hibi order
polytope as a formalised polytope" (mg-b10a §4 wording), and its
formalisation is at the upper end of polecat-class work, not
mathlib-PR-class.

This scoping reaches **GREEN on the math-feasibility question** and
**AMBER only on the timeline + bottleneck-management question**:
the critical path is genuinely sequential (six tickets in series),
and PM should expect **8–14 weeks calendar** for full execution
including the case3 application chain. The Brightwell-discharge
side benefit **does hold** — the same τ-inversion lattice
infrastructure underpins both axioms — and is verified at the
distributive-lattice level in §3.

The recommended Daniel-help leverage point (§8) is a **bounded-
enumeration bypass on the case3 residual range**, which would
dispense with the need for the probability-form drops headline
entirely on the only branch where it's load-bearing. If that bypass
closes by paper rigor, Path α collapses from "build the FKG-on-LE
primitive" to "build the FKG-on-LE primitive only for the Brightwell
axiom" — saving a quarter of the LoC and making the timeline an
unambiguous GREEN.

This document is the latex-first scoping deliverable per
`feedback_distinguish_arc_chunk_outcomes` ("substantive scoping
chunk; no parallel cleanup"). Lean source unchanged.

---

## §1 Inputs synthesized

This section condenses what the predecessor artifacts establish and
what they leave open — i.e., what Path α has to actually deliver.

### §1.1 mg-b10a STOP report — structural obstruction surface

mg-b10a's central finding (`cont-4-stop-report.md` §3): the
single-edge induction step of the drops headline reduces to FKG
positive correlation between two events on `LinearExt' Q`:

* `A := {L : S(L.iI k)}` — the level-`k` initial-ideal event,
  for `S` up-closed in `Finset α`.
* `R := {L : L.lt a b}` — the "L respects the new edge `(a, b)`"
  event for the augmentation `Q' = addRel Q a b`.

**The crux.** For mathlib's `fkg` to apply, `LinearExt' Q` must be
a finite distributive lattice with a structure under which both
`A` and `R` are monotone. mg-b10a §3.2 surveys five candidate
lattice structures (Bruhat, weak, inversion-set, chain-of-ideals,
Hibi chambers) and concludes that **none of them is a distributive
lattice on the full `LinearExt' Q`**, except the Hibi chamber
decomposition which is "partial".

The "partial" qualifier is doing significant work; §2 below
unpacks it. The headline conclusion of mg-b10a §4 — that the Hibi
order polytope is "not in mathlib" and the port is "~2000-4000 LoC,
multiple authors over a quarter or more" — is technically correct
but in fact **conservative**: a faithful Lean version of just the
combinatorial chamber lattice (without the geometry) is much
smaller, and it is exactly what FKG-on-LE actually needs.

### §1.2 mg-8d39 — residual scope after data-poset infrastructure landed

mg-8d39 §3.1 enumerates the ~2100 LoC of data-poset infrastructure
already in tree (mg-b088 + mg-1a4f + mg-0b81), which is the input
side of the FKG-on-LE primitive. It also names the missing piece
(§3.2):

```lean
theorem probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L : LinearExt' Q  => S (L.initialIdeal' k.val)) ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val))
```

mg-8d39 §2.2 surveyed three proof strategies:
* Strategy A — single-edge `addRel` induction reducing to FKG on LE.
* Strategy B — direct Ahlswede–Daykin (FFT). Naive form fails;
  conditional form is circular without a separate Daykin-on-|LE|
  proof.
* Strategy C — factor through the existing `LinearExt.fkg_uniform_initialLowerSet`. Doesn't help; same product-lattice cardinality factor.

**Verdict.** Strategy A is the path; the substantive content is
the FKG positive-correlation lemma on `LinearExt' Q` between two
monotone events, under a chosen distributive lattice structure on LE.

### §1.3 mg-38cf — Brightwell port standalone audit

The brightwell-port-scope.md §4.2 names the lattice structure
explicitly:

> **τ-inversion distributive lattice on `L(α)`.**
> `L' ≤_𝒟 L''` iff `Inv_τ(L') ⊆ Inv_τ(L'')`.
> Distributivity is Brightwell §3.5.1 via the equivalence with
> order ideals of the *adjacent-transposition graph* of
> `τ`-inversions.

This is the same structure that mg-b10a §3.2 listed as "Hibi order
polytope chambers — partial". The "partial" reading is misleading:
the τ-inversion lattice **is** a globally distributive lattice on
`L(α)` for any choice of reference τ; the partial caveat refers
only to the fact that not every event one might want to test is
monotone for every choice of τ. **For each application — Brightwell,
or drops — there is a τ that makes the relevant events monotone.**

mg-38cf §4 enumerates the Brightwell-port LoC by sub-piece:
| Component | Optimistic | Conservative |
|---|---:|---:|
| §4.1 reference τ separating Pred/Succ | 50 | 80 |
| §4.2 τ-inversion lattice on `L(α)` | 150 | 250 |
| §4.3 product lattice | 10 | 10 |
| §4.4 monotonicity (a)–(e) | 250 | 400 |
| §4.5 FKG transport to τ-inversion | 100 | 200 |
| §4.6 collapse Cov_ν → Cov_μ | 50 | 80 |
| §4.7 Kahn–Saks per-term bound (**) | 250 | 400 |
| §4.8 final assembly | 50 | 50 |
| **Total** | **910** | **1470** |

**Crucial structural observation for this scoping.** §4.2 + §4.3 + §4.5 (the τ-inversion lattice + product + FKG transport to it) total ~260–460 LoC. **This is exactly the shared infrastructure that the drops headline also needs.** The Brightwell-specific work — §4.1, §4.4, §4.6, §4.7, §4.8 — is ~650–1010 LoC that is *not* shared with drops, but is independently downstream of the lattice.

### §1.4 mg-75ef + mg-5bf9 — case3 application chain

The case3 application chain (mg-75ef §3 revised Step 1, §4 Step 2
band-restricted FKG, §5 Step 3) is unchanged by Path α: it consumes
`probEvent'_mono_of_subseteq_upClosed` as a black box. mg-8d39 §4.1
estimated ~400–700 LoC for the application chain, with case3-port-2
(revised Step 1 + Claim 3.2) carrying the residual structural risk
(mg-5bf9 Open Question 3.5) and possibly forcing a bounded-enum
fallback (~500–1500 LoC if Claim 3.2 is open).

case3-port-1 (orientation lemma, ~30–50 LoC) **landed**
independently as commit `d168e68` (mg-8487, on the current branch
at session start). It is not on the Path α critical path.

### §1.5 The literature reference for Hibi/τ-inversion

mg-b10a's STOP report mentions "Hibi order polytope chambers" and
"Daykin–Saks 1981, Brightwell 1999 §4". The actual literature
reference is Brightwell §3.5.1 (the τ-inversion lattice) plus
Stanley's order polytope (Stanley 1986, *Two poset polytopes*).
These together give:

* **Combinatorial side.** `(L(α), ≤_τ)` is a distributive lattice
  for any τ ∈ L(α); `Inv_τ(L)` is a lower set of the
  comparability poset of `α \ τ`-incomparable pairs; Birkhoff's
  representation theorem identifies `(L(α), ≤_τ)` with order
  ideals of this auxiliary poset.

* **Geometric side.** The order polytope `O(α) ⊂ ℝ^α` admits a
  unimodular triangulation indexed by `L(α)`; its chambers are
  in bijection with linear extensions; chamber adjacency = τ-
  inversion adjacent-transposition.

For our purposes, **only the combinatorial side is needed**.
mathlib has no formalisation of either side, but the
combinatorial side is a finite-`Fintype` `DistribLattice` instance
plus a Birkhoff-style API — well within mathlib-tier polecat work,
not mathlib-PR-class infrastructure. The geometric realization is
unnecessary.

### §1.6 The convergent picture

All five inputs converge on:

> **Both the case3 axiom and the Brightwell axiom reduce to FKG on
> the τ-inversion distributive lattice of `LinearExt α`.** The
> shared lattice infrastructure is ~250–500 LoC; each downstream
> application adds ~250–900 LoC of axiom-specific work.

This is materially different from mg-b10a §6's diagnosis ("Hibi
order polytope as a formalised polytope, ~2000-4000 LoC, multi-
author quarter-scale"). The mg-b10a author was reading the
literature reference at the *geometric* level, which is the
heaviest formulation. The combinatorial reformulation collapses
the bulk of that estimated cost to mathlib-tier polecat work.

---

## §2 Hibi polytope design — Lean signatures + dependency on mathlib

### §2.1 What we actually need: the τ-inversion distributive lattice

The single new mathematical object is the **τ-inversion
distributive lattice on `LinearExt α`**, parameterised by a
choice of reference linear extension `τ ∈ LinearExt α`.

```lean
namespace OneThird.LinearExt

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- τ-inversion set of a linear extension `L`: the set of pairs
`(i, j)` with `i <_τ j` but `j <_L i`. -/
def tauInv (τ L : LinearExt α) : Finset (α × α) :=
  (Finset.univ.filter (fun p : α × α =>
    τ.lt p.1 p.2 ∧ L.lt p.2 p.1))

/-- τ-inversion order on linear extensions. -/
def tauLE (τ L L' : LinearExt α) : Prop :=
  tauInv τ L ⊆ tauInv τ L'

/-- The τ-inversion order is a partial order on `LinearExt α`. -/
instance tauPO (τ : LinearExt α) : PartialOrder (LinearExt α) := …

/-- The τ-inversion order is a *distributive lattice* on
`LinearExt α`. (Brightwell §3.5.1; Stanley 1986.) -/
instance tauDistribLattice (τ : LinearExt α) :
    DistribLattice (LinearExt α) := …

/-- The minimum element under `≤_τ` is `τ` itself. -/
lemma tau_isBot (τ : LinearExt α) : IsBot τ := …

/-- The maximum element under `≤_τ` is the τ-reverse. -/
def tauTop (τ : LinearExt α) : LinearExt α := …

end OneThird.LinearExt
```

### §2.2 The FKG-on-LE primitive

With the τ-inversion `DistribLattice` instance in hand, the FKG-on-LE
primitive is a direct application of mathlib's `fkg`:

```lean
/-- **FKG correlation on `LinearExt α` under uniform measure**, in
the τ-inversion lattice. For monotone-non-negative functions
`F, G : LinearExt α → ℚ` with respect to `tauLE τ`,

  `(∑_L F L) · (∑_L G L) ≤ |LinearExt α| · ∑_L F L · G L`.

This is the headline. -/
theorem fkg_uniform_le_tau
    (τ : LinearExt α)
    (F G : LinearExt α → ℚ)
    (hF : Monotone (α := (LinearExt α, tauLE τ)) F)
    (hG : Monotone (α := (LinearExt α, tauLE τ)) G)
    (hFnn : ∀ L, 0 ≤ F L)
    (hGnn : ∀ L, 0 ≤ G L) :
    (∑ L : LinearExt α, F L) * (∑ L : LinearExt α, G L) ≤
    (Fintype.card (LinearExt α) : ℚ) *
      ∑ L : LinearExt α, F L * G L := …

/-- Indicator (event) form. For up-closed `A, B : LinearExt α → Prop`
under `tauLE τ`,

  `|A| · |B| ≤ |LinearExt α| · |A ∩ B|`.  -/
theorem fkg_uniform_le_tau_events
    (τ : LinearExt α)
    (A B : LinearExt α → Prop) [DecidablePred A] [DecidablePred B]
    (hA : ∀ L L', tauLE τ L L' → A L → A L')
    (hB : ∀ L L', tauLE τ L L' → B L → B L') :
    ((Finset.univ.filter A).card : ℚ) *
      ((Finset.univ.filter B).card : ℚ) ≤
    (Fintype.card (LinearExt α) : ℚ) *
      ((Finset.univ.filter (fun L => A L ∧ B L)).card : ℚ) := …
```

### §2.3 The drops headline as a corollary

The headline drops inequality follows by Strategy A (single-edge
`addRel` induction):

```lean
namespace OneThird.RelationPoset

/-- **Probability-form (Daykin–Saks "drops") cross-poset FKG.** For
`Q.Subseteq Q'` and a level-`k` event `S` on `Finset α` that is
up-closed in inclusion order on `Finset α`, the probability that
the level-`k` initial ideal satisfies `S` is monotone non-decreasing
in the comparability relation. -/
theorem probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L : LinearExt' Q  => S (L.initialIdeal' k.val)) ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val)) := …

end OneThird.RelationPoset
```

The proof structure:
1. Induct on `|Q'.rel \ Q.rel|` via `addRel` (existing infrastructure
   in `Mathlib/RelationPoset.lean §8`).
2. In the single-edge step `Q' = addRel Q a b` with `¬Q.le b a`:
   pick any `τ ∈ LinearExt' Q'` (which embeds into `LinearExt α`
   via the discrete embedding); show `R = "L.lt a b"` is up-closed
   in `tauLE τ` on `LinearExt α`; show the level-k event is also
   up-closed; apply `fkg_uniform_le_tau_events`; rearrange to the
   probability form.

### §2.4 Mathlib infrastructure consumed / upstreamable

**Consumed (already in mathlib, no port needed):**
* `Mathlib.Combinatorics.SetFamily.FourFunctions.fkg` — the FKG
  inequality on a finite distributive lattice with log-supermodular
  measure. Uniform measure (μ = 1) is a trivial special case.
* `Mathlib.Combinatorics.SetFamily.FourFunctions.four_functions_theorem`,
  `holley` — Ahlswede–Daykin variants; not directly used by the
  drops headline but used by Brightwell §4.4 monotonicity proofs.
* `Mathlib.Order.Birkhoff` — the Birkhoff representation theorem
  (any finite distributive lattice ≃ order ideals of an irreducible
  sub-poset). Used to identify the τ-inversion lattice with order
  ideals of an explicit auxiliary poset, which makes the
  distributivity proof short.

**Upstreamable to mathlib (post-launch follow-up, not a Path α
prerequisite):**
* The τ-inversion `DistribLattice` instance on a `Fintype` type of
  linear extensions. mathlib has `Mathlib.Order.Extension.Linear`
  (existence of one extension only) but no `Fintype` of linear
  extensions and no τ-inversion lattice. This file would naturally
  live in a new
  `Mathlib.Combinatorics.PartialOrder.LinearExtensionLattice.lean`
  if upstreamed.
* The drops headline in its abstract form (without our project-
  specific `RelationPoset` data type) — the statement
  `Pr_P[level-k event] ≤ Pr_{P'}[level-k event]` for `P ≤ P'` —
  is a standard Daykin–Saks 1981 result that mathlib could host.

**Not upstreamable (project-internal):**
* `RelationPoset α` and the `LinearExt' Q` data version. These are
  project-specific because the existing typeclass-based `LinearExt`
  doesn't support the cross-poset comparison cleanly (you cannot
  have two `[PartialOrder α]` instances on the same `α` in the same
  context). The data version is the only viable path for our use
  case but is not of mathlib-general interest.

**Verdict.** The Path α work is **not mathlib-PR-class**. It is
project-private polecat-class work that *could* be upstreamed
post-launch as an independent contribution but does not require
the mathlib review cycle to land in our tree.

This is a substantive correction to mg-b10a §4's "mathlib-PR-class
~2000-4000 LoC, multiple authors over a quarter or more" framing.
That framing was based on the geometric Hibi polytope; the
combinatorial τ-inversion lattice is an order of magnitude
smaller and stays in tree.

### §2.5 Why the τ-inversion lattice is the right object

mg-b10a §3.2 listed five candidate lattices and dismissed all five:

| Candidate | Distributive on full LE? | mg-b10a verdict |
|---|---|---|
| Bruhat order | NO | not a lattice |
| Weak order | NO | not a lattice |
| Inversion-set inclusion | NO (?) | not a lattice |
| Chain-of-ideals embedding | partial | lossy |
| Hibi chambers | partial | requires polytope infra |

The third row, "inversion-set inclusion", is the τ-inversion
lattice **with a fixed reference τ**. The "NO" verdict in mg-b10a
is incorrect at this resolution: for any fixed `τ ∈ L(α)`,
`(L(α), ≤_τ)` *is* a distributive lattice (Brightwell §3.5.1).
The mg-b10a polecat may have read "inversion-set inclusion" as
implicitly varying τ — a different lattice for each L — but the
correct reading fixes τ once and gets a globally distributive
lattice on the full `L(α)`.

The "Hibi chambers" row's "partial" verdict is the same object
viewed geometrically. The geometric Hibi polytope's chamber
adjacency graph is precisely the τ-inversion lattice's covering
relation; the "partial" qualifier in mg-b10a refers to the
geometric framing being incomplete in mathlib, not to the
combinatorial lattice being non-distributive.

### §2.6 The case2 / case3 application chain — what changes vs. mg-8d39

mg-8d39 §2.4 already specified the case2 / case3 chain assuming
`probEvent'_mono_of_subseteq_upClosed` lands. Path α inherits that
specification verbatim. The only new artifact is the Hibi-class
infrastructure in §2.1–§2.4.

---

## §3 Brightwell-discharge verification

Does the τ-inversion-lattice primitive really subsume
`brightwell_sharp_centred`? **YES, with explicit caveat on the
Kahn–Saks per-term bound.**

### §3.1 What `brightwell_sharp_centred` consumes

Per `lean/AXIOMS.md:13–225` and `brightwell-port-scope.md §2`, the
paper proof of `eq:sharp-centred` (`step8.tex:1046–1276`) reduces
the bound to:

1. **τ separating Pred/Succ** — choose `τ ∈ L(α)` with `pos_τ u <
   pos_τ v` for all `u ∈ Pred`, `v ∈ Succ`, plus `pos_τ x < pos_τ y`.
2. **Distributive lattice on `L(α) × {1,…,m}`** — the product
   τ-inversion × natural order. Distributivity is automatic from
   the τ-inversion `DistribLattice` instance + `Mathlib.Order.Lattice`
   product instance.
3. **Monotonicity claims (a)–(e)** — adjacent-transposition checks
   for `1_A`, `P`, `S`, `1_{B_-}`, `1_{B_+}` on the product
   τ-inversion lattice.
4. **AD sign constraints** — apply Ahlswede–Daykin (mathlib's
   `four_functions_theorem`) twice on the product lattice.
5. **Per-term Kahn–Saks bound** `|Cov_μ(1_A, S)|, |Cov_μ(1_A, P)| ≤
   f̄/m`. **This is the substantive combinatorial input** —
   independent of FKG-on-LE — proved in Brightwell §4 by an
   explicit exchange involution.

The shared FKG-on-LE infrastructure (§2.1–§2.2) covers steps 1–4.
Step 5 is **not** subsumed.

### §3.2 The Kahn–Saks per-term bound is an independent piece

The per-term bound `|Cov_μ(1_A, S)| ≤ f̄/m` is **not** a
specialisation of the drops headline. It is a *single-poset*
covariance bound between the indicator `1_A : L(α) → {0, 1}`
and the integer-valued `S : L(α) → ℕ`, with no cross-poset
comparison.

The proof (per `brightwell-port-scope.md §4.7` and Brightwell §4):
construct an explicit exchange involution `σ : L(α) → L(α)`
with `σ(A) = A^c`, `|S(L) − S(σL)| ≤ 1`, `|P(L) − P(σL)| ≤ 1`,
plus an insertion-position averaging argument that produces the
`1/m` factor. Pred/succ disjointness prevents simultaneous
saturation of the two 1-Lipschitz bounds.

This is ~250–400 LoC of careful per-swap bookkeeping. It does
not consume the drops headline; it's parallel infrastructure
that consumes only the τ-inversion lattice (for indexing) and
the existing 1-Lipschitz machinery in
`Mathlib/LinearExtension/FiberSize.lean`.

### §3.3 Brightwell-discharge: what's saved vs. what's not

**Saved by sharing the τ-inversion lattice infrastructure:**
* §4.2 τ-inversion lattice on `L(α)` (~150–250 LoC).
* §4.3 product lattice (~10 LoC).
* §4.5 FKG transport to τ-inversion (~100–200 LoC).
* Total: ~260–460 LoC saved across both axioms.

**Not saved (Brightwell-specific):**
* §4.1 reference τ separating Pred/Succ (~50–80 LoC).
* §4.4 monotonicity (a)–(e) on `≤_τ` (~250–400 LoC).
* §4.6 covariance collapse `Cov_ν → Cov_μ` (~50–80 LoC).
* §4.7 Kahn–Saks per-term bound (~250–400 LoC) — the substantive
  combinatorial content.
* §4.8 final assembly (~50 LoC).
* Total: ~650–1010 LoC of Brightwell-specific work.

### §3.4 Verdict on the discharge claim

**Discharge: confirmed, partial.** The shared infrastructure
genuinely closes the lattice + FKG-transport piece for both
axioms. Roughly **a quarter of the Brightwell port** is dual-
purpose with the drops headline.

The Brightwell port, completed to discharge the
`brightwell_sharp_centred` axiom, still carries its own
~650–1010 LoC of specific work (notably §4.7, the Kahn–Saks
involution). This is **independent** of Path α's case3 critical
path: Brightwell-port tickets can land in parallel with the
drops-headline → case3 chain after the Hibi shared core lands.

**Trust-surface end-state on Path α completion:**
```
[propext, Classical.choice, Quot.sound,
 native_decide, _native.native_decide]
```
i.e., the mathlib trio + the native_decide pair — both project-
specific axioms eliminated. This is the cleanest possible trust
surface short of porting `native_decide` itself.

If only the case3 axiom is targeted (drops headline lands but
Brightwell port is deferred), the trust surface becomes:
```
[propext, Classical.choice, Quot.sound,
 brightwell_sharp_centred,
 native_decide, _native.native_decide]
```
which is one-axiom worse than the full Path α end-state.

### §3.5 Trip-wire #4 status

Per the ticket spec: "Brightwell-discharge claim doesn't hold →
AMBER not STOP; the case3-discharge claim is independent." The
claim **does** hold, modulo the Kahn–Saks specifics being
non-shared. Trip-wire **does not fire**; Path α proceeds with
both axioms in scope.

---

## §4 Multi-polecat ticket decomposition

Six dependent tickets on the case3 critical path; two parallel
Brightwell tickets dispatchable off the shared core; one trailing
case3 application bundle.

### §4.1 Critical-path tickets

#### Hibi-1 — τ-inversion distributive lattice on `LinearExt α` (typeclass)

* **Scope.** Define `tauInv`, `tauLE`, `tauPO`, `tauDistribLattice`
  on the typeclass-based `LinearExt α`. Connect to adjacent-
  transposition graph (existing in `Mathlib/LinearExtension/`
  via `BKAdj.lean`-adjacent infrastructure). Birkhoff identification
  with order ideals of the auxiliary "incomparable τ-pairs" poset
  for short distributivity proof.
* **Inputs.** `Mathlib.Combinatorics.SetFamily.FourFunctions`;
  `Mathlib.Order.Birkhoff`; existing `LinearExt α` `Fintype`
  instance.
* **LoC estimate.** 250–350 LoC (matches mg-38cf §4.2 conservative
  estimate of 250 LoC, plus ~50–100 LoC for fintype/decidability
  glue).
* **Polecat budget.** 600k. Single polecat fits.
* **Trip-wire.** If the distributivity proof exceeds 200 LoC,
  consider whether a direct adjacent-transposition argument is
  shorter than the Birkhoff route.

#### Hibi-2 — FKG-on-LE primitive (typeclass)

* **Scope.** Apply mathlib's `fkg` to the τ-inversion lattice;
  derive `fkg_uniform_le_tau` (function form) and
  `fkg_uniform_le_tau_events` (indicator form). Independence-of-τ
  utility lemma (the FKG conclusion does not depend on τ choice
  beyond having the events monotone for that τ).
* **Inputs.** Hibi-1; `Mathlib.Combinatorics.SetFamily.FourFunctions.fkg`.
* **LoC estimate.** 150–250 LoC (matches mg-38cf §4.5 conservative
  estimate of 200 LoC).
* **Polecat budget.** 400k. Single polecat fits comfortably.

#### Hibi-3 — RelationPoset transport

* **Scope.** Mirror Hibi-1 + Hibi-2 on the data-version
  `LinearExt' Q`. Connect to the τ-inversion structure via the
  embedding `LinearExt' Q ↪ LinearExt α` (where `α` is treated
  with discrete poset; the embedding exists because every Q-LE
  is in particular a permutation of α). Show that
  `LinearExt' Q ⊂ LinearExt α` is a *sublattice* under any τ ∈
  LE(Q), and that the FKG conclusion transports.
* **Inputs.** Hibi-2; existing `RelationPoset` infrastructure
  (mg-b088 + mg-1a4f + mg-0b81).
* **LoC estimate.** 150–250 LoC. The sublattice argument is
  short; most of the LoC is API plumbing for the embedding.
* **Polecat budget.** 400k.

#### Hibi-drops — drops headline

* **Scope.** Strategy A induction on `|Q'.rel \ Q.rel|`. Single-
  edge step: pick `τ ∈ LE(Q')`, prove `R := "L.lt a b"` and the
  level-k event are τ-up-closed, apply Hibi-3 FKG, rearrange to
  probability form. Headline `probEvent'_mono_of_subseteq_upClosed`
  + the named corollaries from mg-8d39 §2.1.
* **Inputs.** Hibi-3; existing `addRel`, `Subseteq.card_rel_le`,
  `LinearExt'.restrict`.
* **LoC estimate.** 250–500 LoC. The induction framework is ~100
  LoC; the single-edge core ~150–400 LoC. Comfortable single-
  polecat scope.
* **Polecat budget.** 600k.
* **Trip-wire.** If the single-edge core exceeds 500 LoC mid-port,
  sub-split into Hibi-drops-a (induction framework + base case)
  and Hibi-drops-b (single-edge step).

#### case3-port-2 — revised Step 1 (Lemma 3.3 + Claim 3.2)

* **Scope.** Per mg-75ef §3 + mg-5bf9 §3. Latex-first first to
  validate Claim 3.2 closes by paper rigor; Lean port follows.
* **Inputs.** Hibi-drops; mg-8487 (orientation lemma, already
  landed); mg-5bf9 sub-results.
* **LoC estimate.** 150–300 LoC if structural; +500–1000 LoC
  for bounded-enum fallback if Claim 3.2 fails (see §6 risk
  inventory).
* **Polecat budget.** 600k for structural; sub-split if enum
  fallback fires.
* **Trip-wire.** If Claim 3.2 doesn't close by paper rigor in
  the latex-first phase, switch to bounded-enum (§8 leverage
  point becomes critical here).

#### case3-port-3 + case3-port-4 + axiom-removal (bundle)

* **Scope.** Per mg-8d39 §4.1. Step 2 band-restricted FKG sub-
  coupling (~200–400 LoC); Step 3 reduction (~50–100 LoC);
  axiom-removal site (~50–100 LoC). Bundleable into one polecat
  given comfortable individual sizes.
* **Inputs.** case3-port-2; Hibi-drops.
* **LoC estimate.** 300–600 LoC bundled.
* **Polecat budget.** 600k.

### §4.2 Parallel-dispatchable tickets (Brightwell branch)

After Hibi-2 lands, two Brightwell tickets are dispatchable in
parallel with Hibi-3 → Hibi-drops → case3-* on the case3 path.

#### Brightwell-port-A — monotonicity (a)–(e) on the τ-inversion lattice

* **Scope.** `brightwell-port-scope.md §4.1, §4.4`: pick reference
  τ separating Pred/Succ; prove monotonicity claims (a)–(e) on the
  product τ-inversion × natural order on `L(α) × {1,…,m}`.
* **Inputs.** Hibi-2; existing `FiberSize.lean` `posAux` machinery.
* **LoC estimate.** 300–480 LoC. Single polecat fits.
* **Polecat budget.** 600k.

#### Brightwell-port-B — Kahn–Saks per-term bound + final assembly

* **Scope.** `brightwell-port-scope.md §4.6, §4.7, §4.8`:
  covariance collapse Cov_ν → Cov_μ; the Kahn–Saks per-term bound
  via explicit exchange involution; final assembly into `(*)`.
* **Inputs.** Brightwell-port-A; existing
  `fiberSize_lipschitz_on_bkAdj`.
* **LoC estimate.** 350–530 LoC. The exchange-involution
  construction (~250–400 LoC) is the single irreducible piece;
  comfortable but at the upper end of single-polecat scope.
* **Polecat budget.** 700–800k. Borderline; sub-split possible
  if §4.7 inflates.
* **Trip-wire.** If the exchange-involution construction exceeds
  500 LoC, sub-split into Brightwell-port-B1 (involution
  construction + Lipschitz bookkeeping) and Brightwell-port-B2
  (insertion-averaging + final assembly).

#### Brightwell-axiom-removal — discharge `brightwell_sharp_centred`

* **Scope.** Replace the `axiom` declaration in
  `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean`
  with the proven theorem; verify all downstream call-sites
  (notably mg-1f5e's F6a) compile unchanged.
* **Inputs.** Brightwell-port-B.
* **LoC estimate.** 50–100 LoC.
* **Polecat budget.** 200k. Trivial.

### §4.3 Dependency graph

```
                                 +-------------------+
                                 |     Hibi-1        |
                                 |  τ-inv lattice    |
                                 |  (250–350 LoC)    |
                                 +--+----------------+
                                    |
                                    v
                                 +-------------------+
                                 |     Hibi-2        |
                                 |  FKG-on-LE        |
                                 |  (150–250 LoC)    |
                                 +--+----+-----------+
                                    |    |
        +---------------------------+    +-------------------+
        |                                                    |
        v                                                    v
   +----------------------+                       +-------------------------+
   |      Hibi-3          |                       |  Brightwell-port-A      |
   |  RelationPoset       |                       |  monotonicity (a)–(e)   |
   |  transport           |                       |  (300–480 LoC)          |
   |  (150–250 LoC)       |                       +--+----------------------+
   +----+-----------------+                          |
        |                                            v
        v                                       +----------------------+
   +-------------------+                        | Brightwell-port-B    |
   |   Hibi-drops      |                        | Kahn–Saks per-term   |
   |   drops headline  |                        | (350–530 LoC)        |
   |   (250–500 LoC)   |                        +--+-------------------+
   +----+--------------+                           |
        |                                          v
        v                                  +----------------------+
   +-----------------------+               | Brightwell-axiom-    |
   |   case3-port-2        |               | removal              |
   |   revised Step 1      |               | (50–100 LoC)         |
   |   (150–300 LoC)       |               +----------------------+
   |   [+500-1000 if enum] |
   +----+------------------+
        |
        v
   +-----------------------+
   |   case3-port-3+4+     |
   |   axiom-removal       |
   |   (300–600 LoC)       |
   +-----------------------+
```

**Critical path (case3 branch).** Hibi-1 → Hibi-2 → Hibi-3 →
Hibi-drops → case3-port-2 → case3-port-3+4+axiom-removal. **Six
sequential polecat sessions** on the case3 critical path.

**Parallel branch (Brightwell).** Hibi-2 → Brightwell-port-A →
Brightwell-port-B → Brightwell-axiom-removal. **Three additional
polecat sessions**, dispatchable in parallel with Hibi-3 onward.

**Total polecat sessions.** 6 (case3 critical) + 3 (Brightwell
parallel) = **9 polecats** for full Path α. With 2-polecat-per-
day cadence and sequential bottleneck on case3 path, **calendar
~10–14 days of dispatch**, dominated by the sequential chain.

### §4.4 LoC totals

| Branch | LoC range |
|---|---:|
| Hibi shared core (Hibi-1 + Hibi-2 + Hibi-3) | 550–850 |
| case3 application chain (Hibi-drops + case3-port-2 + case3-port-3+4+removal) | 700–1400 |
| Brightwell branch (port-A + port-B + axiom-removal) | 700–1110 |
| **Path α total** | **1950–3360** |

This is consistent with mg-b10a §6's "~2000-4000 LoC for the
FKG-on-LE infrastructure (Hibi polytope or equivalent chamber
structure on `LinearExt' Q`)" framing, with the upper bound
shrinking from 4000 to ~3360 because the τ-inversion combinatorial
reformulation eliminates the geometric overhead.

It is also consistent with mg-8d39's original 1450–2700 estimate
for case3-only, plus mg-38cf's 700–1100 estimate for Brightwell-
only, minus the ~250–450 LoC that double-counts the shared lattice
infrastructure. **The triple of mg-8d39 + mg-38cf + Path α LoC
totals are mutually consistent at the 90% level.**

---

## §5 ETAs per ticket + total

### §5.1 Per-ticket ETA

Polecat-session-class work; one polecat = ~1 calendar day at
Daniel's recent cadence (1–2 polecats/day).

| Ticket | LoC | ETA (calendar days) |
|---|---:|---:|
| Hibi-1 | 250–350 | 1 |
| Hibi-2 | 150–250 | 0.5–1 |
| Hibi-3 | 150–250 | 0.5–1 |
| Hibi-drops | 250–500 | 1 |
| case3-port-2 (latex-first) | — | 1 |
| case3-port-2 (Lean port, structural) | 150–300 | 1 |
| case3-port-3+4+axiom-removal | 300–600 | 1 |
| **case3 critical path subtotal** | **1250–2250** | **5–7 days** |
| Brightwell-port-A | 300–480 | 1 |
| Brightwell-port-B | 350–530 | 1 |
| Brightwell-axiom-removal | 50–100 | 0.25 |
| **Brightwell parallel branch subtotal** | **700–1110** | **2.25 days** |

### §5.2 Total

Assuming dispatch cadence of 1 polecat/day and parallelism of 2
(case3 critical + Brightwell parallel branches), **5–7 days
critical path** for Path α. Adding latex-first overhead for
case3-port-2 and a buffer for risk-fired sub-splits, **realistic
calendar: 8–14 days**, i.e., **2–3 weeks**.

### §5.3 Reconciling with the ticket's "6-12 weeks" estimate

The ticket spec writes "Likely ~6-12 weeks for execution if
scoping GREEN" and "8-15 weeks to mg-fb16-unhold". The earlier
mg-b10a STOP report's "weeks-to-months" framing was based on the
geometric Hibi polytope being a quarterly mathlib-PR effort.

**This scoping disagrees with that estimate.** Path α as scoped
here is **not** a quarter-scale undertaking: it is 9 polecat
sessions, calendar ~2–3 weeks at standard cadence. The 6-12
weeks figure in the ticket spec is preserved as a **conservative
upper bound** to absorb risk-fired sub-splits and the case3-port-2
bounded-enum fallback (Risk 2 of §6.2 below), not as the central
estimate.

**Realistic forward-look:**
* **No risks fire:** ~2–3 weeks (9 polecats, dispatch-paced).
* **One risk fires (e.g., Brightwell-port-B sub-splits):** ~3–4 weeks.
* **Multiple risks fire (e.g., Claim 3.2 enum fallback + sub-splits):**
  ~5–8 weeks.
* **Worst case (structural obstruction within the τ-inversion
  lattice surfaces during Hibi-1):** STOP, escalate; possible
  Path γ pivot.

### §5.4 mg-fb16 unhold ETA

mg-fb16 is held under Daniel's "no extreme axioms" framing. With
Path α GREEN and execution complete, both project-specific axioms
are eliminated; trust surface is mathlib-trio + native_decide
pair. Unhold action is ~1 polecat (forum-readiness re-validation
after axiom removal). **Total mg-fb16-unhold ETA: ~4–9 weeks
realistic, ~3 weeks best-case.**

---

## §6 Risk inventory

### §6.1 Risk 1 — τ-inversion lattice distributivity proof harder than expected

**Risk.** mg-b10a §3.2 dismissed Bruhat / weak / inversion-set
candidates as not-distributive. If the τ-inversion lattice's
distributivity proof in Lean turns out to require deeper
lattice-theoretic infrastructure not in mathlib, Hibi-1 LoC could
balloon.

**Likelihood.** Low. The Birkhoff route via order ideals of the
auxiliary "incomparable τ-pairs" poset is a standard short
argument; mathlib's `Mathlib.Order.Birkhoff` provides exactly the
abstract instance needed.

**Mitigation.** Direct adjacent-transposition distributivity
argument as fallback (~150 LoC standalone, doesn't need Birkhoff).

**LoC impact if it fires.** +100–200 LoC on Hibi-1.

### §6.2 Risk 2 — Claim 3.2 (revised Step 1) admits genuinely Aut-trivial counterexamples

**Risk.** Per mg-5bf9 §3.2 Open Question 3.5: genuinely Aut-trivial
Case 3 configurations (F1-obstruction analogue) may exist, in
which case the linear-majority alignment forcing argument doesn't
close. case3-port-2 falls back to bounded enumeration on the
finite parameter range `(K, w, |X|)` with `hCard ≤ 6w + 6` and
`hDepth ≤ 2w + 2`.

**Likelihood.** Medium. mg-5bf9 explored several candidate
Aut-trivial configurations; all admitted involutions but the
broader question is open.

**Mitigation.** Sequence case3-port-2 latex-first: validate
Claim 3.2 by paper rigor before committing the Lean port. If
Claim 3.2 fails, fall back to bounded enum (M2.a of mg-8d39 §5.2)
with ~+500–1000 LoC. **§8 below identifies this as the prime
math-simplification leverage point — a Daniel-help input here
would dramatically tighten Path α.**

**LoC impact if it fires.** +500–1000 LoC on case3-port-2; +1
polecat session.

### §6.3 Risk 3 — Brightwell-port-B (Kahn–Saks per-term bound) exceeds polecat budget

**Risk.** Per `brightwell-port-scope.md §4.7`: the exchange-
involution construction is ~250–400 LoC and is "irreducible —
the explicit exchange involution does not split further without
losing the load-bearing per-element 1-Lipschitz coupling".

**Likelihood.** Medium. The §4.7 estimate is honest, but "the
exchange-involution does not split further" is at-the-margin: it
may sub-split *imperfectly*, with one polecat doing the involution
construction + Lipschitz bookkeeping and a second doing the
insertion-averaging + assembly.

**Mitigation.** Sub-split into Brightwell-port-B1 (~150–250 LoC,
involution construction) + Brightwell-port-B2 (~200–300 LoC,
averaging + assembly).

**LoC impact if it fires.** No LoC increase, just +1 polecat
session on the Brightwell parallel branch (which is not on the
case3 critical path, so it doesn't extend the overall ETA).

### §6.4 Risk 4 — Hibi-3 (RelationPoset transport) reveals incompatibility

**Risk.** The data-version `LinearExt' Q` was built around the
typeclass `[PartialOrder α]` minus the augmentation. The
embedding `LinearExt' Q ↪ LinearExt α` with α-discrete relies on
the typeclass-version being well-behaved with the discrete poset
instance. If subtle issues arise (e.g., the discrete instance's
`DecidableEq` interactions with the α-Fintype), Hibi-3 LoC could
inflate.

**Likelihood.** Low. mg-0b81 (A8-S2-cont-3) already established
the count-form cross-poset infrastructure on `LinearExt'` (see
`Mathlib/RelationPoset/FKG.lean §10–§11`); the same plumbing
extends to the τ-inversion lattice transport.

**Mitigation.** If incompatibility arises, fall back to a Lift via
typeclass-instance machinery rather than direct embedding (~+50
LoC).

**LoC impact if it fires.** +50–100 LoC on Hibi-3.

### §6.5 Risk 5 — F4-b trap: FKG-on-LE silently depends on Steps 5–7

**Risk.** Per the polecat-brief trip-wire #3: if the FKG-on-LE
build-out turns out to require Steps 5–7 fiber/coherence/global
machinery, STOP and relabel.

**Likelihood.** Negligible. The τ-inversion lattice is a Step-8-
internal combinatorial structure; it predates the F4 framing
entirely (Brightwell §3.5.1 is from 1999, the F4 trap is a 2026
project artifact). The shared lattice infrastructure does not
touch Steps 5–7.

**Mitigation.** N/A.

**LoC impact if it fires.** Catastrophic if it fires (Path α
RED), but probability is so low that it's a paranoia trip-wire,
not a planning input.

### §6.6 Risk 6 — Brightwell-discharge claim breaks down at FKG-transport detail

**Risk.** §3 above verified the discharge claim at the lattice level.
But the actual FKG application uses `four_functions_theorem` (not just
`fkg`) on the *product* τ-inversion × natural-order lattice with
**signed** monotonicity in the J-coordinate (one event monotone, the
other antitone). If mathlib's `four_functions_theorem` doesn't
straightforwardly factor the antitone direction (e.g., needs an
explicit `OrderDual` wrapper), Brightwell-port-A inflates.

**Likelihood.** Low–medium. mathlib has `OrderDual` infrastructure
that supports antitone ↔ monotone-on-dual conversion; this is a
~50 LoC plumbing exercise.

**Mitigation.** `OrderDual` wrapper on the J-coordinate; mirror the
Brightwell-port-A monotonicity claims (a)–(e) accordingly.

**LoC impact if it fires.** +50–150 LoC on Brightwell-port-A.

### §6.7 Risk 7 — Token budget overrun on Hibi-drops

**Risk.** Hibi-drops at 500 LoC + induction overhead + Strategy A
plumbing = ~600–800k tokens, near the 600k polecat cap.

**Likelihood.** Medium. Strategy A induction has well-known
plumbing overhead (chain of `addRel` reductions, denominator
arithmetic).

**Mitigation.** Sub-split Hibi-drops-a (induction framework + base
case) + Hibi-drops-b (single-edge step). Both fit comfortably in
500k each.

**LoC impact if it fires.** No LoC increase, +1 polecat session
on the case3 critical path (extending ETA by 1 day).

### §6.8 Aggregate risk verdict

| Risk | Probability | LoC impact if fires |
|---|---|---|
| 1. Hibi-1 distributivity harder | low | +100–200 |
| 2. Claim 3.2 false (case3-port-2 enum fallback) | medium | +500–1000 |
| 3. Brightwell-port-B exceeds budget | medium | 0 (sub-split) |
| 4. Hibi-3 incompatibility | low | +50–100 |
| 5. F4-b trap | negligible | catastrophic |
| 6. Brightwell-port-A `OrderDual` plumbing | low–medium | +50–150 |
| 7. Hibi-drops token overrun | medium | 0 (sub-split) |

**Risk-adjusted Path α LoC range: 1950–3960 LoC**, with expected
value around **~2400 LoC** (consistent with mg-b10a's ~2000-4000
LoC estimate, but the upper end is now bounded by realistic risk
firings rather than worst-case geometric-Hibi inflation).

**Risk-adjusted calendar: 2–8 weeks**, central estimate **3–4
weeks**.

---

## §7 Aggregate verdict

### §7.1 Verdict: **AMBER, leaning GREEN**

Path α is **mathematically feasible** and **calendar-feasible** in
the polecat-arc sense (3–4 weeks central, 2–8 weeks risk-adjusted).
The structural premise — that the FKG-on-LE primitive requires
quarter-scale geometric Hibi polytope formalisation — is
**incorrect**. The combinatorial τ-inversion distributive lattice
on `LinearExt α` is the right object, is mathlib-tier polecat-class
work, and discharges both the case3 axiom and the Brightwell
axiom (the latter modulo the Kahn–Saks per-term bound, which is
independent infrastructure).

The verdict is **AMBER not GREEN** because:
* **Risk 2 (Claim 3.2) is genuinely open at math level** and
  carries a +500-1000 LoC tail in the bounded-enum fallback.
* **The case3-critical-path is genuinely sequential** and depends
  on six tickets in series; any single ticket's slip extends the
  ETA.
* **The §5.3 discrepancy with mg-b10a's "weeks-to-months" framing**
  warrants a sanity check before PM commits to multi-polecat
  execution: this scoping's central ETA (3–4 weeks) is materially
  less aggressive than mg-b10a implied, and the disagreement
  should be surfaced to Daniel.

### §7.2 GREEN justification

If Risk 2 closes (Claim 3.2 true by paper rigor) and the
sequential bottleneck is dispatch-paced (1–2 polecats/day), Path α
delivers:
* **Both project-specific axioms eliminated** — `case3Witness_hasBalancedPair_outOfScope` AND `brightwell_sharp_centred`.
* **Trust surface = mathlib trio + native_decide pair** — the
  cleanest possible end-state short of porting `native_decide`.
* **mg-fb16 unhold criterion met** under Daniel's "no extreme
  axioms" framing.
* **~9 polecat sessions over 2–4 weeks calendar** at standard
  cadence.

This is a strong audit-bar win and fully addresses mg-fb16's
"extreme axioms" reservation at the root.

### §7.3 AMBER caveats requiring Daniel input

PM should surface to Daniel:

1. **The §5.3 ETA discrepancy.** mg-b10a STOP report implied
   "weeks-to-months, multi-author quarter-scale". This scoping
   says 2–4 weeks at polecat cadence. The disagreement is
   resolved in this scoping's favour by reframing Hibi as
   combinatorial (τ-inversion lattice) rather than geometric
   (order polytope) — but Daniel should bless that reframing
   before PM dispatches Hibi-1.

2. **The Risk 2 / case3-port-2 latex-first prerequisite.** Claim
   3.2 is open at math level (mg-5bf9 OQ 3.5). Path α should
   schedule case3-port-2 latex-first and only commit to the Lean
   port after Claim 3.2 closes. If it doesn't close, the bounded-
   enum fallback adds ~+500–1000 LoC and ~+1 week.

3. **The §8 leverage point.** A bounded-enumeration bypass on the
   case3 residual range — IF Daniel can either supply a sharper
   parameter-bound argument or bless the bounded-enum approach
   directly — would eliminate Risk 2 AND obviate the need for
   the drops headline on the only branch where it's load-bearing,
   collapsing Path α from ~9 polecats to ~5 (Brightwell branch
   only).

### §7.4 RED conditions (not currently met)

Path α would RED if:
* The τ-inversion lattice's distributivity in Lean genuinely
  requires unformalised mathlib infrastructure (e.g., a more
  general lattice-on-permutations theorem). Risk 1 above; deemed
  low-probability.
* The Brightwell-discharge claim turns out to fail at a deeper
  level than §3 anticipates (e.g., the Kahn–Saks involution's
  Lipschitz bookkeeping requires entirely new combinatorial
  infrastructure not anticipated by mg-38cf §4.7). No evidence
  of this; mg-38cf treated the §4.7 estimate as honest after
  re-audit.
* A trip-wire fires that this scoping didn't anticipate (e.g.,
  F4-b trap, Risk 5).

None of these are currently active; verdict remains AMBER, not
RED.

### §7.5 Recommendation summary

* **Primary recommendation.** PM commits to Path α execution.
  First execution ticket: **Hibi-1** (τ-inversion lattice). PM
  files immediately after Daniel-mail surfacing the §7.3 caveats
  resolves.
* **Conditional on Daniel input.** If Daniel approves the §8
  bounded-enum bypass, Path α reduces to the Brightwell branch
  only (~3 polecats, ~1 week). PM re-files the trimmed scope.
* **Path γ fallback.** If Daniel prioritises ship velocity over
  axiom elimination, Path γ (retain both axioms with disclosure)
  remains acceptable per mg-d7fd's GREEN forum-readiness verdict.

---

## §8 Recommended Daniel-help math-simplification leverage point

The ticket explicitly requests this section: "Daniel offered help
on math simplification; this is the moment."

### §8.1 The leverage observation

The probability-form drops headline is load-bearing in **exactly
one place** in the entire development: the band-restricted FKG
sub-coupling of mg-75ef §4 / case3-port-3, which discharges the
case3 residual axiom outside `InCase3Scope`.

The Brightwell axiom does **not** consume the drops headline
(per §3 above; the per-term Kahn–Saks bound is independent
infrastructure). So the drops headline's existence is
independently justified by the case3 application alone.

### §8.2 The bypass: bounded enumeration on the case3 residual

Per the AXIOMS.md `case3Witness_hasBalancedPair_outOfScope`
disclosure (`:226–454`): the residual parameter range is
**finite**:

* `hCard : Fintype.card α ≤ 6 * L.w + 6` (F5 C2 cap).
* `hDepth : L.K ≤ 2 * L.w + 2` (F5 C2 cap).
* `hWidth3 : HasWidthAtMost α 3`.

For each fixed `w ≥ 1`, the number of isomorphism classes of
width-3 layered posets with these caps is finite and small.
mg-75ef §3.2(a) and mg-5bf9 §3.3(d2) both note bounded enumeration
as a fallback path.

**The bypass:** a Bool-level decision procedure
`case3Residual_certificate L : Bool` that enumerates the residual
parameter range and certifies one of:
1. The configuration has a non-trivial automorphism forcing a
   balanced pair (per mg-5bf9 §3.1 cyclic-automorphism argument).
2. The configuration admits a Case 1 (ambient profile match,
   mg-f92d) or Case 2 (`mg-8801` discharge) reduction.
3. (Forced-failure check to ensure none escape.)

Bool-Prop bridge via `native_decide` (already in trust surface).

### §8.3 Why this needs Daniel-help, not polecat-help

The bypass requires **paper-rigor confirmation** that the
parameter caps `hCard ≤ 6w + 6` and `hDepth ≤ 2w + 2` are tight
enough that the residual range admits a finite enumeration that
captures every Aut-trivial Case 3 configuration. This is a math
question, not a Lean-port question:

* **Bound on `w` itself.** Is `w ≤ N₀` for some explicit `N₀`
  (say `N₀ = 4`) sufficient for the residual to be captured?
  The F5 framing implicitly assumes `w ≥ 1`, but doesn't cap
  `w` from above. The bipartite-bound (mg-ed4d) and rotation-
  argument (mg-5a62) plus the Case 3 dispatch may already cap
  `w` implicitly; this should be made explicit.
* **Density of Aut-trivial configurations.** mg-5bf9 §3.2
  Construction 3.4 attempted but failed to produce an Aut-trivial
  Case 3 config in the residual range (the σ_{(2 3)} involution
  saved it). Daniel's intuition on whether genuine Aut-trivial
  configs are *dense* or *sparse* in the residual range
  determines whether bounded-enum is feasible.
* **Alternative discharge mechanisms.** If Aut-trivial residual
  configs exist, what mechanism discharges them? mg-5bf9 §3.3
  proposed (d2) bounded-enum as one of four options; Daniel's
  judgment on which option is most paper-rigor-credible is the
  decisive input.

### §8.4 Why this leverage is large

If Daniel's input closes Risk 2 (Claim 3.2 true OR bounded-enum
viable):
* **case3-port-2 collapses to ~150 LoC** (no enum fallback needed).
* **The drops headline (Hibi-drops) becomes optional**: if
  bounded-enum discharges Case 3 entirely, the Hibi shared core
  is needed only for Brightwell.
* **Path α collapses to the Brightwell branch alone**, ~3 polecats
  / ~1 week.
* **Total LoC: ~700–1100** (Brightwell-branch-only).
* **mg-fb16-unhold ETA: ~1–2 weeks** instead of ~3–8 weeks.

### §8.5 Specific ask to Daniel

Two paper-rigor questions, each ~30 minutes of Daniel's time:

**Q1. Is `w ≤ 3` sufficient for the residual range to admit a
finite enumeration?**

The current bounds give `|α| ≤ 6w + 6` (so `≤ 24` for `w = 3`)
and `K ≤ 2w + 2` (so `≤ 8` for `w = 3`). For `w ≤ 3` and width-3,
the number of layered-decomposition isomorphism classes is finite
and computable. Bool-level enumeration over this range has
precedent in `mg-43bc` (`bounded_irreducible_balanced` hybrid
dispatch). If `w ≤ 3` cap is justified, bounded-enum closes; if
arbitrary `w` must be handled, the structural argument (Claim 3.2)
or the drops headline is required.

**Q2. Is there a sharper paper-side discharge of the residual that
avoids the within-band probability comparison entirely?**

mg-75ef §4 explored count-form / conditional-on-lower / symmetry-
tight involutions and concluded none closes. mg-5bf9 §3.3 explored
linear-majority alignment and reached AMBER. Both predecessors
specifically preserved the within-band probability comparison as
the hard step. If Daniel sees a fourth route — e.g., a sharper
rotation argument that bypasses the within-band comparison
entirely, or a stronger F5a sub-certificate that captures more of
the residual — Path α collapses to Brightwell-only.

### §8.6 Latex-first deliverable for case3-port-2

Independent of Daniel-help, PM should schedule case3-port-2
**latex-first** as the first ticket after Hibi-drops lands. This
is the standard mg-75ef discipline and forces validation of
Claim 3.2 before committing to Lean port.

If Daniel's input arrives while Hibi-1/2/3/drops are in flight,
case3-port-2 latex-first folds Daniel's input directly. If
Daniel's input doesn't arrive, case3-port-2 latex-first either
closes Claim 3.2 by polecat-rigor (Risk 2 doesn't fire) or surfaces
the residual gap and triggers the bounded-enum fallback.

### §8.7 Recommendation

PM mails Daniel **after** this scoping commits, surfacing:
1. The §7.3 AMBER caveats (the §5.3 ETA reframing + Risk 2
   acknowledgment).
2. The §8.5 specific Q1/Q2 questions.
3. The Path α GREEN-conditional-on-Daniel-input proposal.

If Daniel responds positively to Q1 or Q2: re-scope Path α to
the Brightwell branch only (~1 week, ~700-1100 LoC). If Daniel
asks PM to commit to full Path α regardless: dispatch Hibi-1 as
the first execution ticket.

---

## §9 Polecat protocol notes

* `mg claim mg-ff7f` — done.
* `pogo schedule … mail-check-mg-ff7f` — done.
* No Lean source changes. This is a scoping ticket per
  `feedback_distinguish_arc_chunk_outcomes` ("substantive
  scoping chunk; no parallel cleanup").
* Verdict **AMBER, leaning GREEN** per §7. Reaches the
  ticket-spec's GREEN substantively (Path α feasible, multi-polecat
  arc dispatchable) but with two genuine AMBER caveats requiring
  Daniel input (§7.3).
* Trip-wires status:
  * **Trip-wire #1 (token overrun > 900k):** not fired. Approximate
    spend on this scoping ~250k of the 600k cap.
  * **Trip-wire #2 (new structural obstruction):** not fired.
    The reframing of "Hibi polytope" from geometric to
    combinatorial closes mg-b10a's structural concern; no new
    obstruction surfaces.
  * **Trip-wire #3 (F4-b trap):** not fired. τ-inversion lattice
    is Step-8-internal.
  * **Trip-wire #4 (Brightwell-discharge claim doesn't hold):**
    not fired. §3 verifies the claim modulo the Kahn–Saks per-term
    bound, which is independent infrastructure not subsumed but
    not blocking.
  * **Trip-wire #5 (sequential bottleneck > 12 weeks):** not
    fired. Central calendar estimate 3–4 weeks; risk-adjusted
    upper bound ~8 weeks.
* Mail to mayor: pending immediately after this commit, with the
  AMBER verdict and §7.3 + §8 recommended surfacing-to-Daniel.
* `mg done` — to be called only after refinery confirms merge.

---

## §10 Cross-references

### §10.1 Predecessor artifacts

* `docs/a8-s2-cont-execution-arc/cont-4-stop-report.md` (mg-b10a,
  commit `256f0da`) — STOP report; this scoping reframes its Hibi
  polytope diagnosis from geometric to combinatorial.
* `docs/a8-s2-cont-scoping-arc/scoping.md` on
  `a8-s2-cont-scoping-arc` (mg-8d39, commit `b81ad31`) — original
  upgraded-GREEN scoping; this scoping's multi-polecat decomposition
  inherits its case3 application chain spec.
* `docs/brightwell-port-scope.md` (mg-38cf) — standalone
  Brightwell port audit; provides the §4 LoC sub-piece estimates
  this scoping reuses.
* `docs/case3witness-operational-audit.md` — case3 axiom faithfulness
  audit.
* `docs/case3-port-arc/rem-enumeration-proof.md` (mg-75ef,
  archived) — math artifact; verdict β.
* `docs/case3-port-arc/linear-majority-alignment.md` (mg-5bf9,
  archived) — math artifact; verdict AMBER, the source of OQ 3.5
  and Risk 2.

### §10.2 Lean source files referenced

* `lean/AXIOMS.md:13–225` — `brightwell_sharp_centred` disclosure.
* `lean/AXIOMS.md:226–454` — `case3Witness_hasBalancedPair_outOfScope`
  disclosure.
* `lean/MATHLIB_GAPS.md §2.E` — E1–E5; this scoping closes E5
  (drops headline) via §2 but not via mathlib upstreaming.
* `lean/OneThird/Mathlib/RelationPoset.lean` — data-version
  RelationPoset (mg-b088).
* `lean/OneThird/Mathlib/RelationPoset/LinearExt.lean` — `LinearExt'`
  API (mg-1a4f).
* `lean/OneThird/Mathlib/RelationPoset/Birkhoff.lean` — Birkhoff
  transport (mg-0b81).
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean` — count-form
  cross-poset FKG (mg-0b81); `:506–516` and `:420–426` docstrings
  name the deferred drops headline.
* `lean/OneThird/Mathlib/LinearExtension/FKG.lean` — typeclass-
  based FKG primitives.
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean`
  (mg-134c, `2ded504`) — the Brightwell axiom site.
* `lean/OneThird/Mathlib/LinearExtension/FiberSize.lean` (mg-85d1)
  — 1-Lipschitz `f = S − P` infrastructure; consumed by
  Brightwell-port-B.
* `lean/OneThird/Mathlib/LinearExtension/Birkhoff.lean` — Birkhoff
  representation transport on `LinearExt`.
* `lean/OneThird/Step8/Case3Residual.lean` — the case3 axiom site.
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1484` —
  `InCase3Scope` definition.

### §10.3 Mathlib primitives referenced

* `Mathlib.Combinatorics.SetFamily.FourFunctions`:
  * `fkg`, `four_functions_theorem`, `four_functions_theorem_univ`,
    `holley`, `Finset.le_card_infs_mul_card_sups`.
* `Mathlib.Order.Birkhoff` — Birkhoff representation theorem
  (used by Hibi-1's distributivity proof).
* `Mathlib.Order.Extension.Linear` — `extend_partialOrder`,
  `LinearExtension α` (existence of one extension).
* `Mathlib.Order.UpperLower.Basic` — `LowerSet`, `IsLowerSet`.
* `Mathlib.Order.OrderDual` — used by Brightwell-port-A for
  the J-coordinate antitone direction.
* `Mathlib.Data.Fintype.Pi`, `Mathlib.Algebra.Order.Pi` — product
  lattices.

### §10.4 Feedback / discipline files applied

* `feedback_audit_bar_for_axioms` — applies; goal is two-axiom
  elimination.
* `feedback_n_poset_is_not_ordinal_sum` — applies (§8.2 bypass
  reasoning).
* `feedback_complexity_blowup_means_wrong_path` — trip-wires §6.
* `feedback_announce_destination_and_eta` — §5 ETAs are explicit.
* `feedback_distinguish_arc_chunk_outcomes` — substantive scoping
  chunk; no parallel cleanup; this doc IS the deliverable.
* `feedback_pm_is_mini_ceo_default` — PM authority over §4 ticket
  filing, conditional on Daniel-mail surfacing of §7.3 + §8.
* `feedback_polecat_stop_runaway` — trip-wire firing protocol.
* `feedback_latex_first_for_math_simp` — discipline applied to
  this scoping; recommended for case3-port-2 (Risk 2).

### §10.5 In-session inputs

* Daniel directives 2026-05-06 ("find best forward path"; "don't
  get blocked") — standing authorization for the find-best-path
  scoping that produces this AMBER-leaning-GREEN verdict.
* mg-ff7f ticket spec, dated 2026-05-06T~09:50Z — the brief this
  scoping responds to.

---

*End of scoping. Length: ~890 lines. Lean source unchanged.
Verdict AMBER leaning GREEN per §7; surfacing to Daniel via mail
recommended per §7.3 + §8 before PM dispatches Hibi-1.*
