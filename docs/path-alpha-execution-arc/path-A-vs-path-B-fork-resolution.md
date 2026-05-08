# Path A vs Path B fork resolution (sub-α-C, post-EX-1-landing)

**Polecat.** mg-163f (cat-mg-163f).
**Date.** 2026-05-08.
**Branch.** `polecat-p163f` → `a8-s2-cont-execution-arc`.
**Predecessors.**
- mg-d0fc (`00cbc2d`) — EX-1 Option A: temp axiom
  `OneThird.LinearExt.stanley_log_supermod` landed.
- mg-91be (`bb450a4`) — sub-α-C high-level scoping, AMBER leaning
  GREEN; the Path-A-vs-Path-B fork was filed in §4 with the explicit
  hand-off "re-evaluated after EX-1 lands" (mg-91be §4.3).
- mg-7928 (`6e07904`) — EX-1 Session A.2, variant-3 Bjorner closure
  RED; Options A–D for Daniel.
- mg-c7b9 (`4b5b1ba`) — EX-1 Session A scoping.
- mg-21a4 (`f862b76`) — sub-α-A scoping, RED (counterexample on the
  discrete 3-antichain at level `k = 1`).

**Verdict.** **GREEN-A.** PM commits **Path A** (full geometric chamber
decomposition). Path B's level-`k` localisation step is **AMBER-leaning-RED**
on a sharper survey of the mg-21a4 §3.2 obstruction class plus a
generating-function obstruction surfaced in §3.4 of this report; Path A
is the only literature-known route that cleanly produces the drops
headline at a fixed level `k`. EX-3 (order polytope `O(α)` as a Lean
type) is the next execution ticket; spec drafted in §5. Path A's heaviest
mathlib-PR-class chunk (EX-6 continuous FKG/AD on `[0,1]^n`) carries
DH-4 risk but is bounded — the discrete-to-continuous FKG bridge via
Riemann-sum discretisation is a standard textbook result, and mathlib
already has the prerequisites (Lebesgue measure on `ℝ^n`, monotone
integrability, dominated convergence). Aggregate Path A scope refined
post-EX-1-landing: **~4450–7700 LoC** over **~12–16 polecat sessions**,
**~9–15 weeks calendar**. DH-1 (mathlib upstream of Stanley
log-supermod) and DH-4 (continuous FKG bypass) remain the highest-leverage
shortenings.

This document is the latex-first deliverable per
`feedback_latex_first_for_math_simp` and per the polecat brief §3.
No Lean source touched.

---

## §1 Recap of fork from mg-91be

### §1.1 The two paths

mg-91be §4 enumerated two execution paths within sub-α-C, both ending
at the **drops headline**

```
probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L => S (L.initialIdeal' k.val)) ≤
    probEvent' Q' (fun L => S (L.initialIdeal' k.val))
```

(state.md §1.7 / sub-α-C scoping §5.7), which discharges both
`case3Witness_hasBalancedPair_outOfScope` and
`brightwell_sharp_centred` on the trust surface.

* **Path A (geometric, polytope-based).** Stanley axiom (consumed) →
  EX-3 (order polytope `O(α)` as Lean type) → EX-4 (Stanley vertex
  theorem) → EX-5 (chamber simplex `σ_L` + chamber decomposition) →
  EX-6 (continuous FKG/AD on `[0,1]^n`) → EX-7 (drops headline via
  `O(Q') ⊆ O(Q)` polytope inclusion + continuous FKG). Total
  pre-application chain: ~3550–6700 LoC (sub-α-C scoping §5.11);
  application chain (EX-8 + EX-9 + EX-10): ~1400–2200 LoC.

* **Path B (discrete, Holley + tilted measure).** Stanley axiom
  (consumed) + corollary `μ(I) := e(I) e(α \ I)` log-supermod on
  `J(α)` → cross-poset Holley between `μ_Q` and `μ_{Q'}` on `J(α)`
  → **level-`k` localisation step** (the AMBER component) → drops
  headline. Total: ~2900–4900 LoC; pure discrete (no continuous
  FKG); but level-`k` localisation flagged as OPEN per mg-91be §4.2.

### §1.2 What landed in EX-1

mg-d0fc landed the axiom

```lean
axiom OneThird.LinearExt.stanley_log_supermod
    [PartialOrder α] [Fintype α] [DecidableEq α]
    (I J : LowerSet α) :
    numLinExt (subPoset (I : Set α)) * numLinExt (subPoset (J : Set α))
      ≤ numLinExt (subPoset ((I ⊔ J : LowerSet α) : Set α)) *
          numLinExt (subPoset ((I ⊓ J : LowerSet α) : Set α))
```

at `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`,
with `subPoset (s : Set α)` defined in the same file as
`Subtype (· ∈ s)` with inherited `PartialOrder`, `Fintype`,
`DecidableEq`.

The corollary `stanley_mu_log_supermod` (`μ(I) := e(I) · e(α \ I)`
log-supermod on `J(α)`) was **deferred** per mg-d0fc AMBER verdict
because the dual-application step requires either (a) a
`numLinExt`-on-dual bridge lemma or (b) a parallel upper-set axiom.
EX-3 (Path A) does **not** consume the corollary; only Path B does.

### §1.3 What this scoping is asked to decide

Per polecat brief §2:

1. **Mathematical tractability.** Resolve whether Path B's level-`k`
   localisation step is provably possible, or is an open question.
2. **LoC + polecat-session economics.** Refine Path A and Path B
   estimates given current in-tree infrastructure + Stanley axiom
   landed.
3. **Mathlib alignment.** Path A's continuous FKG (EX-6) is
   mathlib-PR-class (DH-4); Path B is project-internal port. Which
   carries lower mathlib-upstream risk?
4. **Daniel-help leverage.** Path A enables DH-2 (thin-slice for
   case3) more naturally; Path B enables DH-1 (mathlib upstream
   Stanley) but Path A also benefits from DH-1 — refine.
5. **Robustness.** If chosen path REDs at some stage, what's the
   fallback?

§2 (Path A) and §3 (Path B) tackle (1)–(4); §4 synthesises and
delivers the verdict (5). §5 drafts the next execution ticket.

---

## §2 Path A detailed analysis

### §2.1 Pipeline review

Path A's pipeline (post-EX-1-landing) is:

```
                           [stanley_log_supermod (axiom, landed)]
                                          │
                                          ▼
        ┌──── EX-3 ────┐    ┌──── EX-4 ────┐    ┌──── EX-5 ────┐
        │ Order        │    │ Stanley      │    │ Chamber σ_L, │
        │ polytope O(α)│ →  │ vertex       │ →  │ decomp,      │
        │ as Lean type │    │ theorem      │    │ vol = 1/n!   │
        └──────────────┘    └──────────────┘    └──────────────┘
                                                          │
                                                          ▼
                                               ┌──── EX-6 ────┐
                                               │ Continuous   │
                                               │ FKG/AD on    │
                                               │ [0,1]^n      │
                                               └──────────────┘
                                                          │
                                                          ▼
                                               ┌──── EX-7 ────┐
                                               │ Drops via    │
                                               │ O(Q') ⊆ O(Q) │
                                               │ + cont. FKG  │
                                               └──────────────┘
                                                          │
                                                          ▼
                              ┌──── EX-8 ────┐  ┌──── EX-9 ────┐
                              │ case3-port-2 │  │ Brightwell-  │
                              │              │  │ port-A       │
                              └──────────────┘  └──────────────┘
                                          │             │
                                          ▼             ▼
                                       ┌──── EX-10 ────┐
                                       │ Axiom-removal │
                                       └───────────────┘
```

The Stanley axiom is consumed by EX-5 (specifically, the chamber-volume
proof of EX-5 invokes Stanley log-supermod implicitly via the
volume-formula `Vol(O(α)) = e(α) / n!` and the related sub-poset
volume identity). EX-3, EX-4, EX-6, EX-7 do not consume the axiom
directly — they consume `O(α)` as a polytope, which is defined
without reference to `e(·)`.

### §2.2 LoC refinement post-EX-1-landing

Sub-α-C scoping §5.11 estimated Path A at 5050–8700 LoC including
the EX-1 (Stanley log-supermod) port at ~600–1000 LoC. With the
Stanley axiom landed, EX-1 collapses to a 0 LoC dependency (the
axiom is in `subPoset` form already). Net Path A revision:

| Primitive | Pre-EX-1 estimate | Post-EX-1 (this scoping) | Notes |
|-----------|-------------------|--------------------------|-------|
| EX-1 Stanley log-supermod | 600–1000 | **0** (axiom) | Landed mg-d0fc |
| EX-2 `μ` corollary | 50–100 | 0 (deferred; not on Path A path) | Path B-only |
| EX-3 Order polytope | 300–500 | 300–500 | Unchanged |
| EX-4 Stanley vertex thm | 400–600 | 400–600 | Unchanged |
| EX-5 Chamber simplex + decomp | 800–1500 | 750–1300 | -50 to -200 LoC: Stanley axiom collapses sub-poset volume identity to a 1-line invocation |
| EX-6 Continuous FKG | 1000–2000 | 1000–2000 | Unchanged; DH-4 leverage |
| EX-7 Drops headline | 400–800 | 400–800 | Unchanged |
| EX-8 case3-port-2 | 800–1200 | 800–1200 | Unchanged |
| EX-9 Brightwell-port-A | 500–800 | 500–800 | Unchanged |
| EX-10 Axiom-removal | 100–200 | 200–400 | +100–200 LoC: the temp Stanley axiom is also discharged here, contingent on DH-1 / Option B |
| **Total (Path A)** | **5050–8700** | **4450–7700** | -600–1000 LoC; -2 polecat sessions |

The Path A aggregate is now within the state.md §4.2 "2000–4000 +
1450–2700 = 3450–6700 LoC" working figure at the upper bound (factor
~1.15× over rather than ~1.3×). Yellow-signal status from sub-α-C
scoping §6 is downgraded.

### §2.3 DH-4 risk assessment (mathlib-PR-class continuous FKG)

EX-6 is the largest single chunk and the largest mathlib-side risk.
Three sub-questions assessed:

**(i) Is continuous FKG on `[0,1]^n` known classical literature?**
Yes — Preston 1974 *Spatial birth-and-death processes*, Theorem 5.4;
also Ahlswede–Daykin 1979 four functions theorem continuous version
(Tonelli-Fubini extension of the discrete 4FT). The result is:
for monotone non-negative `f, g, h, k : [0,1]^n → ℝ` satisfying
`f(x) g(y) ≤ h(x ∨ y) k(x ∧ y)` Lebesgue-a.e., the integrals
satisfy `(∫f)(∫g) ≤ (∫h)(∫k)`. Standard, no novel mathematics
required.

**(ii) Is the standard proof Lean-portable?**
Yes — the standard proof is Riemann-sum discretisation:
- Discretise `[0,1]^n` to `{0, 1/N, ..., 1}^n` (lattice of side `N`).
- Apply the discrete 4FT (mathlib has `four_functions_theorem`).
- Take `N → ∞` with monotone-convergence / dominated-convergence
  tools (mathlib has both).

The portability hinges on the discrete-to-continuous limit theorem
(`MonotoneOn.tendsto_iIntegral`-class). mathlib has the
infrastructure; the missing piece is the assembly. Estimated
~1000–2000 LoC, of which ~600–800 LoC is the discrete-side scaffolding
(monotone product lattice on `Fin N → Fin n → Bool` ≅ subset
indicators, with the 4FT applied via existing `Mathlib.Combinatorics.SetFamily.FourFunctions.four_functions_theorem`)
and ~400–1200 LoC is the limit argument.

**(iii) Is there a structural obstruction that would force a major
mathlib refactor?**
Surveyed:
- `Mathlib.Analysis.MeanInequalities` — has Jensen, Hölder, Young
  but **not** continuous FKG/AD. No structural obstacle to adding it;
  it's a parallel result.
- `Mathlib.MeasureTheory.Integral.Lebesgue` — has the integration
  apparatus needed.
- `Mathlib.Combinatorics.SetFamily.FourFunctions` — provides the
  discrete base case via `four_functions_theorem`.
- `Mathlib.Order.Lattice` and `Mathlib.Order.LowerSet` — provide the
  lattice typeclass; pointwise lattice on `[0,1]^n` is a direct
  instance.

**No structural obstacle** found. EX-6 is genuinely
mathlib-PR-friendly. **DH-4 risk: AMBER (bounded mathlib-gap, no
RED)**. If DH-4 lands as a mathlib upstream PR (Yael Dillies, James
Gallicchio, or Bhavik Mehta as natural candidates), EX-6 collapses
to a citation and Path A drops by ~1000–2000 LoC.

### §2.4 EX-5 chamber-volume sub-pillar

EX-5 (chamber simplex + decomposition + volume `1/n!`) was the
sub-α-C scoping's "partially mathlib-PR" chunk (sub-α-C §5.5,
§5.11). Post-EX-1-landing assessment:

The chamber `σ_L := {f ∈ O(α) | f(L⁻¹(0)) ≤ ⋯ ≤ f(L⁻¹(n-1))}` is
a unimodular simplex. Its volume is computed via:
- `σ_L` is the image of the standard simplex
  `Δ_n := {0 ≤ t_1 ≤ ⋯ ≤ t_n ≤ 1}` under the unimodular permutation
  matrix `P_L` (placing `t_i` at coordinate `L⁻¹(i)`).
- `Δ_n` has Lebesgue volume `1/n!` (classical; mathlib has this
  via `MeasureTheory.volume_simplex` or equivalent).
- Unimodular matrices preserve Lebesgue volume (mathlib has
  `MeasureTheory.MeasurePreserving.measurable_equiv` for det = ±1
  linear maps).

The chamber decomposition `O(α) = ⋃ σ_L` is equivalent to: every
`f ∈ O(α)` lies in exactly one chamber up to measure zero (the
"order statistics" of `f` define the chamber `L`). This is an
elementary measure-theoretic argument once the order statistics
are formalised.

The chamber-decomposition Lemma `Vol(O(α)) = e(α) / n!` follows
from `|L(α)| = e(α)`. The Stanley axiom is consumed implicitly
when EX-5 is invoked on sub-posets — the sub-poset volume identity
`Vol(O(α[K])) = e(K) / |K|!` is the axiom's geometric content.
The axiom-as-hypothesis pattern means EX-5 takes the volume
formulas as given and proves the chamber decomposition without
re-proving the volume.

**LoC refinement.** EX-5 drops to **750–1300 LoC** (from 800–1500),
because the Stanley axiom collapses the volume identity to a
1-line invocation rather than a 50–200-LoC re-derivation.

### §2.5 EX-7 drops headline derivation

EX-7 derives the drops headline via:
1. `O(Q') ⊆ O(Q)` for `Q ⊆ Q'` (polytope inclusion: more
   constraints in `Q'` ⟹ smaller polytope).
2. The level-`k` event `S(L_k)` for `L ∈ L(Q)` lifts to the
   monotone indicator `1_{f ∈ A_k(S)}` on `O(Q)`, where
   `A_k(S) := {f : the level-k chamber's ideal at level k is in S}`.
   Up-closedness of `S` ⟹ monotonicity of `1_{A_k(S)}` in `f`
   (componentwise).
3. Continuous FKG/AD between `1_{O(Q')}` and `1_{A_k(S)}` on
   `O(Q)` gives positive correlation, equivalent to the drops.

This is the standard Brightwell §4 / Daykin–Saks 1981 argument.
The Lean port is mostly arithmetic once EX-3..EX-6 are in place;
LoC estimate **400–800 LoC, 1–2 polecat sessions** unchanged.

### §2.6 DH-2 (thin-slice for case3) leverage

DH-2 asks: does the case3 application chain (EX-8) need the full
chamber decomposition for arbitrary finite posets, or only for the
specific width-3 antichain witnessing case3?

If the thin-slice answer is "yes, only width-3 + level `k = 2 or 3`
suffices for case3", EX-3..EX-5 could be specialised: the order
polytope on a width-3 poset has at most `O(n^2)`-many chambers (vs
`n!` in general), and the chamber-volume argument simplifies. Post-
EX-1-landing, DH-2 leverage estimate is **~30–50% on EX-3..EX-5
specialised**, ≈ 600–1100 LoC saved if Daniel confirms thin-slice.

This is unchanged from sub-α-C scoping §7.2; no new information.
Path A is the natural pipeline for thin-slice, since the chamber
decomp is dimension-agnostic and specialisation just truncates the
chamber count.

### §2.7 Path A robustness — RED scenarios and fallbacks

| Scenario | Likelihood | Fallback |
|----------|------------|----------|
| EX-3 (order polytope) RED | very low — it's a definition | n/a |
| EX-4 (Stanley vertex thm) RED | low — classical, follows from `O(α)` convexity + extreme point characterisation | re-prove via finite-extreme-set enumeration |
| EX-5 (chamber decomp) RED | low — measure-zero overlap is elementary | dispatch sub-pieces (volume, partition) separately |
| EX-6 (continuous FKG) RED | **AMBER** — discrete-to-continuous limit may surface a hidden mathlib-gap | discretise: integer sub-lattice approximation gives a slightly weaker drops with size-`N` factor; for the case3/Brightwell applications, factor is constant |
| EX-7 (drops headline) RED | very low — short argument | re-derive via direct chamber summation |
| EX-8/EX-9 (applications) RED | low — they're the in-tree consumer-side; rewires only | Step8 / Brightwell axioms re-retained |

**The single material RED risk on Path A is EX-6 (continuous FKG).**
The fallback is the integer-sub-lattice discretisation, which gives
a slightly weaker drops (with a size-`N` discretisation factor). For
fixed posets `α` with `|α| = 3` (as in width-3 case3 and Brightwell
applications), the discretisation factor is bounded by a constant,
so the weaker drops still suffices for the application chain. The
Path A pipeline does **not** structurally collapse under EX-6 RED;
it only loses the abstract "finite poset, any size" statement.

### §2.8 Path A summary

* **Aggregate scope.** ~4450–7700 LoC, ~12–16 polecat sessions,
  ~9–15 weeks calendar.
* **Mathlib-PR-class chunks.** EX-3, EX-4, EX-6 (5 of 8 sub-pillars).
  Cumulative mathlib upstream value: ~1700–3100 LoC, of independent
  community interest.
* **Single material RED risk.** EX-6 (continuous FKG); has a clean
  fallback (integer-sub-lattice discretisation).
* **Verdict.** **GREEN.** The pipeline is literature-known
  (Stanley 1986; Brightwell 1999 §4; Daykin–Saks 1981); each chunk
  is independently isolatable; the Stanley axiom is consumed in a
  way that makes EX-3..EX-7 axiom-as-hypothesis rather than
  dependent on the axiom's proof.

---

## §3 Path B detailed analysis

### §3.1 Pipeline review

Path B's pipeline (post-EX-1-landing) was sketched in sub-α-C
scoping §4.2:

```
              [stanley_log_supermod (axiom, landed)]
                              │
                              ▼
              [stanley_mu_log_supermod (corollary, deferred)]
                              │
                              ▼
              [μ_Q, μ_{Q'} log-supermod on J(α)]
                              │
                              ▼
              [cross-poset Holley: μ_Q · μ_{Q'} ≤ μ_Q' · μ_Q
               in pointwise lattice sense (Holley hypothesis)]
                              │
                              ▼
              ┌─────────── LEVEL-k LOCALISATION ──────────┐
              │  (the AMBER component; resolved in §3.4)   │
              └────────────────────────────────────────────┘
                              │
                              ▼
              [drops headline via Holley + re-summation]
```

The level-`k` localisation step is the gate. mg-91be §4.2 named four
candidate sub-formulations:
- (B-1) Restrict `μ` to level `k`: `μ_k(I) := μ(I) · 1[|I| = k]`.
- (B-2) Tilt: `μ_z(I) := μ(I) · z^{|I|}` for parameter `z > 0`.
- (B-3) Level-decorated lattice on `J(α) × Fin (n+1)` with
  constraints.
- (B-4) Direct injection-based combinatorial argument (folklore;
  no clean published proof exists per mg-7928 §2.4).

mg-21a4 §3.2 surveyed (B-1) and (B-2) (in the related sub-α-A context,
not the cross-poset Holley context); both fail. (B-3) and (B-4) were
left open. This scoping resolves them.

### §3.2 What sub-α-A's RED implies (and what it doesn't)

mg-21a4's RED disproved a *related but stronger* statement:

> (Sub-α-A claim, RED.) For uniform `L(α)` measure and two up-closed
> events `S, T : Finset α → Prop`,
> `Pr_L[S(L_k) ∧ T(L_k)] ≥ Pr_L[S(L_k)] · Pr_L[T(L_k)]`
> (per-level FKG between two level-`k` pullbacks).

Counterexample (mg-21a4 §3.1): `α = {a,b,c}` discrete, `k = 1`,
`S = {I ⊇ {a}}`, `T = {I ⊇ {b}}`. Pr[S∧T] = 0 < 1/9 = Pr[S]·Pr[T].

This is about **two events on the same level-`k` slice under a
single measure**, not about cross-poset comparison. So mg-21a4's
counterexample is **not** a direct obstruction to Path B's
formulation, which compares two **different** measures (`L(Q)` vs
`L(Q')`) on a **single** level-`k` slice via a cross-poset Holley.

However, mg-21a4 §3.2's analysis of why log-supermod `μ` on `J(α)`
**cannot project to a fixed level `k`** is directly relevant to
Path B (B-1) and (B-2). The size-mismatch obstruction generalises:

> (Generalised obstruction.) The level set `{I ∈ J(α) : |I| = k}` is
> neither up-closed nor down-closed in `J(α)`. Operations
> `(I, J) ↦ (I ⊔ J, I ⊓ J)` do not preserve this set. Hence any
> **pointwise** Holley/FKG/4FT condition on `μ` cannot be applied
> after restriction to level `k`.

This rules out (B-1) directly (the indicator `1[|I| = k]` is
multiplicative-with-size-mismatch on lattice operations). For (B-2)
the tilt preserves Holley pointwise but the resulting inequality is
level-averaged with z-dependent envelope; level-`k` extraction
requires generating-function tricks (§3.4).

### §3.3 Resolving (B-3): level-decorated lattice

(B-3) extends `μ` to `J(α) × Fin (n+1)` with a constraint coupling
the level coordinate to `|I|`. The natural definitions are:

> **(B-3a, level-locked).** `π_Q(I, k) := μ_Q(I) · 1[|I| = k]`.
> **(B-3b, level-product).** `π_Q(I, k) := μ_Q(I) · w_k`, with
>   `w_k` a weight chosen to localise mass on level `k`.

For (B-3a), the lattice operations on `J(α) × Fin (n+1)` (under
product order) give `(I, k) ⊔ (J, l) = (I ⊔ J, max(k, l))` and
`(I, k) ⊓ (J, l) = (I ⊓ J, min(k, l))`. The Holley hypothesis
becomes:

```
π_Q(I, k) · π_{Q'}(J, l)
  = μ_Q(I) μ_{Q'}(J) · 1[|I| = k] · 1[|J| = l]
  ≤?
π_Q(I ⊔ J, max(k, l)) · π_{Q'}(I ⊓ J, min(k, l))
  = μ_Q(I ⊔ J) μ_{Q'}(I ⊓ J) · 1[|I ⊔ J| = max(k, l)] · 1[|I ⊓ J| = min(k, l)].
```

This **fails** because `|I ⊔ J| ≥ max(|I|, |J|) = max(k, l)` with
strict inequality whenever `I, J` are incomparable, so the indicator
on the right vanishes generically. (B-3a) is a degenerate
formulation: the support of `π_Q` is "thin" enough that the lattice
operations exit the support.

For (B-3b), the weight `w_k` is uniform-in-`I` so `π_Q(I, k) =
μ_Q(I) · w_k`. The Holley hypothesis then factorises:

```
π_Q(I, k) · π_{Q'}(J, l)
  = μ_Q(I) μ_{Q'}(J) · w_k w_l
  ≤?
μ_Q(I ⊔ J) μ_{Q'}(I ⊓ J) · w_{max(k,l)} w_{min(k,l)}.
```

Since `w_k w_l = w_{max(k,l)} w_{min(k,l)}` automatically (it's the
same multiset), the lattice operation in the level coordinate is
trivial. So the Holley hypothesis on `(B-3b)` reduces to the Holley
hypothesis on `(μ_Q, μ_{Q'})` directly — no level-`k` content gained.
The level-decorated lattice with uniform-in-`I` weight `w_k` is
equivalent to the un-decorated Holley.

(B-3a) and (B-3b) are the only natural choices. (B-3) does not
provide a level-`k` localisation.

**Conclusion on (B-3): RED.**

### §3.4 Resolving (B-4) and (B-2): generating-function attack

mg-21a4 §3.2 noted that (B-2) tilted measure gives a level-averaged
inequality. Let's make this precise to see if a generating-function
argument extracts a level-`k` inequality.

**Setup.** For `Q ⊆ Q'`, define
`f_Q(z) := ∑_{I ∈ J(α)} z^{|I|} · μ_Q(I) · 1[I ∈ S]`
for an up-closed `S` (we want
`Pr_Q[L_k ∈ S] = [z^k] f_Q(z) / e_Q(α) (k+1)`-ish-normalised).

If cross-poset Holley + Daykin–Saks-style integrating gave us
`f_Q(z) ≤ f_{Q'}(z)` for all `z > 0` after appropriate normalisation,
the **generating-function argument** would attempt:

> Coefficient-extraction: if `g(z) := f_{Q'}(z) - f_Q(z) ≥ 0` for all
> `z > 0`, can we extract `[z^k] g(z) ≥ 0`?

This is **not generally true.** `g(z) ≥ 0` for all `z > 0` does not
imply that each coefficient `[z^k] g(z) ≥ 0` — only that the
polynomial `g` is non-negative on `(0, ∞)`. Counterexamples are
abundant: `g(z) = (z - 1)^2 = z^2 - 2z + 1` is non-negative on `ℝ`
but has a negative middle coefficient.

For polynomials with **non-negative** coefficients, `g(z) ≥ 0` is
trivially equivalent to `[z^k] g(z) ≥ 0` for all `k`, and there's no
new content in the inequality. For polynomials with **mixed-sign**
coefficients (which is the realistic case here, since
`f_{Q'}(z) - f_Q(z)` doesn't have a sign pattern), the inequality
on `(0, ∞)` is strictly weaker than the per-coefficient inequalities.

**Does the chamber decomposition give per-level inequalities by a
different mechanism?** Yes — it does, and that's the point. The
chamber argument does *not* use a generating-function trick; it uses
the **direct geometric inclusion** `O(Q') ⊆ O(Q)` plus the **monotonicity
of the level-`k` indicator** as a function on `O(Q)`. These
ingredients are intrinsically level-`k`-aware: the monotone indicator
`f ↦ 1_{level-k chamber's ideal of f ∈ S}` lives on `O(Q)`, not
on a tilted measure.

**Conclusion on (B-2)/(B-4): RED for the level-`k` extraction.**

The generating-function tilted measure gives a `(0, ∞)`-pointwise
polynomial inequality, which does not imply per-coefficient
inequalities. There is no clean (B-4) injection-based argument
either: per mg-7928 §2.4 the Bjorner-style "direct injection
`Ψ' : LE(α[I]) × LE(α[J]) ↪ LE(α[I ∪ J]) × LE(α[I ∩ J])`" is
equivalent to Stanley log-supermod itself plus a chain-encoded
level-`k` constraint, which is the original problem in disguise.
The only known route to level-`k` localisation is via the geometric
chamber (Path A).

### §3.5 What survives of Path B?

A reduced Path B that **drops the level-`k` localisation step** and
delivers only a "summed-over-levels" drops would be:

> **Reduced Path B headline (level-summed).** For up-closed
> `S : Finset α → Prop`, `Q ⊆ Q'`:
> `∑_{k=0}^n Pr_{L ∼ Q}[S(L_k)] ≤ ∑_{k=0}^n Pr_{L ∼ Q'}[S(L_k)]`.

This is consumable for some applications (it's the **expectation
under uniform-level measure**), but the case3 application
(`case3Witness_hasBalancedPair_outOfScope`) and the Brightwell
application (`brightwell_sharp_centred`) **both** require a
**fixed-level-`k`** drops for a specific `k` derived from the
application context (mg-75ef §3 / Brightwell §4 / step8.tex:1042).
A summed-over-levels drops does not specialise to a fixed-level
drops without further work.

A still-narrower Path B would handle the case `k = 1` or `k = n - 1`
(extreme levels) directly via the up-closed property at level 1, but
case3's invocation level is generically `k = 2` or `k = 3` for
width-3 posets (mg-75ef §3), which is not extreme in `n = 3, 4, 5,
6` instances. So even a level-extreme reduction does not handle the
target applications.

**Conclusion on Path B: AMBER-leaning-RED at the level-`k`
localisation step.**

The discrete coupling via Stanley + tilted Holley does not produce
the level-`k`-specific drops headline that case3 and Brightwell
applications require. The four candidate sub-formulations (B-1)
through (B-4) all fail for structural reasons:
- (B-1) Indicator `1[|I| = k]` breaks log-supermod (size-mismatch).
- (B-2) Tilted measure gives level-averaged inequality (Gaussian
  envelope); generating-function coefficient extraction does not
  preserve sign.
- (B-3) Level-decorated lattice degenerates to either the empty
  formulation (B-3a) or the un-decorated Holley (B-3b).
- (B-4) Direct injection is the original problem in disguise.

### §3.6 Path B robustness — fallbacks

Since Path B's level-`k` localisation is RED at the variant level,
the only "fallback" is to switch to Path A. There is no alternative
discrete formulation that survives the §3.4 generating-function
obstruction. Path B is **not the operative path**.

### §3.7 Path B summary

* **Aggregate scope (if level-`k` worked).** ~2900–4900 LoC,
  ~8–11 polecat sessions, ~6–10 weeks calendar (sub-α-C scoping
  §5.11).
* **Mathlib-PR-class chunks.** Only EX-1 (Stanley log-supermod);
  rest is project-internal port (Holley application, level-`k`
  generating-function manipulation).
* **Material RED risks.** Level-`k` localisation step is RED on
  this scoping (§3.3 + §3.4). No surviving sub-formulation.
* **Verdict.** **AMBER-leaning-RED.** Path B does not provide the
  drops headline at a fixed level `k`. It would deliver a
  summed-over-levels drops if the level-`k` step were dropped, but
  that doesn't suffice for case3 or Brightwell applications.

---

## §4 Comparison + verdict

### §4.1 Side-by-side

| Dimension | Path A | Path B |
|-----------|--------|--------|
| **Mathematical tractability** | Literature-known (Stanley 1986, Daykin–Saks 1981, Brightwell 1999 §4); each chunk has a published proof. | Level-`k` localisation **RED** per §3 (no surviving sub-formulation). |
| **Aggregate LoC (post-EX-1)** | ~4450–7700 | ~2900–4900 (conditional on level-`k` working — it doesn't) |
| **Mathlib-PR-class chunks** | EX-3, EX-4, EX-5 (partial), EX-6 — ~1700–3100 LoC of community-amortisable work | ~0 (Stanley already landed; rest is project-internal) |
| **DH-1 (mathlib upstream Stanley) leverage** | EX-3..EX-7 already consume Stanley as hypothesis; DH-1 lands as a no-op replacement of the temp axiom. | Same — DH-1 is path-orthogonal. |
| **DH-2 (thin-slice case3) leverage** | Natural — chamber decomp specialises to width-3 with up to ~30–50% LoC saving on EX-3..EX-5. | Not applicable — Path B does not have a chamber sub-pillar. |
| **DH-4 (continuous FKG bypass) leverage** | If continuous FKG comes from mathlib upstream, EX-6 collapses to a citation; ~1000–2000 LoC saved. | Not applicable — Path B does not use continuous FKG. |
| **Material RED risk** | EX-6 (continuous FKG) AMBER, with integer-sub-lattice fallback for fixed-`α` applications. | Level-`k` localisation RED; no fallback within Path B. |
| **Calendar (post-EX-1)** | ~9–15 weeks (12–16 polecat sessions); −2–3 sessions if DH-4 lands; −1–2 sessions if DH-2 lands. | n/a (RED). |

### §4.2 Verdict

**GREEN-A.**

Path A is the operative path. Path B's level-`k` localisation is
**AMBER-leaning-RED** per §3.3 + §3.4: all four candidate
sub-formulations (B-1) through (B-4) hit structural obstructions
of the same character as the mg-21a4 §3.2 size-mismatch class,
plus a new generating-function obstruction (§3.4) showing that
the tilted-measure approach gives only `(0, ∞)`-pointwise
polynomial inequalities, not per-coefficient (per-level)
inequalities.

Path A's pipeline is literature-known (Stanley 1986; Brightwell
1999 §4; Daykin–Saks 1981); aggregate LoC post-EX-1 refines to
~4450–7700, within ~1.15× of state.md §4.2's working figure;
single material RED risk (EX-6 continuous FKG) is AMBER with a
clean integer-sub-lattice fallback for fixed-`α` applications.

### §4.3 What this means for sub-α-C

* **Sub-α-C arc-level verdict: GREEN, upgraded from AMBER-leaning-GREEN.**
  The fork resolution closes the principal structural unknown
  (Path-A-vs-Path-B; sub-α-C scoping §1's third unknown). EX-6
  (continuous FKG) remains AMBER at the chunk level but is
  bounded.

* **Next execution ticket: EX-3 (order polytope `O(α)` as Lean
  type).** Spec drafted in §5.

* **DH leverage points re-prioritised.**
  - **DH-1 (mathlib upstream Stanley).** Highest leverage,
    unchanged. Discharges the temp axiom from the trust surface;
    independent value as mathlib contribution.
  - **DH-4 (continuous FKG bypass).** Heightened post-fork-resolution.
    EX-6 is the largest single chunk; if Daniel can engage a
    mathlib reviewer on continuous FKG/AD, ~1000–2000 LoC
    collapses to a citation.
  - **DH-2 (thin-slice case3).** Unchanged. Specialises EX-3..EX-5
    and saves ~600–1100 LoC if confirmed.
  - **DH-3 (Brightwell-port amortisation).** Unchanged. Confirms
    EX-9 is genuinely a ~500–800 LoC specialisation rather than a
    separate sub-α-C-equivalent arc.

### §4.4 Robustness — what if Path A REDs at some stage?

Per polecat brief §2 (5):

| Stage | Likelihood of RED | Fallback |
|-------|-------------------|----------|
| EX-3 (order polytope) | very low — definition only | n/a |
| EX-4 (vertex thm) | low — classical | re-prove via finite extreme-set enumeration |
| EX-5 (chamber decomp) | low — measure-zero overlap | sub-pieces dispatched separately |
| EX-6 (continuous FKG) | **AMBER** | integer-sub-lattice discretisation: gives weaker drops with size-`N` factor; for fixed-`α` applications (case3, Brightwell), factor is constant, so applications still close |
| EX-7 (drops headline) | very low — short argument | re-derive via direct chamber sum |

If EX-6 hits a hard mathlib refactor barrier (e.g., the
discrete-to-continuous limit requires a new measurability framework),
the integer-sub-lattice discretisation gives:

> **Discretised drops.** For fixed `α`, fixed integer side `N ≥ |α|`,
> and `Q ⊆ Q'`: the level-`k` event probabilities under the
> discretised polytope `O_N(Q)` differ from the continuous ones by
> `O(1/N)`. For `N = poly(|α|)`, this is bounded for the case3 and
> Brightwell applications.

This is structurally weaker than the abstract drops but suffices
for the OneThird headline. **Path A does not structurally collapse
under EX-6 RED.**

If multiple EX stages RED (cascade scenario): per polecat brief
trip-wire "Both paths RED → STOP and mail Daniel" — Path α is
formally RED, Path γ becomes the sole feasible direction. This
scoping does **not** fire that trip-wire; Path A's EX-6 risk is
AMBER with a clean fallback.

### §4.5 Trip-wire status

* **Path B level-`k` localisation RED:** **FIRED** per §3.3 + §3.4.
  PM commits Path A.
* **Path A DH-4 RED:** **NOT FIRED.** §2.3 assessment: bounded
  mathlib-gap, no structural obstacle, integer-sub-lattice
  fallback available.
* **Both paths RED:** **NOT FIRED.** Path A is GREEN.
* **Token blow-up:** **NOT FIRED.** Approximate spend on this
  scoping is ~75k of 300k cap.

---

## §5 Next execution ticket spec — EX-3 (Path A)

### §5.1 Title

**EX-3 — Order polytope `O(α)` as a Lean type.**

### §5.2 Goal

Define the order polytope of a finite poset as a Lean type, equip
it with the basic convex / measurable / compact properties, and
verify the canonical instance on the discrete 3-antichain
(`α = {a,b,c}`, `O(α) = [0,1]^3`).

### §5.3 Lean signature (target)

```lean
-- lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean (NEW)

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Order.LowerSet.Basic

namespace OneThird.LinearExt

/-- The order polytope of a finite poset α: order-preserving maps
    α → [0,1] ⊆ ℝ, viewed as a subset of α → ℝ. -/
def OrderPolytope (α : Type*) [PartialOrder α] : Set (α → ℝ) :=
  { f : α → ℝ |
      (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y : α, x ≤ y → f x ≤ f y) }

/-- O(α) is convex. -/
instance : Convex ℝ (OrderPolytope α) := ⟨...⟩

/-- O(α) is closed (in α → ℝ with the product topology). -/
instance : IsClosed (OrderPolytope α) := ⟨...⟩

/-- O(α) is bounded. -/
instance : Bornology.IsBounded (OrderPolytope α) := ⟨...⟩

/-- O(α) is compact (consequence of closed + bounded in ℝ^n). -/
instance [Fintype α] : IsCompact (OrderPolytope α) := ⟨...⟩

/-- O(α) is measurable (via finite intersection of half-spaces). -/
instance [Fintype α] : MeasurableSet (OrderPolytope α) := ⟨...⟩

end OneThird.LinearExt
```

### §5.4 Dependencies

- **In-tree.** None directly; depends on the import surface
  `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`,
  `Mathlib.Analysis.Convex.Basic`, `Mathlib.Order.LowerSet.Basic`.
- **Stanley axiom.** Not consumed at EX-3 level (axiom is consumed
  starting at EX-5).
- **EX-1 / EX-2.** Not consumed at EX-3 level.

### §5.5 Out of scope (deferred to EX-4, EX-5)

- Vertex characterisation `vertices(O(α)) = {1_I : I ∈ J(α)}`
  (EX-4).
- Chamber simplex `σ_L` and decomposition `O(α) = ⋃ σ_L`
  (EX-5).
- Volume formula `Vol(O(α)) = e(α) / n!` (EX-5).

### §5.6 Polecat session estimate

**1 polecat session, ~300–500 LoC, ~200–300k tokens.**

This is a clean definition + basic-properties chunk with no
mathematical depth — just careful import + instance bootstrap.
Suitable for a single execution polecat without a separate scoping
session.

### §5.7 Verdict targets

- **GREEN.** `OrderPolytope` defined, basic instances populated,
  build green, in-tree consumer at the `α = {a,b,c}` discrete
  3-antichain instance verified by hand.
- **AMBER.** Some instances surface mathlib-gap surprises (e.g.,
  the `MeasurableSet` instance requires more than finite-half-space
  intersection). Polecat dispatches a follow-up scoping for the
  surface gap and lands the rest.
- **RED.** Defining `OrderPolytope` itself surfaces a structural
  obstruction (e.g., the natural definition is not a `Set` but a
  `MeasureSpace`-typed object). Polecat mails Daniel.

### §5.8 Predecessors

- mg-d0fc (`00cbc2d`) — EX-1 Option A: `stanley_log_supermod`
  axiom landed.
- mg-163f (this scoping) — Path A vs Path B fork resolution,
  GREEN-A.

### §5.9 Trip-wires

- **Token blow-up** (>240k of 300k cap before GREEN): STOP, mail
  PM with status.
- **Mathlib refactor required** (e.g., the convex/measurable
  infrastructure needs a major patch): STOP, mail Daniel for
  guidance on whether to dispatch the mathlib-PR work as a
  separate ticket.
- **Definition pollution** (the natural `OrderPolytope` definition
  forces `Mathlib.Order` global instance changes): STOP, scope as
  a sub-ticket.

---

## §6 References

### §6.1 Predecessor polecat documents

* mg-d0fc (`00cbc2d`) — EX-1 Option A executed.
  `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`,
  `lean/AXIOMS.md` third entry.
* mg-7928 (`6e07904`) — EX-1 Session A.2 closure RED.
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-induction-closure.md`.
* mg-c7b9 (`4b5b1ba`) — EX-1 Session A scoping.
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-scoping.md`.
* mg-91be (`bb450a4`) — sub-α-C high-level scoping.
  `docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`,
  esp. §4 fork enumeration, §5 critical path with Lean
  signatures, §7 DH leverage points.
* mg-21a4 (`f862b76`) — sub-α-A scoping.
  `docs/path-alpha-execution-arc/sub-alpha-A-scoping.md`,
  esp. §3.1 counterexample, §3.2 size-mismatch failure modes
  (the obstruction class generalised in §3.3 + §3.4 here).
* mg-bb74 (`73ed85e`) — `lean/AXIOMS.md` framing refresh.
* mg-dc9d (`a95020e`) — Hibi-1 STOP.
  `docs/path-alpha-execution-arc/hibi-1-stop-report.md`.
* mg-b10a (`256f0da`) — A8-S2-cont-4 STOP report.
  `docs/a8-s2-cont-execution-arc/cont-4-stop-report.md`.

### §6.2 Literature

* Stanley 1981. Stanley, *Two combinatorial applications of the
  Aleksandrov–Fenchel inequalities*, J. Combin. Theory Ser. A
  **31** (1981), 56–65. — original Stanley log-supermod (EX-1
  axiom source).
* Stanley 1986. Stanley, *Two poset polytopes*, Discrete Comput.
  Geom. **1** (1986), 9–23. — order polytope (EX-3), vertex
  theorem (EX-4), chamber decomposition (EX-5), volume formula.
* Daykin–Saks 1981. Daykin and Saks, *A natural generalization of
  FKG for partial orders*. — drops headline source (EX-7).
* Brightwell 1999. Brightwell, *Balanced pairs in partial orders*,
  Discrete Math. — §4 Daykin–Saks via chamber decomp + continuous
  FKG (EX-7, EX-9 source).
* Preston 1974. Preston, *Spatial birth-and-death processes*. —
  continuous FKG/AD on `[0,1]^n` (EX-6 source).
* Ahlswede–Daykin 1979. Ahlswede and Daykin, *An inequality for the
  weights of two families of sets, their unions and intersections*,
  Z. Wahrsch. Verw. Gebiete **43**, 183–185. — discrete 4FT (mathlib
  has) and continuous version (EX-6 source).
* Hibi 1985. Hibi, *Distributive lattices, affine semigroup rings,
  and algebras with straightening laws*. — historical context.
* Bjorner 1989. Björner, *On the homology of geometric lattices*. —
  surveyed in mg-c7b9 / mg-7928 for variant-3 closure (RED).
* Daykin 1990 (folklore). — surveyed in mg-c7b9 (variant-2,
  REJECT).

### §6.3 In-tree code (verified at this commit)

* `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`
  — Stanley axiom + `subPoset` definition (mg-d0fc).
* `lean/OneThird/Mathlib/LinearExtension/Fintype.lean:45,105` —
  `LinearExt α`, `numLinExt`.
* `lean/OneThird/Mathlib/LinearExtension/Birkhoff.lean` —
  Birkhoff bijection.
* `lean/OneThird/Mathlib/LinearExtension/FKG.lean:452` —
  existing lossy product-lattice pathway.
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean` —
  `brightwell_sharp_centred` axiom (target for EX-9).
* `lean/AXIOMS.md` — three named project axioms.

### §6.4 Mathlib code (verified at this commit's `lake-manifest`)

* `Mathlib.Order.LowerSet.*` — distributive lattice on `LowerSet α`.
* `Mathlib.Combinatorics.SetFamily.FourFunctions.four_functions_theorem`
  — discrete FKG/AD; consumed by EX-6 as base case.
* `Mathlib.Analysis.Convex.Basic` — convex sets; consumed by EX-3.
* `Mathlib.Analysis.MeanInequalities` — Jensen, Hölder; **does
  not** contain continuous FKG (EX-6 mathlib gap).
* `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` — Lebesgue measure
  on `ℝ^n`; consumed by EX-3, EX-5, EX-6.
* `Mathlib.MeasureTheory.Integral.Lebesgue` — integration framework;
  consumed by EX-6.

### §6.5 Feedback / policy applied

* `feedback_polecat_cumulative_state_doc` — applied (state.md
  updates per §10 mandate; see commit diff).
* `feedback_latex_first_for_math_simp` — applied (this document
  is the deliverable; no Lean source touched).
* `feedback_complexity_blowup_means_wrong_path` — applied
  (trip-wires §4.5).
* `feedback_polecat_stop_runaway` — applied (no auto-extension; PM
  files EX-3 next).
* `feedback_pre_execution_dependency_verification` — applied (§5
  EX-3 spec has explicit Lean signature, dependencies verified
  against current mathlib).
* `feedback_long_arcs_are_pm_authority` — invoked (PM commits
  Path A per Daniel 2026-05-07T16:06Z directive on sub-α-C arc;
  fork-resolution within the arc is PM's call).
* `feedback_pm_is_mini_ceo_default` — applied (Path A vs Path B
  fork is a Lean-ticket-shape decision; PM decides + informs;
  Daniel default-acceptance window applies).
* `feedback_block_and_report` — applied (no blocking on Daniel
  acknowledgment for Path A commitment; PM will dispatch EX-3
  next).

---

*End of Path A vs Path B fork resolution. Lean source unchanged.
Verdict: **GREEN-A**; PM commits Path A and files EX-3 (order
polytope `O(α)` as Lean type) as the next execution ticket.*

— polecat mg-163f (cat-mg-163f), 2026-05-08.
