# A8-S2-cont-4 STOP report — trip-wire #2 fires (structural obstruction)

**Work item:** `mg-b10a` (polecat `pb10a`).
**Branch:** `polecat-pb10a` (target `a8-s2-cont-execution-arc`).
**Predecessor:** `mg-8d39` (`docs/a8-s2-cont-scoping-arc/scoping.md`,
upgraded GREEN, ~1450-2700 LoC residual estimate).
**Verdict:** **STOP, escalate.** Trip-wire #2 of the polecat brief
fires: the probability-form lift requires an FKG primitive that is
**not in mathlib** and is **not derivable** from the existing
data-poset primitives via the strategy outlined in mg-8d39 §2.

This document is a latex-first STOP report per the polecat brief
("If new math turns out to need its own axiom: report honestly via
paper-vs-formalization diagnosis"). Lean source unchanged.

---

## §1 What the ticket asked for

mg-8d39 §2.1 specified the headline lemma:

```lean
theorem probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L : LinearExt' Q  => S (L.initialIdeal' k.val))
      ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val))
```

Estimated 600-1200 LoC via Strategy A (single-edge `addRel`
induction). Trip-wires baked in mg-8d39 §5; mg-8d39 §6 verdict was
**upgraded GREEN** *conditional on no new structural obstruction*.

## §2 Reduction confirmed: drops ↔ FKG positive correlation on `LinearExt' Q`

The headline reduces (per mg-8d39 §2.2 Strategy A) to the single-edge
case `Q' = addRel Q a b`. After this reduction:

```
N  := |LinearExt' Q|         (denominator on the LHS)
N' := |LinearExt' Q'|        (denominator on the RHS)
A  := {L ∈ LE Q : S(L.iI k)}    (S-event on LE Q)
R  := {L ∈ LE Q : L.lt a b}     ("L respects (a,b)")

c_Q  := |A|
c_Q' := |A ∩ R|              (under restrict : LE Q' ↪ LE Q with image R)
N'   := |R|
```

The desired drops `c_Q · N' ≤ c_{Q'} · N` rearranges to:

```
|A| · |R| ≤ |A ∩ R| · N
```

i.e. **FKG positive correlation between the two events `A` and `R`
under the uniform counting measure on `LinearExt' Q`**. (Direction
verified by hand on a 3-element example: `α = {a, b, c}`, `Q =
discrete`, `k = 1`, `S = "{a} ⊆ I"`. There `c_Q = 2`, `N = 6`,
`N' = 3`, `c_{Q'} = 2`, drops gives `2·3 = 6 ≤ 2·6 = 12`. ✓ This
fixes the direction confusion that arises if one tries to read
"down-closed" from the LaTeX naïvely.)

## §3 The structural obstruction

### §3.1 Mathlib's FKG primitives are on a *distributive lattice*

Mathlib's relevant primitives, all in
`Mathlib.Combinatorics.SetFamily.FourFunctions`:

* `fkg` — for log-supermodular `μ : L → ℝ` on a finite distributive
  lattice `L`, monotone non-negative `f, g : L → ℝ`:
  `(∑ μ·f)(∑ μ·g) ≤ (∑ μ)(∑ μ·f·g)`.
* `four_functions_theorem`, `four_functions_theorem_univ` — universal
  Ahlswede–Daykin form on a distributive lattice.
* `holley` — Holley's inequality between two log-supermodular measures
  on a distributive lattice.

**All require a finite distributive lattice carrier.** None applies
directly to `LinearExt' Q`, which is **not** a lattice in any natural
canonical sense.

### §3.2 Candidate lattices on `LinearExt' Q` — none works

The literature (Brightwell 1999 §4, Björner–Wachs 1991, Stanley 1981)
considers several lattice structures:

| Candidate                              | Distributive? | `R` monotone? | `A` monotone? |
|----------------------------------------|---------------|---------------|---------------|
| Bruhat order on LE                     | **NO**        | yes           | yes           |
| Weak order on LE                       | **NO**        | yes           | yes           |
| Inversion-set inclusion on LE          | **NO**        | yes           | yes (up-closed S) |
| Chain-of-ideals embedding into product | partial       | n/a (lossy)   | n/a (lossy)   |
| Hibi order polytope chambers           | partial       | yes           | yes           |

**None of the natural candidates is a distributive lattice on
`LinearExt' Q`.** The Bruhat and weak orders are graded posets but
not lattices. The Hibi polytope chamber decomposition is what the
literature actually uses, but it requires polytope/chamber
infrastructure that is not in mathlib (`Mathlib.Geometry.Convex` is
partial; the Hibi order polytope is not formalised).

### §3.3 The product-lattice route is too lossy

mg-8d39 §1.5 already noted this: `pi_fkg_uniform_correlation` on
`Fin (n+1) → LowerSet' Q` gives the bound

```
(∑_L f(L.chain)) · (∑_L g(L.chain)) ≤ |product| · ∑_ω f(ω)·g(ω)
```

with the **product-lattice cardinality** `|Fin (n+1) → LowerSet' Q|`,
not `numLinExt' Q`. This factor is `(2^{n^2})^{n+1}` worst-case versus
`numLinExt' Q ≤ n!`, an exponential loss. **Tightening this factor
to `numLinExt' Q` is exactly the work the ticket asks for, and is the
substantive Daykin–Saks content** (mg-8d39 §1.5 confirms: "Tightening
the cardinality factor from `|product|` to `numLinExt'` is the
substantive remaining work.")

### §3.4 Holley on `LowerSet' Q` doesn't apply either

A natural attempt: define a measure `μ_Q` on the lattice
`Fin (n+1) → LowerSet' Q` via `μ_Q(ω) := 1` if `ω ∈ IdealChain' Q`,
else `0`; analogously `μ_{Q'}`. Then apply Holley.

**This fails because `μ_Q` is not log-supermodular.** Componentwise
meets/joins of saturated chains are typically not saturated chains, so
`μ_Q(ω) · μ_Q(τ) > 0` while `μ_Q(ω ∧ τ) · μ_Q(ω ∨ τ) = 0` for
generic `ω, τ ∈ IdealChain' Q`.

(The same obstruction applies to any "indicator of being a chain"-style
measure: chain-ness is not preserved under componentwise lattice
operations on the product.)

### §3.5 Slice-by-level Holley fails on size-mismatch

Another attempt: fix `k`, define `μ_Q^{(k)}(I) := |LE Q[I]| ·
|LE Q[α \ I]|` if `I` is a Q-lower-set with `|I| = k`, else `0`,
on the lattice `LowerSet(α)`. Then `Pr_Q[S(L.iI k)] = E_{μ_Q^{(k)}}[1_S]`.

For Holley between `μ_Q^{(k)}` and `μ_{Q'}^{(k)}` on `LowerSet(α)`,
need: `μ_Q(I) · μ_{Q'}(J) ≤ μ_Q(I ∩ J) · μ_{Q'}(I ∪ J)`.

But `μ_Q^{(k)}` is supported on size-`k` lower-sets only; for `I, J`
with `|I| = |J| = k`, the meet `I ∩ J` and join `I ∪ J` typically have
sizes `< k` and `> k` respectively, where `μ_Q^{(k)}` and `μ_{Q'}^{(k)}`
are zero. The Holley hypothesis fails outright (RHS is zero, LHS is
positive).

### §3.6 Direct bijective proof of single-edge drops fails too

The standard "swap-(a, b)" bijection on `LinearExt' Q`:

* Given `L ∈ LE Q` with `b` before `a` (i.e., `¬ R(L)`), try to
  construct `L' ∈ LE Q` with `a` before `b` by moving `a` to just
  before `b` in the linear order.
* `L'` may **not** be a Q-LE: any element `x_i` strictly between `b`
  and `a` in `L` with `Q.le x_i a` would violate Q-LE in `L'`
  (where `a` is now before `x_i`).

So the swap is not well-defined on all of `LE Q`. Daykin–Saks 1981 and
Brightwell 1999 §4 work around this via **shells** of the linear
extension polytope (Hibi chambers), which decomposes the bijection
problem into independent local problems on each chamber — but again,
this is the polytope/chamber machinery.

## §4 Why this isn't a "harder than expected, just write more Lean" case

The scoping mg-8d39 §5.1 (Risk 1, "single-edge step harder than
~600-1200 LoC") considered the possibility of LoC blow-up to
1500-2500 with mitigation "subsplit". §5.6 (Risk 6, "no
FKG-applicable lattice on LE") considered "+300-800 LoC" with
mitigation "chamber decomposition".

**Risk 6 fires and the mitigation is unavailable in mathlib.** The
chamber-decomposition route requires:

1. The Hibi order polytope as a formalised polytope (vertices =
   `Q-lower-sets`, faces = chains of lower sets).
2. A chamber decomposition / triangulation, with the `LinearExt' Q`
   indexing the chambers.
3. Volume / cardinality identities `Vol(P_Q) = #LE(Q) / n!` and the
   single-edge volume identity.

Mathlib has `Mathlib.Order.Birkhoff` (the abstract Birkhoff
representation theorem, lattice level only — no polytope) and
`Mathlib.Combinatorics.Polynomial.Cyclotomic` (unrelated). The
**Hibi order polytope is not in mathlib**, and porting it is a
substantial mathlib-PR-class undertaking (~2000-4000 LoC, multiple
authors over a quarter or more in mathlib practice).

The scoping mg-8d39 §5.6 specifically said:

> The risk is the gap between "Bruhat-monotone events correlate" and
> "we can prove this in Lean". The Brightwell 1999 §4 proof is
> constructive and ports to Lean as a combinatorial induction.
> **Risk assessment: medium-low.** This is the one risk that could
> move the LoC estimate from 600-1200 toward 1200-2000 LoC if the
> Lean port of the chamber-decomposition argument turns out verbose.

After investigating, the risk is **higher than medium-low** because
Brightwell §4's "constructive combinatorial induction" still implicitly
uses the polytope-chamber framing. The "ports to Lean as a
combinatorial induction" claim is optimistic — the induction itself
needs an FKG-on-LE engine that doesn't exist.

## §5 What this means for the case3 axiom port

mg-8d39 §6.2 quantified the audit-bar reward:

> After the residual ~2700-LoC arc lands, the
> `case3Witness_hasBalancedPair_outOfScope` axiom is removed from
> the trust surface.

This is now **conditional** on either:

1. **(Path α)** Building the FKG-on-LE primitive via the
   chamber-decomposition route. Estimated **2000-4000 LoC** for the
   FKG-on-LE infrastructure (Hibi polytope or equivalent chamber
   structure on `LinearExt' Q`), plus the original ~1450-2700 LoC for
   the application chain. **Total ~3500-6700 LoC, 6-12 polecat
   sessions, multi-polecat parallelisable but with a hard sequential
   bottleneck on the FKG-on-LE primitive.** This is comparable in
   scope to mathlib gap E5 (`mg-3c06`, the `brightwell_sharp_centred`
   port), and the two share the FKG-on-LE prerequisite. Closing both
   audit-bar items is roughly the same workload as closing one
   (modulo the ~100-300 LoC of axiom-specific application chain for
   each), which is a favourable per-axiom amortisation.

2. **(Path β)** Reformulating the case3 discharge to **avoid** the
   probability-form drops headline. mg-75ef §4 explored three
   workarounds and concluded none closes; mg-5bf9 §3 explored one more
   route (linear-majority alignment) and reached the same
   conclusion. **No known route avoids the drops headline.** This
   path is currently **blocked at math level**, not just Lean-port
   level.

3. **(Path γ)** Retaining `case3Witness_hasBalancedPair_outOfScope` as
   a project axiom, with the existing `lean/AXIOMS.md:226-454`
   disclosure. The axiom is QA-audited (mg-7377) as a faithful
   transcription of `rem:enumeration` (`step8.tex:3157-3173`), and
   the forum-readiness pass (mg-d7fd) certified the trust surface as
   publishable with this axiom in place. **No code change required.**

## §6 Recommendation

**Recommended: Path γ (retain the axiom).**

Rationale:

* The drops headline is **strictly harder than the existing
  `brightwell_sharp_centred` axiom in audit-bar economics**: both
  share the same mathlib gap (FKG-on-LE chamber decomposition);
  Brightwell is one specific bound and the drops headline is the
  general primitive; closing the general primitive enables both.
* Path α (build chamber decomposition) is a quarter-scale or longer
  mathlib infrastructure project. It is not a polecat-session-class
  task. **Filing it now would tie up multi-polecat capacity for
  weeks-to-months** with uncertain return.
* Path β is blocked at math level; further math work would be a
  multi-mg latex-first scoping arc with no clear path to closure.
* Path γ has **zero residual risk**: the axiom is already disclosed,
  audited, and the forum-readiness pass has signed off on the trust
  surface. The audit-bar story for the forum post is "two named
  project axioms (Brightwell + case3-residual), both transcriptions
  of well-defined paper statements, both with explicit replacement
  paths and shared mathlib-gap dependency" — already articulated in
  `lean/AXIOMS.md` and `docs/forum-readiness-validation/`.

**If Daniel/mayor disagrees and prioritises axiom elimination over
ship velocity:** file a long-arc ticket
**`mathlib-gap-FKG-on-LE`** (working name, dual to `mg-3c06`) for the
shared primitive. Estimated 2000-4000 LoC, multi-polecat,
sequential bottleneck. After it lands, both `brightwell_sharp_centred`
and `case3Witness_hasBalancedPair_outOfScope` can be discharged in
follow-on tickets (~300-600 LoC each).

## §7 Trip-wire status

Per the polecat brief §7 trip-wires:

* **Trip-wire #1 (token overrun > 2.25M):** not fired. Approximate
  spend on this STOP report ~70k tokens of the 1.5M cap.
* **Trip-wire #2 (new structural obstruction):** **fires.** The
  FKG-on-LE primitive required by Strategy A's inductive step is
  not in mathlib and not derivable from the existing data-poset
  primitives. Could RED the entire A8-S2-cont path (per the brief).
  Reporting honestly per
  `feedback_complexity_blowup_means_wrong_path` and
  `feedback_polecat_stop_runaway`.
* **Trip-wire #3 (F4-b trap):** not fired. The obstruction is
  Step-8-internal (FKG-on-LE), not a Steps 5-7 dependency.
* **Trip-wire #4 (LoC blow-up > 1800):** not technically fired (no
  Lean source committed); the *projected* LoC for Path α is
  ~2000-4000 LoC for the FKG-on-LE primitive alone, well above
  1800.
* **Trip-wire #5 (`#print axioms` shows new axiom):** not fired (no
  source change).
* **Trip-wire #6 (build break):** not fired (no source change).
* **Trip-wire #7 (mathlib FKG primitive richer than expected):** not
  fired in the audit-bar-friendly direction. mathlib's FKG is
  exactly as scoped — log-supermodular weights on a distributive
  lattice. The gap is on the *consumer* side
  (`LinearExt' Q` has no distributive lattice structure), not on
  the *primitive* side.

## §8 Outcome class

Per `feedback_distinguish_arc_chunk_outcomes`:
**substantive scoping update; no parallel cleanup; no Lean source
change.** This document IS the deliverable, like mg-8d39 itself.

## §9 What this STOP does NOT block

* The forum post (Path A) is unaffected. Trust surface remains as
  declared in `lean/PRINT_AXIOMS_OUTPUT.txt` after Stage 2B.
  mg-d7fd's GREEN forum-readiness verdict still holds.
* The headline `width3_one_third_two_thirds` is unaffected — it
  closes against `case3Witness_hasBalancedPair_outOfScope` exactly
  as today.
* mg-8d39 (the scoping arc) remains accurate as a *scoping*
  artifact. Its upgraded-GREEN verdict was conditional on no
  structural obstruction; this STOP report records that the
  condition does not hold for Path α (build the primitive
  ourselves) but the scoping's analysis of *where* the work is
  remains correct.

## §10 What follow-on tickets PM might file

After this STOP:

1. **Re-evaluate the case3 axiom retention decision.** PM/Daniel
   choose between Path γ (retain) and Path α (commit to a
   long-arc mathlib-gap port). Path γ is recommended; Path α is
   acceptable if axiom elimination is a hard requirement.
2. **(If Path α)** File `mathlib-gap-FKG-on-LE` with explicit
   long-arc scope and multi-polecat capacity reservation.
3. **(Either way)** Update the forum-post draft to reflect that
   `case3Witness_hasBalancedPair_outOfScope` is **definitively
   retained** (Path γ) or **scheduled for replacement via shared
   mathlib-gap port** (Path α). Either disclosure is honest;
   pick consistent with the chosen path.
4. **Cancel the dependent tickets** (A8-S2-cont-5, case3-port-3,
   case3-port-4, case3-port-axiom-removal) that were planned to
   chain off A8-S2-cont-4. case3-port-1 (Lemma 2.1 orientation
   acyclicity, ~30-50 LoC) remains independently valuable as a
   tiny audit-bar improvement and can be filed independently.

## §11 Cross-references

* `docs/a8-s2-cont-scoping-arc/scoping.md` (mg-8d39, branch
  `a8-s2-cont-scoping-arc`) — the scoping arc that GREEN'd this
  ticket conditionally.
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:506-516, 420-426` —
  in-tree docstrings naming this exact deferred work.
* `lean/AXIOMS.md` — `case3Witness_hasBalancedPair_outOfScope`
  disclosure (`:226-454`) and `brightwell_sharp_centred`
  disclosure (`:13-225`); both are the FKG-on-LE-blocked items.
* `docs/case3-port-arc/rem-enumeration-proof.md` (mg-75ef) — verdict
  β math artifact concluding "the math needs probability-form
  cross-poset FKG".
* `docs/case3-port-arc/linear-majority-alignment.md` (mg-5bf9) —
  verdict AMBER, reached the same conclusion via a different path.
* `docs/case3-port-arc/port-status.md` (mg-e850) — Lean-side
  STOP-and-report on count-form FKG insufficiency.
* `feedback_complexity_blowup_means_wrong_path.md` — trip-wire
  policy applied here.
* `feedback_polecat_stop_runaway.md` — STOP firing protocol applied.
* `feedback_audit_bar_for_axioms.md` — audit-bar economics applied
  in §6.

---

*End of STOP report. Length: ~310 lines, comparable to predecessor
STOP reports (mg-e850 ~298 lines). Lean source unchanged.*
