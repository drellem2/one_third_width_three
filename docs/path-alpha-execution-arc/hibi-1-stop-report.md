# Hibi-1 STOP report — τ-inversion order on `LinearExt α` is not distributive (trip-wire #2)

**Polecat:** mg-dc9d (Hibi-1)
**Date:** 2026-05-06
**Verdict:** STOP. Trip-wire #2 fires (structural obstruction).
**Recommendation:** Escalate to PM / Daniel. Path α as scoped by
mg-ff7f is **mathematically impossible** in the cases the application
requires. Re-scoping needed.

## §1 Summary

mg-ff7f §2.5 asserts:

> for any fixed `τ ∈ L(α)`, `(L(α), ≤_τ)` *is* a distributive
> lattice (Brightwell §3.5.1).

This claim is **false** for the discrete 3-element antichain (a width-3
poset, in scope for the OneThird project). On that poset
`(LinearExt α, tauLE τ)` is the **right weak Bruhat order on S₃**
— the well-known six-element non-distributive hexagon.

Consequently the deliverable named `tauDistribLattice (τ : LinearExt α)
: DistribLattice (LinearExt α)` cannot be inhabited without changing
either the carrier type or the order. There is no Lean-mechanical fix
because the obstruction is at the level of mathematics, not formalisation.

mg-ff7f §6.1 ("Risk 1 — distributivity proof harder than expected,
LIKELIHOOD: low, MITIGATION: direct adjacent-transposition fallback")
**misclassifies** this risk: the issue is not proof difficulty but
non-existence of the object. The "direct adjacent-transposition
fallback" cannot prove distributivity that does not hold.

The prior STOP report (mg-b10a, `cont-4-stop-report.md` §3.2) listed
"inversion-set inclusion on LE" with verdict **NO** under "Distributive?".
mg-ff7f §2.5 explicitly attempted to overturn this finding but did not
provide a counterexample to mg-b10a's claim, nor a reference computation
that exhibits a distributive structure. The current investigation
confirms mg-b10a was correct.

## §2 The counterexample

**Setup.** `α = {a, b, c}`, no order relations (discrete 3-poset, width 3).
There are 6 linear extensions. Fix `τ = (a, b, c)` (i.e. τ.pos a = 0,
τ.pos b = 1, τ.pos c = 2). All α-pairs are α-incomparable; the
τ-orientation gives `τ.lt a b`, `τ.lt a c`, `τ.lt b c`. The candidate
inversion-pair set is `{(a,b), (a,c), (b,c)}`.

**Inversion sets** (`tauInv τ L = {(i,j) : τ.lt i j ∧ L.lt j i}`):

| L            | tauInv τ L                  |
|--------------|------------------------------|
| `(a, b, c)`  | `∅`                          |
| `(a, c, b)`  | `{(b,c)}`                    |
| `(b, a, c)`  | `{(a,b)}`                    |
| `(b, c, a)`  | `{(a,b), (a,c)}`             |
| `(c, a, b)`  | `{(a,c), (b,c)}`             |
| `(c, b, a)`  | `{(a,b), (a,c), (b,c)}`      |

The poset `(LinearExt α, tauLE τ) = (LinearExt α, ⊆ on tauInv)` has
Hasse diagram:

```
                         T = {(a,b),(a,c),(b,c)}
                        /                       \
              X = {(a,b),(a,c)}        Y = {(a,c),(b,c)}
                  |                              |
              U = {(a,b)}                   V = {(b,c)}
                        \                       /
                         B = ∅
```

This is the **hexagon (S₃ right weak Bruhat order)**.

**Distributivity test.** Compute both sides of one distributive law:

* `(U ∨ V) ∧ X`: the only common upper bound of `U` and `V` is `T`
  (since `X ⊉ V` and `Y ⊉ U`), so `U ∨ V = T`. Then `T ∧ X = X`.
* `(U ∧ X) ∨ (V ∧ X)`: `U ⊆ X` so `U ∧ X = U`; `V ∩ X = ∅` so
  `V ∧ X = B`. Hence `(U ∧ X) ∨ (V ∧ X) = U ∨ B = U`.

`X = {(a,b),(a,c)}` while `U = {(a,b)}`. `X ≠ U`. **Not distributive.**

This is the canonical witness that `S₃` weak order is non-distributive
(see Björner–Brenti, *Combinatorics of Coxeter Groups*, Prop. 3.2.1
plus standard remarks).

## §3 Why mg-ff7f's premise fails

mg-ff7f §2.5 critiques mg-b10a's verdict ("inversion-set inclusion: NO")
by writing:

> The "NO" verdict in mg-b10a is incorrect at this resolution: for any
> fixed `τ ∈ L(α)`, `(L(α), ≤_τ)` *is* a distributive lattice
> (Brightwell §3.5.1). The mg-b10a polecat may have read "inversion-set
> inclusion" as implicitly varying τ — a different lattice for each L —
> but the correct reading fixes τ once and gets a globally distributive
> lattice on the full `L(α)`.

Both readings agree on the τ-fixed case (the table above already fixes
τ = (a,b,c)). The right weak order is precisely the τ-fixed
inversion-set inclusion, and it is non-distributive. mg-b10a was
correct; mg-ff7f's correction is wrong.

The likely source of confusion is conflating two distinct distributive
lattices that appear in the Brightwell / Hibi / Stanley literature:

1. **`J(P)` — the lattice of order ideals of `P`.** Always distributive
   (Birkhoff 1937). This is the lattice that appears in Hibi's theorem
   on order polytope vertices, and it is the lattice that mathlib
   provides as `LowerSet α` (already used in
   `OneThird/Mathlib/LinearExtension/Birkhoff.lean`).

2. **`(L(P), ≤_τ)` — linear extensions of `P` ordered by τ-inversion
   set inclusion.** *Not* a distributive lattice in general (this
   investigation; mg-b10a §3.2; standard fact about S_n weak order).
   For width-2 ("two-dimensional") posets it happens to be distributive,
   which is the special case Brightwell discusses. For general width
   (in particular width 3, the OneThird scope), it is not.

The OneThird application (drops headline + Brightwell port) involves
posets of width ≤ 3, including the discrete-3 case as a sub-instance
(any time `RelationPoset.rel = ∅` on three or more elements). So the
scope under which Hibi-1 is dispatched is precisely the scope under
which the lattice fails to be distributive.

## §4 Existing infrastructure already gives FKG-on-LE — without a
lattice on `LinearExt α`

The repo already contains a working FKG-on-LE pathway in
`lean/OneThird/Mathlib/LinearExtension/FKG.lean`. The route there is:

1. Apply `pi_fkg_uniform_correlation` on the **product distributive
   lattice** `Fin (n+1) → LowerSet α` (the ambient product of order
   ideals of α; always distributive, mathlib `fkg` applies).
2. Embed `LinearExt α ↪ Fin (n+1) → LowerSet α` via
   `initialLowerSetChain` (the saturated chain of initial ideals).
3. Use non-negativity to upper-bound the LinearExt-sum by the
   product-lattice-sum.

The result `LinearExt.fkg_uniform_initialLowerSet` (FKG.lean:452)
is exactly an FKG-on-LE statement for monotone non-negative
`F, G : LowerSet α → β` pulled back along the level-`k` projection
`L ↦ L.initialLowerSet k`. This works because **`LowerSet α` is
distributive** (it always is — Birkhoff), not because `LinearExt α`
is distributive (it isn't, in general).

mg-b10a §3.3 already noted that this product-lattice route is
*lossy* — the multiplicative factor is `|product| = (2^{|J(α)|})^{n+1}`
rather than the desired `numLinExt α`. mg-ff7f's premise was that
tightening this loss requires `tauDistribLattice (LinearExt α)`. The
present STOP confirms that route is unavailable. The
cardinality-tightening problem reverts to mg-b10a's framing: it
genuinely requires Hibi polytope chamber infrastructure (or some
equivalent), not just a `DistribLattice` instance on `LinearExt α`.

## §5 Trip-wire #2 (per polecat brief §"Trip-wires")

The polecat brief lists:

> **2. A new structural obstruction surfaces** — e.g., the
> τ-inversion lattice's Birkhoff identification requires
> `Mathlib.Order.Birkhoff` extension that doesn't exist → STOP,
> escalate. Could RED Path α.

This is the trip-wire that fires. The structural obstruction is the
non-distributivity of the τ-inversion order, not a missing Birkhoff
extension. The action prescribed is the same: STOP, escalate, do not
auto-extend.

Per `feedback_polecat_stop_runaway`: block, report, no auto-extension;
PM mails Daniel; polecat returns to mg-344a workspace.

## §6 What this means for Path α

Path α as scoped depended on the chain
`Hibi-1 → Hibi-2 → Hibi-3 → Hibi-drops → case3-port-2 →
case3-port-axiom-removal`, with Hibi-1 as the **first and most
load-bearing** ticket. Hibi-1 cannot land as scoped. Therefore:

* **Hibi-2 (FKG-on-LE primitive consuming `tauDistribLattice`)** —
  cannot be scoped/dispatched in its current form.
* **Hibi-3 (RelationPoset transport)** — same.
* **Hibi-drops (drops headline)** — same.
* **case3-port-2** — depends on Hibi-drops.
* **case3-port-axiom-removal** — depends on the entire chain.

mg-ff7f §7 verdict was **AMBER leaning GREEN**. The present finding
**RED**s the path as currently scoped. Re-scoping options (in roughly
decreasing order of attractiveness):

1. **Sub-path-α-A: rescope the FKG primitive.** Drop the
   `DistribLattice (LinearExt α)` requirement. Try to push the
   product-lattice route (existing
   `pi_fkg_uniform_correlation` plumbing) further — accept the
   `|product|` factor and see if it survives downstream. mg-b10a §3.3
   said this factor is exponentially too loose for the drops headline,
   so this likely fails too — but the failure is at a different layer
   and may admit a different mitigation (e.g., a per-level FKG with
   `numLinExt α`-sized normalization that works for level-`k` pullback
   events specifically, even without a global LE lattice).

2. **Sub-path-α-B: identify a sub-class of posets where the lattice
   IS distributive.** 2-dimensional posets (width 2 with extra
   structure) admit the τ-inversion lattice. If the OneThird
   application chain only invokes Hibi-style FKG on 2-dimensional
   sub-posets, the obstruction here may not bind.

3. **Sub-path-α-C: Hibi polytope chamber infrastructure** — what
   mg-b10a originally identified as the right route, what mg-ff7f tried
   to avoid, and what is genuinely a quarter-scale mathlib-PR
   undertaking.

4. **Path β / γ / etc.** — alternative routes that don't go through
   FKG-on-LE at all.

A re-scoping investigation is required before any further Path α
execution tickets are dispatched.

## §7 Status of this polecat session

Per the polecat brief: STOP firing means *block, report, no
auto-extension; PM mails Daniel; return to mg-344a workspace.*

Token usage: well under cap (no Lean coding attempted; investigation
only). No Lean changes made. No commits attempted. This document is
the only artefact.

Next steps for the polecat session:

1. Mail mayor with this report's link and a brief summary (next).
2. Wait for mayor instructions. Do not exit.
3. If mayor says "land the report doc and close mg-dc9d", commit
   this single-doc deliverable, push, refinery-submit, and follow the
   normal mg done flow.
4. If mayor says "stop, no merge", remain idle until terminated.

## §8 Cross-references

* mg-ff7f, scoping.md §2.5 (false claim) and §6.1 (misclassified risk).
* mg-b10a, `docs/a8-s2-cont-execution-arc/cont-4-stop-report.md` §3.2
  (correct prior identification of the obstruction).
* `OneThird/Mathlib/LinearExtension/FKG.lean` — existing
  product-lattice FKG-on-LE infrastructure that does *not* depend on
  `tauDistribLattice`.
* `feedback_polecat_stop_runaway` — applies.
* `feedback_complexity_blowup_means_wrong_path` — applies.
* `feedback_audit_bar_for_axioms` — n/a (no axioms touched).
* `feedback_announce_destination_and_eta` — applies (this report
  serves as the destination announcement).

— polecat mg-dc9d (cat-mg-dc9d), 2026-05-06.
