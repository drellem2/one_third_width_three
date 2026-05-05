# Deliverable B — Signature design + consumer cascade analysis

**EXPLORATORY ONLY — NOT a live program.**

Sub-deliverable B of `mg-fefe` (Option-C validation arc 1).
Doc-only. No Lean source changes; no signature changes; no new
axioms. Verifies that an Option-C signature can replace `hC3 :
Step8.Case3Witness.{u}` without cascading rewrites beyond the
signature itself, per `feedback_signature_regressions` and
trip-wire 4 of `feedback_complexity_blowup_means_wrong_path`.

---

## §0 — TL;DR

Three candidate signatures considered. **Candidate A (discharge
in place — no signature change)** is the recommended design and
has a uniformly **MECHANICAL** cascade across all 7 operational
consumers. Candidate B (K=2-restricted from `mg-e0b8` §4a)
triggers a **CASCADE** on `lem_layered_balanced` (full F3
recursion rewrite). Candidate C (bundled ACL + trigger +
certificate) triggers cascades in `lem_layered_balanced` *and*
the bipartite dispatch chain.

**Verdict:** the operational-load-bearing universal scope of
`Case3Witness.{u}` (mg-e0b8 §3a) is best **preserved** as a
universal `def : Prop` and **discharged in place** by an
in-tree theorem composing K=1 (inline) / K=2 (Option-C: ACL +
F1-trigger + Bool certificate) / K ≥ 3 (F3 step + existing
axiom + existing certificate). This minimises signature cascade
to zero while absorbing the K-dispatch into the discharge proof.
The cascade lives **inside** the discharge proof, not in the
consumer chain.

This is the **mg-e0b8 audit's recommendation in disguise**: the
universal-quantifier reading is purely the F3-recursion proxy it
is documented to be (audit §5b), so we keep it and prove it.
Trip-wire 4 (CASCADE rewrites in 3+ modules from a signature
change) does **not** fire because the signature does not change.

---

## §1 — Inputs and constraints

### Operational consumer inventory (from `mg-e0b8` §2 — re-confirmed)

| Site | File:line | Role | K invoked at |
|---|---|---|---|
| C1. `lem_layered_balanced` (K ≥ 2 branch) | `LayeredBalanced.lean:548` | **Sole `exact hC3` site** | `2 ≤ L.K` (any K ≥ 2 the input carries) |
| C2. `lem_layered_balanced_subtype` | `LayeredBalanced.lean:602` | Threads to recursive `lem_layered_balanced`. | inherits |
| C3. `layered_implies_balanced` | `LayeredBalanced.lean:719` | One-line wrapper. | inherits |
| C4. `mainTheoremInputsOf` | `MainAssembly.lean:238-247` | Threads into `caseC` and `decompReductionOrConclude`. | inherits |
| C5. `width3_one_third_two_thirds_assembled` | `MainAssembly.lean:320-339` | Threads through `mainAssembly`. | inherits |
| C6. `width3_one_third_two_thirds_via_step8` | `MainAssembly.lean:352-357` | Re-export. | inherits |
| C7. `width3_one_third_two_thirds` | `MainTheorem.lean:52-57` | **Headline.** | inherits |

Site C1 is the only **applies** site; sites C2–C7 are pure
**threading** sites (they pass `hC3` along without consuming it).

### Adjacent in-tree primitives that interact with `hC3`

* `Case3Witness.{u}` — outer, `LayeredBalanced.lean:438`. Universal
  `Prop`; the symbol replaced/discharged.
* `InSitu.Case3Witness L` — inner negation predicate,
  `Case3Dispatch.lean:181`. **Distinct symbol** (parametrised by
  `L`, encodes "neither Case 1 nor Case 2"); consumed by the
  axiom below. **Out of scope** for this deliverable's signature
  change (the inner symbol is not `hC3` and is not visible at
  the headline).
* `case3Witness_hasBalancedPair_outOfScope` axiom —
  `Case3Residual.lean:208`. Consumes `InSitu.Case3Witness L`;
  closes K ≥ 3 out-of-scope leaves. Stays as-is.
* `case3_certificate` — `Case3Enum/Certificate.lean:57`. K=3
  Bool certificate; stays as-is.
* `bipartite_balanced_enum_general` —
  `BipartiteEnumGeneral.lean:210`. K=2 three-way dispatch;
  consumes `Case2FKGSubClaim`. Stays as-is for the F1-inactive
  regime; the F1-active K=2 strict residual remains open
  independently (`mg-b666` Track 1).

### Mathematical content to preserve

Per `feedback_signature_regressions`, any new signature must
preserve `hC3`'s mathematical content:

> **`hC3` content.** For every K=2/3/etc layered width-3
> non-chain `β` with `|β| ≥ 2`, there exists a balanced pair
> in `β`.

Option-C's discharge route per the ticket and `mg-344a`
(§Update 2026-05-05T~12:30Z):

> **Replace hC3 with: ACL lemma + class catalog + residual
> certificate.**

The "ACL lemma" is the alternating-cancellation invariant
(`mg-acc8`); "class catalog" is mg-e112 §A's 40-class
enumeration; "residual certificate" is a K=2 Bool certificate
analogous to `case3_certificate` over the 40-class catalog
(~300-500 LoC per `path-c-cleanup-roadmap.md` §6b). Combined
with Deliverable A (F1-inactive ⇒ N-poset-core ⇒ structural
witness) and the existing K ≥ 3 axiom, this discharges the
universal `Case3Witness.{u}` content.

---

## §2 — Three candidate signatures

### Candidate A — Discharge in place (no signature change)

```lean
-- Signature unchanged: keep `Case3Witness.{u}` as a `def : Prop`.
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    HasBalancedPair β

-- New: prove it as a theorem in tree.
theorem Case3Witness_proof : Case3Witness.{u} := by
  intro β _ _ _ LB hW3 hNC h2
  -- K-dispatch on `LB.K`:
  -- (K=1) — single antichain ≤ 3, dispatch via `bipartite_balanced_enum`.
  -- (K=2) — Option-C: ACL invariant + F1 trigger
  --         (Deliverable A: F1-inactive ⇒ N-poset-core ⇒
  --         compoundSwap diagonal swap, mg-c0c7) + Bool
  --         certificate over the 40-class catalog (mg-e112 §A,
  --         ~300-500 LoC, native_decide).
  -- (K ≥ 3) — F3 step + reducible-step lift + leaves:
  --     • InCase3Scope:  case3_certificate (K=3 Bool cert)
  --     • ¬ InCase3Scope: case3Witness_hasBalancedPair_outOfScope
  --                      (existing axiom)
  sorry  -- discharge work; outside Deliverable B's scope.

-- Headline becomes hypothesis-free: existing call-sites lose one
-- argument.
theorem width3_one_third_two_thirds [...] :=
  width3_one_third_two_thirds_via_step8 ... Case3Witness_proof ...
```

**Mathematical content.** Preserves `hC3`'s content exactly: the
universal Prop is unchanged, only its status (hypothesis ↔
discharged theorem) flips. ACL + N-core + Bool certificate are
**inside** the proof, supplied to the K=2 branch of the
discharge case-split, with K=1 and K ≥ 3 routed to existing
infrastructure.

**Cascade per consumer.**

| Site | Tag | Rewrite |
|---|---|---|
| C1. `lem_layered_balanced` | **MECHANICAL** | Body unchanged: still `exact hC3 α L hW3 hNotChain' h2`. The `hC3` hypothesis stays in the signature; the *theorem application* at C7 stops threading it. |
| C2. `lem_layered_balanced_subtype` | **MECHANICAL** | Same: body unchanged; signature unchanged; theorem application stops threading. |
| C3. `layered_implies_balanced` | **MECHANICAL** | Same. |
| C4. `mainTheoremInputsOf` | **MECHANICAL** | Stops threading `hC3` to `caseC` and `decompReductionOrConclude`; signature drops the `hC3` parameter. |
| C5. `width3_one_third_two_thirds_assembled` | **MECHANICAL** | Drops `hC3` parameter; supplies `Case3Witness_proof` instead inside the body. |
| C6. `width3_one_third_two_thirds_via_step8` | **MECHANICAL** | Same. |
| C7. `width3_one_third_two_thirds` (headline) | **MECHANICAL** | Drops `hC3` parameter from the public signature; the headline becomes hypothesis-free. |

**Optional simplification.** C1–C3 (the `lem_layered_balanced`
chain) can keep `hC3 : Case3Witness.{u}` as an *internal*
hypothesis indefinitely — i.e., they remain hypothesis-shaped.
The cascade then concentrates at C5–C7, which gain
`Case3Witness_proof` as a one-liner application. Either way,
no body changes are needed at C1–C3.

**Cascade verdict for A:** **7 × MECHANICAL, 0 × MODERATE,
0 × CASCADE**. Trip-wire 4 does not fire.

### Candidate B — `K2RestrictedCase3Witness` (audit §4a sketch)

```lean
def K2RestrictedCase3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    LB.K = 2 →                           -- new constraint
    HasBalancedPair β
```

**Mathematical content.** **Strictly weaker** than the universal
`Case3Witness.{u}` (it only covers K=2). To preserve `hC3`'s
content we must additionally close K ≥ 3 elsewhere — i.e., make
the F3 recursion explicit in `lem_layered_balanced` so that K ≥
3 leaves are dispatched through `case3_certificate` /
`case3Witness_hasBalancedPair_outOfScope` directly, and the
`K2RestrictedCase3Witness` hypothesis sees only the K = 2 sub-poset
visited at the recursion's K = 2 leaves.

Per `mg-e0b8` §3a, **`lem_layered_balanced` does not currently
do F3 recursion**: the K ≥ 2 branch jumps directly to `hC3` on
the input poset. So Candidate B requires a full F3-recursive
rewrite of `lem_layered_balanced` (~150–250 LoC per
`mg-072c` / `mg-0fa0` planned scope; the full bundle is ~480–700
LoC per `mg-e0b8` §5c).

**Cascade per consumer.**

| Site | Tag | Rewrite |
|---|---|---|
| C1. `lem_layered_balanced` | **CASCADE** | The K ≥ 2 branch must be replaced by F3 strong-induction on `\|α\|` with reducible-step descent + leaf dispatch (K=1 / K=2 → K2-restricted hyp / K ≥ 3 → existing axiom + cert). ~150–250 LoC. |
| C2. `lem_layered_balanced_subtype` | **MODERATE** | Receives `K2RestrictedCase3Witness` instead of `Case3Witness` and threads through. Signature update + proof of subtype's `LB.K = 2` precondition (or re-ranging if the recursive call descends into a sub-poset whose K differs). |
| C3. `layered_implies_balanced` | **MECHANICAL** | Wrapper — adopts new hypothesis. |
| C4. `mainTheoremInputsOf` | **MODERATE** | Threading shape changes; `caseC` and `decompReductionOrConclude` need `LB.K = 2` to be supplied (or to abandon the K=2-only assumption — which forces re-ranging). |
| C5. `width3_one_third_two_thirds_assembled` | **MODERATE** | Same threading concern. |
| C6. `width3_one_third_two_thirds_via_step8` | **MECHANICAL** | Re-export. |
| C7. `width3_one_third_two_thirds` (headline) | **MODERATE** | The public hypothesis weakens. Existing callers (none in repo, but external) would need to supply the K=2-restricted variant. |

**Cascade verdict for B:** **1 × CASCADE, 4 × MODERATE,
2 × MECHANICAL**. **Trip-wire 4 fires** at C1 (a single-module
CASCADE; per `feedback_complexity_blowup_means_wrong_path`,
trip-wire 4 fires at "3+ modules" but this is a single module
that requires substantive new infrastructure — borderline).
The MODERATE count (4) is concerning but not fatal.

The audit (mg-e0b8 §4b) already concluded that this candidate is
**sound but not a discharge** — it remains a hypothesis-shaped
Prop until the case-2-strict residual closes (Track 1 obstruction
or A8-S2-cont infrastructure). So Candidate B's signature
change is real and the cascade is real.

### Candidate C — Bundled ACL + structural-trigger signature

```lean
structure Step8OptionCBundle.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β) : Prop where
  /-- ACL invariant (sign-imbalance bound). -/
  acl : ACLBound LB
  /-- F1-inactive ⇒ N-poset-core trigger (Deliverable A). -/
  f1_inactive_trigger :
    F1Inactive LB → NPosetCore β
  /-- Bool certificate over the 40-class K=2 catalog. -/
  k2_cert : K2Case3CertCatalog LB
  /-- F1-active dispatch (within-band ⪯-pair → ...). -/
  f1_active_trigger : F1Active LB → HasBalancedPair β
  /-- K ≥ 3 axiom thread + reducible lift composition.  -/
  k3_lift : 3 ≤ LB.K → HasBalancedPair β
```

**Mathematical content.** Preserves `hC3`'s content: every
balanced-pair conclusion that `hC3` produces is reproducible
from this bundle via case-dispatch on F1-active vs F1-inactive
and reducible vs irreducible. But the bundle bakes **dispatch
decisions** into the signature itself — which is an
anti-pattern per `feedback_signature_regressions` and contrary
to mg-e112 §C's "decoupled primitive" principle.

**Cascade per consumer.**

| Site | Tag | Rewrite |
|---|---|---|
| C1. `lem_layered_balanced` | **CASCADE** | Same F3 rewrite as Candidate B, **plus** dispatch logic to invoke the bundle's fields per F1 status. The body has to call `bundle.f1_inactive_trigger` or `bundle.f1_active_trigger` and compose with the K=2 certificate. ~250–400 LoC. |
| C2. `lem_layered_balanced_subtype` | **CASCADE** | Bundle does not naturally carry through to sub-poset (each field is L-parametrised). Restricting the bundle to `D.Mid` requires bundle-level restrict machinery (~50–100 LoC of new infra). |
| C3. `layered_implies_balanced` | **MODERATE** | Wrapper adopts new bundle shape. |
| C4. `mainTheoremInputsOf` | **CASCADE** | Threading bundle through the assembled main theorem requires bundle-restriction at each `decompReductionOrConclude` recursion step — same restrict-machinery dependency as C2. |
| C5. `width3_one_third_two_thirds_assembled` | **MODERATE** | Bundle propagates. |
| C6. `width3_one_third_two_thirds_via_step8` | **MODERATE** | Re-export. |
| C7. `width3_one_third_two_thirds` (headline) | **MODERATE** | Public signature changes shape. |

**Cascade verdict for C:** **3 × CASCADE, 4 × MODERATE,
0 × MECHANICAL**. **Trip-wire 4 fires** decisively (3 modules
with substantive cascade rewrites). Candidate C is **dead** by
the trip-wire: the bundle shape is operationally too tightly
coupled to dispatch to admit a clean restrict.

Additionally: bundling F1-active into the signature **regresses**
on `feedback_signature_regressions` because it bakes the
case-dispatch into the bundle rather than letting the bundle
cover the universal balanced-pair conclusion uniformly.

---

## §3 — Verdict — Candidate A wins

### §3a. Cascade summary

| Candidate | × MECHANICAL | × MODERATE | × CASCADE | Trip-wire 4? |
|---|---|---|---|---|
| **A — Discharge in place** | **7** | 0 | 0 | **NO** |
| B — K2RestrictedCase3Witness | 2 | 4 | 1 | borderline |
| C — Bundled | 0 | 4 | 3 | **YES (fires)** |

### §3b. Mathematical content preservation

| Candidate | Universal `Case3Witness.{u}` content preserved? |
|---|---|
| **A — Discharge in place** | **YES** — signature unchanged. |
| B — K2RestrictedCase3Witness | NO — restricts to K=2, requires K ≥ 3 closure elsewhere. |
| C — Bundled | YES if bundle's fields jointly dispatch the universal; but bakes dispatch into signature (anti-pattern). |

### §3c. Operational soundness

**Candidate A is the audit's recommendation in disguise.** The
audit (`mg-e0b8` §5b) reads:

> The universal-quantifier reading is **not load-bearing in
> principle** — the universal scope of `Case3Witness.{u}` is a
> modelling choice that absorbs the F3 recursion into the
> hypothesis. A signature restatement to a non-universal shape
> is mathematically possible (and mechanically natural after a
> rewrite of `lem_layered_balanced`), provided the K ≥ 3 and
> K = 2 case-2-strict gaps are closed by other means.

Candidate A respects the universal scope (preserves it) and
**absorbs the K-dispatch back into the discharge proof** rather
than into the signature. This means:

1. **C1 — C3 stay structurally clean.** They keep treating `hC3`
   as a hypothesis; only their callers change (drop the parameter).
2. **K ≥ 3 leaves close via existing infrastructure** (no new
   axioms beyond `case3Witness_hasBalancedPair_outOfScope`,
   `case3_certificate`, `Lean.ofReduceBool`).
3. **K = 2 closure** is the substantive new work (Option-C: ACL
   invariant + F1-trigger + Bool certificate over 40 classes),
   landing inside the `Case3Witness_proof` body.
4. **Headline becomes hypothesis-free** in C7 — the user-visible
   improvement that motivates Option-C in the first place.

### §3d. Why Candidate A is robust to the K=2 case-2-strict residual

The audit emphasizes that even within K=2, the case-2-strict
sub-regime (within-band ⪯-pair, `mg-b666`) is **open** with
`Case2FKGSubClaim` provably false. Candidate A handles this by
**baking the case-2-strict closure into the K=2 branch of
`Case3Witness_proof`**, via:

* The Bool certificate over the 40-class catalog (`mg-e112` §A)
  closes case-2-strict structurally — direct enumeration.
* This bypasses the FKG sub-claim entirely (bypass option (α) per
  `path-c-cleanup-roadmap.md` §6b).
* `bipartite_balanced_enum_general` stays as-is in the F1-inactive
  / N-core regime (where it works); the F1-active regime routes
  through the Bool certificate inside `Case3Witness_proof`.

So Candidate A absorbs the existing Track 1 obstruction into the
Bool-certificate work — which is exactly the scope the ticket's
Deliverable C is sizing.

### §3e. Verdict tag

**GREEN on the signature design.** Candidate A has cascade
0 × CASCADE, 7 × MECHANICAL across all consumers. The
mathematical content of `hC3` is preserved exactly, and Option-C's
ACL + F1 + Bool certificate content lands inside the discharge
proof rather than altering the signature.

The execution arc (Daniel-confirmed) builds:

1. **K=2 Option-C closure** (ACL + F1-trigger via Deliverable A
   + 40-class Bool certificate) — ~300–500 LoC.
2. **F3 step proof** (`hStep` for
   `hasBalancedPair_of_layered_strongInduction_width3`) — ~150–
   250 LoC, sized in Deliverable C.
3. **Compose into `Case3Witness_proof`** — ~30–50 LoC.
4. **Drop `hC3` parameter** at C5–C7 — ~10–20 LoC.

Total ~480–700 LoC, matching the `mg-e0b8` §5c bundle estimate.

---

## §4 — Trip-wire checks

### 4a. Trip-wire 4 — signature cascade unbounded

**Candidate A:** signature unchanged ⇒ no signature cascade.
Trip-wire 4 does **not** fire.

**Candidate B:** 1 × CASCADE on `lem_layered_balanced` + 4 ×
MODERATE. Borderline; the per-module module count is below the
"3+ modules with substantive cascade" trip-wire, but the single
CASCADE is a substantial body rewrite. **Marginal.**

**Candidate C:** 3 × CASCADE + 4 × MODERATE. Trip-wire 4 fires.
**Dead.**

### 4b. `feedback_signature_regressions` — content preservation

Candidate A: PASS (signature unchanged ⇒ content unchanged).
Candidate B: PARTIAL (content weakens to K=2; K ≥ 3 closed elsewhere
under explicit hypothesis).
Candidate C: PASS-with-caveat (content preserved, but bundle bakes
dispatch into signature — anti-pattern).

### 4c. `feedback_audit_bar_for_axioms`

No new axioms in any candidate. Existing axioms
(`case3Witness_hasBalancedPair_outOfScope`, `Lean.ofReduceBool`
via `native_decide`, `brightwell_sharp_centred`) are reused
without modification.

### 4d. `feedback_complexity_blowup_means_wrong_path` —
operational-load-bearing finding from mg-e0b8 is bounded?

**Candidate A:** YES. The mg-e0b8 finding (universal-quantifier
reading load-bearing because of `K = |α|` invocation at C1) is
**preserved**, not circumvented. Candidate A doesn't try to
push K = 2 restriction up to the call-site; it leaves the
universal scope alone and discharges it.

**Candidate B and C:** trip-wire reads inconclusive because
they require an F3 rewrite to make the operational K = 2 ask
match the signature's K = 2 restriction. The "operational
load-bearing" finding is real, and Candidates B/C address it by
adding F3 infrastructure — which **is** the cascade.

### 4e. `feedback_n_poset_is_not_ordinal_sum`

Candidate A's K=2 branch invokes Deliverable A's
F1-inactive ⇒ N-poset-core trigger. The N-poset extraction
preserves the N-poset's structural identity (induced sub-poset,
not ordinal-sum collapse). PASS.

---

## §5 — Cross-references

* `docs/case3witness-operational-audit.md` (`mg-e0b8`)
  - §2 — call-site inventory (consumer list).
  - §3 — operational K-range (load-bearing finding).
  - §4a — `K2RestrictedCase3Witness` sketch (Candidate B's basis).
  - §4b — why audit §4a does not suffice alone.
  - §5c — bundle scope estimate (~480–700 LoC).
* `docs/proof-approaches-catalog-1/in-tree-primitive-inventory.md`
  (`mg-e112` §C)
  - §4 — `Case3Witness` def vs `InSitu.Case3Witness L` distinction.
  - §9 — `case3_certificate` machinery (reusable for K=2 cert).
  - §10 — `case3Witness_hasBalancedPair_outOfScope` axiom (K ≥ 3
    leaves).
* `docs/option-c-validation-arc-1/f1-inactive-n-core-proof.md`
  (Deliverable A) — F1-inactive ⇒ N-poset-core trigger that
  Candidate A's K=2 branch consumes.
* `docs/path-c-cleanup-roadmap.md`
  - §6b — K=2 finite-enumeration alternative (~300-500 LoC).
  - §6c — discharge-route documentation.
* `lean/OneThird/Step8/LayeredBalanced.lean:438-444` —
  `Case3Witness.{u}` def.
* `lean/OneThird/Step8/LayeredBalanced.lean:548` — sole `exact
  hC3` site.
* `lean/OneThird/Step8/LayerOrdinal.lean:472` — F3 framework
  (consumed by Candidate A's K ≥ 3 branch).
* `lean/OneThird/Step8/Case3Residual.lean:208` — K ≥ 3
  out-of-scope axiom (consumed by Candidate A's K ≥ 3 branch).
* `lean/OneThird/Step8/Case3Enum/Certificate.lean:57` —
  `case3_certificate` (K=3 only; consumed by Candidate A's
  K ≥ 3 / `InCase3Scope` branch).
* `feedback_signature_regressions`, `feedback_audit_bar_for_axioms`,
  `feedback_complexity_blowup_means_wrong_path` — all PASS for
  Candidate A.

---

## §6 — Provenance

Sub-deliverable B of `mg-fefe`. Filed 2026-05-05 by polecat.
Origin: Daniel directive 2026-05-05T~15:24Z + `mg-344a` Update
2026-05-05T~12:30Z. The signature design is doc-only and
**presupposes** the discharge-proof work in the execution arc;
this deliverable verifies only that the signature change is
**bounded** (Candidate A: zero cascade), not that the discharge
proof is feasible (Deliverable C scopes the K ≥ 3 portion;
Daniel's existing arc 4.0 §8.2 + `path-c-cleanup-roadmap.md`
§6b sized the K = 2 portion).
