# Deliverable C — K ≥ 3 lift plan

**EXPLORATORY ONLY — NOT a live program.**

Sub-deliverable C of `mg-fefe` (Option-C validation arc 1).
Doc-only. No Lean source changes; no signature changes; no new
axioms. Plans the K ≥ 3 portion of the Option-C bundle: F3 step
proof + leaf-closure inventory + LoC estimate.

---

## §0 — TL;DR

**Verdict: AMBER on Deliverable C.**

The K ≥ 3 lift plan is **bounded** for the operational headline
path (K = |α|, w = |α| + 1 from `layeredFromBridges`), where the
F5 C2 leaf-closer's caps `K ≤ 2w + 2` and `|α| ≤ 6w + 6` always
hold. At the F3 step's leaves under headline inputs, the existing
in-tree machinery — `bipartite_balanced_enum` (K=1),
Option-C K=2 closure (Deliverables A + Bool cert),
`case3_certificate` (K ∈ InCase3Scope), and
`case3Witness_hasBalancedPair_outOfScope` (K ≥ 3 outside scope)
— covers every leaf the F3 recursion bottoms at.

**Coverage gap at K > 2w + 2 leaves** (raised but not strictly a
trip-wire 2 fire): the universal `Case3Witness.{u}` def
(`LayeredBalanced.lean:438-444`) ranges over **all** layered
inputs `(β, LB)`, not just headline-path-shape ones. Width-3
layered irreducible posets with K > 2w + 2 do **exist**
structurally (e.g., a K = 5, w = 1, |α| = 5 "zigzag" of singleton
bands; see §3 for the explicit witness), and no in-tree
leaf-closer covers them. Discharging the universal therefore
requires either (i) a small **signature tightening** of
`Case3Witness.{u}` to add the F5 C2 caps as hypotheses
(adjusting Candidate A from Deliverable B to **Candidate A'**),
or (ii) new leaf-closer infrastructure for K > 2w + 2 leaves
(out of PM scope and arguably the F4-b paper-tier escalation
that Deliverable B avoids).

Recommendation: pair the execution arc with **Candidate A'** —
Candidate A's discharge-in-place plus a one-line tightening that
adds `LB.K ≤ 2 * LB.w + 2 ∧ Fintype.card β ≤ 6 * LB.w + 6` to
`Case3Witness.{u}`. The tightening is mechanical at the operational
consumer (`LayeredBalanced.lean:548`): the headline path supplies
both inequalities trivially since K = |α| and w = |α| + 1. No new
primitives or axioms are needed.

**No new project axioms** are introduced. No new structural facts
F6/F7 are surfaced (the "K > 2w + 2 width-3 layered irreducible
poset exists" observation is a **coverage gap of the existing
leaf-closer's hypothesis profile**, not a new combinatorial fact;
the underlying posets are width-2 by construction and balanced
by direct LE enumeration).

---

## §1 — Setup: F3 strong-induction descent

The F3 framework `hasBalancedPair_of_layered_strongInduction_width3`
(`lean/OneThird/Step8/LayerOrdinal.lean:472`, `mg-a735`) supplies
the strong-induction skeleton:

```lean
theorem hasBalancedPair_of_layered_strongInduction_width3.{u}
    (hStep : ∀ (α : Type u) [...] (L : LayeredDecomposition α),
        HasWidthAtMost α 3 →
        2 ≤ Fintype.card α →
        ¬ OneThird.IsChainPoset α →
        (∀ (β : Type u) [...] (LB : LayeredDecomposition β),
          Fintype.card β < Fintype.card α →
          HasWidthAtMost β 3 → 2 ≤ Fintype.card β →
          ¬ OneThird.IsChainPoset β →
          OneThird.HasBalancedPair β) →   -- IH on smaller |β|
        OneThird.HasBalancedPair α) :
    ∀ (α : Type u) [...] (L : LayeredDecomposition α),
      HasWidthAtMost α 3 → 2 ≤ Fintype.card α →
      ¬ OneThird.IsChainPoset α →
      OneThird.HasBalancedPair α
```

To prove `Case3Witness.{u}` (or its tightened variant in §6) as a
theorem, we supply `hStep` such that, given α with width 3,
|α| ≥ 2, ¬ chain, and an IH on smaller posets, we produce
`HasBalancedPair α`.

**Descent strategy** (per `mg-e0b8` §3b, also pre-discussed in
`mg-072c` / `mg-0fa0`):

* Try `LayerOrdinalReducible L k` for some `k ∈ {1, ..., L.K - 1}`.
  If found: `OrdinalDecompOfReducible L k hRed` gives D :
  `OrdinalDecomp α`. Apply IH to D.Lower and D.Upper (both
  strictly smaller in |·|). Lift via `OrdinalDecomp.
  hasBalancedPair_lift_lower` or `_upper` (`mg-7f06`,
  `Mathlib/LinearExtension/Subtype.lean:1227, 1268`).
* Otherwise (`LayerOrdinalIrreducible L`): close at the leaf
  using K-dispatch (§2 below).

---

## §2 — Leaf catalogue (irreducible)

For an irreducible leaf `(α, L)` with `width 3`, `|α| ≥ 2`,
`¬ IsChainPoset α`, dispatch on `L.K`:

### §2.a — K = 1

Single antichain `L_1` of size ≤ 3 (by L1 `band_size`). Every
pair is incomparable; `Pr_α[x < y] = 1/2`. Closer:
`bipartite_balanced_enum` (`BipartiteEnum.lean:288`) with
`A := Finset.univ`, `B := ∅`. Already inline at
`LayeredBalanced.lean:498-518`. **Mechanical** in `hStep`.

### §2.b — K = 2

The K=2 obstruction family of mg-e112 §A (40 classes). Closed
by Option-C K=2 closure:

* **F1-active sub-regime** (32 classes per mg-e112 §A §4 corrected
  count; specifically: 2 classes at |α|=3, ~5 at |α|=4, ~6 at
  |α|=5, ~10 at |α|=6, plus the (3,2) duals — re-derived
  precisely from the matrices in mg-e112 §A §2): closed by the
  K=2 Bool certificate over the 40-class catalog (~300-500 LoC,
  per `path-c-cleanup-roadmap.md` §6b). The certificate uses
  `native_decide` against `case3_certificate`'s Bool kit
  (`Case3Enum.lean`, `BoundedIrreducibleBalanced.lean:872+`).
* **F1-inactive sub-regime** (8 classes per mg-e112 §A §4
  corrected count; subset of the 40 catalog): for `|α| ∈
  {4, 5, 6}` (6 classes), closed via Deliverable A's
  F1-inactive ⇒ N-poset-core trigger + the existing
  `compoundSwap` / `matching_exists_of_K2_irreducible_noWithinBand`
  machinery (`mg-c0c7`, `CompoundMatching.lean:663`). For the
  degenerate |α|=3 antichain F1-inactive sub-cases (`K2-N3-AC`
  and `K2-N3-AC'`), closed by `bipartite_balanced_enum` directly
  (no edges; trivially balanced).

The K=2 sub-step is the substantive new work in the execution
arc; ~300-500 LoC scoped here as **moderate**.

### §2.c — K ≥ 3, within F5 C2 caps (`K ≤ 2w + 2 ∧ |α| ≤ 6w + 6`)

Sub-dispatch on `InCase3Scope L.w (Fintype.card α) L.K`:

* **InCase3Scope** (`K = 3 ∧ 1 ≤ w ≤ 4 ∧ |α| ≤ 9 (w=1) or 7
  (w≥2)`): closed by `case3_certificate`
  (`Case3Enum/Certificate.lean:57`, `mg-fd88`) via the
  `case3_balanced_w{1,2,3,4}` Bool certificate. Already lifted
  to Prop via `bounded_irreducible_balanced_hybrid`'s `hCert`
  branch (`BoundedIrreducibleBalanced.lean:1660`). Consumes
  `Lean.ofReduceBool` axiom (already in tree).
* **¬ InCase3Scope** (still within K ≤ 2w + 2 ∧ |α| ≤ 6w + 6,
  but outside the K=3 cert scope): closed by
  `case3Witness_hasBalancedPair_outOfScope`
  (`Case3Residual.lean:208`, `mg-b846`). Consumes the **inner**
  `Case3Witness L` (Case3Dispatch.lean:181 — the negation of
  Case 1 ambient match and Case 2 within-band ⪯-pair). The
  inner `Case3Witness L` is structurally derivable in this
  branch by classical excluded middle on the dispatch
  predicates.

Both sub-cases are dispatched by `bounded_irreducible_balanced_hybrid`'s
existing `(hCert, hStruct)` interface, with `hCert` and `hStruct`
each delivered from the appropriate in-tree primitive. **Mechanical
to wire** in `hStep` once the case-split structure is laid out.

### §2.d — K ≥ 3, outside F5 C2 caps (`K > 2w + 2` OR `|α| > 6w + 6`)

**Coverage gap.** No in-tree leaf-closer covers this range:

* `bounded_irreducible_balanced_hybrid` requires `K ≤ 2w + 2 ∧
  |α| ≤ 6w + 6` (`BoundedIrreducibleBalanced.lean:1660`).
* `case3_certificate` requires `K = 3 ∧ 1 ≤ w ≤ 4 ∧ |α| ≤ 9`.
* `case3Witness_hasBalancedPair_outOfScope` requires
  `L.K ≤ 2 * L.w + 2 ∧ Fintype.card α ≤ 6 * L.w + 6`
  (`Case3Residual.lean:208`).

Width-3 layered irreducible posets with `K > 2w + 2` and/or
`|α| > 6w + 6` exist (§3 below). But:

* **At the operational headline path**, `layeredFromBridges`
  forces `K = |α|` and `w = |α| + 1` (`LayeredBridges.lean:248`),
  so `2w + 2 = 2|α| + 4 ≥ |α| = K` and `6w + 6 = 6|α| + 12 ≥
  |α| = |α|` — both caps hold automatically.
* **At F3-descent sub-posets**: the recursion calls
  `lem_layered_balanced_subtype` (`LayeredBalanced.lean:602`)
  which uses `L.restrict D.Mid` (preserving `L.w`). The
  restricted K is bounded by the cut size, and the sub-poset's
  |·| is strictly smaller. Since w stays the same and K shrinks,
  the caps remain satisfied if they held on the parent.

So **the coverage gap is vacuous at every input the operational
headline path can produce**. But the universal `Case3Witness.{u}`
def is over arbitrary `(β, LB)` — the gap is real at the def-level.

The mitigation strategy is documented in §6 (signature tightening,
Candidate A' adjustment to Deliverable B's Candidate A).

---

## §3 — Witness for the K > 2w + 2 coverage gap

For Deliverable C's "verify each leaf case is closed by existing
in-tree machinery" task, we exhibit a width-3 layered irreducible
input outside the F5 C2 caps:

### The K = 5, w = 1, |α| = 5 zigzag

Take α = {1, 2, 3, 4, 5} with `band i = i` (singleton bands;
`band_size = 1 ≤ 3` ✓; `band_antichain` vacuous on singletons).
Set `L.w = 1`. Then (L2-forced) gives:

* `band x + 1 < band y → x < y`, i.e., `band x < band y - 1 →
  x < y`.
* So 1 < 3, 4, 5 (forced); 2 < 4, 5 (forced); 3 < 5 (forced).
* The remaining cross-band pairs (1, 2), (2, 3), (3, 4), (4, 5)
  are **not forced**; we set them all incomparable to make the
  poset irreducible.

Verify the layered axioms:

* L1 `band_size`: each band has 1 ≤ 3. ✓
* L1b `band_antichain`: vacuous (singleton bands). ✓
* L2-forced: as above, all forced comparabilities are present. ✓
* L2-upward `cross_band_lt_upward`: `x < y → band x ≤ band y` —
  no comparabilities reverse direction. ✓

Verify width:

* The set {2, 3} is an antichain (incomparable). {3, 4}, {4, 5},
  {1, 2} likewise. No 3-element antichain exists (any 3 distinct
  elements include two non-adjacent bands, which are forced
  comparable). So **width = 2 ≤ 3** ✓.

Verify irreducibility at every cut:

* k = 1: (1, 2) incomparable, band 1 ≤ 1, band 2 ≥ 2. ✓ Not
  reducible.
* k = 2: (2, 3) incomparable. ✓
* k = 3: (3, 4) incomparable. ✓
* k = 4: (4, 5) incomparable. ✓

So **`(α, L)` is layered, width-3 (in fact width-2), irreducible,
non-chain, with K = 5 and w = 1**. The F5 C2 caps fail:
`K = 5 > 2w + 2 = 4`.

This poset is **not closeable by any existing in-tree leaf-closer**
(per the §2.d enumeration). Its `HasBalancedPair α` conclusion is
true (verified by direct LE enumeration: the pair (4, 5) has
Pr = 5/8 ∈ [1/3, 2/3]; |L(α)| = 8 by enumeration), but proving
it in Lean requires either a width-2 / width-3 paper-level
balanced-pair theorem (paper-tier infrastructure) or per-class
treatment.

The witness is not exotic — it's a generic singleton-band layered
poset at small w. Its existence shows the coverage gap is not a
trip-wire-2 "new structural fact" but a **scope mismatch**
between the universal `Case3Witness.{u}` def and the operational
caps of in-tree leaf-closers.

---

## §4 — `hStep` shape and LoC estimate

### §4.a — Skeleton

Sketch of `hStep` for `Case3Witness_proof` (or its tightened
Candidate A' variant):

```lean
intro α _ _ _ L hW3 h2 hNotChain ih
-- Try reducible cut.
by_cases hRed : ∃ k, 1 ≤ k ∧ k < L.K ∧ LayerOrdinalReducible L k
case pos =>
  obtain ⟨k, hk1, hkK, hRedk⟩ := hRed
  let D := OrdinalDecompOfReducible L k hRedk
  -- Try IH on D.Lower; if it has an incomparable pair, use it.
  -- Else try D.Upper; one of them must (else α is a chain,
  -- contradiction with hNotChain).
  by_cases hLowChain : OneThird.IsChainPoset (D.Lower : Finset α)
  case neg =>
    have hLow := ih (↥D.Lower) ... (by omega : |D.Lower| < |α|) ...
    exact OrdinalDecomp.hasBalancedPair_lift_lower D hLow
  case pos =>
    have hUpNotChain : ¬ OneThird.IsChainPoset (D.Upper : Finset α) :=
      ...  -- from hNotChain + hLowChain
    have hUp := ih (↥D.Upper) ... ...
    exact OrdinalDecomp.hasBalancedPair_lift_upper D hUp
case neg =>
  -- Irreducible leaf.  K-dispatch.
  push_neg at hRed
  have hIrr : LayerOrdinalIrreducible L := ...  -- from hRed
  rcases Nat.lt_or_ge L.K 2 with hK1 | hKge2
  case inl =>
    -- K = 1: single antichain.
    exact bipartite_balanced_enum_K1 ...
  case inr =>
    rcases Nat.lt_or_ge L.K 3 with hK2 | hKge3
    case inl =>
      -- K = 2: Option-C closure.
      exact option_c_K2_closure L hW3 hIrr h2 hNotChain hKeq2 ...
      -- (Combines Deliverable A's F1 trigger + 40-class Bool cert.)
    case inr =>
      -- K ≥ 3.  Apply caps (assumed via def tightening — see §6).
      -- Sub-dispatch on InCase3Scope.
      have hCard : Fintype.card α ≤ 6 * L.w + 6 := hCardCap
      have hDepth : L.K ≤ 2 * L.w + 2 := hDepthCap
      have hw : 1 ≤ L.w := ...  -- from K ≥ 3 + L2-forced
      exact bounded_irreducible_balanced_hybrid L hW3 hIrr hKge3 hw
        hCard hDepth (hCert := fun hScope =>
          case3_certificate_lifted L hW3 hIrr hKge3 hw hScope ...)
        (hStruct := fun hScope =>
          case3Witness_hasBalancedPair_outOfScope L hW3 hIrr
            hKge3 hw hCard hDepth hScope (innerC3OfDispatch L hIrr))
```

The two named pieces — `option_c_K2_closure` (~300-500 LoC,
Deliverable C does **not** scope this — it's the K=2 substantive
work) and `innerC3OfDispatch` (a classical excluded-middle
dispatch, ~10-20 LoC) — are the only non-mechanical sub-pieces.

### §4.b — LoC estimate (in `hStep`)

| Component | LoC | Notes |
|---|---|---|
| Reducible-cut search and dispatch | 30–50 | `by_cases` + `OrdinalDecompOfReducible` + lift. |
| Lower vs Upper IH selection | 20–30 | Chain-classification of D.Lower / D.Upper. |
| K = 1 branch | 5–10 | Re-use of `bipartite_balanced_enum`. |
| K = 2 branch (call into `option_c_K2_closure`) | 5–10 | Just an `exact` after type matching. |
| K ≥ 3 branch (`bounded_irreducible_balanced_hybrid` wiring) | 30–50 | Cap proofs + cert/struct branches. |
| `innerC3OfDispatch` helper | 10–20 | Classical em on Case 1 / Case 2 predicates. |
| Glue and book-keeping | 30–50 | Hypothesis re-folds, type ascriptions. |
| **Total `hStep`** | **130–220** | |
| K = 2 closure (separate, from §2.b) | 300–500 | The substantive new math; out of Deliverable C scope. |
| Final `Case3Witness_proof` composition | 30–50 | Composes hStep with F3 framework + Candidate A' caps wiring. |
| **Total bundle (excl. K=2 closure)** | **160–270** | |
| **Total bundle (incl. K=2 closure)** | **460–770** | |

The bundle estimate matches `mg-e0b8` §5c's **~480-700 LoC**
estimate within rounding tolerance. The hStep proof itself
(~130-220 LoC) is the central piece for K ≥ 3; the rest is
boilerplate.

### §4.c — Load-bearing pattern

The recursion descent's invariant:

> At every recursion depth, the current sub-poset `(β, LB)`
> has `LB.w` (preserved from parent), `LB.K ≤` parent's K (via
> `restrict`), `Fintype.card β <` parent's card (strictly
> smaller). The F5 C2 caps `K ≤ 2w + 2 ∧ |α| ≤ 6w + 6` hold at
> the headline-path top and are preserved by descent (since w
> stays and both K and |·| only shrink).

This invariant is the load-bearing fact that lets `bounded_
irreducible_balanced_hybrid`'s caps work uniformly across the
recursion. The Candidate A' tightening (§6) makes the invariant
**explicit at the type level** by adding the caps as
hypotheses to `Case3Witness.{u}`.

---

## §5 — Cross-reference to mg-e112 §C primitives

Per the ticket's task 4 ("if any primitive is missing for the
lift, flag explicitly"), we audit mg-e112 §C against the
needed primitives for the K ≥ 3 lift. **Result: every needed
primitive is in tree.** No new primitive is missing for the
F3 step proof at K ≥ 3 within F5 C2 caps.

| Need | mg-e112 §C primitive | File:line | Status |
|---|---|---|---|
| Reducible-cut detection | `LayerOrdinalReducible` | `LayerOrdinal.lean:88` | In tree (§C §2). |
| Reducible-cut → ordinal decomp | `OrdinalDecompOfReducible` | `LayerOrdinal.lean:108` | In tree (§C §2). |
| Lift balanced-pair from Lower | `OrdinalDecomp.hasBalancedPair_lift_lower` | `Mathlib/LinearExtension/Subtype.lean:1227` | In tree (§C §1). |
| Lift balanced-pair from Upper | `..._lift_upper` | `:1268` | In tree (§C §1). |
| K=1 antichain | `bipartite_balanced_enum` | `BipartiteEnum.lean:288` | In tree (§C §6). |
| K=2 closure (Option-C) | (NEW) Bool certificate over 40 classes | n/a | **Not in tree.** Substantive new work, ~300-500 LoC, scoped in execution arc not here. |
| K ≥ 3 in InCase3Scope | `case3_certificate` (lifted) | `Case3Enum/Certificate.lean:57` + bridges | In tree (§C §9). |
| K ≥ 3 hybrid dispatch | `bounded_irreducible_balanced_hybrid` | `BoundedIrreducibleBalanced.lean:1660` | In tree (§C — implicit in §9). |
| K ≥ 3 outside InCase3Scope | `case3Witness_hasBalancedPair_outOfScope` | `Case3Residual.lean:208` | In tree (§C §10). |
| Inner Case3Witness dispatch | `InSitu.Case3Witness L` (negation form) | `Case3Dispatch.lean:181` | In tree (§C §4). |
| F3 framework | `hasBalancedPair_of_layered_strongInduction_width3` | `LayerOrdinal.lean:472` | In tree (§C §7). |
| Width preservation under restrict | (composition of `LayeredDecomposition.restrict` + width-3 transfer in `lem_layered_balanced_subtype`) | `LayeredBalanced.lean:602+` | In tree. |
| K > 2w + 2 leaf coverage | (none) | — | **Coverage gap (§2.d, §3).** Mitigation: signature tightening, §6. |

The single missing primitive is the K=2 Bool certificate over the
40-class catalog (`mg-e112` §A); per `path-c-cleanup-roadmap.md`
§6b this is ~300-500 LoC. The execution arc would build it; it
is not the `hStep` proof's content.

The K > 2w + 2 leaf coverage gap is **not** a missing in-tree
primitive in the conventional sense — it's a coverage gap of
existing leaf-closers' hypothesis profiles. The mitigation in
§6 (signature tightening) avoids needing to build new
infrastructure.

---

## §6 — Mitigation: Candidate A' (signature tightening)

### §6.a — Modified `Case3Witness.{u}` def

```lean
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    LB.K ≤ 2 * LB.w + 2 →             -- new constraint
    Fintype.card β ≤ 6 * LB.w + 6 →   -- new constraint
    HasBalancedPair β
```

(Optionally: replace the explicit `Nat` inequalities with a
named predicate `WithinF5C2Caps LB`. Does not change cascade.)

### §6.b — Cascade impact relative to Deliverable B's Candidate A

Compared to Candidate A (no signature change at all), Candidate A'
adds **one line of obligation** at each consumer that applies
`hC3 : Case3Witness.{u}`:

| Site | Tag | Rewrite |
|---|---|---|
| C1. `lem_layered_balanced` (`:548`) | **MECHANICAL** | At the `exact hC3 α L hW3 hNotChain' h2` site, supply the two cap proofs. For headline-path inputs (`L = layeredFromBridges ...`), both follow trivially from `K = |α|, w = |α| + 1`. ~3-5 LoC. |
| C2-C7 | **MECHANICAL** | Threading sites — re-state the universal under the new shape. No body changes; signature shape change. |

So Candidate A' has **7 × MECHANICAL, 0 × MODERATE, 0 × CASCADE**
— same trip-wire-4 status as Candidate A. The cap proofs at C1
are trivially discharged by `omega` after substituting `K = |α|`
and `w = |α| + 1`.

The only consideration: C1's call site needs the headline path's
`K = |α|` and `w = |α| + 1` to be visible — which they are, since
`L : LayeredDecomposition α` is constructed via
`layeredFromBridges` and its fields are `simp`-normalized.

### §6.c — Why this is the right tightening

Two distinct rationales converge:

1. **Operational soundness.** All headline-path inputs land in
   the F5 C2 caps automatically; the tightening makes this
   explicit. No path that the headline can produce is excluded.
2. **Audit-bar discipline.** Tightening the def **does not**
   add a new project axiom — it *uses* the existing leaf-closer
   axioms (case3_certificate via Lean.ofReduceBool;
   case3Witness_hasBalancedPair_outOfScope) within their declared
   hypothesis profiles. Per `feedback_audit_bar_for_axioms`, this
   is a sound use of declared infrastructure.

Compared to alternatives:

* **Build new K > 2w + 2 leaf-closer.** Requires either a
  general width-2 / width-3 balanced-pair paper-level theorem
  (paper-tier escalation; Option-α territory per `mg-acc8`'s
  AMBER verdict) or per-class enumeration of width-3 layered
  irreducible posets at K ≥ 5 (combinatorial blowup; trip-wire 1
  fires).
* **New project axiom for K > 2w + 2.** Audit-bar violation per
  the ticket's "no new project axioms unilaterally" constraint.
  STOP signal.

So **signature tightening (Candidate A')** is the only
audit-bar-clean mitigation.

### §6.d — Mathematical content preservation

Per `feedback_signature_regressions`, `Case3Witness.{u}`'s
content must be preserved. Candidate A' **strictly weakens** the
universal: where Candidate A would prove `∀ (β, LB) ..., HBP β`,
Candidate A' proves `∀ (β, LB) (caps), HBP β`. This is content
**preservation modulo cap restriction**.

Operationally, the consumer at `:548` always satisfies the caps
(headline path), so the tightened universal is *equally usable*
in the discharge chain. The mathematical content of `hC3` —
"every layered width-3 non-chain poset within F5 C2 caps has a
balanced pair" — is a **truer reflection** of what existing
in-tree machinery actually proves.

The K > 2w + 2 case (vacuous at the operational headline path,
substantive at the def level) is correctly *not claimed* in the
tightened def — matching the in-tree machinery's coverage.

---

## §7 — Trip-wire checks

### §7.a — Trip-wire 2: new structural fact F6/F7?

The K > 2w + 2 coverage gap is a **scope mismatch** between the
universal `Case3Witness.{u}` def and the leaf-closers' caps —
**not** a new structural fact about K ≥ 3 layered irreducible
posets. The K = 5, w = 1 zigzag in §3 is generic singleton-band
construction; its existence and width-2-irreducibility are
elementary; its `HasBalancedPair α` conclusion holds by direct
LE enumeration.

Reading the ticket's trip-wire 2 strictly:

> **Trip-wire 2 check:** if cataloguing surfaces a new structural
> fact (F6, F7) about K ≥ 3 leaves not present in K=2, STOP and
> report.

What we surfaced is a **coverage gap**, not a "new structural
fact". F1, F2, F3 in `why-hC3-is-structural.md` describe what
arguments fail (cardinality obstruction, Brightwell vacuity,
the 0.276/(1/3) gap). The K > 2w + 2 gap doesn't introduce a
new failure mode of an argument; it shows that an existing
argument's hypothesis profile doesn't span the universal def.
**Trip-wire 2 does not strictly fire.**

That said: this is borderline reportable as a new sub-fact.
We surface it in the verdict (§0) and recommend mitigation
(§6) to keep PM/Daniel review aware. Marked AMBER in §0.

### §7.b — Trip-wire 1: complexity blowup

The hStep estimate of ~130-220 LoC + ~300-500 LoC for the K=2
sub-step is within the `mg-e0b8` §5c bundle estimate. No
combinatorial blowup. **Trip-wire 1 does not fire.**

### §7.c — Trip-wire 4: signature cascade unbounded

Candidate A' adds 1 × MECHANICAL line at C1 + threading shape
changes at C2-C7. **Trip-wire 4 does not fire.**

### §7.d — Audit-bar discipline

No new project axioms. Existing in-tree axioms
(`case3Witness_hasBalancedPair_outOfScope`, `Lean.ofReduceBool`
via `native_decide`, `brightwell_sharp_centred`) reused within
their declared hypothesis profiles.
**`feedback_audit_bar_for_axioms` PASS.**

### §7.e — F4-b trap (relabelling-as-progress)

The K ≥ 3 lift plan does not invoke fresh fiber/coherence
machinery. It composes existing primitives:
F3 strong-induction frame + reducible-step descent +
hybrid leaf-closer. **F4-b trap does not fire.**

---

## §8 — Cross-references

* `docs/case3witness-operational-audit.md` (`mg-e0b8`)
  - §3b — F3-recursive rewrite landscape; K ≥ 3 leaves persist.
  - §5c — bundle scope estimate (~480-700 LoC) — matches §4.b.
* `docs/proof-approaches-catalog-1/in-tree-primitive-inventory.md`
  (`mg-e112` §C)
  - §1 — OrdinalDecomp lift primitives.
  - §2 — LayeredDecomposition / LayerOrdinalReducible / cross_band_lt_upward.
  - §6 — bipartite_balanced_enum (K=1, K=2/w=0).
  - §7 — F3 strong-induction framework.
  - §9 — case3_certificate Bool kit.
  - §10 — case3Witness_hasBalancedPair_outOfScope axiom.
* `docs/option-c-validation-arc-1/f1-inactive-n-core-proof.md`
  (Deliverable A) — F1-inactive ⇒ N-poset-core, consumed by
  K=2 sub-step in §2.b.
* `docs/option-c-validation-arc-1/signature-design.md`
  (Deliverable B) — Candidate A discharge-in-place; this
  Deliverable C upgrades to Candidate A' (with cap tightening).
* `docs/path-c-cleanup-roadmap.md` §6b — K=2 finite-enumeration
  alternative (~300-500 LoC; the substantive K=2 sub-step in
  §2.b).
* `lean/OneThird/Step8/LayerOrdinal.lean:472` — F3 framework.
* `lean/OneThird/Step8/LayerOrdinal.lean:108` —
  `OrdinalDecompOfReducible`.
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1660` —
  `bounded_irreducible_balanced_hybrid`.
* `lean/OneThird/Step8/Case3Residual.lean:208` —
  `case3Witness_hasBalancedPair_outOfScope` axiom.
* `lean/OneThird/Step8/LayeredBridges.lean:248` —
  `layeredFromBridges` (sets K = |α|, w = |α|+1 at the headline
  path).
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1227, 1268` —
  `OrdinalDecomp.hasBalancedPair_lift_lower / _upper`.

---

## §9 — Provenance

Sub-deliverable C of `mg-fefe`. Filed 2026-05-05 by polecat.
Origin: Daniel directive 2026-05-05T~15:24Z + `mg-344a` Update
2026-05-05T~12:30Z. Doc-only; no Lean source changes.

The K ≥ 3 plan composes existing in-tree machinery — no new
mathematical content beyond the F3-step glue. The K > 2w + 2
coverage gap is surfaced honestly with the Candidate A'
mitigation; the verdict at §0 reflects this as AMBER, not GREEN.
