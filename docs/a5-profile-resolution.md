# A5-B4 — Profile mismatch resolution: hybrid certificate + structural argument

**Work item:** `mg-43bc` (split from `mg-ff49` / A5).
**Surfaced by:** `pc-ff49` analysis of A5's bridge layer.
**Status:** decided — see §3 below.

---

## 1. The mismatch

Two inhabitants of `OneThird/Step8/BoundedIrreducibleBalanced.lean`
have incompatible scopes:

| Object                              | Source                                       | Scope                                                                                 |
|-------------------------------------|----------------------------------------------|---------------------------------------------------------------------------------------|
| `bounded_irreducible_balanced`      | `BoundedIrreducibleBalanced.lean:1205-1222`  | `1 ≤ w`, `3 ≤ K ≤ 2w+2`, `\|α\| ≤ 6w+6`                                                |
| `InCase3Scope`                      | `BoundedIrreducibleBalanced.lean:1109-1111`  | `K = 3`, `1 ≤ w ≤ 4`, `(w=1 → \|α\| ≤ 9) ∧ (2 ≤ w → \|α\| ≤ 7)`                          |
| `Case3Enum.case3_certificate`       | `Case3Enum/Certificate.lean:57-62`           | `(w=1, K=3, \|α\| ≤ 9)`, `(w∈{2,3,4}, K=3, \|α\| ≤ 7)`                                   |

`bounded_irreducible_balanced`'s hypothesis profile is the **wider** of
the three. `InCase3Scope` exactly matches what `case3_certificate`
covers. The wider profile is **not** discharged by the certificate
alone — the gap appears in two ways:

* **Depth gap.** For `w=1`, the wider profile permits `K ∈ {3, 4}`
  (`K ≤ 2w+2 = 4`); the certificate only covers `K = 3`. For larger
  `w` the gap grows (e.g. `w=2 ⇒ K ∈ {3,4,5,6}`).
* **Size gap.** The wider profile permits `|α| ≤ 6w+6` (so `≤ 18`
  for `w=2`); the certificate caps `|α| ≤ 7` for `w ≥ 2`.

Both gaps are real: at `(w=1, K=4, |α| ≤ 12)` an irreducible width-3
layered poset is not in `InCase3Scope`, and the `K=3` Bool
enumeration cannot witness it.

The wider profile is what `step8.tex` calls `prop:in-situ-balanced`
(`step8.tex:2965-2970`):

> Let `Q` be a layered width-3 poset of interaction width `w` and
> depth `K ≥ 2`, with `|Q| ≤ 3(3w+1)`. Then `Q` contains a balanced
> pair.

Note `K ≥ 2`, not `K = 3`. The paper proves this in three cases
(`step8.tex:2972-3048`):

* **Case 1** — symmetric within-band pair with full ambient match.
  Closed by an automorphism / `Equiv.swap` argument.
* **Case 2** — FKG profile-ordering on a within-band pair. Closed by
  Ahlswede–Daykin / FKG plus the rotation argument of
  `prop:bipartite-balanced`, **provided** the three two-sided profiles
  in `A` form a chain in the product order `⪯`.
* **Case 3** — *residual* width-3 profile antichain: `|A| = 3` (or
  symmetric `|B| = 3`) with three pairwise `⪯`-incomparable profiles.
  The paper defers this to `lem:enum` (`step8.tex:3050-3056`), the
  "finite enumeration of bounded-depth irreducible layered posets",
  which in Lean is exactly `case3_certificate`.

So Cases 1 and 2 are **structural**; Case 3 is the
**enumeration residual**. The certificate covers Case 3. The wider
profile in `bounded_irreducible_balanced` is the union of all three.

---

## 2. Resolution options considered

### Option 1 — Tighten `bounded_irreducible_balanced` to `InCase3Scope`

**Rejected.** Would require the F3 strong-induction driver
(`hasBalancedPair_of_layered_strongInduction`,
`LayerOrdinal.lean:362-396`) to descend `K` to exactly `3` at every
irreducible leaf. There is no such mechanism in the paper or in the
in-tree F3 framework: the F3 recursion descends `|α|` via
* Case A (K=1) — direct antichain;
* Case B (`L` reducible) — IH on factors;
* Case C1 (`W ⊊ X` after window-localisation) — IH on the strictly
  smaller window;
* Case C2 (`W = X`, irreducible, bounded) — base case.

The base case (C2) carries `K ∈ [3, 2w+2]` by construction;
irreducibility is precisely the obstruction to further band cuts.
Forcing `K = 3` at the leaf is not a property of the recursion — it
is an additional *math claim* unsupported by the paper.

### Option 2 — Widen `case3_certificate` to cover `K ∈ [2, 2w+2]`

**Rejected.** Two reasons:

1. **Computational blowup.** The current `case3_certificate` runs
   `native_decide` over `~344K` configurations at `(w=1, K=3, |α|≤9)`
   in `~13s` (per `Case3Enum/Certificate.lean:23-27`). Extending to
   `K ∈ [2, 4], |α| ≤ 12` for `w=1` is roughly a 5x blowup; for
   `w=2`, `K ∈ [2, 6], |α| ≤ 18` is exponential and exceeds the
   10-minute lake-build target (`Case3Enum/Certificate.lean:30-33`).
2. **Architectural mismatch.** `enum_case3.py` and the in-Lean
   `bandSizesGen` enumerator are hardcoded to `K = 3`. Re-engineering
   them for variable `K` is non-trivial and produces an artefact that
   the paper never claims as the discharge of `prop:in-situ-balanced`.

### Option 3 — Hybrid: certificate for Case 3 (K=3 residual) + structural argument for Cases 1, 2

**Selected.** Matches the paper's actual proof structure of
`prop:in-situ-balanced` exactly. The dispatch is:

* If the C2 leaf falls in `InCase3Scope` *and* Cases 1 and 2 of the
  paper proof do **not** apply (i.e. we are at the residual
  "width-3 profile antichain" configuration), discharge via
  `case3_certificate`.
* Otherwise, discharge via the structural Cases 1 / 2 (FKG +
  automorphism) — these handle every `K ≥ 2` uniformly, including
  `K ≥ 4` and `|α|` outside the certificate's size cap.

The structural argument is exactly the content of pre-filed work item
**mg-A8** (`lean/README.md:139-145`), already flagged at "high"
priority by the `pc-4a4b` Q1 re-read.

---

## 3. Decision

**Adopt Option 3 (hybrid).** This decision:

1. Keeps `bounded_irreducible_balanced` at the **wider profile**
   (`step8.tex prop:in-situ-balanced` exactly), which is the right
   target statement for the F3 recursion's C2 leaf.
2. Acknowledges that the discharge is **two-piece**:
   * `case3_certificate` for the Case-3 residual (in `InCase3Scope`
     after Cases 1, 2 are ruled out), and
   * a structural FKG / automorphism argument (mg-A8) for the
     remainder.
3. Adds explicit Lean infrastructure that *names* the dispatch, so
   downstream consumers (Path C of `docs/gap-analysis.md`, mg-A8) can
   build against a typed split rather than against a bare hypothesis.

Why Option 3 over leaving the dispatch implicit:

* The current `bounded_irreducible_balanced` is a stub
  (`fun … hEnum => hEnum`) with no internal structure. Whoever
  discharges its `hEnum` hypothesis has no in-tree guidance about
  *how* the discharge decomposes. Naming the dispatch produces
  better hand-off to the next polecat working mg-A8 / Path A.
* It also clarifies the relationship between the certificate's scope
  (`InCase3Scope`) and the wider profile, which the gap-analysis
  doc identifies as a load-bearing question.

---

## 4. Lean changes

### 4a. `BoundedIrreducibleBalanced.lean`

* Add a `bounded_irreducible_balanced_hybrid` theorem that takes
  **two** Prop-level dispatch witnesses:
  * `hCert : InCase3Scope L.w (Fintype.card α) L.K → HasBalancedPair α`
    — supplied by the caller from `case3_certificate` after the §1
    order-iso transport / §3 Bool↔Prop bridge (Path A);
  * `hStruct : ¬ InCase3Scope L.w (Fintype.card α) L.K → HasBalancedPair α`
    — supplied by the caller from the FKG / automorphism Cases 1
    and 2 of `prop:in-situ-balanced` (mg-A8).
* The theorem dispatches on `Decidable (InCase3Scope ...)` (the
  predicate is decidable: `Nat.decEq`, `Nat.decLe`).
* Re-derive the existing wider `bounded_irreducible_balanced` from
  the hybrid form: collapse the two dispatch hypotheses into the
  monolithic `hEnum : HasBalancedPair α` to preserve backward
  compatibility with documentation citations.
* Update the module docstring (`§4` header and the
  `bounded_irreducible_balanced` docstring) to call out the hybrid
  resolution and reference this doc.

### 4b. `LayeredBalanced.lean`

* Update the docstring of `Case3Witness` to note that downstream
  discharge of `Case3Witness` ultimately decomposes into the two
  dispatch witnesses above (certificate + structural). The
  predicate itself stays as the universal `∀ β, …` statement — no
  signature change — because the K ≥ 2 branch of
  `lem_layered_balanced` short-circuits to `hC3` rather than
  invoking F3 (per the gap-analysis "non-bridge" section).

### 4c. No signature changes to `Case3Witness`, `lem_layered_balanced`, or `width3_one_third_two_thirds`.

Keeping these stable preserves the published top-level interface and
the existing build. The hybrid restructuring is *internal* to
`BoundedIrreducibleBalanced.lean`, threading through to the
forthcoming Path A / mg-A8 implementations.

### 4d. No new sorry's or axioms.

The new dispatch theorem is a tautology in the same sense as the
existing stubs: it takes two Prop-level witnesses and combines them.
The actual Bool→Prop bridge (Path A) and the structural FKG argument
(mg-A8) remain to be implemented; both are filed work items
producing the witnesses the dispatch consumes.

---

## 5. Hand-off

* **Path A** (`docs/gap-analysis.md` §4): now consumes
  `bounded_irreducible_balanced_hybrid`'s `hCert` slot. The encoding
  bridge from `case3_certificate` to `HasBalancedPair α` lands as a
  proof of `InCase3Scope L.w (Fintype.card α) L.K → HasBalancedPair α`.
* **mg-A8** (`lean/README.md:139-145`): now consumes
  `bounded_irreducible_balanced_hybrid`'s `hStruct` slot. The FKG /
  automorphism argument lands as a proof of
  `¬ InCase3Scope L.w (Fintype.card α) L.K → HasBalancedPair α`.
* **Path C** (`docs/gap-analysis.md` §4): wires both into the F3
  `hStep` to discharge `Case3Witness` constructively, eliminating the
  top-level hypothesis on `width3_one_third_two_thirds`.

---

## 6. References

* `step8.tex` `prop:in-situ-balanced` (lines `2965-2970`); proof
  `2972-3048`; Cases 1, 2, 3 at `2984-3047`.
* `step8.tex` `lem:enum` (lines `3050-3056`).
* `lean/README.md` mg-A8 (line `139`).
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean` —
  `bounded_irreducible_balanced` (line `1205`),
  `bounded_irreducible_balanced_inScope` (line `1230`),
  `InCase3Scope` (line `1109`).
* `lean/OneThird/Step8/Case3Enum/Certificate.lean` —
  `case3_certificate` (line `57`).
* `lean/OneThird/Step8/LayeredBalanced.lean` — `Case3Witness`
  (line `402`), `lem_layered_balanced` (line `452`).
* `lean/OneThird/Step8/LayerOrdinal.lean` —
  `hasBalancedPair_of_layered_strongInduction` (line `362`).
* `docs/gap-analysis.md` (mg-3813) — full Case3Witness gap analysis.
