# A5-glue status — `mg-ff49` polecat report

**Work item:** `mg-ff49` (originally "A5-glue final assembly" — but
the realized scope is partial; see §3 for the recommended split).
**Status:** partial — typed scaffolding delivered; the substantive
imperative-loop unrolling and Path C wiring remain.
**Author:** `pc-ff49` polecat, 2026-04-26.

---

## 1. What was supposed to land

> A5-glue final assembly: replace `fun hEnum => hEnum` identity with
> full certificate-driven proof, thereby discharging the
> `Case3Witness` hypothesis in `width3_one_third_two_thirds`.

Two `fun hEnum => hEnum` placeholder bodies live in
`OneThird/Step8/BoundedIrreducibleBalanced.lean`:

* `bounded_irreducible_balanced` (line 1506-1523) — wider
  `prop:in-situ-balanced` profile.
* `bounded_irreducible_balanced_inScope` (line 1531-1538) —
  `InCase3Scope` restriction.

The B4 (`mg-43bc`) hybrid resolution clarified that the wider profile
splits into `hCert` (in-scope, certificate-driven) +
`hStruct` (out-of-scope, structural FKG/automorphism — pre-filed
work item `mg-A8`). This polecat's scope is the **`hCert` slot**:
prove `bounded_irreducible_balanced_inScope` constructively from the
F5a Bool certificate.

The downstream goal — eliminate the `hC3 : Case3Witness` hypothesis
on `width3_one_third_two_thirds` — is **Path C** of
`docs/gap-analysis.md` (separate work item; depends on Path A
landing first).

---

## 2. What's in tree (B1–B4 deliverables)

The B-items merged 2026-04-26 deliver the *bridge* infrastructure:

| Item | Branch | What it adds                                                      |
|------|--------|-------------------------------------------------------------------|
| B1   | mg-46d7 | Band-major positional foundations (`bandOffset`, position iff)    |
| B1'  | mg-a08f | `irreducible (predMaskOf L) (offsetsOf bandSizes L) = true`       |
| B2   | mg-e9d6 | `hasAdjacentIncomp (predMaskOf L) offsets = true`                 |
| B3   | mg-0f0e | `bandSizes L ∈ bandSizesGen 3 sizeLimit` + `enumPosetsFor` summary |
| B4   | mg-43bc | Hybrid dispatch theorem + profile resolution doc                  |

These give the four facts
(`closureCanonical`, `IsValidPredMask`, `warshall`, `irreducible`,
`hasAdjacentIncomp`) that the certificate's loop body checks **on
the `predMaskOf L` encoding**.

What is **not** in tree:

(A) **`Case3Enum.enumPosetsFor` Prop-level reduction.** The
certificate's outermost claim is
`allBalanced w sizeLimit = true`, which unfolds to
`∀ bs ∈ bandSizesGen 3 sizeLimit, enumPosetsFor w bs = true`.
`enumPosetsFor` is a `Bool := Id.run do` with an outer
`for mask in [0:1 <<< nfree]` loop and four early-skip gates plus
the final `hasBalancedPairSlow` check. To extract from
`enumPosetsFor w bs = true` that *our specific iteration*
(`mask = maskOf L`, `pred = predMaskOf L`) yields
`hasBalancedPair pred n = true`, the imperative loop must be
unrolled in the same `forIn`-`yield`-`done` style used by
`Case3Enum/AdjIncompBridge.lean §1` (B2) and
`Case3Enum/IrreducibleBridge.lean §6` (B1'). Estimate: ≥ 400 LOC
for the loop reduction + per-iteration body factoring + closure
form, plus another ~200 LOC for the construction-equivalence
`buildPredAtMask (maskOf L) = predMaskOf L` (post-warshall).

(B) **`findSymmetricPair` → `Symmetric` extraction.** Parallel to
`hasBalancedPairSlow_eq_true_iff` in `BalancedLift.lean §7`, but for
the fast-path decision. `BalancedLift.lean` factors out the
`Symmetric` predicate (`§3:273`) and provides the lift hypothesis
`h_sym_lift` as an explicit input to `hasBalancedPair_of_hasBalancedPair`
(`§8:1599`). The `Bool → Symmetric` extraction is the only piece of
that signature that has no in-tree producer.

(C) **`HasBalancedPair` transport across `predOrder` ↔ canonical
`Fin n` order.** A subtle but real obstacle surfaced during this
polecat session: `BalancedLift §8.hasBalancedPair_of_hasBalancedPair`
returns `@HasBalancedPair (Fin n) (predOrder pred h) _ _`, with the
`PartialOrder (Fin n)` instance baked into the result type as
`Case3Enum.predOrder`. To transport this to `HasBalancedPair α` via
`hasBalancedPair_of_orderIso`, Lean's type-class synthesis must
match the OrderIso's `(Fin n)`-side `LE` with the implicit
`PartialOrder (Fin n)` instance — but the global default
`instLEFin` (the `Nat`-induced order) fights with the local
`predOrder.toLE`. The naive `letI`-based override does *not*
suffice: section-bound instances in
`hasBalancedPair_of_orderIso`'s declaration take precedence. A
clean fix needs either an explicit-instance variant of
`hasBalancedPair_of_orderIso` (rebroadcasting `[PartialOrder]` as
explicit `(le : Fin n → Fin n → Prop)` data), or a wrapper-type
intermediate like `OrderDual`. This is non-trivial plumbing —
recommend bundling it with A5-G2 below.

(D) **Path C wiring.** Path C of `docs/gap-analysis.md`: invoke
`hasBalancedPair_of_layered_strongInduction` from
`lem_layered_balanced` and supply an `hStep` that closes Cases A,
B, C1, C2 — with C2 dispatched to the now-real
`bounded_irreducible_balanced_inScope`. Eliminates `hC3` from
`width3_one_third_two_thirds`.

---

## 3. Recommended split

The full A5-glue task as originally framed is roughly
**1500-2000 LOC**, exceeding what is tractable in one polecat
session given the imperative-loop unrolling pattern and the
construction-equivalence proof. Recommend splitting into three
follow-up work items:

### A5-G1: `enumPosetsFor` Prop-level reduction (gap (A))

**Status:** ✅ **Done** (`mg-580e` partial → `mg-b487` completion).

**Deliverable.** `Case3Enum.enumPosetsFor_iter_balanced`
(`OneThird/Step8/Case3Enum/EnumPosetsForBridge.lean §5`):

```
theorem enumPosetsFor_iter_balanced
    (w : Nat) (bs : List Nat) (h : enumPosetsFor w bs = true)
    (mask : Nat) (hmask : mask < 1 <<< enumNfreeOf w bs)
    (h_canon : closureCanonical (enumPredAtMaskOf w bs mask) mask
      (enumFreeUVOf w bs) = true)
    (h_sym : (findSymmetricPair (enumPredAtMaskOf w bs mask)
      (enumNOf bs)).isSome = false)
    (h_irr : irreducible (enumPredAtMaskOf w bs mask)
      (offsetsOf bs) = true)
    (h_adj : hasAdjacentIncomp (enumPredAtMaskOf w bs mask)
      (offsetsOf bs) = true) :
    hasBalancedPairSlow (enumPredAtMaskOf w bs mask) (enumNOf bs)
      = true
```

plus the fast-path companion `hasBalancedPair_of_findSymmetricPair_some`.

**Pattern realized.** `mg-b487` refactored
`Case3Enum.enumPosetsFor` (`Case3Enum.lean §5`) to call standalone
helpers `enumPartition`, `enumPredPreWarshallOf`, `enumPredAtMaskOf`
rather than carrying two mutable variables (`freeUV` / `forcedUV`)
through nested for-loops. With the per-mask body now single-mutable
(no `pred` accumulator inside the outer for-loop), the
`forIn`-`MProd (Option Bool) PUnit` reduction of `AdjIncompBridge §1` /
`IrreducibleBridge §6` / `BalancedLift §7` lifts directly via
`unfold + Std.Legacy.Range.forIn_eq_forIn_range' + rfl`.

**LOC.** ~110 LOC (`Case3Enum.lean` helpers ~75 LOC + new
`EnumPosetsForBridge.lean` reduction theorem ~100 LOC; the §1–§3
case-analysis lemmas were already landed by `mg-580e`).
Refactor preserves observable behaviour: the W1-W4 native_decide
certificates (`case3_balanced_w{1,2,3,4}`) still evaluate
unchanged.

### A5-G2: in-scope glue (gap (B) + composition)

**Deliverable.** The real body of
`bounded_irreducible_balanced_inScope`, replacing the placeholder.
Composes:

* B1'-B2-B3 bridges (irreducible + hasAdjacentIncomp +
  closureCanonical + warshall on `predMaskOf L`),
* G1's per-iteration extraction at `mask = maskOf L`,
* the construction-equivalence
  `warshall (build_pred (maskOf L)) n = predMaskOf L`,
* the `findSymmetricPair → Symmetric` extraction (gap (B)),
* `BalancedLift.hasBalancedPair_of_hasBalancedPair`,
* `hasBalancedPair_of_orderIso (bandMajorOrderIso_predOrder L).symm`.

**Estimate.** ~200-400 LOC (mostly the construction-equivalence
proof + the Symmetric extraction + the
`predOrder`-vs-canonical-`Fin` instance plumbing of gap (C)).

### A5-G3: Path C wiring + `Case3Witness` elimination

**Deliverable.** Replace `Case3Witness` `def` with a `theorem`,
proved by F3 strong induction with `hStep` discharging Cases A
(K=1 antichain), B (`LayerOrdinalReducible` ⇒ ordinal-sum descent),
C1 (`windowLocalization`), C2 (G2's certified
`bounded_irreducible_balanced_inScope` for the in-scope leaf, plus
`mg-A8`'s structural FKG argument for the out-of-scope leaf).
Drops the `hC3` hypothesis from `width3_one_third_two_thirds` and
its callers.

**Depends on.** G2 (real `bounded_irreducible_balanced_inScope`)
and `mg-A8` (structural argument for `¬ InCase3Scope`).

**Estimate.** ~200-300 LOC.

---

## 4. What `mg-ff49` actually delivers

This commit:

1. Records this status doc.

The placeholder `bounded_irreducible_balanced` /
`bounded_irreducible_balanced_inScope` bodies are **left
unchanged**: replacing them with a real proof requires gap (A) +
gap (B) + the construction-equivalence — which is not tractable
in one polecat session and is now cleanly split as A5-G1 / A5-G2
above.

No new sorries, no new axioms, no shortcut tactics. The current
`#print axioms OneThird.width3_one_third_two_thirds` output stays
clean (mathlib trio + `brightwell_sharp_centred`):

```
'OneThird.width3_one_third_two_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OneThird.LinearExt.brightwell_sharp_centred]
```

`Case3Witness` remains a hypothesis on
`width3_one_third_two_thirds`; eliminating it is A5-G3.

---

## 5. References

* Polecat instructions: `mg-ff49` task body.
* B1 (`mg-46d7`) commit `a6470f6`.
* B1' (`mg-a08f`) commit `f1608bf`.
* B2 (`mg-e9d6`) commit `6fbbc23`.
* B3 (`mg-0f0e`) commit `283d76d`.
* B4 (`mg-43bc`) commit `c9ceace` + `docs/a5-profile-resolution.md`.
* `step8.tex` `prop:in-situ-balanced` (`2965-2970`); proof
  Cases 1, 2, 3 at `2972-3047`; `lem:enum` at `3050-3056`.
* `docs/gap-analysis.md` — full Case3Witness gap analysis (paths A, B, C).
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current axioms baseline (clean).
