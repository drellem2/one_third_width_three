# Main-theorem gap analysis (`mg-3813`)

Read-only audit of the headline theorem
`OneThird.width3_one_third_two_thirds` and its transitive callees. The
question driving this audit: are there any unproved Prop-level
hypotheses or caller-side identity discharges that block the theorem
from being applicable, beyond the named axiom
`brightwell_sharp_centred`?

**TL;DR.** Yes — exactly one. The headline theorem carries a
hypothesis `hC3 : Step8.Case3Witness` that is never constructed
anywhere in the codebase, and the `K ≥ 2` branch of
`lem_layered_balanced` discharges by re-applying that hypothesis.
Several other "caller-side discharge" theorems (`bounded_irreducible_balanced`,
`kahnLinialBaseCase`, `smallNFiniteEnum`) exist with the same
structural shape but are **not on the call graph** of
`width3_one_third_two_thirds`, so they are not part of this gap.
No additional axioms beyond `brightwell_sharp_centred` are declared
under `lean/OneThird/`.

---

## 1. The `Case3Witness` gap

### 1a. Theorem statement

`lean/OneThird/MainTheorem.lean:38-43`:

```lean
theorem width3_one_third_two_thirds.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hC3 : Step8.Case3Witness.{u}) :
    HasBalancedPair α :=
  Step8.width3_one_third_two_thirds_assembled hP hNonChain hC3
```

The third hypothesis `hC3 : Step8.Case3Witness.{u}` is the load-bearing
unproved input.

### 1b. The witness statement

`lean/OneThird/Step8/LayeredBalanced.lean:402-408`:

```lean
def Case3Witness.{u} : Prop :=
  ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
    (LB : Step8.LayeredDecomposition β),
    HasWidthAtMost β 3 →
    ¬ IsChainPoset β →
    2 ≤ Fintype.card β →
    HasBalancedPair β
```

This is a `Prop` defined *as the conclusion of* `lem_layered_balanced`
(modulo argument re-ordering). Every constructor for it would already
be a complete proof of the layered case.

### 1c. The discharge identity

`lean/OneThird/Step8/LayeredBalanced.lean:452-512`:

```lean
theorem lem_layered_balanced.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (L : LayeredDecomposition α) (h2 : 2 ≤ Fintype.card α)
    (hNotChain : ¬ OneThird.IsChainPoset α)
    (hW3 : HasWidthAtMost α 3)
    (hC3 : Case3Witness.{u}) :
    OneThird.HasBalancedPair α := by
  ...
  rcases Nat.lt_or_ge L.K 2 with hK1 | _hK2
  · -- K = 1: bipartite_balanced_enum on the single antichain.
    ...
  · -- K ≥ 2: discharged by direct application of hC3.
    exact hC3 α L hW3 hNotChain' h2
```

The `K ≥ 2` branch is closed by *direct application of the same
hypothesis* — there is no F3 strong induction, no `bounded_irreducible_
balanced` invocation, no Bool-certificate lift. The recursion driver
(`hasBalancedPair_of_layered_strongInduction`,
`LayerOrdinal.lean:362`) is defined in tree but is not called from
this branch.

### 1d. The non-bridge

`lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:460-477`:

```lean
theorem bounded_irreducible_balanced
    (L : LayeredDecomposition α)
    (_hWidth3 : HasWidthAtMost α 3)
    (_hIrr : LayerOrdinalIrreducible L)
    (_hK3 : 3 ≤ L.K) (_hw : 1 ≤ L.w)
    (_hCard : Fintype.card α ≤ 6 * L.w + 6)
    (_hDepth : L.K ≤ 2 * L.w + 2)
    (hEnum : HasBalancedPair α) :
    HasBalancedPair α :=
  hEnum
```

This theorem is `fun … hEnum => hEnum` — an identity function dressed
as a Prop-level lift of F5a's Bool certificate. Its only role is to
*document* the dispatch shape; it is not invoked by any code in the
codebase (verified by `grep -rn "exact bounded_irreducible_balanced\|
:= bounded_irreducible_balanced\| bounded_irreducible_balanced [^_]"
lean/OneThird/`). The same shape applies to
`bounded_irreducible_balanced_inScope` (`:485-492`).

### 1e. The Bool certificate exists; the bridge does not

`lean/OneThird/Step8/Case3Enum.lean:35-37` (the deferred-encoding
note):

> The lift of this certificate to an abstract
> `∀ (L : LayeredDecomposition α), … → HasBalancedPair α` statement
> requires an encoding argument (choose element labelling within
> each band; prove probability invariance under relabelling) that
> is deferred to a separate work item on the F5 recursion.

`Case3Enum.case3_certificate` (`lean/OneThird/Step8/Case3Enum/
Certificate.lean:57-62`) is a fully-proved Bool-level conjunction:

```lean
theorem case3_certificate :
    allBalanced 1 9 = true ∧
    allBalanced 2 7 = true ∧
    allBalanced 3 7 = true ∧
    allBalanced 4 7 = true :=
  ⟨case3_balanced_w1, case3_balanced_w2, case3_balanced_w3,
   case3_balanced_w4⟩
```

The `numLinExt`-side §1 transport infrastructure (order-iso
invariance of `HasBalancedPair`, `numLinExt`, `probLT`) is also
present (`BoundedIrreducibleBalanced.lean:107-244`). What is missing
is (i) the band-major Fin-n labelling actually used as an order
iso, and (ii) the `Case3Enum.hasBalancedPair` (Bool, on bitmasks) ↔
`HasBalancedPair α` (Prop, on the encoded poset) identification —
plus a recursion driver that handles the parameter ranges *outside*
the Bool certificate's certified scope.

### 1f. Scope difference table

The `Case3Witness` ∀-family quantifies over **every** width-3
non-chain layered β with `|β| ≥ 2`. The Bool certificate covers a
strict subset.

| Parameter      | `Case3Witness` requires       | `case3_certificate` covers           | `InCase3Scope` predicate (`BoundedIrreducibleBalanced.lean:364-366`) |
|----------------|-------------------------------|--------------------------------------|----------------------------------------------------------------------|
| Depth `K`      | any `K ≥ 1`                   | `K = 3` only                         | `K = 3`                                                              |
| Interaction `w`| any `w ∈ ℕ`                   | `w ∈ {1, 2, 3, 4}`                   | `1 ≤ w ≤ 4`                                                          |
| Size `\|β\|`     | any `\|β\| ≥ 2`                 | `≤ 9` (w=1), `≤ 7` (w∈{2,3,4})       | `(w=1 → card ≤ 9) ∧ (2 ≤ w → card ≤ 7)`                              |
| Width          | `HasWidthAtMost β 3`          | width-3 (per band-size encoding)     | (carried separately as `_hWidth3`)                                   |
| Irreducibility | none                          | `irreducible` (per Bool check)       | (carried separately as `_hIrr`)                                      |

The certificate's scope was deliberately restricted to keep
`native_decide` builds under the 10-minute lake-build target
(`Case3Enum/Certificate.lean:25-34`); full-depth and full-size
enumeration are out of reach for `native_decide` at `v4.29.1`.

### 1g. Why the gap is not closed by what is in tree

* The `Case3Witness` ∀-family is universal in `K`, `w`, `|β|`. The
  certificate is bounded in all three. So even with a complete
  Bool↔Prop bridge, `case3_certificate` would only discharge a
  *bounded sub-class* of the ∀-family.

* The shortfall (`K ≥ 4`, or `K = 3` outside the size cap) is
  exactly what the F3 strong-induction driver
  (`hasBalancedPair_of_layered_strongInduction`) is designed to
  reduce to the bounded base case via the Case-B (ordinal-sum
  descent) and Case-C1 (window-localisation) cuts of `step8.tex`
  §G4. That driver exists but `lem_layered_balanced` does not call
  it; the K≥2 branch shortcuts to `hC3` instead.

* The `layeredFromBridges` witness used as `caseR_to_caseC` is a
  singleton-band layering with `w = |α| + 1` (so (L2) is vacuous),
  which lies entirely outside the certificate's `w ∈ {1,2,3,4}`
  scope. Even a fully-bridged Bool certificate would not cover the
  `LayeredDecomposition` that the main assembly actually feeds to
  `lem_layered_balanced`.

---

## 2. Other gaps on the call graph from `width3_one_third_two_thirds`

Walking the call graph:

```
OneThird.width3_one_third_two_thirds       (MainTheorem.lean:38)
└── Step8.width3_one_third_two_thirds_assembled (MainAssembly.lean:306)
    ├── Step8.mainAssembly                  (MainAssembly.lean:263) [proved]
    │   └── I.caseC ∘ I.caseR_to_caseC      (via MainTheoremInputs)
    │        ├── caseC = lem_layered_balanced (LayeredBalanced.lean:452)
    │        │    ├── K=1: bipartite_balanced_enum (BipartiteEnum.lean:284) [proved]
    │        │    └── K≥2: hC3 α L hW3 hNotChain' h2     [GAP — §1]
    │        └── caseR_to_caseC = layeredFromBridges (LayeredBridges.lean:181) [proved]
    └── Step8.mainTheoremInputsOf           (MainAssembly.lean:224) [proved, threads hC3]
```

Each non-`hC3` discharge on this graph was inspected:

* `bipartite_balanced_enum` (`BipartiteEnum.lean:284-310`) — fully
  proved; used the symmetry `Equiv.swap u v` argument that replaces
  the prior `fkg_case_output` axiom.
* `layeredFromBridges` (`LayeredBridges.lean:181-283`) — fully
  proved; produces a singleton-band layered decomposition with
  `K = |α|`, `w = |α| + 1`. Vacuously satisfies (L2). All bridge
  invocations (`Bridge.step5/step6/step7_layered`) discharge with
  trivial inputs.
* `mainAssembly` (`MainAssembly.lean:263-275`) — fully proved.
* `mainTheoremInputsOf` (`MainAssembly.lean:224-235`) — fully
  proved; just bundles the dependencies and threads `hC3`.

**Result.** The only unproved caller-side discharge on the call
graph is the `hC3` re-application at `LayeredBalanced.lean:512`.

### Other identity-discharge theorems (not on the call graph)

For the record, these theorems exist in tree with the same structural
"caller-side identity" shape, but are *not* invoked from
`width3_one_third_two_thirds`:

| Theorem                                 | File / line                              | Identity body                          | Reachable from main? |
|-----------------------------------------|------------------------------------------|----------------------------------------|----------------------|
| `bounded_irreducible_balanced`          | `BoundedIrreducibleBalanced.lean:460-477`| `hEnum` returned as-is                 | No (no callers)      |
| `bounded_irreducible_balanced_inScope`  | `BoundedIrreducibleBalanced.lean:485-492`| `hEnum` returned as-is                 | No (no callers)      |
| `kahnLinialBaseCase`                    | `SmallN.lean:167-177`                    | `hKL` returned as-is                   | No (only used in `lem_small_n`, which only `mainAssembly_smallN` invokes — not on main path) |
| `smallNFiniteEnum`                      | `SmallN.lean:201-211`                    | `hEnum` returned as-is                 | No (same path)       |
| `lem_small_n`                           | `SmallN.lean:233-246`                    | dispatches to two identities above     | No (only `mainAssembly_smallN`)|
| `mainAssembly_smallN`                   | `MainAssembly.lean:283-289`              | wrapper around `lem_small_n`           | No                   |
| `lem_layered_balanced_subtype`          | `LayeredBalanced.lean:532-566`           | recurses through `lem_layered_balanced`| No (no callers)      |
| `layered_implies_balanced`              | `LayeredBalanced.lean:682-690`           | aliases `lem_layered_balanced`         | No (no callers)      |

These are documentation/scaffolding theorems left in place for
future work (F5a-ℓ Bool↔Prop bridge, the Kahn–Linial port, the
small-`n` regime). They do not block `width3_one_third_two_thirds`.

The F3 recursion driver
`hasBalancedPair_of_layered_strongInduction`
(`LayerOrdinal.lean:362-396`) is fully proved as a generic strong
induction, but no `hStep` instance is provided that closes Case A /
B / C uniformly — and since the main proof bypasses it via `hC3`,
this is dead-code infrastructure rather than a gap.

---

## 3. Axioms

`grep -rEn "^(axiom )" lean/OneThird/` finds exactly one declaration:

```
lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159:axiom brightwell_sharp_centred
```

This matches `lean/PRINT_AXIOMS_OUTPUT.txt`:

```
'OneThird.width3_one_third_two_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OneThird.LinearExt.brightwell_sharp_centred]
```

`#print axioms` does **not** surface the `Case3Witness` gap because
`hC3` is a *hypothesis of the theorem statement*, not an axiom. The
theorem is sorry-free and axiom-clean as stated; the gap is that no
caller in the codebase can produce a `Case3Witness` to apply it to.
`grep -rEn "(^| )sorry( |$)" lean/OneThird/` returns nothing.

---

## 4. Recommendation

Three paths are on the table for closing the gap. Based on what is
already in tree:

### Path A — Port the Bool→Prop encoding bridge for `case3_certificate`

What it requires:

* Define the band-major order isomorphism
  `α ≃o Fin (Fintype.card α)` for any width-3 layered `α` in scope
  (use `Fintype.equivFin` per band; the within-band order is
  irrelevant by `probLT_of_orderIso`, already proved at
  `BoundedIrreducibleBalanced.lean:198-221`).
* Identify `Case3Enum.hasBalancedPair pred n` (Bool, on a
  predecessor-bitmask encoding) with `HasBalancedPair (Fin n)` for
  the encoded poset. This is the `countLinearExtensions ↔ numLinExt`
  identification flagged by both
  `Case3Enum.lean:35-37` and `BoundedIrreducibleBalanced.lean:339-345`.
* Compose with `hasBalancedPair_of_orderIso` to discharge
  `bounded_irreducible_balanced` for any `(L.w, |α|, L.K) ∈
  InCase3Scope`.

What it does *not* address: parameter ranges outside `InCase3Scope`
(any `K ≠ 3`, any `w ∉ {1,…,4}`, any `|α|` exceeding the cap). So
on its own it does not produce a `Case3Witness` constructor — it
discharges the bounded base case only.

In-tree readiness: §1 transport infra is done; §2 band-major
labelling has the helpers (`bandSizes`, `bandSize_le_three`,
`sum_bandSize_eq_card`) but the `≃o Fin n` builder is missing; §3
bridge is the deferred piece flagged in `Case3Enum.lean:35-37`. The
`AllBalancedSound` packaging predicate is gestured at in module
docs but not defined.

### Path B — Widen the certificate

What it requires: re-run `enum_case3.py` with larger size caps and
larger `w` until coverage extends to whatever the F3 recursion
ultimately demands. Per `Case3Enum/Certificate.lean:25-34`, this is
hours-to-days of compute even single-threaded, and `native_decide`
evaluation in lake builds becomes a bottleneck at the 10-minute
target.

What it does *not* address: any `K ≠ 3` case, since the certificate
is hardwired to `K = 3` (and the F3 recursion descent is what would
reduce arbitrary `K` to `K = 3`).

In-tree readiness: the Python script and JSON schema exist; the
Lean side (`allBalanced`, `bandSizesGen`) parameterises over
`(w, sizeLimit)` so dropping in larger numbers is mechanical. But
this path alone cannot close `Case3Witness`.

### Path C — Redesign the recursion

What it requires:

* Actually invoke `hasBalancedPair_of_layered_strongInduction` from
  `lem_layered_balanced` instead of shortcutting to `hC3`.
* Provide an `hStep` that closes Case A (K=1 antichain — already
  done by `bipartite_balanced_enum`), Case B (ordinal-sum descent
  via `LayerOrdinalReducible` / F4's chained-lift), and Case C1
  (window-localisation via `windowLocalization`,
  `LayeredBalanced.lean:103`) with the IH, and dispatches Case C2
  to the bounded base case from Path A.
* Close the residual Case C2 base via Path A's encoding bridge for
  `(K, w, card) ∈ InCase3Scope`.

What it does *not* address: the bridge from Bool certificate to
Prop-level base case still has to exist. Path C uses Path A as a
sub-routine.

In-tree readiness: F1 (`LayerOrdinalReducible`,
`OrdinalDecompOfReducible`), F2
(`exists_adjacent_not_lt_of_irreducible`), F3
(`hasBalancedPair_of_layered_strongInduction`), F4
(`OrdinalChainLift`, `OrdinalDecomp.hasBalancedPair_lift`) are all
in tree. The `windowLocalization` lemma is in tree
(`LayeredBalanced.lean:103`). The chained-lift lemmas
`OrdinalChainLift.cons` /
`OrdinalDecomp.hasBalancedPair_lift` exist. F5a's Bool certificate
exists. So most of the *components* are in tree; what is missing is
the case-by-case discharge function that wires them through
`hStep`.

### Tractability assessment

**Path A is the most tractable next step**, but it does not on its
own close `Case3Witness`. It is the prerequisite for Path C and
delivers a cleanly testable artefact (`bounded_irreducible_balanced`
becomes a real lift, not a `fun … hEnum => hEnum` identity). Once
Path A lands, Path C is a straightforward case-split using
in-tree lemmas — F1–F5a all exist. Path B is the worst option:
build-time pain, doesn't close the universal case, and still leaves
`K ≠ 3` outside scope.

**Suggested ordering for `mg-46af` and successors:**

1. Path A: define `α ≃o Fin (Fintype.card α)` band-major iso;
   identify `Case3Enum.hasBalancedPair` with `HasBalancedPair (Fin
   n)`; replace `bounded_irreducible_balanced`'s identity body
   with the certificate-driven proof. Leaves `Case3Witness` open
   but turns one identity into a real theorem.
2. Path C: write the `hStep` for
   `hasBalancedPair_of_layered_strongInduction` using existing F1–F4
   infrastructure plus the now-proved
   `bounded_irreducible_balanced`. Define `Case3Witness` as a
   `theorem`, not a `def`. Drop `hC3` from
   `width3_one_third_two_thirds`.

Path C is the one that produces an applicable main theorem; Path A
is the prerequisite that makes Path C's base case real.
