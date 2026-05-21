/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.ChainPotentials
import OneThird.Step8.ConcreteChainLiftData

/-!
# Step 8 — Synchronization-map wiring for the S7-F bridge (Piece 3, sub-arc B)

This file is **sub-ticket B of FULL REFACTOR Phase-2 Piece 3** — the
S7-F bridge (`lem:layered-from-step7`, `step8.tex:2009-2089`). Work
item `mg-120d`.

## What this delivers

The S7-F bridge consumes a `ChainLiftData α`
(`ChainPotentials.lean:328`) and must build a ground-set
`LayeredDecomposition` on `X \ X^exc`. The band assembly
(`step8.tex:2108-2111`)

```
  L_k := { a_k, b_{f_AB(k)}, c_{f_AC(k)} } ∩ (X \ X^exc)
```

is driven by the **synchronization maps** `f_AB, f_AC, f_BC`. Per the
Checkpoint-3 re-scope (`docs/state-S7F-Checkpoint3-Session1.md`,
mg-ca83) these maps are **input** carried by the `ChainLiftData` —
they are *not* constructed here. This file **wires** them into the
band-assembly-ready form:

* **Orphan handling.** The paper's `f_••` are *partial* — undefined
  at chain-tail orphans, which the paper absorbs into `X^exc_sync`
  (`step8.tex:2050-2055`). The Lean port must make the "undefined"
  decision **decidable**. `SyncMap.IsOrphan` is the decidable orphan
  predicate (`SyncMap.decidableIsOrphan`); `SyncMap.orphans` is the
  orphan index `Finset`; `ChainLiftData.refOrphans` collects the
  band-anchor orphans of `f_AB`/`f_AC`. (The ground-set
  `X^exc_sync : Finset α` is assembled by sub-ticket S7-F-A out of
  these orphan index sets — it needs `DecidableEq α` for the chain
  image and is therefore scoped there, not here.)
* **Domain extension.** Off the orphan set the maps are *total*:
  `SyncMap.onDomain` is the genuine total function on the defined
  subset, `SyncMap.extend` the total extension to all chain indices
  with a fallback, and `ChainLiftData.fABwired`/`fACwired` are the
  band-assembly-ready maps on `X \ X^exc_sync`.
* **Monotonicity.** The paper's `f_••` are weakly monotone wherever
  defined (`step8.tex:2102-2106`). `SyncMap.onDomain_monotone` lifts
  the `SyncMap.weakly_monotone` field to a genuine `Monotone`, and
  `ChainLiftData.fABwired_monotone`/`fACwired_monotone` propagate it
  across chains to the poset order — the input the band assembly's
  (L4) verification (`step8.tex:2153-2167`) consumes.

## Scope discipline — Resolution A (`hCex` domain-pin)

Per the Piece-3 design note, this file works against the **bare**
`ChainLiftData` (Resolution A). The structure carries no soundness
invariant tying the orphan count to `K_bw`, so the paper's per-chain
bound `|X^exc_sync| ≤ K_bw` (`step8.tex:2053`) is **not derivable
here** — it is an ill-posed obligation against the bare structure.
It is instead **made explicit** as the named predicate
`ChainLiftData.BoundedSyncOrphans`, a downstream hypothesis (pinned
at the bridge call site via `hCex`, or a Resolution-B soundness
field). What *is* derivable from the bare structure —
`refOrphans_card_le` and `orphan_count_le_of_bounded`, the structural
half of paper item (i) — is proved unconditionally / from that
hypothesis.

## Cross-references

* `lean/OneThird/Step8/ChainPotentials.lean` — `SyncMap` (`:211`),
  `ChainLiftData` (`:328`), `IndexedChain`/`ChainTriple`.
* `lean/OneThird/Step8/ConcreteChainLiftData.lean` —
  `gridChainLiftData`, the F7a concrete witness (mg-974c) the §6
  non-triviality certificates instantiate against.
* `step8.tex:2009-2111` — `lem:layered-from-step7`; `2050-2055` the
  chain-tail orphans; `2102-2106` the sync maps' weak monotonicity.
* `docs/state-S7F-B-Session1.md` — this session's state doc.

No new axioms or sorries are introduced.
-/

namespace OneThird
namespace Step8

namespace SyncMap

variable {nA nB : ℕ}

/-! ### §1 — Chain-tail orphans: the decidable "undefined" decision -/

/-- **Chain-tail orphan predicate** (`step8.tex:2050-2055`).

`f.IsOrphan i` holds when the partial sync map has *no* partner for
index `i` — the paper's "`f_••` undefined at a chain tail". The Lean
port must make this decision decidable; the `Decidable` instance
below discharges that requirement. -/
def IsOrphan (f : SyncMap nA nB) (i : Fin nA) : Prop :=
  f.partner i = none

instance decidableIsOrphan (f : SyncMap nA nB) (i : Fin nA) :
    Decidable (f.IsOrphan i) := by
  unfold IsOrphan; infer_instance

@[simp] lemma isOrphan_iff (f : SyncMap nA nB) (i : Fin nA) :
    f.IsOrphan i ↔ f.partner i = none := Iff.rfl

/-- **Orphan index set** — the chain-tail orphans of a sync map as a
`Finset`. Their ground-set images make up the `X^exc_sync` that
sub-ticket S7-F-A assembles. -/
def orphans (f : SyncMap nA nB) : Finset (Fin nA) :=
  (Finset.univ : Finset (Fin nA)).filter (fun i => (f.partner i).isNone)

@[simp] lemma mem_orphans {f : SyncMap nA nB} {i : Fin nA} :
    i ∈ f.orphans ↔ f.partner i = none := by
  simp [orphans, Option.isNone_iff_eq_none]

lemma mem_orphans_iff_isOrphan {f : SyncMap nA nB} {i : Fin nA} :
    i ∈ f.orphans ↔ f.IsOrphan i := mem_orphans

/-- An index is *not* an orphan exactly when it lies in the domain —
the orphan set and the domain partition `Fin nA`. -/
lemma not_mem_orphans_iff_mem_domain {f : SyncMap nA nB} {i : Fin nA} :
    i ∉ f.orphans ↔ i ∈ f.domain := by
  rw [mem_orphans, mem_domain, Option.isSome_iff_ne_none]

lemma mem_domain_iff_not_isOrphan {f : SyncMap nA nB} {i : Fin nA} :
    i ∈ f.domain ↔ ¬ f.IsOrphan i := by
  rw [← not_mem_orphans_iff_mem_domain, mem_orphans_iff_isOrphan]

/-- The orphan set is the complement of the domain. -/
lemma orphans_eq_compl_domain (f : SyncMap nA nB) :
    f.orphans = f.domainᶜ := by
  ext i
  simp only [Finset.mem_compl, mem_orphans, mem_domain,
    Option.isSome_iff_ne_none, not_not]

/-- Domain and orphan set jointly exhaust the `nA` chain indices —
every chain element is either synchronized or a tail orphan. -/
lemma card_domain_add_card_orphans (f : SyncMap nA nB) :
    f.domain.card + f.orphans.card = nA := by
  rw [orphans_eq_compl_domain]
  simp

/-- A defined index yields an explicit partner witness. -/
lemma exists_partner_of_mem_domain {f : SyncMap nA nB} {i : Fin nA}
    (h : i ∈ f.domain) : ∃ j : Fin nB, f.partner i = some j := by
  rw [mem_domain] at h
  exact Option.isSome_iff_exists.mp h

/-! ### §2 — Domain extension: the total map on the synchronized set -/

/-- **The sync map restricted to its domain**, as a genuine *total*
function `f.domain → Fin nB`. Off the orphan set the paper's partial
`f_••` is total; `onDomain` is that total map — the band-assembly
input. -/
def onDomain (f : SyncMap nA nB) (i : f.domain) : Fin nB :=
  (f.partner i.1).get (mem_domain.mp i.2)

/-- `onDomain` is a genuine section of `partner`: the partial map
agrees with its total restriction on the domain. -/
lemma partner_eq_some_onDomain (f : SyncMap nA nB) (i : f.domain) :
    f.partner i.1 = some (f.onDomain i) :=
  (Option.some_get (mem_domain.mp i.2)).symm

/-- **Monotonicity, raw form.** On the domain the sync map is weakly
monotone — directly from the `SyncMap.weakly_monotone` field. -/
lemma onDomain_le_onDomain (f : SyncMap nA nB) {i i' : Fin nA}
    (hi : i ∈ f.domain) (hi' : i' ∈ f.domain) (h : i ≤ i') :
    f.onDomain ⟨i, hi⟩ ≤ f.onDomain ⟨i', hi'⟩ :=
  f.weakly_monotone i i' h _ (f.partner_eq_some_onDomain ⟨i, hi⟩) _
    (f.partner_eq_some_onDomain ⟨i', hi'⟩)

/-- **Monotonicity, packaged.** The domain-restricted sync map is a
`Monotone` function — the Lean form of the paper's "weakly monotone
wherever defined" (`step8.tex:2102-2106`). -/
lemma onDomain_monotone (f : SyncMap nA nB) : Monotone f.onDomain := by
  intro a b hab
  exact f.onDomain_le_onDomain a.2 b.2 hab

/-- **Total extension to all chain indices.** `f.extend d` sends each
defined index to its genuine partner and each orphan to a fallback
`d`. Total on `Fin nA`; agrees with `onDomain` on the domain. -/
def extend (f : SyncMap nA nB) (d : Fin nB) : Fin nA → Fin nB :=
  fun i => (f.partner i).getD d

lemma extend_eq_onDomain (f : SyncMap nA nB) (d : Fin nB) (i : f.domain) :
    f.extend d i.1 = f.onDomain i := by
  rw [extend, f.partner_eq_some_onDomain i, Option.getD_some]

lemma extend_eq_default_of_isOrphan (f : SyncMap nA nB) (d : Fin nB)
    {i : Fin nA} (h : f.IsOrphan i) : f.extend d i = d := by
  rw [extend, h, Option.getD_none]

/-- When there are no chain-tail orphans the extended map needs no
fallback and is `Monotone` on *all* of `Fin nA`. -/
lemma extend_monotone_of_orphans_empty (f : SyncMap nA nB) (d : Fin nB)
    (h : f.orphans = ∅) : Monotone (f.extend d) := by
  intro i i' hii'
  have hi : i ∈ f.domain :=
    not_mem_orphans_iff_mem_domain.mp (by rw [h]; simp)
  have hi' : i' ∈ f.domain :=
    not_mem_orphans_iff_mem_domain.mp (by rw [h]; simp)
  rw [f.extend_eq_onDomain d ⟨i, hi⟩, f.extend_eq_onDomain d ⟨i', hi'⟩]
  exact f.onDomain_le_onDomain hi hi' hii'

end SyncMap

namespace ChainLiftData

variable {α : Type*} [PartialOrder α] [Fintype α] (D : ChainLiftData α)

/-! ### §3 — Orphan inclusion at the chain level -/

/-- **Reference-chain orphan indices.** The band `L_k` is anchored at
`a_k ∈ A` and reads off `b_{f_AB(k)}, c_{f_AC(k)}`; `a_k` is a sync
orphan exactly when `f_AB` *or* `f_AC` is undefined at `k`. The
ground-set `X^exc_sync` (sub-ticket S7-F-A) is the chain image of
this index set together with `f_BC`'s orphans. -/
def refOrphans : Finset (Fin D.triple.A.length) :=
  D.fAB.orphans ∪ D.fAC.orphans

/-- The band-anchor orphan count is bounded by the `f_AB`/`f_AC`
orphan counts — unconditional, from the bare structure. -/
lemma refOrphans_card_le :
    D.refOrphans.card ≤ D.fAB.orphans.card + D.fAC.orphans.card := by
  unfold refOrphans
  exact Finset.card_union_le _ _

/-- An A-index off `refOrphans` is in `f_AB`'s domain — the band
anchor map is total on `X \ X^exc_sync`. -/
lemma fAB_mem_domain_of_not_refOrphan {k : Fin D.triple.A.length}
    (h : k ∉ D.refOrphans) : k ∈ D.fAB.domain := by
  rw [← SyncMap.not_mem_orphans_iff_mem_domain]
  exact fun hk => h (Finset.mem_union_left _ hk)

/-- An A-index off `refOrphans` is in `f_AC`'s domain. -/
lemma fAC_mem_domain_of_not_refOrphan {k : Fin D.triple.A.length}
    (h : k ∉ D.refOrphans) : k ∈ D.fAC.domain := by
  rw [← SyncMap.not_mem_orphans_iff_mem_domain]
  exact fun hk => h (Finset.mem_union_right _ hk)

/-! ### §4 — The `|X^exc_sync| ≤ K_bw` bound, made explicit

Per the Piece-3 design note (Resolution A): the bare `ChainLiftData`
carries **no** invariant tying the orphan count to `K_bw`, so the
paper's per-chain bound `|X^exc_sync| ≤ K_bw` (`step8.tex:2053`) is
**not** provable here. Rather than fabricate a proof, the bound is
made explicit as a named predicate — a downstream hypothesis pinned
at the bridge call site via `hCex` (Resolution A), or a soundness
field of a strengthened structure (Resolution B). -/

/-- **The paper's per-chain orphan bound, as a hypothesis.** Each of
the three sync maps has at most `K_bw` chain-tail orphans
(`step8.tex:2053`). Each conjunct is a decidable `Nat` comparison,
hence checkable on any concrete witness (see §6). -/
def BoundedSyncOrphans : Prop :=
  D.fAB.orphans.card ≤ D.K_bw ∧
    D.fAC.orphans.card ≤ D.K_bw ∧
    D.fBC.orphans.card ≤ D.K_bw

/-- **Paper item (i), `X^exc_sync` part.** Under `BoundedSyncOrphans`
the total chain-tail orphan count is `≤ 3·K_bw` — the `O_T(1)` bound
the bridge's depth estimate consumes. Any ground-set `X^exc_sync`
assembled from these orphan indices (sub-ticket S7-F-A) inherits
`|X^exc_sync| ≤ 3·K_bw`, since a chain image only shrinks
cardinality. -/
lemma orphan_count_le_of_bounded (h : D.BoundedSyncOrphans) :
    D.fAB.orphans.card + D.fAC.orphans.card + D.fBC.orphans.card
      ≤ 3 * D.K_bw := by
  obtain ⟨h1, h2, h3⟩ := h
  omega

/-! ### §5 — The band-assembly-ready wired maps -/

/-- **`f_AB` wired** — for a non-orphan band anchor `a_k`, the
`B`-chain index `f_AB(k)`. Total on `X \ X^exc_sync`; consumed by the
band assembly `L_k := {a_k, b_{f_AB(k)}, c_{f_AC(k)}}`. -/
def fABwired {k : Fin D.triple.A.length} (h : k ∉ D.refOrphans) :
    Fin D.triple.B.length :=
  D.fAB.onDomain ⟨k, D.fAB_mem_domain_of_not_refOrphan h⟩

/-- **`f_AC` wired** — the `C`-chain index `f_AC(k)` for a non-orphan
band anchor. -/
def fACwired {k : Fin D.triple.A.length} (h : k ∉ D.refOrphans) :
    Fin D.triple.C.length :=
  D.fAC.onDomain ⟨k, D.fAC_mem_domain_of_not_refOrphan h⟩

/-- **Monotonicity of the wired `f_AB`, propagated to the poset.**
For non-orphan anchors `k ≤ k'`, the synchronized `B`-elements stay
ordered: `b_{f_AB(k)} ≤ b_{f_AB(k')}`. This is the index-level weak
monotonicity (`SyncMap.onDomain_le_onDomain`) composed with the
strict monotonicity of chain `B` — the input the band assembly's
(L4) verification (`step8.tex:2153-2167`) consumes. -/
lemma fABwired_monotone {k k' : Fin D.triple.A.length}
    (h : k ∉ D.refOrphans) (h' : k' ∉ D.refOrphans) (hkk' : k ≤ k') :
    D.triple.B.elem (D.fABwired h) ≤ D.triple.B.elem (D.fABwired h') :=
  D.triple.B.strictMono.monotone
    (D.fAB.onDomain_le_onDomain (D.fAB_mem_domain_of_not_refOrphan h)
      (D.fAB_mem_domain_of_not_refOrphan h') hkk')

/-- **Monotonicity of the wired `f_AC`, propagated to the poset.**
For non-orphan anchors `k ≤ k'`, `c_{f_AC(k)} ≤ c_{f_AC(k')}`. -/
lemma fACwired_monotone {k k' : Fin D.triple.A.length}
    (h : k ∉ D.refOrphans) (h' : k' ∉ D.refOrphans) (hkk' : k ≤ k') :
    D.triple.C.elem (D.fACwired h) ≤ D.triple.C.elem (D.fACwired h') :=
  D.triple.C.strictMono.monotone
    (D.fAC.onDomain_le_onDomain (D.fAC_mem_domain_of_not_refOrphan h)
      (D.fAC_mem_domain_of_not_refOrphan h') hkk')

end ChainLiftData

/-! ### §6 — Non-triviality certificates on the F7a concrete witness

The wiring above is exercised against `gridChainLiftData`
(`ConcreteChainLiftData.lean`, mg-974c) — a genuine width-3 non-chain
poset with a real chain-tail orphan. These certificates discharge the
ticket's non-triviality bar: the orphan handling carries genuine
content, not a vacuous `∅`. -/

namespace GridChainLift

/-- `f_AB` has no chain-tail orphans — it is total. -/
theorem gridChainLiftData_fAB_orphans :
    gridChainLiftData.fAB.orphans = ∅ := by decide

/-- `f_BC` has no chain-tail orphans — it is total. -/
theorem gridChainLiftData_fBC_orphans :
    gridChainLiftData.fBC.orphans = ∅ := by decide

/-- `f_AC` has a **genuine** chain-tail orphan — the band anchor
`a_0 = (0,0)` whose chain potential `0` is more than `K_bw = 1` from
every `C`-element (`gridChainLiftData_orphan_forced`). The orphan
handling is non-vacuous. -/
theorem gridChainLiftData_fAC_has_orphan :
    gridChainLiftData.fAC.orphans.Nonempty := by decide

/-- `f_AC` has *exactly one* chain-tail orphan. -/
theorem gridChainLiftData_fAC_orphan_card :
    gridChainLiftData.fAC.orphans.card = 1 := by decide

/-- The genuine orphan is concretely the band anchor `a_0`. -/
theorem gridChainLiftData_fAC_orphan_zero :
    gridChainLiftData.fAC.IsOrphan ⟨0, by decide⟩ := by decide

/-- **The orphan bound holds on the genuine witness** — each sync map
has at most `K_bw = 1` chain-tail orphans (`f_AC` has exactly one).
`BoundedSyncOrphans` is satisfiable and tight. -/
theorem gridChainLiftData_boundedSyncOrphans :
    gridChainLiftData.BoundedSyncOrphans :=
  ⟨by decide, by decide, by decide⟩

/-- Paper item (i) is genuine on the witness: the total chain-tail
orphan count `1 ≤ 3·K_bw = 3`. -/
theorem gridChainLiftData_orphan_count :
    gridChainLiftData.fAB.orphans.card + gridChainLiftData.fAC.orphans.card
        + gridChainLiftData.fBC.orphans.card ≤ 3 * gridChainLiftData.K_bw :=
  gridChainLiftData.orphan_count_le_of_bounded
    gridChainLiftData_boundedSyncOrphans

/-- **The wired maps are total off the orphan set.** Band anchors
`a_1`, `a_2` are not orphans, so `f_AB` and `f_AC` both deliver a
partner there — `fABwired`/`fACwired` are well-defined. -/
theorem gridChainLiftData_wired_total :
    (⟨1, by decide⟩ : Fin gridChainLiftData.triple.A.length) ∉
      gridChainLiftData.refOrphans ∧
    (⟨2, by decide⟩ : Fin gridChainLiftData.triple.A.length) ∉
      gridChainLiftData.refOrphans :=
  ⟨by decide, by decide⟩

/-- **The wired `f_AB` is genuinely non-constant** on the witness:
non-orphan anchors `a_1`, `a_2` map to *distinct* `B`-elements
(`b_{f_AB(1)} = (1,0) ≠ (1,1) = b_{f_AB(2)}`). The monotonicity
content carried by `fABwired_monotone` is real, not vacuous. -/
theorem gridChainLiftData_fABwired_genuine :
    gridChainLiftData.triple.B.elem
        (gridChainLiftData.fABwired gridChainLiftData_wired_total.1) ≠
      gridChainLiftData.triple.B.elem
        (gridChainLiftData.fABwired gridChainLiftData_wired_total.2) := by
  decide

end GridChainLift

end Step8
end OneThird
