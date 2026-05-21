/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.ExceptionalSet
import OneThird.Step8.SyncMaps
import OneThird.Step8.LayeredReduction

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Step 8 — S7-F bridge sub-ticket C: the `LayeredDecomposition` on `X ∖ X^exc`

This file is **FULL REFACTOR Phase-2, Piece 3 (the S7-F bridge),
sub-ticket C** (work item `mg-bcc9`). It ports **item (ii) of paper
`lem:layered-from-step7`** (`step8.tex:2066-2167`): assemble the
`LayeredDecomposition` on the ground set `X ∖ X^exc` from a
`ChainLiftData α` and verify the layered invariants `(L1)`–`(L4)` of
`def:layered` (`step8.tex:1983-2007`).

## What the paper does (`step8.tex:2098-2167`, item (ii))

After removing the exceptional set `X^exc` (sub-ticket A), the paper
assembles a band map and verifies, with `w := K_bw + 2`:

* `(L1)` each band `L_k` has `|L_k| ≤ 3` and is an antichain;
* `(L2)` `i < j − w ⇒ x <_P y` for `x ∈ L_i`, `y ∈ L_j`;
* `(L3)` `|i − j| > w ⇒ x, y` comparable;
* `(L4)` cross-band comparabilities are directed upward.

## The band map — the chain potential, normalised

The paper's band assembly `L_k := {a_k, b_{f_AB(k)}, c_{f_AC(k)}}`
groups chain elements of *close potential* — the synchronization maps
`f_••` are themselves defined as the potential-argmin alignment
(`step8.tex:2098-2106`). The honest Lean realisation of "the band of
`z`" is therefore the **chain potential of `z`, normalised to a
`1`-indexed `ℕ` band label**:

```
  bridgeBand z := (a(z) − a_min).toNat + 1.
```

This is exactly the band map of the genuine in-tree witness
`GridChainLift.gridLayered` (`ConcreteChainLiftData.lean:303`,
`band = i+j+1 = potFun+1`), which mg-974c established as the target
object shape. The interaction width is `w := K_bw + 2` (paper
`step8.tex:2121`); `w ≤ 4` follows from `K_bw ≤ 2` (`lem:bandwidth`).
`w` is a genuine function of the genuine field `K_bw` and is genuinely
consumed by `forced_lt` — *not* an inert `4 ≤ 4` literal (the
Checkpoint-3 Finding-D bar).

## The Resolution-A obligation — `PotPosetMono`

`(L2)`, `(L4)` and the `(L1)` antichain clause all need the potential
to be strictly increasing along **every comparable cover of the
poset**, not merely along the three Dilworth chains. The bare
`ChainPotential` (`ChainPotentials.lean:267`) carries strict
monotonicity along the chains *only* — cross-chain comparabilities
(which genuinely occur: e.g. `(0,0) <_P (1,1)` in the grid) are
unconstrained. This is paper `prop:71` content.

Per the **Piece-3 design note (Resolution A)** — the pattern of
sub-ticket A's `ExcBudget` and sub-ticket B's `BoundedSyncOrphans` —
this missing soundness fact is **not fabricated** and the
`ChainLiftData` structure is **not strengthened** (that would be
Resolution B). It is **made explicit** as the named, decidable
predicate `ChainLiftData.PotPosetMono`, a downstream hypothesis to be
discharged at the bridge call site from `hCex` + the Steps-1-7
cascade (sub-ticket S7-F-Z). `PotPosetMono` is genuinely satisfiable
(the grid satisfies it, `§5`) and genuinely fails for a pathological
bare structure, so it is a real soundness filter.

**The `(L2)` decision point closes under Resolution A.** The
load-bearing `forced_lt` step does *not* need a strengthened
structure: `X^exc_band` (sub-ticket A) was *defined* as exactly the
bandwidth-excess locus, so on the complement `X ∖ X^exc` every
incomparable pair has potential gap `≤ K_bw < w` — the comparability
half of `(L2)` is a structural tautology of the complement, and only
the *direction* needs `PotPosetMono`. No escalation to Resolution B
is required.

## Cross-references

* `lean/OneThird/Step8/ExceptionalSet.lean` — `Xexc` (sub-ticket A);
  `Xexc_band`'s definition is the `(L2)` lever.
* `lean/OneThird/Step8/SyncMaps.lean` — sub-ticket B; `Xexc_sync`
  (orphans) is folded into `Xexc`, so `X ∖ X^exc` is orphan-free.
* `lean/OneThird/Step8/LayeredReduction.lean:113` —
  `LayeredDecomposition` (the structure assembled here).
* `lean/OneThird/Step8/ConcreteChainLiftData.lean` —
  `gridChainLiftData` / `gridLayered`, the F7a witnesses the `§5`
  discharge instantiates against.
* `step8.tex:1983-2007` — `def:layered`, the `(L1)`–`(L4)` invariants.
* `step8.tex:2066-2167` — `lem:layered-from-step7` item (ii).

No `sorry`. No new `axiom` (`AXIOMS.md` unchanged).
-/

namespace OneThird
namespace Step8

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
  [DecidableLE α]

/-! ### §1 — The potential range and the `prop:71` obligation -/

/-- The set of potential values taken on `α`. -/
noncomputable def potImage (D : ChainLiftData α) : Finset ℤ :=
  Finset.univ.image D.pot.a

/-- The minimum potential value (`0` if `α` is empty). The band map
normalises `a` against this floor so band labels are `1`-indexed
naturals. -/
noncomputable def potMin (D : ChainLiftData α) : ℤ :=
  if h : (potImage D).Nonempty then (potImage D).min' h else 0

/-- The maximum potential value (`0` if `α` is empty). Bounds the
depth `K` of the layering. -/
noncomputable def potMax (D : ChainLiftData α) : ℤ :=
  if h : (potImage D).Nonempty then (potImage D).max' h else 0

lemma mem_potImage (D : ChainLiftData α) (x : α) :
    D.pot.a x ∈ potImage D :=
  Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- `potMin` is a genuine lower bound for the potential. -/
lemma potMin_le (D : ChainLiftData α) (x : α) :
    potMin D ≤ D.pot.a x := by
  have hx := mem_potImage D x
  have hne : (potImage D).Nonempty := ⟨_, hx⟩
  rw [potMin, dif_pos hne]
  exact Finset.min'_le _ _ hx

/-- `potMax` is a genuine upper bound for the potential. -/
lemma le_potMax (D : ChainLiftData α) (x : α) :
    D.pot.a x ≤ potMax D := by
  have hx := mem_potImage D x
  have hne : (potImage D).Nonempty := ⟨_, hx⟩
  rw [potMax, dif_pos hne]
  exact Finset.le_max' _ _ hx

/-- **`prop:71` poset-monotonicity of the chain potential**
(`step8.tex:2159-2167`, `step7.tex:1004-1013`).

The chain potential is strictly increasing along **every** comparable
cover of the poset `α`, not just along the three Dilworth chains.

This is **not** a consequence of the bare `ChainLiftData`: the
`ChainPotential` structure (`ChainPotentials.lean:267`) carries strict
monotonicity along the chains *only*, and genuine width-3 posets have
cross-chain comparabilities (`(0,0) <_P (1,1)` in the grid) which the
bare potential leaves unconstrained. Per the Piece-3 design note
(Resolution A) it is made explicit here as a named hypothesis — the
S7-F-C analogue of `ExcBudget` (sub-ticket A) and `BoundedSyncOrphans`
(sub-ticket B) — to be discharged downstream (S7-F-Z) from `hCex` plus
the Steps-1-7 cascade. It is a decidable predicate, hence checkable on
any concrete witness (see `§5`). -/
def ChainLiftData.PotPosetMono (D : ChainLiftData α) : Prop :=
  ∀ x y : α, x < y → D.pot.a x < D.pot.a y

/-! ### §2 — `(L1)` antichain-size: potential level sets have `≤ 3` elements

The bands of the bridge decomposition are the level sets of the chain
potential. Each such level set has `≤ 3` elements — a structural fact
of the **bare** `ChainLiftData`: the potential is strictly monotone
(hence injective) along each Dilworth chain, so a fixed potential
value is attained at most once per chain, and the three chains cover
`α`. This is the `|L_k| ≤ 3` half of paper `(L1)` (`step8.tex:2123`). -/

/-- A potential value `v` is attained at most once on a Dilworth chain
whose chain-restricted potential is injective. -/
lemma chain_level_card_le_one (D : ChainLiftData α) (v : ℤ)
    (C : IndexedChain α)
    (hinj : Function.Injective (fun i : Fin C.length => D.pot.a (C.elem i))) :
    ((Finset.univ.filter (fun x : α => D.pot.a x = v)) ∩ C.support).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_inter, Finset.mem_filter, IndexedChain.mem_support] at hx hy
  obtain ⟨⟨_, hxv⟩, i, hxi⟩ := hx
  obtain ⟨⟨_, hyv⟩, j, hyj⟩ := hy
  have hij : (fun i : Fin C.length => D.pot.a (C.elem i)) i =
      (fun i : Fin C.length => D.pot.a (C.elem i)) j := by
    simp only []
    rw [hxi, hyj, hxv, hyv]
  have := hinj hij
  rw [← hxi, ← hyj, this]

/-- **`(L1)` antichain-size, `|L_k| ≤ 3`.** Every potential level set
has at most three elements. Proved from the bare `ChainLiftData`: the
chain potential is injective on each of the three Dilworth chains
(`ChainPotential.injective_on_{A,B,C}`) and the chains cover `α`
(`ChainTriple.cover`). -/
theorem potLevel_card_le (D : ChainLiftData α) (v : ℤ) :
    (Finset.univ.filter (fun x : α => D.pot.a x = v)).card ≤ 3 := by
  have hA := chain_level_card_le_one D v D.triple.A D.pot.injective_on_A
  have hB := chain_level_card_le_one D v D.triple.B D.pot.injective_on_B
  have hC := chain_level_card_le_one D v D.triple.C D.pot.injective_on_C
  set F := Finset.univ.filter (fun x : α => D.pot.a x = v) with hF
  have hcover : F ⊆ (F ∩ D.triple.A.support) ∪ (F ∩ D.triple.B.support)
      ∪ (F ∩ D.triple.C.support) := by
    intro x hx
    rcases D.triple.cover x with hxA | hxB | hxC
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_inter.mpr ⟨hx, IndexedChain.mem_support.mpr hxA⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_inter.mpr ⟨hx, IndexedChain.mem_support.mpr hxB⟩))))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_inter.mpr ⟨hx, IndexedChain.mem_support.mpr hxC⟩))
  have hcard := Finset.card_le_card hcover
  have hu1 := Finset.card_union_le ((F ∩ D.triple.A.support)
    ∪ (F ∩ D.triple.B.support)) (F ∩ D.triple.C.support)
  have hu2 := Finset.card_union_le (F ∩ D.triple.A.support)
    (F ∩ D.triple.B.support)
  omega

/-! ### §3 — The band map and the `LayeredDecomposition` on `X ∖ X^exc` -/

/-- The potential of `x`, normalised against the floor `potMin` to a
natural number. The band label is `potShift + 1`. -/
noncomputable def potShift (D : ChainLiftData α) (x : α) : ℕ :=
  (D.pot.a x - potMin D).toNat

/-- `potShift` cast back to `ℤ` is the genuine normalised potential —
the normalisation loses no information (the potential is `≥ potMin`). -/
lemma potShift_cast (D : ChainLiftData α) (x : α) :
    (potShift D x : ℤ) = D.pot.a x - potMin D :=
  Int.toNat_of_nonneg (by have := potMin_le D x; omega)

/-- The depth of the layering: the normalised potential range, plus
one (band labels are `1, …, K`). -/
noncomputable def bridgeK (D : ChainLiftData α) : ℕ :=
  (potMax D - potMin D).toNat + 1

/-- **The band map** (`step8.tex:2108-2121`). The band label of an
element of `X ∖ X^exc` is its chain potential, normalised to a
`1`-indexed natural. This is the band map of the genuine in-tree
witness `GridChainLift.gridLayered` (`band = potFun + 1`). -/
noncomputable def bridgeBand (D : ChainLiftData α)
    (z : ↥((Xexc D)ᶜ)) : ℕ :=
  potShift D z.val + 1

/-- An element of `X ∖ X^exc` is not bandwidth-exceptional — it lies
in no incomparable pair of potential gap `> K_bw`. The complement
half of paper `(L2)`. -/
lemma not_mem_Xexc_band_of_mem_compl (D : ChainLiftData α)
    {z : α} (h : z ∈ (Xexc D)ᶜ) : z ∉ Xexc_band D := by
  rw [Finset.mem_compl] at h
  intro hb
  exact h (by rw [Xexc]; exact Finset.mem_union.mpr (Or.inl
    (Finset.mem_union.mpr (Or.inr hb))))

/-- The band label determines the potential value: every element of
band `k` has chain potential `potMin + (k − 1)`. -/
lemma bridgeBand_pot_of_eq (D : ChainLiftData α) {z : ↥((Xexc D)ᶜ)}
    {k : ℕ} (h : bridgeBand D z = k) :
    D.pot.a z.val = potMin D + ((k : ℤ) - 1) := by
  have hc := potShift_cast D z.val
  rw [bridgeBand] at h
  omega

/-- **The S7-F bridge layered decomposition** (paper
`lem:layered-from-step7` item (ii), `step8.tex:2066-2167`).

The `LayeredDecomposition` of the ground set `X ∖ X^exc`, with band
map the normalised chain potential and interaction width
`w := K_bw + 2`. All four `(L1)`–`(L4)` invariants of `def:layered`
are verified:

* `band_size` / `band_antichain` — `(L1)`: bands are potential level
  sets, `≤ 3` elements (`potLevel_card_le`), and antichains (a
  comparable pair would have *strictly* increasing potential by
  `hMono`, so could not share a band);
* `forced_lt` — `(L2)`: if `band x + w < band y` then the potential
  gap exceeds `K_bw`, so an incomparable pair would put `x` in
  `X^exc_band` — impossible on `X ∖ X^exc`; hence `x, y` are
  comparable, and `hMono` fixes the direction `x <_P y`;
* `cross_band_lt_upward` — `(L4)`: `x <_P y` strictly increases the
  potential (`hMono`), hence the band label.

`(L3)` is the derived corollary `LayeredDecomposition.comparable_of_far`.

The single hypothesis `hMono : D.PotPosetMono` is the Resolution-A
named obligation (paper `prop:71`); see the module docstring. -/
noncomputable def bridgeLayered (D : ChainLiftData α)
    (hMono : D.PotPosetMono) : LayeredDecomposition (↥((Xexc D)ᶜ)) where
  K := bridgeK D
  w := D.K_bw + 2
  band := bridgeBand D
  band_pos z := by rw [bridgeBand]; omega
  band_le z := by
    rw [bridgeBand, bridgeK]
    have : potShift D z.val ≤ (potMax D - potMin D).toNat := by
      rw [potShift]
      exact Int.toNat_le_toNat (by have := le_potMax D z.val; omega)
    omega
  band_size k := by
    classical
    set T : Finset (↥((Xexc D)ᶜ)) :=
      (Finset.univ : Finset (↥((Xexc D)ᶜ))).filter
        (fun z => bridgeBand D z = k) with hT
    have hinj : Function.Injective (fun z : ↥((Xexc D)ᶜ) => z.val) :=
      Subtype.val_injective
    have hSub : T.image (fun z : ↥((Xexc D)ᶜ) => z.val) ⊆
        Finset.univ.filter
          (fun x : α => D.pot.a x = potMin D + ((k : ℤ) - 1)) := by
      intro a ha
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha
      obtain ⟨z, hz, hzeq⟩ := ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hzeq]
      exact bridgeBand_pot_of_eq D hz
    calc T.card
        = (T.image (fun z : ↥((Xexc D)ᶜ) => z.val)).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.univ.filter
            (fun x : α => D.pot.a x = potMin D + ((k : ℤ) - 1))).card :=
          Finset.card_le_card hSub
      _ ≤ 3 := potLevel_card_le D _
  band_antichain k := by
    classical
    intro a ha b hb hne hle
    simp only [Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at ha hb
    have hlt : a < b := lt_of_le_of_ne hle hne
    have hlt_val : a.val < b.val := hlt
    have hpot : D.pot.a a.val < D.pot.a b.val := hMono _ _ hlt_val
    have ha' := bridgeBand_pot_of_eq D ha
    have hb' := bridgeBand_pot_of_eq D hb
    rw [ha', hb'] at hpot
    omega
  forced_lt x y h := by
    -- `band x + w < band y` ⇒ potential gap `> K_bw`.
    rw [bridgeBand, bridgeBand] at h
    have hcx := potShift_cast D x.val
    have hcy := potShift_cast D y.val
    have hgap : (D.K_bw : ℤ) < D.pot.a y.val - D.pot.a x.val := by omega
    have hltpot : D.pot.a x.val < D.pot.a y.val := by omega
    -- The forced comparability `x <_P y`.
    by_contra hcon
    by_cases hle : x.val ≤ y.val
    · exact hcon (lt_of_le_of_ne hle
        (fun he => absurd (he ▸ hltpot) (lt_irrefl _)))
    · by_cases hle2 : y.val ≤ x.val
      · have hyx : y.val < x.val :=
          lt_of_le_of_ne hle2 (fun he => hle (le_of_eq he.symm))
        have := hMono _ _ hyx
        omega
      · -- `x.val` and `y.val` incomparable: `x.val ∈ X^exc_band`.
        have hband : x.val ∈ Xexc_band D := by
          rw [mem_Xexc_band]
          exact ⟨y.val, hle, hle2, Or.inr hgap⟩
        exact not_mem_Xexc_band_of_mem_compl D x.2 hband
  cross_band_lt_upward x y h := by
    have hlt_val : x.val < y.val := h
    have hpot : D.pot.a x.val < D.pot.a y.val := hMono _ _ hlt_val
    rw [bridgeBand, bridgeBand]
    have hcx := potShift_cast D x.val
    have hcy := potShift_cast D y.val
    omega

/-! ### §3b — Connection to the synchronization wiring (sub-ticket B)

The exceptional set `X^exc` folds in `X^exc_sync` — the chain-tail
orphans of the synchronization maps (sub-ticket A built `X^exc_sync`
out of sub-ticket B's orphan index sets). Hence the ground set
`X ∖ X^exc` is **orphan-free**: every band anchor `a_k` lying in
`X ∖ X^exc` has defined synchronization partners, so sub-ticket B's
wired maps `ChainLiftData.fABwired`/`fACwired` apply to it. This is
the sense in which the bridge band assembly consumes the synchronized
pairs of sub-ticket B. -/

/-- A band anchor `a_k` lying in `X ∖ X^exc` is **not** a
synchronization orphan of `f_AB` or `f_AC`. The bands of the bridge
decomposition therefore carry genuine synchronized partners. -/
lemma anchor_not_refOrphan (D : ChainLiftData α)
    {k : Fin D.triple.A.length}
    (h : D.triple.A.elem k ∈ (Xexc D)ᶜ) : k ∉ D.refOrphans := by
  rw [Finset.mem_compl] at h
  intro hk
  apply h
  rw [Xexc]
  refine Finset.mem_union.mpr (Or.inr ?_)
  rw [Xexc_sync]
  rw [ChainLiftData.refOrphans, Finset.mem_union] at hk
  rcases hk with hk | hk
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
      (Finset.mem_image_of_mem _ hk))))
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
      (Finset.mem_image_of_mem _ hk))))

/-- **Sub-ticket B's wired maps apply on `X ∖ X^exc`.** Every band
anchor of the ground set `X ∖ X^exc` lies in `f_AB`'s domain, so
`ChainLiftData.fABwired` (sub-ticket B) delivers a genuine
`B`-synchronized partner for it. -/
lemma fAB_defined_on_compl (D : ChainLiftData α)
    {k : Fin D.triple.A.length} (h : D.triple.A.elem k ∈ (Xexc D)ᶜ) :
    k ∈ D.fAB.domain :=
  D.fAB_mem_domain_of_not_refOrphan (anchor_not_refOrphan D h)

/-- Likewise every band anchor of `X ∖ X^exc` lies in `f_AC`'s
domain — `ChainLiftData.fACwired` (sub-ticket B) applies. -/
lemma fAC_defined_on_compl (D : ChainLiftData α)
    {k : Fin D.triple.A.length} (h : D.triple.A.elem k ∈ (Xexc D)ᶜ) :
    k ∈ D.fAC.domain :=
  D.fAC_mem_domain_of_not_refOrphan (anchor_not_refOrphan D h)

/-! ### §4 — The `(L1)`–`(L4)` invariants, named; the `w ≤ 4` cap

The four invariants are the structure fields of `bridgeLayered`; this
section exposes them under the paper's `(L1)`–`(L4)` names and records
the `w = K_bw + 2 ≤ 4` interaction-width cap (paper `step8.tex:2121`,
the third re-pinned bridge cap of MA-Sig §4.2 §E). -/

/-- The interaction width is `K_bw + 2` — a genuine function of the
`ChainLiftData` bandwidth field, *not* an inert literal. -/
@[simp] theorem bridgeLayered_w (D : ChainLiftData α)
    (hMono : D.PotPosetMono) :
    (bridgeLayered D hMono).w = D.K_bw + 2 := rfl

/-- **The interaction-width cap `w ≤ 4`** (`step8.tex:2121`, MA-Sig
§4.2 §E third cap). Since `w = K_bw + 2`, it is exactly `K_bw ≤ 2`
(`lem:bandwidth`). Not an inert `4 ≤ 4`: `forced_lt` genuinely
consumes `w`. -/
theorem bridgeLayered_w_le_four (D : ChainLiftData α)
    (hMono : D.PotPosetMono) (hKbw : D.K_bw ≤ 2) :
    (bridgeLayered D hMono).w ≤ 4 := by
  rw [bridgeLayered_w]; omega

/-- **`(L1)` — antichain size.** Each band has `≤ 3` elements. -/
theorem bridgeLayered_L1_size (D : ChainLiftData α)
    (hMono : D.PotPosetMono) (k : ℕ) :
    (((Finset.univ : Finset (↥((Xexc D)ᶜ))).filter
      (fun z => (bridgeLayered D hMono).band z = k)).card) ≤ 3 :=
  (bridgeLayered D hMono).band_size k

/-- **`(L1)` — antichain.** Each band is an antichain in `X ∖ X^exc`. -/
theorem bridgeLayered_L1_antichain (D : ChainLiftData α)
    (hMono : D.PotPosetMono) (k : ℕ) :
    IsAntichain (· ≤ ·)
      ((((Finset.univ : Finset (↥((Xexc D)ᶜ))).filter
        (fun z => (bridgeLayered D hMono).band z = k))) :
          Set (↥((Xexc D)ᶜ))) :=
  (bridgeLayered D hMono).band_antichain k

/-- **`(L2)` — forced cross-band comparability.** If `x` sits in a
band more than `w` below `y`'s band, then `x <_P y`. The load-bearing
invariant — closed under Resolution A (see the module docstring). -/
theorem bridgeLayered_L2 (D : ChainLiftData α) (hMono : D.PotPosetMono)
    (x y : ↥((Xexc D)ᶜ))
    (h : (bridgeLayered D hMono).band x + (bridgeLayered D hMono).w
      < (bridgeLayered D hMono).band y) : x < y :=
  (bridgeLayered D hMono).forced_lt x y h

/-- **`(L3)` — far-apart bands are comparable.** Derived from `(L2)`
via `LayeredDecomposition.comparable_of_far`: if the band labels of
`x` and `y` differ by more than `w`, then `x` and `y` are comparable
in `X ∖ X^exc`. -/
theorem bridgeLayered_L3 (D : ChainLiftData α) (hMono : D.PotPosetMono)
    (x y : ↥((Xexc D)ᶜ))
    (h : (bridgeLayered D hMono).w <
      max ((bridgeLayered D hMono).band x) ((bridgeLayered D hMono).band y)
        - min ((bridgeLayered D hMono).band x)
          ((bridgeLayered D hMono).band y)) :
    x < y ∨ y < x :=
  (bridgeLayered D hMono).comparable_of_far h

/-- **`(L4)` — cross-band direction.** Any comparability `x <_P y`
runs upward in band index: `band x ≤ band y`. -/
theorem bridgeLayered_L4 (D : ChainLiftData α) (hMono : D.PotPosetMono)
    (x y : ↥((Xexc D)ᶜ)) (h : x < y) :
    (bridgeLayered D hMono).band x ≤ (bridgeLayered D hMono).band y :=
  (bridgeLayered D hMono).cross_band_lt_upward x y h

/-- **Paper `lem:layered-from-step7` item (ii), bundled** — the
ground set `X ∖ X^exc` admits a layered decomposition of interaction
width `≤ 4`. The contract-shaped existence statement (MA-Sig §4.2 §E,
the `L.w ≤ 4` cap). -/
theorem exists_bridgeLayered_w_le_four (D : ChainLiftData α)
    (hMono : D.PotPosetMono) (hKbw : D.K_bw ≤ 2) :
    ∃ L : LayeredDecomposition (↥((Xexc D)ᶜ)), L.w ≤ 4 :=
  ⟨bridgeLayered D hMono, bridgeLayered_w_le_four D hMono hKbw⟩

/-! ### §5 — Grid discharge: a concrete, non-degenerate verification

The sub-ticket-C analogue of `ExceptionalSet.grid_Xexc_card_le`
(sub-ticket A) and `SyncMaps.gridChainLiftData_boundedSyncOrphans`
(sub-ticket B). On the genuine width-3 non-chain carrier
`Fin 3 × Fin 3` with the F7a witness `gridChainLiftData`
(`ConcreteChainLiftData.lean`, mg-974c):

* the Resolution-A obligation `PotPosetMono` **holds** — `grid_PotPosetMono`;
* the bridge produces a genuine `LayeredDecomposition` on the
  8-element ground set `Grid ∖ {(0,0)}` with interaction width
  `w = K_bw + 2 = 3 ≤ 4` and depth `K = 5`;
* the band map is **non-degenerate** — it takes distinct values on
  distinct anti-diagonals (`grid_bridgeLayered_band_nonconstant`),
  so `w ≤ 4` is a genuine invariant tied to a real band map, not an
  inert `4 ≤ 4` (the Checkpoint-3 Finding-D bar). -/

namespace GridChainLift

/-- **The Resolution-A obligation is satisfiable.** The grid's chain
potential `potFun (i,j) = i + j` is strictly monotone along *every*
comparable cover of the grid order, not merely along the columns. -/
theorem grid_PotPosetMono : gridChainLiftData.PotPosetMono := by
  unfold ChainLiftData.PotPosetMono
  decide

/-- The grid bridge layered decomposition — the genuine output object
on the 8-element ground set `Grid ∖ X^exc`. -/
noncomputable def gridBridgeLayered :
    LayeredDecomposition (↥((Xexc gridChainLiftData)ᶜ)) :=
  bridgeLayered gridChainLiftData grid_PotPosetMono

/-- The grid bridge has interaction width `w = 3` — genuinely
`K_bw + 2` with the *tight* `K_bw = 1` (`gridChainLiftData_bandwidth_tight`),
not an inert literal. -/
theorem grid_bridgeLayered_w : gridBridgeLayered.w = 3 := by decide

/-- **`w ≤ 4` discharged on the grid F7a witness**, with no free
hypothesis. -/
theorem grid_bridgeLayered_w_le_four : gridBridgeLayered.w ≤ 4 := by
  rw [grid_bridgeLayered_w]; decide

/-- The grid bridge has depth `K = 5` — the genuine normalised
potential range `{0,…,4}`. The layering is non-trivial (depth `> 1`). -/
theorem grid_bridgeLayered_K : gridBridgeLayered.K = 5 := by decide

/-- **The band map is genuinely non-constant.** The grid elements
`(0,1)` and `(2,2)` (both off `X^exc = {(0,0)}`) land in *different*
bands — `w ≤ 4` is tied to a real, non-inert band map. -/
theorem grid_bridgeLayered_band_nonconstant :
    gridBridgeLayered.band ⟨(0, 1), by rw [Finset.mem_compl, grid_Xexc]; decide⟩
      ≠ gridBridgeLayered.band
        ⟨(2, 2), by rw [Finset.mem_compl, grid_Xexc]; decide⟩ := by
  decide

/-- **Paper item (ii) discharged on the grid F7a witness** — the
8-element ground set `Grid ∖ X^exc` admits a layered decomposition of
interaction width `≤ 4`. The sub-ticket-C acceptance certificate. -/
theorem grid_exists_bridgeLayered :
    ∃ L : LayeredDecomposition (↥((Xexc gridChainLiftData)ᶜ)), L.w ≤ 4 :=
  exists_bridgeLayered_w_le_four gridChainLiftData grid_PotPosetMono
    (by decide)

end GridChainLift

end Step8
end OneThird
