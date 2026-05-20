/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step1.GroundSet
import OneThird.Step1.BKMoves
import OneThird.Step1.BadSet
import OneThird.Step1.Corollaries

/-!
# Step 1 — assembly: the four-part local interface theorem and its corollaries

This file is the **assembly stage of the Step 1 Lean port** of the
Option A' FULL REFACTOR (`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md`,
mg-d8c7 §2.1; work item mg-794c, ticket OneThird-S1-D).  It integrates
the three parallel Wave-1 ports

* **S1-A** (mg-30e3, `Step1/GroundSet.lean`) — parts (i) coordinate map
  and (ii) raw-fiber decomposition;
* **S1-B** (mg-2e24, `Step1/BKMoves.lean` + `Step1/BadSet.lean`) —
  part (iii) BK-move classification and part (iv) bad-set structural
  backbone;
* **S1-C** (mg-bcf2, `Step1/Overlap.lean` + `Step1/Corollaries.lean`) —
  the commuting-square / commuting-cube cores of `cor:overlap` and
  `cor:triple-overlap`,

into the single four-part **local interface theorem** `thm:interface`
(`step1.tex:144-195`) and its two corollaries.

## Main results

* `InterfaceConclusion x y` — the four-part conclusion of `thm:interface`
  as a named proposition: (i) the coordinate map into the `(t+1)×(t+1)`
  grid, (ii) the raw-fiber decomposition `L(P) = F_{x,y} ⊔ Bad_{x,y}`,
  (iii) the BK-move classification, (iv) the bad-set structural backbone.
* `thm_interface` — the assembled local interface theorem: for a
  width-3 poset and a rich pair `(x, y)`, `InterfaceConclusion x y`
  holds.  This is the **headline Step 1 deliverable**.
* `thm_interface_nonvacuous` — the mg-794c acceptance witness:
  `thm_interface` instantiates non-vacuously at the concrete width-3
  non-chain poset `Antichain3` (no Subsingleton-on-empty baseline).
* `IsInterfaceMove x y L hk` — the predicate "the BK move of `L` at
  position `k` belongs to the `(x, y)` interface": its swapped pair has
  both elements in `{x, y} ∪ C(x, y)` and at least one in `{x, y}`.
  This is exactly the move shape established by part (iii) for every
  coordinate-changing move.
* `disjointPos_of_no_adjacency` — the **part-(iii) → corollaries
  bridge**: from interaction-locus exclusion, an `(x, y)`-interface
  move and a `(u, v)`-interface move sit at disjoint positions.
* `cor_overlap` — `cor:overlap` assembled: on a regular overlap, two
  interface moves span a commuting `2×2` BK square.
* `cor_triple_overlap` — `cor:triple-overlap` assembled: on a regular
  triple overlap, three interface moves span a commuting `2×2×2` BK
  cube.

## Part (iv) — a deliberate faithfulness decision

S1-B (mg-2e24) surfaced a paper-side imprecision: `step1.tex:308-311`
claims the incomparability locus `I(z)` of an *external* element `z`
has **length** `≤ 2`, but a literal width-3 argument yields only the
**order-convexity** of `I(z)` (a width-4 antichain would force
`z ∈ commonNbhd x y`, contradicting externality).  S1-D resolves this
by **landing the order-convexity form** (`incompLocus_ordConvex`) as
part (iv) of `thm_interface`, *not* the unprovable `|I(z)| ≤ 2` length
bound.  This is faithful: per S1-B's analysis the qualitative
"`Bad_{x,y}` is one-dimensional" conclusion — and every downstream use
in `cor:overlap` / `cor:triple-overlap` — survives with the weaker
`O(n · t²)` bad-set bound the convexity form supports.  No axiom and
no `sorry` are introduced.  See `docs/state-S1-B-bkmoves-badset-Session1.md`
and `docs/state-S1-D-Session1.md`.

## Cross-references

* `step1.tex:144-195` — `thm:interface`, the four-part target.
* `step1.tex:429` — `cor:overlap`.
* `step1.tex:516` — `cor:triple-overlap`.
* `OneThird/Step1/GroundSet.lean`, `BKMoves.lean`, `BadSet.lean`,
  `Overlap.lean`, `Corollaries.lean` — the S1-A/B/C ports assembled here.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.1 — piece-1 spec.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — The four-part conclusion of `thm:interface` -/

/-- **The four-part conclusion of the local interface theorem**
(`thm:interface`, `step1.tex:144-195`), as a named proposition over a
pair `(x, y)`.

* **Part (i)** — coordinate map: the common-neighbour set is a chain
  and the coordinate map `π_{x,y}` lands in the `(t+1)×(t+1)` grid
  `{0,…,t}²`.
* **Part (ii)** — raw-fiber decomposition: the raw fibers cover
  `V(bkGraph α)` and `L(P) = F_{x,y} ⊔ Bad_{x,y}`.
* **Part (iii)** — BK-move classification: every BK move either fixes
  `(i, j, σ)`, flips `σ` only, shifts `i` by `±1` only, or shifts `j`
  by `±1` only.
* **Part (iv)** — bad-set structural backbone: the common neighbours
  are pairwise comparable; the incomparability locus `I(z)` is
  order-convex; there are `n - t - 2` external elements; and a raw
  fiber confined to a single axis-parallel line carries at most
  `t + 1` extensions.  (See the module note on the part-(iv)
  faithfulness decision.) -/
def InterfaceConclusion (x y : α) : Prop :=
  -- Part (i): coordinate map into the (t+1)×(t+1) grid {0,…,t}².
  (IsChain (· ≤ ·) (commonNbhd x y) ∧
   ∀ L : LinearExt α,
     localCoord x y L ∈
       (Finset.range (commonNbhdLength x y + 1)) ×ˢ
         (Finset.range (commonNbhdLength x y + 1))) ∧
  -- Part (ii): raw-fiber decomposition L(P) = F_{x,y} ⊔ Bad_{x,y}.
  ((Finset.univ : Finset (LinearExt α)).biUnion
      (fun L₀ => rawFiber x y L₀ (signMarker x y L₀)) = Finset.univ ∧
   goodFiberSet x y ∪ badSet x y = Finset.univ ∧
   Disjoint (goodFiberSet x y) (badSet x y)) ∧
  -- Part (iii): BK-move classification.
  (∀ L L' : LinearExt α, BKAdj L L' →
    (iCoord x y L = iCoord x y L' ∧ jCoord x y L = jCoord x y L' ∧
        signMarker x y L = signMarker x y L') ∨
    (signMarker x y L = ! signMarker x y L' ∧
        iCoord x y L = iCoord x y L' ∧ jCoord x y L = jCoord x y L') ∨
    ((iCoord x y L' = iCoord x y L + 1 ∨ iCoord x y L = iCoord x y L' + 1) ∧
        jCoord x y L = jCoord x y L' ∧
        signMarker x y L = signMarker x y L') ∨
    ((jCoord x y L' = jCoord x y L + 1 ∨ jCoord x y L = jCoord x y L' + 1) ∧
        iCoord x y L = iCoord x y L' ∧
        signMarker x y L = signMarker x y L')) ∧
  -- Part (iv): bad-set structural backbone ("Bad_{x,y} is one-dimensional").
  ((∀ a ∈ commonNbhdFinset x y, ∀ b ∈ commonNbhdFinset x y, a ≤ b ∨ b ≤ a) ∧
   (∀ z c c' c'' : α,
      c ∈ incompLocus x y z → c'' ∈ incompLocus x y z →
      c' ∈ commonNbhdFinset x y → c ≤ c' → c' ≤ c'' →
      c' ∈ incompLocus x y z) ∧
   (externalFinset x y).card = Fintype.card α - commonNbhdLength x y - 2 ∧
   (∀ (F : Finset (LinearExt α)) (i₀ : ℕ),
      (∀ L₁ ∈ F, ∀ L₂ ∈ F,
        localCoord x y L₁ = localCoord x y L₂ →
        signMarker x y L₁ = signMarker x y L₂ → L₁ = L₂) →
      (∃ ε : Bool, ∀ L ∈ F, signMarker x y L = ε) →
      (∀ L ∈ F, iCoord x y L = i₀) →
      F.card ≤ commonNbhdLength x y + 1))

/-! ### §2 — The assembled local interface theorem -/

/-- **The local interface theorem** `thm:interface` (`step1.tex:144-195`),
assembled in full.

For a width-3 poset `α` and a rich pair `(x, y)`, all four parts hold:
the coordinate map, the raw-fiber decomposition, the BK-move
classification, and the bad-set structural backbone
(`InterfaceConclusion x y`).

This is the headline deliverable of the Step 1 cascade port.  Its proof
is pure assembly: part (i) is `localInterface_coordMap_groundSet`
(S1-A), part (ii) is `localInterface_rawFiber_groundSet` (S1-A),
part (iii) is `bkMove_classification` (S1-B), and part (iv) bundles
`commonNbhdFinset_comparable`, `incompLocus_ordConvex`,
`card_externalFinset` and `collinear_fiber_card_le` (S1-B).

The richness threshold `T` and `IsRich T x y` are the paper's
hypothesis — `thm:interface` is stated *for a rich pair*.  Only the
incomparability `hxy.1` is consumed by the proof; the width hypothesis
`hP` is load-bearing in parts (i), (iii) and (iv) (it feeds
`commonNbhd_isChain_of_width3`). -/
theorem thm_interface (hP : HasWidthAtMost α 3) (T : ℕ) (x y : α)
    (hxy : IsRich T x y) : InterfaceConclusion x y := by
  unfold InterfaceConclusion
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Part (i) — coordinate map (S1-A).
    exact localInterface_coordMap_groundSet hP T x y hxy
  · -- Part (ii) — raw-fiber decomposition (S1-A).
    exact localInterface_rawFiber_groundSet x y
  · -- Part (iii) — BK-move classification (S1-B).
    exact fun L L' h => bkMove_classification hP hxy.1 h
  · -- Part (iv.a) — common neighbours are pairwise comparable (S1-B).
    exact fun a ha b hb => commonNbhdFinset_comparable hP hxy.1 ha hb
  · -- Part (iv.b) — order-convexity of the incomparability locus (S1-B).
    exact fun _ _ _ _ hc hc'' hc' h1 h2 => incompLocus_ordConvex hc hc'' hc' h1 h2
  · -- Part (iv.c) — external-element count (S1-B).
    exact card_externalFinset hxy.1
  · -- Part (iv.d) — per-fiber size bound for collinear bad fibers (S1-B).
    exact fun _ _ hinj hsign hline => collinear_fiber_card_le hinj hsign hline

/-! ### §3 — Interface moves and the part-(iii) → corollaries bridge

The S1-C commuting-square / commuting-cube verifications
(`cor_overlap_commuting_square`, `cor_triple_overlap_commuting_cube`)
take a *disjoint-support* hypothesis (`DisjointPos`).  The paper states
`cor:overlap` / `cor:triple-overlap` on the *regular* overlap, where
the disjoint-support property is *derived* from interaction-locus
exclusion via the BK-move classification (part (iii)).  This section
wires that derivation. -/

/-- **`(x, y)`-interface move** — the BK move of `L` at position `k`
"belongs to the `(x, y)` interface": its swapped pair
`{L.symm k, L.symm (k+1)}` has both elements in `{x, y} ∪ C(x, y)` and
at least one element in `{x, y}`.

This is precisely the move shape established by `thm:interface`
part (iii): a coordinate-changing move is a swap of `{x, y}`, `{x, c}`
or `{y, c}` for a common neighbour `c` (`bkSwap_signFlip`,
`bkSwap_iCoord_shift`, `bkSwap_jCoord_shift` of `Step1/BKMoves.lean`),
and every such pair satisfies both clauses below. -/
def IsInterfaceMove (x y : α) (L : LinearExt α) {k : Fin (Fintype.card α)}
    (hk : k.val + 1 < Fintype.card α) : Prop :=
  (L.toFun.symm k ∈ insert x (insert y (commonNbhdFinset x y)) ∧
   L.toFun.symm ⟨k.val + 1, hk⟩ ∈ insert x (insert y (commonNbhdFinset x y))) ∧
  (L.toFun.symm k ∈ ({x, y} : Finset α) ∨
   L.toFun.symm ⟨k.val + 1, hk⟩ ∈ ({x, y} : Finset α))

/-- **The part-(iii) → corollaries bridge.**  If no element of `{x, y}`
is `L`-adjacent to any element of `{u, v} ∪ C(u, v)` (interaction-locus
exclusion), then an `(x, y)`-interface move at position `k` and a
`(u, v)`-interface move at position `m` have **disjoint support**.

Proof.  Suppose the position intervals `{k, k+1}`, `{m, m+1}` overlap
(`¬ DisjointPos k m`, i.e. `m ≤ k+1` and `k ≤ m+1`).  The `(x, y)`-move
contributes an element `a ∈ {x, y}` at one of positions `k`, `k+1`;
both elements of the `(u, v)`-move (at positions `m`, `m+1`) lie in
`{u, v} ∪ C(u, v)`.  Whenever the intervals overlap, `a` is
`L`-adjacent to one of those two elements — contradicting the
no-adjacency hypothesis. -/
lemma disjointPos_of_no_adjacency {x y u v : α} {L : LinearExt α}
    (hno : ∀ a ∈ ({x, y} : Finset α),
           ∀ b ∈ insert u (insert v (commonNbhdFinset u v)),
           ¬ LPosAdj L a b)
    {k m : Fin (Fintype.card α)}
    (hk : k.val + 1 < Fintype.card α) (hm : m.val + 1 < Fintype.card α)
    (hxy_move : L.toFun.symm k ∈ ({x, y} : Finset α) ∨
                L.toFun.symm ⟨k.val + 1, hk⟩ ∈ ({x, y} : Finset α))
    (huv_move : L.toFun.symm m ∈ insert u (insert v (commonNbhdFinset u v)) ∧
                L.toFun.symm ⟨m.val + 1, hm⟩ ∈
                  insert u (insert v (commonNbhdFinset u v))) :
    DisjointPos k m := by
  by_contra hnd
  simp only [DisjointPos, not_or, not_lt] at hnd
  obtain ⟨hmk, hkm⟩ := hnd
  -- Positions of the (u,v)-move's two swapped elements.
  have hposm : (L.pos (L.toFun.symm m)).val = m.val := by simp [LinearExt.pos]
  have hposm1 : (L.pos (L.toFun.symm ⟨m.val + 1, hm⟩)).val = m.val + 1 := by
    simp [LinearExt.pos]
  -- The {x,y} element `a` of the (x,y)-move, its position `pa`.
  obtain ⟨a, ha_mem, pa, hpa, hpa_range⟩ :
      ∃ a, a ∈ ({x, y} : Finset α) ∧ ∃ pa, (L.pos a).val = pa ∧
        (pa = k.val ∨ pa = k.val + 1) := by
    rcases hxy_move with h | h
    · exact ⟨L.toFun.symm k, h, k.val, by simp [LinearExt.pos], Or.inl rfl⟩
    · exact ⟨L.toFun.symm ⟨k.val + 1, hk⟩, h, k.val + 1,
        by simp [LinearExt.pos], Or.inr rfl⟩
  -- Whenever the intervals overlap, `a` is L-adjacent to a (u,v)-move element.
  have hcases :
      (pa + 1 = m.val ∨ m.val + 1 = pa) ∨
      (pa + 1 = m.val + 1 ∨ m.val + 1 + 1 = pa) := by omega
  rcases hcases with hc | hc
  · exact hno a ha_mem (L.toFun.symm m) huv_move.1
      (by unfold LPosAdj; rw [hpa, hposm]; exact hc)
  · exact hno a ha_mem (L.toFun.symm ⟨m.val + 1, hm⟩) huv_move.2
      (by unfold LPosAdj; rw [hpa, hposm1]; exact hc)

/-- Interaction-locus exclusion from regular-overlap membership: if
`L` lies in the regular overlap `Ω°_{xy,uv}`, then no element of
`{x, y}` is `L`-adjacent to any element of `{u, v} ∪ C(u, v)`. -/
lemma not_adjacency_of_regularOverlap {x y u v : α} {L : LinearExt α}
    (hL : L ∈ regularOverlap x y u v) :
    ∀ a ∈ ({x, y} : Finset α),
    ∀ b ∈ insert u (insert v (commonNbhdFinset u v)),
    ¬ LPosAdj L a b := by
  intro a ha b hb hadj
  have hLover : L ∈ overlap x y u v :=
    regularOverlap_subset_overlap x y u v hL
  have hLnotInt : L ∉ interactionLocus x y u v :=
    Finset.disjoint_left.mp
      (regularOverlap_disjoint_interactionLocus x y u v) hL
  exact hLnotInt (mem_interactionLocus_iff.mpr ⟨hLover, a, ha, b, hb, hadj⟩)

/-- Interaction-locus exclusion from regular-*triple*-overlap membership:
if `L` lies in `Ω°°°_{xyz}`, all three pairwise interaction loci are
avoided. -/
lemma not_adjacency_of_regularTripleOverlap {x y z : α} {L : LinearExt α}
    (hL : L ∈ regularTripleOverlap x y z) :
    (∀ a ∈ ({x, y} : Finset α),
       ∀ b ∈ insert y (insert z (commonNbhdFinset y z)), ¬ LPosAdj L a b) ∧
    (∀ a ∈ ({x, y} : Finset α),
       ∀ b ∈ insert x (insert z (commonNbhdFinset x z)), ¬ LPosAdj L a b) ∧
    (∀ a ∈ ({y, z} : Finset α),
       ∀ b ∈ insert x (insert z (commonNbhdFinset x z)), ¬ LPosAdj L a b) := by
  unfold regularTripleOverlap at hL
  rw [Finset.mem_sdiff] at hL
  obtain ⟨hLtriple, hLnotbad⟩ := hL
  have hLxy : L ∈ goodFiberSet x y :=
    tripleOverlap_subset_goodFiberSet_xy x y z hLtriple
  have hLyz : L ∈ goodFiberSet y z :=
    tripleOverlap_subset_goodFiberSet_yz x y z hLtriple
  have hLxz : L ∈ goodFiberSet x z :=
    tripleOverlap_subset_goodFiberSet_xz x y z hLtriple
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hadj
    refine hLnotbad ?_
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact mem_interactionLocus_iff.mpr
      ⟨Finset.mem_inter.mpr ⟨hLxy, hLyz⟩, a, ha, b, hb, hadj⟩
  · intro a ha b hb hadj
    refine hLnotbad ?_
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact mem_interactionLocus_iff.mpr
      ⟨Finset.mem_inter.mpr ⟨hLxy, hLxz⟩, a, ha, b, hb, hadj⟩
  · intro a ha b hb hadj
    refine hLnotbad ?_
    apply Finset.mem_union_right
    exact mem_interactionLocus_iff.mpr
      ⟨Finset.mem_inter.mpr ⟨hLyz, hLxz⟩, a, ha, b, hb, hadj⟩

/-! ### §4 — The two corollaries, assembled -/

/-- **`cor:overlap`** (`step1.tex:429`), assembled.

On the regular overlap `Ω°_{xy,uv}` of two rich interfaces, an
`(x, y)`-interface move and a `(u, v)`-interface move commute and span
an embedded commuting `2×2` BK square (a piece of the local `ℤ²`
grid).

This is the assembled form of `cor_overlap_commuting_square`
(S1-C, `Step1/Corollaries.lean`): the disjoint-support hypothesis the
square verification needs is *derived here* from regular-overlap
membership via the BK-move classification (`disjointPos_of_no_adjacency`,
which wires `thm:interface` part (iii)). -/
theorem cor_overlap {x y u v : α} {L : LinearExt α}
    (hL : L ∈ regularOverlap x y u v)
    {k m : Fin (Fintype.card α)}
    (hk : k.val + 1 < Fintype.card α) (hm : m.val + 1 < Fintype.card α)
    (hkinc : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩)
    (hminc : L.toFun.symm m ∥ L.toFun.symm ⟨m.val + 1, hm⟩)
    (hkmove : IsInterfaceMove x y L hk)
    (hmmove : IsInterfaceMove u v L hm) :
    ∃ L₃ : LinearExt α,
      BKCommSquare L (L.swapAdj k hk hkinc) (L.swapAdj m hm hminc) L₃ := by
  have hdisj : DisjointPos k m :=
    disjointPos_of_no_adjacency (not_adjacency_of_regularOverlap hL)
      hk hm hkmove.2 hmmove.1
  exact ⟨_, cor_overlap_commuting_square L hk hm hkinc hminc hdisj⟩

/-- **`cor:triple-overlap`** (`step1.tex:516`), assembled.

On the regular triple overlap `Ω°°°_{xyz}` of three rich interfaces, an
`(x, y)`-interface move, a `(y, z)`-interface move and an
`(x, z)`-interface move pairwise commute and span an embedded commuting
`2×2×2` BK cube (the local `ℤ³` cube model consumed by Step 7 gap G4).

This is the assembled form of `cor_triple_overlap_commuting_cube`
(S1-C, `Step1/Corollaries.lean`): the three pairwise disjoint-support
hypotheses are *derived here* from regular-triple-overlap membership
via the BK-move classification. -/
theorem cor_triple_overlap {x y z : α} {L : LinearExt α}
    (hL : L ∈ regularTripleOverlap x y z)
    {p₁ p₂ p₃ : Fin (Fintype.card α)}
    (hp₁ : p₁.val + 1 < Fintype.card α)
    (hp₂ : p₂.val + 1 < Fintype.card α)
    (hp₃ : p₃.val + 1 < Fintype.card α)
    (hi₁ : L.toFun.symm p₁ ∥ L.toFun.symm ⟨p₁.val + 1, hp₁⟩)
    (hi₂ : L.toFun.symm p₂ ∥ L.toFun.symm ⟨p₂.val + 1, hp₂⟩)
    (hi₃ : L.toFun.symm p₃ ∥ L.toFun.symm ⟨p₃.val + 1, hp₃⟩)
    (hm₁ : IsInterfaceMove x y L hp₁)
    (hm₂ : IsInterfaceMove y z L hp₂)
    (hm₃ : IsInterfaceMove x z L hp₃) :
    ∃ v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃ : LinearExt α,
      BKCommCube L v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃ := by
  obtain ⟨hno12, hno13, hno23⟩ := not_adjacency_of_regularTripleOverlap hL
  have d₁₂ : DisjointPos p₁ p₂ :=
    disjointPos_of_no_adjacency hno12 hp₁ hp₂ hm₁.2 hm₂.1
  have d₁₃ : DisjointPos p₁ p₃ :=
    disjointPos_of_no_adjacency hno13 hp₁ hp₃ hm₁.2 hm₃.1
  have d₂₃ : DisjointPos p₂ p₃ :=
    disjointPos_of_no_adjacency hno23 hp₂ hp₃ hm₂.2 hm₃.1
  exact bkCommCube_of_disjoint L hp₁ hp₂ hp₃ hi₁ hi₂ hi₃ d₁₂ d₁₃ d₂₃

/-! ### §5 — Non-vacuity: `thm:interface` instantiated at `Antichain3`

Per the mg-794c acceptance bar, the assembled `thm:interface` must
instantiate non-vacuously at a concrete width-3 non-chain poset, with
no Subsingleton-on-empty degeneracy.  The witness is `Antichain3` —
the 3-element antichain (`Fin 3`, discrete order) built by the S1-A
port — with the rich pair `(a0, a1)`. -/

/-- **Non-vacuity of the assembled local interface theorem.**

At the concrete width-3 non-chain poset `Antichain3` with the rich
pair `(a0, a1)`:

* the poset has **width exactly 3** and is **genuinely not a chain** —
  the hypotheses of `thm_interface` are satisfiable, not vacuous;
* `(a0, a1)` is a **genuine rich pair** with common-neighbour-chain
  length `t = 1 > 0`, so the coordinate codomain `{0,…,t}²` is the
  honest `2 × 2` grid `{0,1}²`;
* `2 ≤ numLinExt Antichain3` — the linear-extension set decomposed by
  the interface theorem is **not a subsingleton** (no
  Subsingleton-on-empty baseline);
* a **concrete BK edge exists** on `Antichain3`, so part (iii)'s
  universal quantifier over BK moves is **not vacuous**;
* the assembled `thm_interface` **fires**, delivering the full
  four-part `InterfaceConclusion a0 a1`.

This is the mg-794c (OneThird-S1-D) acceptance witness. -/
theorem thm_interface_nonvacuous :
    HasWidth Antichain3 3 ∧
    ¬ IsChainPoset Antichain3 ∧
    IsRich 1 Antichain3.a0 Antichain3.a1 ∧
    commonNbhdLength Antichain3.a0 Antichain3.a1 = 1 ∧
    2 ≤ numLinExt Antichain3 ∧
    (∃ L L' : LinearExt Antichain3, BKAdj L L') ∧
    InterfaceConclusion Antichain3.a0 Antichain3.a1 := by
  refine ⟨Antichain3.hasWidth, Antichain3.not_isChainPoset,
    Antichain3.isRich_a0_a1, Antichain3.commonNbhdLength_a0_a1,
    Antichain3.two_le_numLinExt, ?_, ?_⟩
  · -- A concrete BK edge: part (iii)'s domain is non-empty.
    have h1lt : 1 < Fintype.card (LinearExt Antichain3) := by
      have h := Antichain3.two_le_numLinExt
      unfold numLinExt at h
      omega
    obtain ⟨L, L', hne⟩ := Fintype.one_lt_card_iff.mp h1lt
    obtain ⟨w⟩ := bkGraph_preconnected Antichain3 L L'
    cases w with
    | nil => exact absurd rfl hne
    | cons h _ => exact ⟨_, _, h⟩
  · -- The assembled `thm_interface` fires at this concrete poset.
    exact thm_interface Antichain3.hasWidthAtMost 1
      Antichain3.a0 Antichain3.a1 Antichain3.isRich_a0_a1

end OneThird
