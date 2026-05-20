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

## §6 — S1-E: the part-(iv) bad-set bound is blocked by an `IsGoodFiber`
## faithfulness defect (mg-c2d7)

The follow-on S1-E (work item mg-c2d7) was scoped by the Checkpoint-1
audit (mg-8b95) to *assemble* the part-(iv) bad-set cardinality bound
`|Bad_{x,y}| = O(|Z| · t²)`.  Executing it surfaced that the
assembly-only framing is unsound: the bound cannot be assembled on the
landed definitions because the S1-A `IsGoodFiber` order-convexity
clause (G2, `LocalCoords.lean`) is **too strong**.  G2 demands the
coordinate image be *rectangle*-convex, but a genuine constant-sign
raw fiber's image is a *triangle* (`signMarker = true` forces
`iCoord ≤ jCoord`), never a rectangle for `t ≥ 1`.  Section §6 below
proves, fully and concretely on `Antichain3`, that **every** raw fiber
of the rich pair `(a0, a1)` is therefore rejected:
`goodFiberSet a0 a1 = ∅` and `badSet a0 a1 = 𝓛(P)`
(`interface_part_iv_faithfulness_defect`).  S1-E is a block-and-report:
the Checkpoint-1 AMBER gap is a *definition-layer* bug, not an assembly
gap, and closing it requires first re-porting the `IsGoodFiber` G2
clause (outside the S1-E file scope).  See
`docs/state-S1-E-Session1.md`.

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

/-! ### §6 — Part-(iv) faithfulness probe: the `IsGoodFiber` G2 defect (S1-E)

**Work item mg-c2d7 (OneThird-S1-E).**  The Checkpoint-1 audit
(`docs/state-S1234-QA-Checkpoint1-Session1.md`, mg-8b95) flagged the
part-(iv) **bad-set cardinality bound** `|Bad_{x,y}| = O(|Z|·t²)` as
*undelivered* and scoped S1-E as an *assembly-only* follow-on
(audit §8.1: "the strip count and `collinear_fiber_card_le` are in
tree — what is missing is the assembly").

Executing S1-E surfaced that the assembly-only framing rests on a false
premise.  The strip-count machinery is **not** in tree, and — more
fundamentally — the bad-set bound **cannot be assembled on top of the
landed `IsGoodFiber` definition**, because its order-convexity clause
(G2, `LocalCoords.lean:209-214`) is *too strong*:

* G2 demands the coordinate image `π_{x,y}(F)` be **rectangle-convex**
  in `ℕ²` (for `p ≤ q` in the image, the whole axis-aligned rectangle
  `[p,q]` lies in the image).
* But a genuine raw fiber has constant sign, and `signMarker = true`
  forces `iCoord ≤ jCoord` (`iCoord_le_jCoord_of_sign_true` below):
  the image lies in the **triangle** `{(i,j) : i ≤ j}`, never a
  rectangle for `t ≥ 1`.  A sign-`+` good fiber therefore cannot
  contain both `(0,0)` and `(1,1)` (`goodFiber_image_no_unit_square`).
* The verdict is decisive on the concrete width-3 non-chain poset
  `Antichain3` (the very non-vacuity witness of §5): **every** raw
  fiber of the rich pair `(a0, a1)` is rejected, so
  `goodFiberSet a0 a1 = ∅` and `badSet a0 a1 = 𝓛(P)`
  (`interface_part_iv_faithfulness_defect`).  The operative part-(iv)
  content `|Bad| ≪ |F|` is not merely undelivered — under the landed
  definition it is **inverted**.

These theorems are the machine-checked backing of the S1-E
block-and-report (`docs/state-S1-E-Session1.md`).  Closing the
Checkpoint-1 AMBER gap requires first re-porting the S1-A `IsGoodFiber`
G2 clause (`LocalCoords.lean`, **out of the S1-E file scope**) to the
paper's genuine order-convexity notion; only then is the
`O(|Z|·t²)` assembly meaningful.  See the state document for the full
analysis and forward options. -/

/-- **Sign `+` ⇒ `iCoord ≤ jCoord`.**  If `x <_L y` then every common
neighbour preceding `x` also precedes `y`, so the first coordinate never
exceeds the second.  The image of a constant-sign-`+` fiber lies in the
triangle `{(i,j) : i ≤ j}` — *not* a rectangle. -/
theorem iCoord_le_jCoord_of_sign_true {x y : α} {L : LinearExt α}
    (h : signMarker x y L = true) : iCoord x y L ≤ jCoord x y L := by
  rw [signMarker_eq_true_iff] at h
  unfold iCoord jCoord
  exact Finset.card_le_card (fun z hz => by
    rw [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, lt_trans hz.2 h⟩)

/-- **Sign `−` ⇒ `jCoord ≤ iCoord`.**  The mirror of
`iCoord_le_jCoord_of_sign_true`: a constant-sign-`−` fiber's image lies
in the triangle `{(i,j) : j ≤ i}`. -/
theorem jCoord_le_iCoord_of_sign_false {x y : α} {L : LinearExt α}
    (h : signMarker x y L = false) : jCoord x y L ≤ iCoord x y L := by
  rw [signMarker_eq_false_iff] at h
  have hle : L.pos y ≤ L.pos x := not_lt.mp h
  unfold iCoord jCoord
  exact Finset.card_le_card (fun z hz => by
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_of_lt_of_le hz.2 hle⟩)

/-- A raw fiber depends only on the external-equivalence class of its
anchor: if `L` and `L₀` are externally equivalent then they anchor the
same raw fiber (at any sign).  This is the genuine — non-tautological —
content behind part (ii)'s "the raw fibers are equivalence classes". -/
theorem rawFiber_eq_of_externalEquiv {x y : α} {L L₀ : LinearExt α}
    (ε : Bool) (h : ExternalEquiv x y L L₀) :
    rawFiber x y L₀ ε = rawFiber x y L ε := by
  ext L'
  simp only [mem_rawFiber]
  exact ⟨fun ⟨he, hs⟩ => ⟨he.trans h.symm, hs⟩,
         fun ⟨he, hs⟩ => ⟨he.trans h, hs⟩⟩

/-- Membership characterisation of the good-fiber set: `L` is good iff
its own raw fiber (at `L`'s sign) is good. -/
theorem mem_goodFiberSet {x y : α} {L : LinearExt α} :
    L ∈ goodFiberSet x y ↔
      ∃ L₀, IsGoodFiber x y (rawFiber x y L₀ (signMarker x y L)) ∧
            L ∈ rawFiber x y L₀ (signMarker x y L) := by
  classical
  unfold goodFiberSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **The `IsGoodFiber` G2 defect (sign `+`).**  A good fiber whose
elements all carry sign `+` cannot have *both* `(0,0)` and `(1,1)` in
its coordinate image: G2 would then force `(1,0)` into the image, but
`(1,0)` violates `iCoord ≤ jCoord`.  So G2 rejects every genuine
two-dimensional sign-`+` fiber. -/
theorem goodFiber_image_no_unit_square {x y : α} {F : Finset (LinearExt α)}
    (hF : IsGoodFiber x y F) (hsign : ∀ L ∈ F, signMarker x y L = true)
    (h00 : ((0, 0) : ℕ × ℕ) ∈ F.image (localCoord x y))
    (h11 : ((1, 1) : ℕ × ℕ) ∈ F.image (localCoord x y)) : False := by
  have h10 : ((1, 0) : ℕ × ℕ) ∈ F.image (localCoord x y) :=
    hF.2.1 (0, 0) h00 (1, 1) h11 (by norm_num) (by norm_num) (1, 0)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  rw [Finset.mem_image] at h10
  obtain ⟨L, hLF, hLc⟩ := h10
  have hle := iCoord_le_jCoord_of_sign_true (hsign L hLF)
  unfold localCoord at hLc; rw [Prod.mk.injEq] at hLc; omega

/-- **The `IsGoodFiber` G2 defect (sign `−`).**  The mirror of
`goodFiber_image_no_unit_square`: a good constant-sign-`−` fiber cannot
contain both `(0,0)` and `(1,1)` — G2 would force `(0,1)`, which
violates `jCoord ≤ iCoord`. -/
theorem goodFiber_image_no_unit_square' {x y : α} {F : Finset (LinearExt α)}
    (hF : IsGoodFiber x y F) (hsign : ∀ L ∈ F, signMarker x y L = false)
    (h00 : ((0, 0) : ℕ × ℕ) ∈ F.image (localCoord x y))
    (h11 : ((1, 1) : ℕ × ℕ) ∈ F.image (localCoord x y)) : False := by
  have h01 : ((0, 1) : ℕ × ℕ) ∈ F.image (localCoord x y) :=
    hF.2.1 (0, 0) h00 (1, 1) h11 (by norm_num) (by norm_num) (0, 1)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  rw [Finset.mem_image] at h01
  obtain ⟨L, hLF, hLc⟩ := h01
  have hle := jCoord_le_iCoord_of_sign_false (hsign L hLF)
  unfold localCoord at hLc; rw [Prod.mk.injEq] at hLc; omega

namespace Antichain3

/-! The four linear extensions of `Antichain3` exhibiting the two
corner coordinates `(0,0)` and `(1,1)` in each sign class. -/

/-- The 3-cycle `a0 ↦ 1, a1 ↦ 2, a2 ↦ 0` (the `a2`-first order). -/
def permCyc : Fin 3 ≃ Fin 3 where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The transposition `a0 ↔ a1` (the `a1 < a0 < a2` order). -/
def permSwap : Fin 3 ≃ Fin 3 where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide
  right_inv := by decide

/-- The reversal `a0 ↔ a2` (the `a2 < a1 < a0` order). -/
def permRev : Fin 3 ≃ Fin 3 where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide
  right_inv := by decide

/-- Order `a0 < a1 < a2`: sign `+`, local coordinate `(0,0)`. -/
noncomputable def extId : LinearExt Antichain3 :=
  linExtOfEquiv (finCongr Antichain3.card_eq.symm)

/-- Order `a2 < a0 < a1`: sign `+`, local coordinate `(1,1)`. -/
noncomputable def extCyc : LinearExt Antichain3 :=
  linExtOfEquiv (permCyc.trans (finCongr Antichain3.card_eq.symm))

/-- Order `a1 < a0 < a2`: sign `−`, local coordinate `(0,0)`. -/
noncomputable def extSwap : LinearExt Antichain3 :=
  linExtOfEquiv (permSwap.trans (finCongr Antichain3.card_eq.symm))

/-- Order `a2 < a1 < a0`: sign `−`, local coordinate `(1,1)`. -/
noncomputable def extRev : LinearExt Antichain3 :=
  linExtOfEquiv (permRev.trans (finCongr Antichain3.card_eq.symm))

/-- On `Antichain3` there are no external elements, so the
external-ordering equivalence relates *every* pair of linear
extensions: there is a single external class, refined only by sign. -/
lemma externalEquiv_total (L L' : LinearExt Antichain3) :
    ExternalEquiv a0 a1 L L' := by
  have hcover : insert a0 (insert a1 (commonNbhdFinset a0 a1))
      = (Finset.univ : Finset Antichain3) := by
    rw [commonNbhdFinset_a0_a1]; decide
  exact ⟨fun a _ ha _ => absurd (hcover ▸ Finset.mem_univ a) ha,
         fun a _ _ ha => absurd (hcover ▸ Finset.mem_univ a) ha⟩

private lemma lt_of_pos {L : LinearExt Antichain3} {p q : Antichain3}
    {m n : ℕ} (hp : (L.pos p).val = m) (hq : (L.pos q).val = n)
    (h : m < n) : L.lt p q := by
  change L.pos p < L.pos q; rw [Fin.lt_def, hp, hq]; exact h

private lemma not_lt_of_pos {L : LinearExt Antichain3} {p q : Antichain3}
    {m n : ℕ} (hp : (L.pos p).val = m) (hq : (L.pos q).val = n)
    (h : n ≤ m) : ¬ L.lt p q := by
  change ¬ L.pos p < L.pos q; rw [Fin.lt_def, hp, hq]; omega

lemma sign_extId : signMarker a0 a1 extId = true := by
  rw [signMarker_eq_true_iff]
  exact lt_of_pos (by decide : (extId.pos a0).val = 0)
    (by decide : (extId.pos a1).val = 1) (by norm_num)

lemma sign_extCyc : signMarker a0 a1 extCyc = true := by
  rw [signMarker_eq_true_iff]
  exact lt_of_pos (by decide : (extCyc.pos a0).val = 1)
    (by decide : (extCyc.pos a1).val = 2) (by norm_num)

lemma sign_extSwap : signMarker a0 a1 extSwap = false := by
  rw [signMarker_eq_false_iff]
  exact not_lt_of_pos (by decide : (extSwap.pos a0).val = 1)
    (by decide : (extSwap.pos a1).val = 0) (by norm_num)

lemma sign_extRev : signMarker a0 a1 extRev = false := by
  rw [signMarker_eq_false_iff]
  exact not_lt_of_pos (by decide : (extRev.pos a0).val = 2)
    (by decide : (extRev.pos a1).val = 1) (by norm_num)

private lemma iCoord_eq {L : LinearExt Antichain3} {v : ℕ}
    (h : (if L.lt a2 a0 then (1 : ℕ) else 0) = v) : iCoord a0 a1 L = v := by
  unfold iCoord
  rw [commonNbhdFinset_a0_a1, Finset.filter_singleton]
  by_cases hc : L.lt a2 a0
  · rw [if_pos hc] at h ⊢; rw [Finset.card_singleton]; omega
  · rw [if_neg hc] at h ⊢; simp; omega

private lemma jCoord_eq {L : LinearExt Antichain3} {v : ℕ}
    (h : (if L.lt a2 a1 then (1 : ℕ) else 0) = v) : jCoord a0 a1 L = v := by
  unfold jCoord
  rw [commonNbhdFinset_a0_a1, Finset.filter_singleton]
  by_cases hc : L.lt a2 a1
  · rw [if_pos hc] at h ⊢; rw [Finset.card_singleton]; omega
  · rw [if_neg hc] at h ⊢; simp; omega

lemma localCoord_extId : localCoord a0 a1 extId = (0, 0) := by
  unfold localCoord
  rw [iCoord_eq (L := extId) (v := 0) (by
        rw [if_neg (not_lt_of_pos (by decide : (extId.pos a2).val = 2)
          (by decide : (extId.pos a0).val = 0) (by norm_num))]),
      jCoord_eq (L := extId) (v := 0) (by
        rw [if_neg (not_lt_of_pos (by decide : (extId.pos a2).val = 2)
          (by decide : (extId.pos a1).val = 1) (by norm_num))])]

lemma localCoord_extCyc : localCoord a0 a1 extCyc = (1, 1) := by
  unfold localCoord
  rw [iCoord_eq (L := extCyc) (v := 1) (by
        rw [if_pos (lt_of_pos (by decide : (extCyc.pos a2).val = 0)
          (by decide : (extCyc.pos a0).val = 1) (by norm_num))]),
      jCoord_eq (L := extCyc) (v := 1) (by
        rw [if_pos (lt_of_pos (by decide : (extCyc.pos a2).val = 0)
          (by decide : (extCyc.pos a1).val = 2) (by norm_num))])]

lemma localCoord_extSwap : localCoord a0 a1 extSwap = (0, 0) := by
  unfold localCoord
  rw [iCoord_eq (L := extSwap) (v := 0) (by
        rw [if_neg (not_lt_of_pos (by decide : (extSwap.pos a2).val = 2)
          (by decide : (extSwap.pos a0).val = 1) (by norm_num))]),
      jCoord_eq (L := extSwap) (v := 0) (by
        rw [if_neg (not_lt_of_pos (by decide : (extSwap.pos a2).val = 2)
          (by decide : (extSwap.pos a1).val = 0) (by norm_num))])]

lemma localCoord_extRev : localCoord a0 a1 extRev = (1, 1) := by
  unfold localCoord
  rw [iCoord_eq (L := extRev) (v := 1) (by
        rw [if_pos (lt_of_pos (by decide : (extRev.pos a2).val = 0)
          (by decide : (extRev.pos a0).val = 2) (by norm_num))]),
      jCoord_eq (L := extRev) (v := 1) (by
        rw [if_pos (lt_of_pos (by decide : (extRev.pos a2).val = 0)
          (by decide : (extRev.pos a1).val = 1) (by norm_num))])]

/-- **The sign-`+` raw fiber of `(a0, a1)` on `Antichain3` is bad.**
It contains `extId` (coordinate `(0,0)`) and `extCyc` (coordinate
`(1,1)`); by `goodFiber_image_no_unit_square` G2 fails. -/
theorem not_isGoodFiber_plus :
    ¬ IsGoodFiber a0 a1 (rawFiber a0 a1 extId true) := by
  intro hF
  have hmemId : extId ∈ rawFiber a0 a1 extId true := by
    have := self_mem_rawFiber a0 a1 extId
    rwa [sign_extId] at this
  have hmemCyc : extCyc ∈ rawFiber a0 a1 extId true :=
    mem_rawFiber.mpr ⟨externalEquiv_total extCyc extId, sign_extCyc⟩
  refine goodFiber_image_no_unit_square hF
    (fun L hL => signMarker_of_mem_rawFiber hL) ?_ ?_
  · exact Finset.mem_image.mpr ⟨extId, hmemId, localCoord_extId⟩
  · exact Finset.mem_image.mpr ⟨extCyc, hmemCyc, localCoord_extCyc⟩

/-- **The sign-`−` raw fiber of `(a0, a1)` on `Antichain3` is bad.** -/
theorem not_isGoodFiber_minus :
    ¬ IsGoodFiber a0 a1 (rawFiber a0 a1 extId false) := by
  intro hF
  have hmemSwap : extSwap ∈ rawFiber a0 a1 extId false :=
    mem_rawFiber.mpr ⟨externalEquiv_total extSwap extId, sign_extSwap⟩
  have hmemRev : extRev ∈ rawFiber a0 a1 extId false :=
    mem_rawFiber.mpr ⟨externalEquiv_total extRev extId, sign_extRev⟩
  refine goodFiber_image_no_unit_square' hF
    (fun L hL => signMarker_of_mem_rawFiber hL) ?_ ?_
  · exact Finset.mem_image.mpr ⟨extSwap, hmemSwap, localCoord_extSwap⟩
  · exact Finset.mem_image.mpr ⟨extRev, hmemRev, localCoord_extRev⟩

/-- **The interface theorem's good-fiber set is EMPTY on `Antichain3`.**
Every linear extension's raw fiber — sign `+` or sign `−` — is rejected
by G2.  This refutes the implicit assumption of the part-(ii)
decomposition that `goodFiberSet` is the bulk of `𝓛(P)`. -/
theorem goodFiberSet_a0_a1_eq_empty :
    goodFiberSet a0 a1 = (∅ : Finset (LinearExt Antichain3)) := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro L hL
  obtain ⟨L₀, hgood, -⟩ := mem_goodFiberSet.mp hL
  rw [rawFiber_eq_of_externalEquiv (signMarker a0 a1 L)
        (externalEquiv_total extId L₀)] at hgood
  cases hs : signMarker a0 a1 L with
  | true => rw [hs] at hgood; exact not_isGoodFiber_plus hgood
  | false => rw [hs] at hgood; exact not_isGoodFiber_minus hgood

/-- **The interface theorem's bad set is ALL of `𝓛(P)` on `Antichain3`.**
The operative part-(iv) negligibility `|Bad| ≪ |F|` is inverted. -/
theorem badSet_a0_a1_eq_univ :
    badSet a0 a1 = (Finset.univ : Finset (LinearExt Antichain3)) := by
  unfold badSet
  rw [goodFiberSet_a0_a1_eq_empty, Finset.sdiff_empty]

/-- **Part-(iv) faithfulness defect (S1-E headline, mg-c2d7).**

On the concrete width-3 non-chain poset `Antichain3` with the rich pair
`(a0, a1)` (`t = 1`), the landed `IsGoodFiber` order-convexity clause
(G2) rejects *both* sign classes' raw fibers, so the good-fiber set is
empty and the bad set is all of `𝓛(P)`.

This is the machine-checked witness that the Checkpoint-1 AMBER gap is
**not** an assembly gap: the part-(iv) bad-set cardinality bound
`|Bad| = O(|Z|·t²)` cannot be assembled on top of the current
`IsGoodFiber` definition, because that definition classifies the
genuine two-dimensional good fibers as bad.  Closing the gap requires
re-porting the S1-A `IsGoodFiber` G2 clause first.  See
`docs/state-S1-E-Session1.md`. -/
theorem interface_part_iv_faithfulness_defect :
    ¬ IsGoodFiber a0 a1 (rawFiber a0 a1 extId true) ∧
    ¬ IsGoodFiber a0 a1 (rawFiber a0 a1 extId false) ∧
    goodFiberSet a0 a1 = (∅ : Finset (LinearExt Antichain3)) ∧
    badSet a0 a1 = (Finset.univ : Finset (LinearExt Antichain3)) :=
  ⟨not_isGoodFiber_plus, not_isGoodFiber_minus,
   goodFiberSet_a0_a1_eq_empty, badSet_a0_a1_eq_univ⟩

end Antichain3

end OneThird
