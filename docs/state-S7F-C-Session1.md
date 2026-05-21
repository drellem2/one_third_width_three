# State — S7-F-C — Session 1: assemble the `LayeredDecomposition` on `X ∖ X^exc`, verify `(L1)`–`(L4)`

**Ticket:** mg-bcc9 (OneThird-S7-F-C — S7-F bridge sub-arc C: assemble
the `LayeredDecomposition` on `X ∖ X^exc` with `L.w ≤ 4`, verify the
`(L1)`–`(L4)` invariants).
**Type:** Lean deliverable.
**Parent:** FULL REFACTOR Phase 2, Piece 3 (the S7-F bridge);
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 sub-arc
`mg-S7-F-C`.
**Depends:** mg-08d7 (S7-F-A — `Xexc` + the `|X^exc|` bound);
mg-120d (S7-F-B — the wired synchronization maps).
**Predecessors read:** `docs/PROOF-STRUCTURE-ONBOARDING.md`;
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3;
`docs/state-S7F-A-Session1.md`; `docs/state-S7F-B-Session1.md`;
`docs/state-S7F-R1-Session1.md`; `step8.tex:1983-2167`.

---

## §0. Verdict — **GREEN — `LayeredDecomposition (X ∖ X^exc)` assembled, `(L1)`–`(L4)` verified, `w ≤ 4`. Resolution A succeeds; (L2) closes.**

Paper item (ii) of `lem:layered-from-step7` (`step8.tex:2066-2167`) is
**ported**. The deliverable is `lean/OneThird/Step8/BridgeLayered.lean`
(NEW, sorry-free, **no new `axiom`**, builds clean, imported into
`OneThird.lean`; full `OneThird` build green):

* `bridgeLayered D hMono : LayeredDecomposition (↥((Xexc D)ᶜ))` — the
  genuine ground-set `LayeredDecomposition` on `X ∖ X^exc`, with band
  map the **normalised chain potential** and interaction width
  `w := K_bw + 2`. All four `def:layered` invariants `(L1)`–`(L4)` are
  discharged as honest structure fields;
* `bridgeLayered_w_le_four` — the `w ≤ 4` cap, from `K_bw ≤ 2`
  (`lem:bandwidth`); `bridgeLayered_w` pins `w = K_bw + 2`;
* `bridgeLayered_L1_size` / `_L1_antichain` / `_L2` / `_L3` / `_L4` —
  the four invariants exposed under the paper's `(L1)`–`(L4)` names
  (`(L3)` derived from `(L2)` via `comparable_of_far`);
* `exists_bridgeLayered_w_le_four` — the contract-shaped existence
  `∃ L : LayeredDecomposition (X∖X^exc), L.w ≤ 4` (MA-Sig §4.2 §E,
  the third re-pinned cap);
* the construction is **discharged unconditionally on the F7a grid
  witness** (`§5`): `gridBridgeLayered` is a genuine
  `LayeredDecomposition` on the 8-element `Grid ∖ {(0,0)}` with
  `K = 5`, `w = 3`, a **non-constant** band map.

**`#print axioms`** of `bridgeLayered`, `bridgeLayered_L2`, `_L4`,
`exists_bridgeLayered_w_le_four`, the grid certificates, `potLevel_card_le`,
`anchor_not_refOrphan`: only `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx`, no project axiom. `AXIOMS.md` unchanged.

---

## §1. THE RESOLUTION-A-vs-B DECISION POINT — `(L2)` closes under Resolution A

The ticket flagged the `(L2)` verification (`forced_lt`) as the
load-bearing step and the Resolution-A-vs-B fork. **Outcome:
Resolution A succeeds. `(L2)` closes. No escalation to Resolution B;
no block-and-report.**

### §1.1. Why `(L2)` closes from the bare structure

`(L2)` `forced_lt` is `band x + w < band y → x <_P y` for
`x, y ∈ X ∖ X^exc`. With the potential band map this unfolds to: if
the chain-potential gap `a(y) − a(x)` exceeds `w = K_bw + 2`, then
`x <_P y`.

The **comparability half is a structural tautology of the
complement**, needing *no* soundness hypothesis. `X^exc_band`
(sub-ticket A, `ExceptionalSet.lean`) was *defined* as exactly

```
  X^exc_band := { z : ∃ y, z, y incomparable ∧ |a z − a y| > K_bw }.
```

So on `X ∖ X^exc ⊆ X ∖ X^exc_band`, an incomparable pair `(x, y)`
with `a(y) − a(x) > K_bw` would witness `x ∈ X^exc_band ⊆ X^exc` —
contradicting `x ∈ X ∖ X^exc`. Hence `x` and `y` are comparable.
This is the lever the ticket anticipated: "the (L2) verification
should use that the *complement* `X ∖ X^exc_band` has every
incomparable pair within `K_bw`" (`state-S7F-A-Session1.md` §6).

The **direction half** — comparable `⇒ x <_P y` (not `y <_P x`) —
needs the potential to be strictly increasing along poset covers
(rule out `y <_P x` with `a(x) < a(y)`). That is the one genuine
soundness input, named `PotPosetMono` (§1.2).

A degenerate poset (`Δ_ℓ`, the 3-disjoint-chains family) can never be
a minimal γ-counterexample — it has symmetric balanced pairs. But the
`(L1)`–`(L4)` verification does **not even need** that exclusion: the
invariants hold on `X ∖ X^exc` for *every* bare `ChainLiftData`,
because `X^exc_band`'s definition makes the bandwidth bound a
tautology of the complement. For `Δ_ℓ` the verification still goes
through — `X^exc` is simply large (its `O_T(1)` *cardinality* bound is
what fails for `Δ_ℓ`, and that is `ExcBudget`'s domain, sub-ticket A /
S7-F-Z, **not** the `(L1)`–`(L4)` invariants). The §11.3 falseness
lives in the *depth/cardinality* bound, not in `(L1)`–`(L4)`.

### §1.2. The Resolution-A named obligation — `PotPosetMono`

`(L2)`'s direction, `(L4)` (`cross_band_lt_upward`), and the `(L1)`
antichain clause all need:

```
  ChainLiftData.PotPosetMono D  :=  ∀ x y : α, x <_P y → a x < a y
```

— paper `prop:71`: the chain potential is strictly increasing along
**every comparable cover of the poset**, not merely along the three
Dilworth chains. The bare `ChainPotential` (`ChainPotentials.lean:267`)
carries strict monotonicity along the chains *only*; cross-chain
comparabilities (which genuinely occur — `(0,0) <_P (1,1)` in the
grid) are unconstrained, so `PotPosetMono` is **not** derivable from
the bare structure.

Per the **Piece-3 design note (Resolution A)**, this is **not
fabricated** and the `ChainLiftData`/`ChainPotential` structures are
**not strengthened** (that would be Resolution B). It is **made
explicit** as the named, decidable predicate
`ChainLiftData.PotPosetMono` — the S7-F-C analogue of sub-ticket A's
`ExcBudget` and sub-ticket B's `BoundedSyncOrphans` — a downstream
hypothesis to be discharged at the bridge call site from `hCex` plus
the Steps-1-7 cascade (sub-ticket S7-F-Z). It is genuinely satisfiable
(the grid satisfies it, `grid_PotPosetMono`, `by decide`) and
genuinely fails for a pathological bare structure, so it is a real
soundness filter, not an inert hypothesis.

`bridgeLayered` takes exactly one hypothesis: `hMono : D.PotPosetMono`.
(`K_bw ≤ 2` is needed only for the *separate* `w ≤ 4` theorem, not to
build the structure.)

### §1.3. Why Resolution B was not needed

Resolution B (strengthen `ChainLiftData`/`ChainPotential` with
soundness fields) would be warranted only if `(L2)` could not close
even with a named hypothesis — e.g. if `(L2)` were *false* on
`X ∖ X^exc` for some inhabitant. It is not: `(L2)` is provable for
*every* bare `ChainLiftData` given `PotPosetMono`, because the
comparability half is a complement tautology and the direction half
is exactly `PotPosetMono`. Resolution A is the lighter, correct
choice; `state-S7F-A-Session1.md` §8 / `state-S7F-B-Session1.md` §7
note that a future Resolution-B re-scope would absorb
`ExcBudget`/`BoundedSyncOrphans`/`PotPosetMono` into the strengthened
structure, but Piece 3 does **not** require it.

---

## §2. The deliverable — `BridgeLayered.lean`

Namespace `OneThird.Step8`. `variable {α} [PartialOrder α]
[Fintype α] [DecidableEq α] [DecidableLE α]`.

### §2.1. The band map — the normalised chain potential

The paper's band assembly `L_k := {a_k, b_{f_AB(k)}, c_{f_AC(k)}}`
(`step8.tex:2108-2121`) groups chain elements of **close potential**:
the synchronization maps `f_••` are themselves the potential-argmin
alignment (`step8.tex:2098-2106`). The honest, in-tree-witnessed Lean
realisation of "the band of `z`" is therefore the chain potential of
`z`, normalised to a `1`-indexed `ℕ`:

```
  potShift D x   := (a x − potMin D).toNat            -- ℕ
  bridgeBand D z := potShift D z.val + 1              -- band label ≥ 1
```

This is **exactly** the band map of the genuine in-tree witness
`GridChainLift.gridLayered` (`ConcreteChainLiftData.lean:303`,
`band = gridBand = potFun + 1`), which mg-974c established as the
target object shape. `potMin`/`potMax` (`§1` of the file) are the
`min'`/`max'` of the potential image (`0` on an empty carrier);
`potMin_le`/`le_potMax` are the genuine bounds; `potShift_cast`
records that the `Int.toNat` normalisation loses no information.

| Lean | Paper | Content |
|---|---|---|
| `bridgeBand D` | the band map `z ↦ k` | normalised chain potential |
| `bridgeK D` | depth `K` | `(potMax − potMin).toNat + 1` |
| `w := D.K_bw + 2` | interaction width | `step8.tex:2121` |

### §2.2. The `(L1)`–`(L4)` verification (`§3`–`§4` of the file)

| Invariant | Lean field | Discharge |
|---|---|---|
| `(L1)` size `≤ 3` | `band_size` | `potLevel_card_le`: bands are potential level sets; each chain (potential injective on it) hits a value once; cover ⇒ `≤ 3`. **Bare structure only.** |
| `(L1)` antichain | `band_antichain` | a comparable in-band pair would have *strictly* increasing potential (`PotPosetMono`) yet equal band ⇒ equal potential — contradiction. |
| `(L2)` forced | `forced_lt` | §1.1: gap `> K_bw` + incomparable ⇒ `X^exc_band` ⇒ contradiction; `PotPosetMono` fixes direction. |
| `(L3)` far ⇒ comparable | `comparable_of_far` (derived) | corollary of `(L2)` — `bridgeLayered_L3`. |
| `(L4)` cross-band dir. | `cross_band_lt_upward` | `x <_P y ⇒ a x < a y` (`PotPosetMono`) `⇒ band x ≤ band y`. |

`potLevel_card_le` (`§2` of the file, paper `(L1)`'s `|L_k| ≤ 3`) is
proved purely from the **bare** `ChainLiftData`: the chain potential
is injective on each Dilworth chain
(`ChainPotential.injective_on_{A,B,C}`) and the chains cover `α`
(`ChainTriple.cover`).

The non-triviality bar (Checkpoint-3 Finding D — "no inert
`4 ≤ 4`"): `w = K_bw + 2` is a genuine function of the genuine
`ChainLiftData` field `K_bw`, and `forced_lt` genuinely consumes `w`
in `band x + w < band y`. `w ≤ 4` reduces to `K_bw ≤ 2`
(`lem:bandwidth`), not to a literal tautology.

### §2.3. Connection to sub-ticket B (`§3b` of the file)

`X^exc` folds in `X^exc_sync` (sub-ticket A built it from sub-ticket
B's orphan index sets). So `X ∖ X^exc` is **orphan-free**:
`anchor_not_refOrphan` proves every band anchor `a_k` of `X ∖ X^exc`
is not a synchronization orphan, and `fAB_defined_on_compl` /
`fAC_defined_on_compl` consume sub-ticket B's
`ChainLiftData.fAB_mem_domain_of_not_refOrphan` to show the wired
maps `fABwired`/`fACwired` apply on `X ∖ X^exc`. This is the sense in
which the bridge band assembly consumes "the synchronized pairs
(S7-F-B output)".

### §2.4. The grid discharge (`§5` of the file)

The sub-ticket-C analogue of `grid_Xexc_card_le` (A) /
`gridChainLiftData_boundedSyncOrphans` (B). On the F7a witness
`gridChainLiftData` (3×3 grid):

| Theorem | Content |
|---|---|
| `grid_PotPosetMono` | the Resolution-A obligation **holds** (`by decide`). |
| `gridBridgeLayered` | the genuine `LayeredDecomposition` on `Grid ∖ {(0,0)}` (8 elements). |
| `grid_bridgeLayered_w` | `w = 3` — genuinely `K_bw + 2`, `K_bw = 1` tight. |
| `grid_bridgeLayered_K` | depth `K = 5` — non-trivial layering. |
| `grid_bridgeLayered_band_nonconstant` | `(0,1)` and `(2,2)` land in different bands — the band map is real, not inert. |
| `grid_bridgeLayered_w_le_four` | `w ≤ 4`, no free hypothesis. |
| `grid_exists_bridgeLayered` | paper item (ii) discharged on the witness. |

The discharge is non-degenerate: the layered decomposition is genuine
(`K = 5 > 1`, band map non-constant), and `grid_PotPosetMono`
exercises a genuine soundness filter — `PotPosetMono` would be *false*
for a non-monotone bare potential.

---

## §3. Scope boundary — what S7-F-C does *not* deliver

* **`ExcBudget` discharge** (the `O_T(1)` cardinality / depth bound,
  paper item (ii)'s `K ≥ |X|/6`) — sub-ticket A's `ExcBudget`
  interface, discharged from `hCex` + cascade by **sub-ticket
  S7-F-Z**. The `(L1)`–`(L4)` invariants here hold regardless of
  `|X^exc|`'s size; the depth bound is orthogonal.
* **The perturbation lift** `HasBalancedPair (X∖X^exc) →
  HasBalancedPair X` (paper item (iii)) — sub-ticket **S7-F-D** (the
  chain-removal subtype lift / `exc_perturb`).
* **Discharging `PotPosetMono`** (paper `prop:71`) from the bridge
  call-site `hCex` + the Steps-1-7 cascade — sub-ticket **S7-F-Z**
  integration. S7-F-C names the obligation and proves it satisfiable;
  it does not wire it.
* **`K_bw ≤ 2`** is consumed as a stated input (`lem:bandwidth`,
  scoping §2.3); its cascade derivation is Piece 1 / S7-F-Z.

---

## §4. Acceptance bars

- [x] Read-first set consumed: onboarding doc; scoping §2.3; S7-F-A
  and S7-F-B state docs; state-S7F-R1; `step8.tex:1983-2167`.
- [x] `LayeredDecomposition (↥((Xexc D)ᶜ))` constructed —
  `bridgeLayered`, band map = normalised chain potential.
- [x] `(L1)`–`(L4)` all genuinely verified as honest structure fields
  + exposed under paper names (`bridgeLayered_L1_size`,
  `_L1_antichain`, `_L2`, `_L3`, `_L4`).
- [x] `L.w ≤ 4` proved — `bridgeLayered_w_le_four`, genuine
  `w = K_bw + 2`, not an inert literal (Checkpoint-3 Finding-D bar).
- [x] **Resolution-A-vs-B decision point resolved: Resolution A.**
  `(L2)` closes from the bare structure + the named obligation
  `PotPosetMono`; no Resolution-B escalation, no block-and-report.
- [x] The Resolution-A obligation `PotPosetMono` (paper `prop:71`)
  named explicitly, proved satisfiable on the F7a witness.
- [x] Sub-ticket B's wired maps consumed (`§3b`: `anchor_not_refOrphan`,
  `fAB_defined_on_compl`, `fAC_defined_on_compl`).
- [x] Concrete non-degenerate discharge on the F7a grid witness
  (`gridBridgeLayered`: `K = 5`, `w = 3`, non-constant band map).
- [x] No degenerate/inert witness; no `sorry`; no new `axiom`;
  `AXIOMS.md` unchanged (`#print axioms`: only
  `propext`/`Classical.choice`/`Quot.sound`).
- [x] File builds; imported into `OneThird.lean`; full `OneThird`
  build green (1446 jobs).

---

## §5. Forward action — Piece 3 status

* **Sub-arc mg-S7-F-C is complete.** The `LayeredDecomposition` on
  `X ∖ X^exc` and the `(L1)`–`(L4)` verification are in tree.
* **mg-S7-F-D (chain-removal subtype lift)** — extend
  `OrdinalDecomp.hasBalancedPair_lift` to the `exc_perturb`-driven
  exceptional-set deletion; transfers `HasBalancedPair (X∖X^exc)` to
  `HasBalancedPair X` (paper item (iii)).
* **mg-S7-F-Z (integration + QA)** — wire A–D together; discharge the
  three named Resolution-A obligations (`ExcBudget`,
  `BoundedSyncOrphans`, **`PotPosetMono`**) from the bridge call-site
  `hCex` + the Steps-1-7 cascade.

---

## §6. Cross-reference index

### §6.1. Lean (this session)

* `lean/OneThird/Step8/BridgeLayered.lean` (NEW) — namespace
  `OneThird.Step8`.
  * `potImage`, `potMin`, `potMax`, `potMin_le`, `le_potMax` — the
    potential range.
  * `ChainLiftData.PotPosetMono` — the Resolution-A named obligation
    (paper `prop:71`).
  * `chain_level_card_le_one`, `potLevel_card_le` — the `(L1)`
    `|L_k| ≤ 3` level-set bound (bare structure).
  * `potShift`, `potShift_cast`, `bridgeK`, `bridgeBand` — the band
    map.
  * `not_mem_Xexc_band_of_mem_compl`, `bridgeBand_pot_of_eq` —
    helpers.
  * `bridgeLayered` — the `LayeredDecomposition (↥((Xexc D)ᶜ))`.
  * `anchor_not_refOrphan`, `fAB_defined_on_compl`,
    `fAC_defined_on_compl` — the sub-ticket-B connection.
  * `bridgeLayered_w`, `bridgeLayered_w_le_four`,
    `bridgeLayered_L1_size`/`_L1_antichain`/`_L2`/`_L3`/`_L4`,
    `exists_bridgeLayered_w_le_four` — the `(L1)`–`(L4)` API + `w ≤ 4`.
  * `GridChainLift.grid_PotPosetMono`, `gridBridgeLayered`,
    `grid_bridgeLayered_{w,K,w_le_four,band_nonconstant}`,
    `grid_exists_bridgeLayered` — the `§5` grid discharge.
* `lean/OneThird.lean` — adds the `BridgeLayered` import.

### §6.2. Lean (consumed, unmodified)

* `lean/OneThird/Step8/ChainPotentials.lean:267/328` —
  `ChainPotential`, `ChainLiftData`; `injective_on_{A,B,C}`,
  `ChainTriple.cover`.
* `lean/OneThird/Step8/ExceptionalSet.lean` — `Xexc`, `Xexc_band`,
  `Xexc_sync`, `mem_Xexc_band`, `syncOrphans` (sub-ticket A).
* `lean/OneThird/Step8/SyncMaps.lean` — `ChainLiftData.refOrphans`,
  `fAB_mem_domain_of_not_refOrphan`, `SyncMap.domain` (sub-ticket B).
* `lean/OneThird/Step8/LayeredReduction.lean:113` —
  `LayeredDecomposition`, `comparable_of_far`.
* `lean/OneThird/Step8/ConcreteChainLiftData.lean` —
  `gridChainLiftData`, `gridLayered` (F7a witnesses, mg-974c).

### §6.3. Predecessor docs / work items

* `docs/state-S7F-A-Session1.md` (mg-08d7) — `Xexc`, `ExcBudget`.
* `docs/state-S7F-B-Session1.md` (mg-120d) — wired sync maps,
  `BoundedSyncOrphans`.
* `docs/state-S7F-R1-Session1.md` (mg-974c) — the concrete
  `ChainLiftData`; F7a GREEN.
* `docs/state-MA-Sig-Session1.md` §4.2 §E, §11.3 — the bridge
  contract; the bare-structure soundness gap (Resolution A vs B).
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 — Piece 3.
* `step8.tex:1983-2007` — `def:layered` (`(L1)`–`(L4)`);
  `step8.tex:2066-2167` — `lem:layered-from-step7` item (ii).

---

## §7. Maintenance contract

This file is the state record for FULL REFACTOR Phase-2 Piece-3
sub-arc C (mg-bcc9). It owns the Lean file `Step8/BridgeLayered.lean`.
Supersede it only if a later session changes that file's deliverable.
If Piece 3 adopts MA-Sig §11.3 resolution (B) (a strengthened
`ChainLiftData`/`ChainPotential` carrying soundness fields), the named
obligation `ChainLiftData.PotPosetMono` here should become a field of
the strengthened structure and §1.2 re-evaluated; record that in the
same commit.
