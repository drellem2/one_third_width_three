# State — S7-F-A — Session 1: construct `X^exc` from the `ChainLiftData`, bound `|X^exc|`

**Ticket:** mg-08d7 (OneThird-S7-F-A — S7-F bridge sub-ticket A:
construct the exceptional set `X^exc` from the `ChainLiftData`, bound
its cardinality).
**Type:** Lean deliverable.
**Parent:** FULL REFACTOR Phase 2, Piece 3 (the S7-F bridge);
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 sub-arc
`mg-S7-F-A`.
**Depends:** mg-3119 (S7F-R2 — reconciled the bridge contract to
consume a `ChainLiftData`); mg-974c (S7F-R1 — concrete non-degenerate
`ChainLiftData` constructible, F7a GREEN).
**Predecessors read:** `docs/PROOF-STRUCTURE-ONBOARDING.md`;
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3;
`docs/state-S7F-R1-Session1.md`; `docs/state-S7F-Checkpoint3-Session1.md`;
`docs/state-MA-Sig-Session1.md` §4.1/§4.2 §E/§11.

---

## §0. Verdict — **GREEN — `X^exc` constructed, `|X^exc| ≤ C_exc T` proved**

Paper item (i) of `lem:layered-from-step7` (`step8.tex:2056-2065`) is
**ported**. The deliverable is
`lean/OneThird/Step8/ExceptionalSet.lean` (NEW, sorry-free, no new
`axiom`, builds clean, imported into `OneThird.lean`):

* the exceptional set `X^exc` and its three pieces `X^exc_mono`,
  `X^exc_band`, `X^exc_sync` are each constructed as a `Finset α`
  **derived from the bare `ChainLiftData α` fields** (`triple`,
  `pot`, `K_bw`, `fAB`, `fAC`, `fBC`) plus the poset order of `α`;
* the cardinality bound `|X^exc| ≤ C_exc T` is **proved**, in two
  forms — a fully concrete hypothesis-explicit form
  (`Xexc_card_le_of_budget`) and the contract-shaped corollary
  (`Xexc_card_le`);
* the whole construction is **discharged unconditionally on the F7a
  grid witness** (`gridChainLiftData`): `X^exc` computes to the
  non-empty `{(0,0)}`, `ExcBudget` holds for every `T`, the bound
  closes with no free hypothesis (`grid_Xexc_card_le`).

**The bound is genuine and `O_T(1)`, not inert.** `C_exc T = c₁ T + 6`
is a fixed `O_T(1)` function (`c₁ T` the abstract Step-5 constant
`c_1(T)`; the `+6 = 3·2` the explicit `3·K_bw` orphan contribution at
`K_bw ≤ 2`). `X^exc_mono = ∅` is *proved* (earned from the
`ChainPotential.strictMono` fields), not asserted. `|X^exc_sync|`'s
reduction to the three orphan counts is hypothesis-free. Nothing in
the load-bearing path is `card_union_le` alone.

**Scoped disclosure (§3) — not a hedge.** The `O_T(1)` bound is
**not** provable from the *bare* `ChainLiftData` (it is false on the
`Δ_ℓ` degenerate family — MA-Sig §11.3). The genuine cascade facts
are pinned as the `ExcBudget D T` interface; discharging `ExcBudget`
from the bridge's `hCex` + the Steps-1-7 cascade is **Piece-1 /
sub-arc S7-F-Z** integration, explicitly *not* sub-ticket A. This is
the Resolution-A design (PIECE-3 DESIGN NOTE): build against the bare
structure, name the exact extra obligation.

---

## §1. What sub-ticket A is

The S7-F bridge `lem:layered-from-step7` (`step8.tex:2009-2089`)
consumes a `ChainLiftData α` and outputs a ground-set
`LayeredDecomposition {a // a ∉ Xexc}` with the re-pinned three-cap
form (`Xexc.card ≤ C_exc T`; band-nonempty; `L.w ≤ 4`). The paper
proof has three items: (i) `|X^exc| ≤ C_exc(T) = O_T(1)`; (ii) the
layered decomposition on `X∖X^exc`; (iii) the perturbation transfer.

**Sub-ticket A = paper item (i)**: construct `X^exc` and bound it.
Sub-arcs B (sync maps), C (band assembly + (L1)-(L4)), D
(chain-removal lift), Z (integration) are separate tickets.

---

## §2. The deliverable — `ExceptionalSet.lean`

Namespace `OneThird.Step8`. `variable {α} [PartialOrder α]
[Fintype α] [DecidableEq α] [DecidableLE α]`.

### §2.1. The three pieces (`step8.tex:2034-2055`)

| Lean | Paper | Definition (from `ChainLiftData` fields) |
|---|---|---|
| `Xexc_mono D` | `X^exc_mono` | union over the three chains of the indices where `pot` fails strict chain-monotonicity, imaged to `α`. |
| `Xexc_band D` | `X^exc_band` | `univ.filter` of `z` sitting in an incomparable pair `(z,y)` with chain-potential gap `> K_bw`. |
| `Xexc_sync D` | `X^exc_sync` | the chain-tail orphans: `A`-elements with `fAB`/`fAC` undefined, `B`-elements with `fBC` undefined. |
| `Xexc D` | `X^exc` | `Xexc_mono D ∪ Xexc_band D ∪ Xexc_sync D`. |

**Design choices, faithfulness:**

* **`X^exc_mono` is genuinely empty** (`Xexc_mono_eq_empty`). The Lean
  `ChainPotential` (`ChainPotentials.lean:267`) carries
  `strictMono{A,B,C}` as *fields* — it is the *post-`prop:71`*
  monotone potential. The non-monotonicity locus is still defined as
  a real filter over the chain indices (`monoExcIdx{A,B,C}`), and its
  emptiness is *earned* from the `strictMono` fields — not asserted.
  This is faithful: the paper says `X^exc_mono` is "empty in branch
  (a)" and `o(1)`-mass after `prop:71` in branch (b).
* **`X^exc_band` uses the chain-potential-gap form**, not the paper's
  "rich" qualifier. The paper's `X^exc_band` is the bandwidth-excess
  *rich* endpoints; `Rich⋆` is not a `ChainLiftData` field. The
  potential-gap form `|a z − a y| > K_bw` over *all* incomparable
  pairs is the exact negation of the genuine `lem:bandwidth` content
  already proved for the concrete witness
  (`gridChainLiftData_bandwidth_genuine`, `ConcreteChainLiftData.lean`).
  Dropping the "rich" qualifier only *enlarges* the set, so the
  cardinality bound stays faithful (a genuine over-approximation).
  The gap is written `abs`-free as `K_bw < a z − a y ∨ K_bw < a y − a z`
  to keep the filter predicate kernel-reducible.
* **`X^exc_sync`** reads the paper's "a partner in another chain is
  undefined by `f_••`" literally: an element is a sync orphan iff the
  synchronization map *out of* its chain index is `none`. There are
  three sync maps (`fAB`, `fAC` on `A`-indices, `fBC` on `B`-indices);
  the paper's "`≤ K_bw` per chain" becomes "`≤ K_bw` per sync map".

### §2.2. The cardinality bound (paper item (i))

* `Xexc_mono_eq_empty : Xexc_mono D = ∅` — earned from `strictMono`.
* `Xexc_eq_band_union_sync : Xexc D = Xexc_band D ∪ Xexc_sync D` —
  `X^exc_mono` drops out.
* `Xexc_sync_card_le : (Xexc_sync D).card ≤ (syncOrphans D.fAB).card
  + (syncOrphans D.fAC).card + (syncOrphans D.fBC).card` —
  **hypothesis-free**, subadditivity of `card` over `∪`/`image`.
* **`Xexc_card_le_of_budget`** — the fully concrete bound. Given a
  band budget `B`, the three per-sync-map orphan bounds (`≤ K_bw`),
  and `hKbw : K_bw ≤ 2`:
  ```
  |X^exc| ≤ B + 6.
  ```
  No abstract constant, no `opaque`, no axiom. The `+6 = 3·2`
  absorbs the three orphan sets at `K_bw ≤ 2`.
* **`Xexc_card_le`** — the contract corollary `|X^exc| ≤ C_exc T`
  under `ExcBudget D T`, with `C_exc T := c₁ T + 6` (`MA-Sig §4.1`,
  paper `C_exc(T) = 3 c_1(T)`).

### §2.3. The grid discharge (§5 of the file)

The sub-ticket-A acceptance certificate — analogue of mg-974c's
`f7a_chainLiftData_constructible`. On the F7a witness
`gridChainLiftData` (the 3×3 grid, a genuine width-3 non-chain
poset):

| Theorem | Content |
|---|---|
| `grid_Xexc_mono` | `X^exc_mono = ∅`. |
| `grid_Xexc_band` | `X^exc_band = ∅` — proved from `gridChainLiftData_bandwidth_genuine` (every incomparable pair within `K_bw = 1`). |
| `grid_Xexc_sync` | `X^exc_sync = {(0,0)}` — the genuine `f_AC` chain-tail orphan (`gridChainLiftData_orphan_forced`). |
| `grid_Xexc` | `X^exc = {(0,0)}` — **non-empty**: the construction is non-vacuous. |
| `grid_Xexc_card` | `|X^exc| = 1`. |
| `grid_excBudget` | `ExcBudget gridChainLiftData T` for **every** `T`, no free hypothesis. |
| `grid_Xexc_card_le` | `|X^exc| ≤ C_exc T` for every `T`, no free hypothesis. |

The discharge is non-degenerate: `X^exc` is genuinely non-empty
(`{(0,0)}`), and `grid_excBudget` exercises a genuine soundness
filter — `ExcBudget` would be **false** for the degenerate `Δ_ℓ`
family (empty sync maps ⇒ every chain element an orphan, orphan count
unbounded).

---

## §3. The `ExcBudget` interface — what is and is not in scope

**Why the bound needs a hypothesis bundle.** The bare `ChainLiftData`
carries no soundness invariant (MA-Sig §11.3): it is inhabited for
`Δ_ℓ` (3 disjoint chains, `SyncMap.empty` maps, `K_bw := 0`), where
`X^exc_sync` is *all* of `A ∪ B` — not `O_T(1)`. A theorem asserting
`|X^exc| ≤ C_exc T` from the bare structure alone would be **false**.
This is the §11.3 caveat, anticipated by R1.

**`ExcBudget D T`** (a `Prop` structure) pins the precise extra facts
— exactly the paper's three `O_T(1)` ingredients:

* `band_le : (Xexc_band D).card ≤ c₁ T` — `lem:bandwidth`, pushed to
  ground support.
* `orphan_{AB,AC,BC} : (syncOrphans D.f••).card ≤ D.K_bw` — the
  per-chain orphan bound (`step8.tex:2191`, "`≤ K_bw` per chain").

(`X^exc_mono` needs no field — it is *proved* empty.)

`ExcBudget` is **not inert**: it is genuinely satisfiable (the grid
satisfies it for every `T`, `grid_excBudget`) and genuinely *fails*
for `Δ_ℓ`. It is a real soundness filter.

**In scope for sub-ticket A:** the construction, the bound modulo
`ExcBudget`, and the unconditional grid discharge. **Out of scope
(S7-F-Z / Piece 1):** deriving `ExcBudget D T` from the bridge's
`hCex : IsGammaCounterexample α γ` + the Steps-1-7 cascade outputs.
This is the Resolution-A design from the PIECE-3 DESIGN NOTE: build
against the bare structure, thread `hCex`, name the exact obligation.

---

## §4. The `opaque c₁` constant

`MA-Sig §4.1` pins `def C_exc : ℕ → ℕ` (paper `C_exc(T) = 3 c_1(T)`).
The Step-5 constant `c_1(T)` of `lem:endpoint-mono` is supplied by the
not-yet-ported Steps-1-7 cascade (Piece 1). It is modelled here by
`opaque c₁ : ℕ → ℕ` — an **opaque definition, not an axiom**: it does
not appear in `#print axioms`, and `AXIOMS.md` is unchanged.

The load-bearing content is `Xexc_card_le_of_budget`, which takes the
band budget as an explicit `B : ℕ` and **does not mention `c₁`** — so
the genuine mathematical content is independent of the `opaque`
modelling choice. `Xexc_card_le` / `C_exc` / `ExcBudget` are the thin
contract-shaped packaging on top.

When Piece 1 lands the genuine Step-5 constant, `c₁` should be
replaced by the real cascade output and `Xexc_card_le` re-proved (it
is a one-line corollary of `Xexc_card_le_of_budget`).

`#print axioms Xexc_card_le_of_budget` / `Xexc_card_le` /
`grid_Xexc_card_le`: only the standard `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx`, no project axiom.

---

## §5. Acceptance bars

- [x] Read-first set consumed: onboarding doc; scoping §2.3; R1 state
  doc; Checkpoint-3 audit; MA-Sig §4/§11.
- [x] `X^exc_mono`, `X^exc_band`, `X^exc_sync` each constructed as a
  `Finset α` derived from the `ChainLiftData` fields.
- [x] `X^exc` = the union; `Xexc_eq_band_union_sync` proved.
- [x] `|X^exc| ≤ C_exc T` proved — genuine `O_T(1)` bound, not inert
  (`Xexc_card_le_of_budget` concrete + `Xexc_card_le` contract form).
- [x] `X^exc_mono = ∅` *earned* from `ChainPotential.strictMono`,
  not asserted.
- [x] No degenerate/inert witness; no `sorry`; no new `axiom`;
  `AXIOMS.md` unchanged.
- [x] File builds; imported into `OneThird.lean`; full `OneThird`
  build green.
- [x] Concrete non-degenerate discharge on the F7a grid witness
  (`X^exc = {(0,0)}` non-empty; bound closes with no free hypothesis).
- [x] The `ExcBudget` interface (the S7-F-Z obligation) named and
  documented; the §11.3 bare-structure caveat disclosed honestly.
- [x] Non-triviality bar cleared: the bound is genuine `O_T(1)`;
  the obligation is well-posed (not ill-posed — Resolution A).

---

## §6. Forward action — Piece 3 status

* **Sub-arc mg-S7-F-A is complete.** `X^exc` and the item-(i)
  cardinality bound are in tree.
* **mg-S7-F-B (synchronization maps)** — parallelizable; defines
  `f_AB/f_AC/f_BC` on `X∖X^exc` with monotonicity. May reuse
  `syncOrphans` / `Xexc_sync` from this file.
* **mg-S7-F-C (band assembly)** — constructs the
  `LayeredDecomposition (X∖X^exc)` with `L.w ≤ 4`; the (L1)-(L4)
  verifications. Will consume `Xexc` and `Xexc_eq_band_union_sync`.
  Note the design choice that `X^exc_band` is the all-incomparable-pairs
  potential-gap form — the (L2) verification should use that the
  *complement* `X∖X^exc_band` has every incomparable pair within
  `K_bw`.
* **mg-S7-F-Z (integration)** — must discharge `ExcBudget D T` from
  `hCex` + the cascade. This is where the §3 obligation lands.

---

## §7. Cross-reference index

### §7.1. Lean (this session)

* `lean/OneThird/Step8/ExceptionalSet.lean` (NEW) — namespace
  `OneThird.Step8`.
  * `monoExcIdx{A,B,C}`, `Xexc_mono`, `Xexc_band`, `Xexc_sync`,
    `Xexc` — the constructions.
  * `syncOrphans`, `mem_syncOrphans`, `mem_Xexc_band` — helpers.
  * `Xexc_mono_eq_empty`, `Xexc_eq_band_union_sync`,
    `Xexc_sync_card_le` — hypothesis-free structural facts.
  * `c₁` (opaque), `C_exc`, `ExcBudget` — the contract packaging.
  * `Xexc_card_le_of_budget` (concrete), `Xexc_card_le` (contract) —
    paper item (i).
  * `grid_Xexc{_mono,_band,_sync,,_card}`, `grid_excBudget`,
    `grid_Xexc_card_le` — the §5 grid discharge.
* `lean/OneThird.lean` — adds the `ExceptionalSet` import.

### §7.2. Lean (consumed, unmodified)

* `lean/OneThird/Step8/ChainPotentials.lean:328` — `ChainLiftData α`;
  `:211` `SyncMap`; `:267` `ChainPotential`.
* `lean/OneThird/Step8/ConcreteChainLiftData.lean` —
  `gridChainLiftData` and `gridChainLiftData_bandwidth_genuine`,
  `gridChainLiftData_orphan_forced` (the §5 inputs).

### §7.3. Predecessor docs / work items

* `docs/state-S7F-R1-Session1.md` (mg-974c) — the concrete
  `ChainLiftData`; F7a GREEN.
* `docs/state-S7F-Checkpoint3-Session1.md` (mg-ca83) — Checkpoint 3;
  the bridge consumes a `ChainLiftData`.
* `docs/state-MA-Sig-Session1.md` §4.1 (`C_exc`), §4.2 §E (the
  bridge contract), §11.3 (the bare-structure caveat).
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 — Piece 3.
* `step8.tex:2009-2089` — `lem:layered-from-step7`, item (i).

---

## §8. Maintenance contract

This file is the state record for FULL REFACTOR Phase-2 Piece 3
sub-arc `mg-S7-F-A` (mg-08d7). It owns the Lean file
`Step8/ExceptionalSet.lean`. Supersede it only if a later session
changes that file's deliverable. If Piece 3 adopts MA-Sig §11.3
resolution (B) (a strengthened `ChainLiftData` carrying the soundness
invariant), the `ExcBudget` interface here should be re-evaluated —
some of its fields may become derivable from the strengthened
structure.
