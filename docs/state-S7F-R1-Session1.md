# State — S7-F R1 — Session 1: re-point Piece 2 to a concrete `ChainLiftData`; settle F7a

**Ticket:** mg-974c (OneThird-S7F-R1 — re-point Piece 2 concretisation
to a concrete `ChainLiftData`; settle the F7a constructibility
question).
**Type:** Lean deliverable + go/no-go on an open question.
**Parent:** FULL REFACTOR Phase 2, Checkpoint-3 re-scope
(`docs/state-S7F-Checkpoint3-Session1.md`, mg-ca83 §6 R1).
**Depends:** mg-3119 (S7F-R2 — the reconciled bridge contract).
**Predecessors read:** `docs/PROOF-STRUCTURE-ONBOARDING.md`;
`docs/state-S7F-Checkpoint3-Session1.md` (the Checkpoint-3 audit —
defines F7a); `docs/state-MA-Sig-Session1.md` §11 (the R2 reconciled
contract); `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.2/§2.3.

---

## §0. Verdict — **GREEN — F7a is constructible**

**A concrete, non-degenerate `ChainLiftData α` for a width-3 non-chain
poset IS constructible.** F7a — the open question Checkpoint 3 flagged
and R2 left provisional — is **settled GREEN**.

The deliverable is `lean/OneThird/Step8/ConcreteChainLiftData.lean`
(NEW, sorry-free, axiom-free, builds clean, imported into
`OneThird.lean`): `gridChainLift.gridChainLiftData` is a concrete
`ChainLiftData (Fin 3 × Fin 3)` on the 3×3 grid — a genuine width-3,
non-chain, 9-element finite poset — and it is **non-degenerate on
every axis Checkpoint 3 Finding D flagged**:

| Finding D degeneracy (rejected for `L_S7E`) | This deliverable |
|---|---|
| constant BFS potential (`signedWeight := fun _ => 0`) | `potFun (i,j) = i + j` — **non-constant**, 5 distinct values `{0,1,2,3,4}` (`gridChainLiftData_pot_nonconstant`) |
| empty sync maps (`SyncMap.empty`, all `none`) | `f_AB`, `f_BC` total + non-constant; `f_AC` genuinely partial with a real orphan (`gridChainLiftData_sync_genuine`) |
| inert bound (`bandwidth ≤ 4` reducing to `4 ≤ 4`) | `K_bw = 1` is the **actual** max potential gap over incomparable pairs, and **tight** (`gridChainLiftData_bandwidth_genuine`, `_bandwidth_tight`) |
| zero budget / empty sets | three genuine length-3 chains covering all 9 elements (`gridChainLiftData_chains_genuine`) |

`f7a_chainLiftData_constructible` packages it as the exact codomain of
the §4.2 §D′ constructor: `∃ cld : ChainLiftData α, cld.K_bw ≤ 2`.

**Scoped disclosure (not a hedge — a real limitation, §4 below).**
GREEN here means the **structure is constructible**. It does *not*
mean the S7-F bridge *body* is dischargeable: per MA-Sig §11.3 the
**bare** `ChainLiftData` structure carries no soundness invariant, so
it is inhabited even for the `Δ_ℓ` family where the bridge conclusion
fails. That gap — §11.3 resolution (B), a *strengthened* structure —
is a **Piece-3 / F7-bridge** concern, explicitly **not** F7a and not
R1. R1 settles exactly what F7a asked: *is the structure
constructible, non-degenerately?* Yes.

Per MA-Sig §11.4 this is **case 1**: R1 lands GREEN with a concrete
non-degenerate `ChainLiftData α` matching the **bare** structure, so
**§4.2 §D′/§E stand as pinned** — no re-pin needed.

---

## §1. What R1 is, and what F7a is

Checkpoint 3 (mg-ca83) found Piece 2 delivered the wrong object:
`L_S7E : Step7.LayeredWidth3` is a rich-pair window-confinement
packaging (a `bandwidth : ℕ` plus a partition of `richPairs`), with no
poset-structural content; the S7-F bridge `lem:layered-from-step7`
consumes a **`ChainLiftData α`** instead — the bundle of a Dilworth
triple `A/B/C`, a chain potential, the sync maps `f_AB/f_AC/f_BC`, and
a bandwidth constant `K_bw` (`Step8/ChainPotentials.lean:328-340`).

R2 (mg-3119) reconciled the bridge contract (MA-Sig §4.2 §E/§D′,
scoping §2.3) to consume a `ChainLiftData α`. R2 explicitly left one
question open and flagged the whole contract **provisional** on it:

> **F7a.** Is a concrete, **non-degenerate** `ChainLiftData α`
> constructible for `α` a width-3 non-chain poset? No concrete
> `ChainLiftData` instance existed in tree (mg-ca83 §6 R1: referenced
> only in `LayeredBridges.lean` / `MainAssembly.lean` / its own
> defining file, never instantiated).

R1 (this ticket) settles F7a. Per the ticket, the valid outcomes were
(a) construct the concrete `ChainLiftData` genuinely, or (b)
RED-block-and-report if it genuinely cannot be constructed for a
minimal counterexample — *without* papering over with a degenerate or
inert witness. Outcome: **(a) — constructed genuinely.**

---

## §2. The deliverable — `gridChainLiftData`

`lean/OneThird/Step8/ConcreteChainLiftData.lean`, namespace
`OneThird.Step8.GridChainLift`.

**Carrier.** `Grid := Fin 3 × Fin 3` under the product partial order
— a width-3, non-chain, 9-element finite poset (the same type as
`Step5/G1G2Grounded.lean`'s `W3`; `W3_widthAtMost_three` /
`W3_not_chain` already establish width 3 and non-chain in tree). The
grid is a genuine, *content-rich* carrier — unlike `Antichain3` (the
`L_S7E_antichain3` carrier), it has genuine cross-chain
comparabilities, so the sync maps and potential carry real content.

**The `ChainLiftData` components (`ChainPotentials.lean:328`):**

* **`triple : ChainTriple Grid`** — the three columns
  `A = {0}×Fin 3`, `B = {1}×Fin 3`, `C = {2}×Fin 3`, each a genuine
  strictly-monotone length-3 `IndexedChain`, jointly covering all 9
  elements (`cover` discharged by `decide`). This is a genuine
  Dilworth cover for a width-3 poset.
* **`pot : ChainPotential triple`** — the potential
  `a(i,j) = i + j` (the grid rank function), `ℤ`-valued, strictly
  increasing along every column. **Non-constant**: 5 distinct values.
* **`K_bw := 1`** — the bandwidth constant. **Non-inert**: §3 proves
  `1` is the *actual* maximum chain-potential gap across incomparable
  pairs, and that it is tight.
* **`fAB, fAC, fBC : SyncMap`** — the `K_bw`-windowed argmin
  alignments:
  * `f_AB = [0, 0, 1]` — total, non-constant. (`A` potentials
    `[0,1,2]`; `B` potentials `[1,2,3]`; each `A` index aligns to the
    nearest `B` index within the `K_bw=1` window.)
  * `f_AC = [none, 0, 0]` — **genuinely partial**. `A` index `0`
    (element `(0,0)`, potential `0`) is a chain-tail orphan
    (`X^exc_sync`): its potential is more than `K_bw=1` away from
    *every* element of `C` (potentials `[2,3,4]`), so it has no
    `C`-partner. This is a real bandwidth-window exclusion, *not* an
    arbitrary `none` — `gridChainLiftData_orphan_forced` proves it.
  * `f_BC = [0, 0, 1]` — total, non-constant.

  All three are weakly monotone (`weakly_monotone` by `decide`); none
  is `SyncMap.empty`.

The whole file is sorry-free and axiom-free; the field obligations
are discharged by explicit tactics (`fin_cases` + `decide` for the
strict-monotone chains and potential; `decide` for the finite
`cover` / `weakly_monotone` / bandwidth facts).

---

## §3. Non-degeneracy — clearing every Finding D bar

The ticket's non-triviality bar: *no inert bounds, no degenerate
witness (constant potential / zero budget / empty sets); the sync
maps and chain potential must carry genuine content.* Each is
discharged by a named theorem.

* **`gridChainLiftData_pot_nonconstant`** — `potFun` takes 5 distinct
  values. The potential is genuinely non-constant — the opposite of
  Finding D's constant BFS potential.
* **`gridChainLiftData_bandwidth_genuine`** — *every* incomparable
  pair `x, y` of grid elements has `|potFun x − potFun y| ≤ K_bw`.
  This is the genuine `lem:bandwidth` content: `K_bw` is the *actual*
  width bound, not a free parameter fixed to a literal. **This is the
  property that distinguishes a genuine carrier from a `Δ_ℓ`-style
  vacuous one** — see §4.
* **`gridChainLiftData_bandwidth_tight`** — there is an incomparable
  pair with potential gap *exactly* `K_bw = 1`. So `K_bw` cannot be
  lowered to `0`: the bound is tight, hence non-inert.
* **`gridChainLiftData_sync_genuine`** — `f_AB`, `f_BC` have full
  domain (`= univ`) and are non-constant; `f_AC` has a non-empty but
  *proper* domain (the genuine orphan). No sync map is `SyncMap.empty`.
* **`gridChainLiftData_orphan_forced`** — the `f_AC` orphan is genuine
  `X^exc_sync`: `A` index `0` is strictly more than `K_bw` away from
  every element of `C`. The orphan is *forced* by the bandwidth
  window, which makes `K_bw` load-bearing in the construction.
* **`gridChainLiftData_chains_genuine`** — three real length-3 chains
  covering the full 9-element ground set.

---

## §4. The §11.3 caveat — what GREEN does *not* mean

This is disclosed prominently because it is a real limitation, not a
hedge. MA-Sig §11.3 established:

> The **bare** `ChainLiftData α` structure carries no field asserting
> that `pot` / the sync maps are the genuine Steps-1-7 cascade
> output. It is **inhabited for `Δ_ℓ`** (the 3-disjoint-chains
> family) — take the three chains, any strictly-monotone potential,
> `SyncMap.empty` maps, `K_bw := 0` — yet the bridge conclusion
> `C(Δ_ℓ)` (a layered decomposition with `w ≤ 4`) is **false** for
> large `ℓ`.

So: **constructibility of the structure (F7a, settled GREEN here)
does not by itself make the S7-F bridge *body* go through.** That is
the separate §11.3 resolution-(B) question — strengthen the structure
with soundness/consistency fields so that *every* inhabitant drives
the bridge conclusion. Resolution (B) is a **Piece-3 / F7-bridge**
concern; it is explicitly *not* F7a and *not* R1's scope.

R1 does, however, demonstrate `gridChainLiftData` is the **genuine**
kind of witness, not a `Δ_ℓ`-style vacuous-but-inhabited one, with
two independent in-tree proofs:

1. **`gridChainLiftData_bandwidth_genuine`** — the grid's chain
   potential confines *every* incomparable pair within `K_bw = 1`.
   This property is provably **false** for `Δ_ℓ`: disjoint chains
   have cross-chain incomparable pairs whose potential gaps grow with
   `ℓ`, so no finite `K_bw` bounds them. The grid *has* a genuine
   bandwidth bound; `Δ_ℓ` does not.
2. **`gridLayered` / `grid_admits_bounded_layered`** (§7 of the Lean
   file) — the grid carrier admits a genuine ground-set
   `LayeredDecomposition Grid` with depth `K = 5` and interaction
   width `w = 1 ≤ 4` — the exact object shape the S7-F bridge is
   meant to *produce*. (The `w = 1` is tight: `w = 0` fails
   `forced_lt`.) This is a concrete *witness* that the target exists
   for this `α` — it is **not** the bridge itself (the bridge is the
   general `ChainLiftData α → LayeredDecomposition` function, Piece
   3). For `Δ_ℓ` with large `ℓ` no such bounded-`w` decomposition
   exists.

So the GREEN verdict is honest and load-bearing: a concrete
non-degenerate `ChainLiftData` exists, *and* the chosen carrier is a
genuine one on which the whole pipeline (bandwidth bound + layered
decomposition `w ≤ 4`) genuinely closes.

---

## §5. MA-Sig §11.4 — case 1 applies; the contract stands

MA-Sig §11.4 enumerated three F7a resolutions:

1. **R1 lands GREEN with a concrete non-degenerate `ChainLiftData α`
   matching the bare structure** ⇒ §4.2 §D′/§E **stand as pinned**.
2. R1 finds the bare structure insufficient and *strengthens* it ⇒
   re-pin §4.2 §D′/§E to the strengthened type.
3. R1 returns RED-not-constructible ⇒ reopen §4.2 §D′/§E.

**This R1 is case 1.** `gridChainLiftData` matches the **bare**
`ChainLiftData` structure as defined at `ChainPotentials.lean:328` —
no fields added, no structure change. Therefore **§4.2 §D′
(`chainLiftData_of_cascade`) and §E (`lem_layered_from_step7`) stand
as pinned by R2; no re-pin is required.**

The MA-Sig contract was flagged GREEN-reconciled-**PROVISIONAL** by
R2, provisional precisely on F7a. With F7a now GREEN, the
provisionality on *constructibility* is discharged. The contract's
remaining open work — the §11.3 resolution-(B) soundness question and
the actual cascade wiring into `chainLiftData_of_cascade` — is
Piece-3 execution, tracked there, not a contract defect.

---

## §6. Forward action — Piece 3 status

* **Checkpoint 3's R1 is complete.** Both halves of the Checkpoint-3
  re-scope (mg-ca83 §6) are now done: R2 (mg-3119) reconciled the
  contract; R1 (this ticket) settled F7a GREEN and delivered the
  concrete `ChainLiftData`.
* **Piece 3 (the S7-F bridge, sub-arcs mg-S7-F-A …) is unblocked on
  the F7a question.** The bridge input type is pinned
  (`ChainLiftData α`), and a concrete non-degenerate inhabitant
  exists. Piece 3 may now be scoped/dispatched.
* **Piece 3 inherits the §11.3 resolution-(B) decision.** Before or
  during Piece 3, the bridge designers must decide whether the bridge
  body is provable from the *bare* `ChainLiftData` (relying on `hCex`
  as the domain pin, MA-Sig §11.3 resolution (A)) or whether the
  structure needs soundness fields (resolution (B)). R1 does not
  pre-empt that choice; it only confirms the bare structure is
  inhabited non-degenerately.
* **`L_S7E` / `LayeredWidth3` / `prop_72` / `lem_bandwidth_le_four`**
  remain in tree as sound **Step-7 internal** scaffolding (mg-ca83 §6
  R3). They are not deleted and not the bridge input; their role is
  unchanged by R1.

---

## §7. Acceptance bars

- [x] Read-first set consumed: onboarding doc; Checkpoint-3 audit;
  MA-Sig §11 (R2 reconciled contract); scoping §2.2/§2.3.
- [x] A concrete `ChainLiftData α` term constructed in Lean —
  `gridChainLiftData : ChainLiftData (Fin 3 × Fin 3)`.
- [x] Dilworth triple `A/B/C` — three genuine length-3 chains
  covering the 9-element ground set.
- [x] Chain potential — genuine, non-constant (5 distinct values),
  strictly monotone along each chain.
- [x] Sync maps `f_AB/f_AC/f_BC` — genuine content; not
  `SyncMap.empty`; one genuinely partial with a real orphan.
- [x] `K_bw` — non-inert; proven to be the actual, tight max
  potential gap over incomparable pairs.
- [x] Non-triviality bar cleared on every Finding D axis (§3 table).
- [x] No degenerate/inert witness; no `sorry`; no new axiom.
- [x] File builds; imported into `OneThird.lean`; full `OneThird`
  build green.
- [x] F7a verdict stated clearly (§0) with the §11.3 caveat
  disclosed honestly (§4).
- [x] MA-Sig §11.4 resolution recorded — case 1 (§5).

---

## §8. Cross-reference index

### §8.1. Lean (this session)

* `lean/OneThird/Step8/ConcreteChainLiftData.lean` (NEW) — the
  concrete `ChainLiftData`; namespace `OneThird.Step8.GridChainLift`.
  * `gridChainLiftData` — the deliverable.
  * `f7a_chainLiftData_constructible` — the F7a verdict theorem.
  * `gridChainLiftData_{K_bw_le_two, bandwidth_genuine,
    bandwidth_tight, pot_nonconstant, sync_genuine, orphan_forced,
    chains_genuine}` — non-degeneracy certificates.
  * `gridLayered` / `grid_admits_bounded_layered` — the genuine
    `LayeredDecomposition` corroboration (§4).
* `lean/OneThird.lean` — adds the `ConcreteChainLiftData` import.

### §8.2. Lean (consumed, unmodified)

* `lean/OneThird/Step8/ChainPotentials.lean:328-340` —
  `ChainLiftData α` (the structure instantiated); `:211` `SyncMap`;
  `:238` `SyncMap.empty`; `:267` `ChainPotential`; `:132`
  `ChainTriple`; `:70` `IndexedChain`.
* `lean/OneThird/Step8/LayeredReduction.lean:113-147` —
  `LayeredDecomposition` (the `gridLayered` target type).
* `lean/OneThird/Step5/G1G2Grounded.lean:132` — `W3 := Fin 3 × Fin 3`
  (the same carrier; `W3_widthAtMost_three` / `W3_not_chain`).

### §8.3. Predecessor docs / work items

* `docs/state-S7F-Checkpoint3-Session1.md` (mg-ca83) — Checkpoint 3;
  §6 R1 the re-scope; Finding D the degeneracy bar.
* `docs/state-MA-Sig-Session1.md` §11 (mg-3119 / R2) — the
  reconciled contract; §11.3 the bare-structure caveat; §11.4 the
  F7a provisionality cases.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.2/§2.3 — the
  re-pointed Piece 2 / Piece 3 boundary.
* `docs/PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #9 — the
  `LayeredWidth3 ≠ LayeredDecomposition` standing lesson.

---

## §9. Maintenance contract

This file is the state record for FULL REFACTOR Phase-2 Checkpoint-3
part R1 (mg-974c). It is a delivery snapshot; it owns the Lean file
`Step8/ConcreteChainLiftData.lean`. Supersede it only if a later
session changes that file's deliverable. If Piece 3 adopts §11.3
resolution (B) and strengthens the `ChainLiftData` structure, the
`gridChainLiftData` witness here must be updated in the same commit
that lands the strengthened structure, and this file's §5 (case 1)
re-evaluated.
