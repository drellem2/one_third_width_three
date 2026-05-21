# State — MA-Cascade — Session 1: the Steps 1-7 cascade wiring

**Owner.** `mg-52e0` (OneThird-MA-Cascade) — FULL REFACTOR Phase 2,
Piece 4 (the `MainAssembly` proof-by-contradiction refactor), body
sub-ticket.

**Scope.** Build the Steps-1-7 cascade wiring of the pinned Piece-4
signature contract `docs/state-Piece4-Sig-Session1.md` (mg-92a8) §4.5:
`stepsOneToSevenCascade` (producing the Step-5 dichotomy from the
low-conductance witness) and the **F2-widened** `chainLiftData_of_cascade`
(producing a bridge-ready `ChainLiftData`).

**Deliverable.** `lean/OneThird/Step8/Cascade.lean` (NEW), wired into
`lean/OneThird.lean`. `lake build OneThird` succeeds (1459 jobs).

---

## §0. Verdict — GREEN-cascade-wiring-landed + one disclosed axiom

The Steps-1-7 cascade wiring is built to the mg-92a8 §4.5 pinned
signatures. The single most important pin — **finding F2**, the
F2-widened `chainLiftData_of_cascade` codomain emitting all three
conjuncts (`K_bw ≤ 2`, `PotPosetMono`, `ExcBudget cld T`) — is
honoured: `Step5C` and `chainLiftData_of_cascade` both emit the full
three-conjunct codomain the landed S7-F bridge `lem_layered_from_step7`
consumes. The codomain is **satisfiability-verified against the landed
bridge** (`grid_Step5C` / `grid_Step5C_fires_bridge`) — the
non-triviality bar (the 8th-vacuity lesson) is met.

The genuine mathematical content of Steps 1-7 is not in tree and is
not portable in this ticket's budget; it is delivered as **one named
project axiom** `stepsOneToSevenCascade`, certified in `AXIOMS.md`.
This is a `sorry → documented axiom` upgrade (the Steps-1-7 gap was
the `MainAssembly.lean` cap-5 `sorry`), not new debt. Four findings
F-Cascade-1..4 record the drift from the mg-92a8 contract; all are
recorded in that contract's §10.2 per its §9 maintenance clause.

---

## §1. What landed

`lean/OneThird/Step8/Cascade.lean`:

| Symbol | Kind | Axioms |
|---|---|---|
| `HypothesisArithmetic` | structure (paper Hypothesis A `hyp:arith`) | — |
| `c5` / `c6` / `delta0` / `T_zero` | `opaque` (Piece-1 constants; not axioms) | — |
| `n_zero : ℚ → ℕ → ℕ` | def (contract §4.5 realisability threshold) | — |
| `n_zero_ceil_ge` | theorem (correctness of `n_zero`) | axiom-free |
| `Step5R` / `Step5C` | def (the two cascade outcomes) | — |
| `not_hasBalancedPair_of_isGammaCounterexample` | theorem | axiom-free |
| `stepsOneToSevenCascade` | **axiom** (the Steps-1-7 cascade) | `stepsOneToSevenCascade` |
| `chainLiftData_of_cascade` | theorem (F2-widened constructor) | axiom-free |
| `GridChainLift.grid_Step5C` | theorem (non-vacuity) | axiom-free |
| `GridChainLift.grid_Step5C_fires_bridge` | theorem (non-vacuity) | axiom-free |

`#print axioms`: `chainLiftData_of_cascade` and the four supporting
theorems depend only on `propext` / `Classical.choice` / `Quot.sound`.
`stepsOneToSevenCascade` is the one new project axiom.

---

## §2. Design

The genuine Steps-1-7 mathematical content (BK-expansion ⇒ Steps 1-4
staircase ⇒ Step-5 Rich-or-Collapse ⇒ Step-6 closures ⇒ Step-7
layered collapse) is one indivisible gap. The "gap" is conserved: it
must surface as exactly one axiom (or `sorry`), since the pinned
signatures forbid adding a fresh cascade hypothesis. The design
places it cleanly:

* **`Step5C α T := ∃ cld, cld.K_bw ≤ 2 ∧ cld.PotPosetMono ∧
  ExcBudget cld T`** — the F2-widened bridge-ready codomain. This *is*
  `chainLiftData_of_cascade`'s output type, so the constructor is a
  genuine extraction.
* **`Step5R α γ T := HasBalancedPair α`** — the richness route's net
  conclusion (Step 5 (R) composed with Step 6 `cor:pointwise`). In the
  proof-by-contradiction it is excluded by `hCex`.
* **`stepsOneToSevenCascade` (axiom)** — produces `Step5R ∨ Step5C`
  from the low-conductance witness `hS`. Consumes `hS` and every other
  cascade hypothesis (all load-bearing for an axiom).
* **`chainLiftData_of_cascade` (axiom-free theorem)** — `rcases` on
  `Step5R ∨ Step5C`: the `Step5R` branch is closed by
  `not_hasBalancedPair_of_isGammaCounterexample hγ_pos hCex` (so `hCex`
  is load-bearing, per contract §5.3); the `Step5C` branch is the
  direct F2-widened extraction.

This split keeps the contract-pinned `chainLiftData_of_cascade` a
genuine theorem and isolates the un-ported math in one transparently
named axiom — `#print axioms width3_one_third_two_thirds` will show
`stepsOneToSevenCascade`, immediately legible to an auditor as "Steps
1-7 not yet ported".

---

## §3. Non-vacuity — satisfiable against the landed bridge

The acceptance bar (8th-vacuity lesson): the cascade output must be
satisfiable against the landed bridge.

* `grid_Step5C (T) : Step5C (Fin 3 × Fin 3) T` — the R1 witness
  `gridChainLiftData` (`ConcreteChainLiftData.lean`, mg-974c) inhabits
  all three F2-widened conjuncts on a genuine width-3 non-chain
  9-element poset, via `gridChainLiftData_K_bw_le_two`,
  `grid_PotPosetMono`, `grid_excBudget`.
* `grid_Step5C_fires_bridge (T)` — that `Step5C` witness feeds
  `lem_layered_from_step7` directly to a genuine three-cap output.

Both `PotPosetMono` and `ExcBudget` provably *fail* on the degenerate
`Δ_ℓ` family (contract §5.3), so the codomain is a genuine soundness
filter, not a disguised `True`.

---

## §4. Findings — drift from the mg-92a8 contract

Recorded in `docs/state-Piece4-Sig-Session1.md` §10.2 per that
contract's §9 maintenance clause.

* **F-Cascade-1** — `stepsOneToSevenCascade` is a named project axiom,
  not a theorem (§4.5 said theorem). The Steps-1-7 cascade is not in
  tree; this is the contract §7 "hold-the-line" situation. The honest
  representation is a paper-faithful, `AXIOMS.md`-certified axiom.
* **F-Cascade-2** — contract §6's axiom accounting was incomplete; the
  corrected post-refactor headline axiom set is
  `{brightwell_sharp_centred, lem_layered_balanced_irreducible_base,
  stepsOneToSevenCascade}`. The Steps-1-7 gap was a `sorry`; Piece 4
  upgrades it to a documented axiom.
* **F-Cascade-3** — `Step5R`/`Step5C` carry genuine content rather
  than wrapping the structurally-weak in-tree `Step5.Step5Richness`/
  `Step5.Step5Collapse` (which would be vacuous).
* **F-Cascade-4** — `chainLiftData_of_cascade`'s `hP`/`hI` are inert
  (given the F2-widened `Step5C`); `hγ_pos`/`hCex`/`hCascade` are
  load-bearing. `[DecidableLE α]` was added (needed by `ExcBudget`;
  §4.5 omitted it — same as the F7 finding).

---

## §5. Cross-reference index

* `lean/OneThird/Step8/Cascade.lean` — the deliverable.
* `lean/OneThird/Step8/LayeredFromStep7.lean:152` —
  `lem_layered_from_step7`, the S7-F bridge `chainLiftData_of_cascade`
  feeds.
* `lean/OneThird/Step8/TheoremEWiring.lean` —
  `theoremE_lowConductanceWitness`, producing the `hS` input.
* `lean/OneThird/Step8/ConcreteChainLiftData.lean` —
  `gridChainLiftData`, the R1 non-vacuity witness.
* `lean/AXIOMS.md` — the `stepsOneToSevenCascade` certification entry.
* `docs/state-Piece4-Sig-Session1.md` (mg-92a8) §4.2/§4.5/§5.3/§6/§9/
  §10.2 — the pinned contract and the landing record.
* Work items: mg-52e0, mg-92a8, mg-7969 (MinCex), mg-3638 (ThmE),
  mg-02cd (Piece 3), mg-65de (Piece 6), mg-974c (R1 witness),
  mg-ca83 (Checkpoint 3), mg-ac13 / mg-6ab8 (Steps-1-7 axiomatisation
  posture).
