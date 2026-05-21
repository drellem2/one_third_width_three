# State — S7-F-Z — Session 1: integration + QA — finalise `lem_layered_from_step7`, Piece 3 complete

**Ticket:** mg-02cd (OneThird-S7-F-Z — S7-F bridge: integration and
QA, finalize `lem_layered_from_step7`).
**Type:** Lean deliverable (integration).
**Parent:** FULL REFACTOR Phase 2, Piece 3 (the S7-F bridge);
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 sub-arc
`mg-S7-F-Z`. **When this lands, Piece 3 is complete.**
**Depends:** mg-876f (S7-F-D), transitively mg-08d7 (A), mg-120d (B),
mg-bcc9 (C), mg-974c (R1).
**Predecessors read:** `docs/PROOF-STRUCTURE-ONBOARDING.md`;
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3;
`docs/state-S7F-A-Session1.md`; `docs/state-S7F-B-Session1.md`;
`docs/state-S7F-C-Session1.md`; `docs/state-S7F-D-Session1.md`;
`docs/state-S7F-R1-Session1.md`; `docs/state-MA-Sig-Session1.md`
§4.2 §E + §4.3 + §11.

---

## §0. Verdict — **GREEN — `lem_layered_from_step7` finalised; Piece 3 complete**

The S7-F bridge is **assembled and finalised**. The deliverable is
`lean/OneThird/Step8/LayeredFromStep7.lean` (NEW, sorry-free, **no new
`axiom`**, builds clean, imported into `OneThird.lean`; full
`OneThird` build green, 1448 jobs) plus the `compactifySelf`
extension to `lean/OneThird/Step8/LayeredDecomposition/Compactify.lean`:

* **`lem_layered_from_step7`** — the finalised S7-F bridge. Consumes a
  `ChainLiftData α` (`cld`) with `K_bw ≤ 2` and the two Resolution-A
  obligations (`hMono : cld.PotPosetMono`, `hBudget : ExcBudget cld T`),
  produces the re-pinned **three-cap** output — `Xexc.card ≤ C_exc T`,
  band-nonempty on `[1, L.K]`, `L.w ≤ 4` — on the carrier `↥(Xexcᶜ)`.
  Sorry-free; `#print axioms` = `propext`/`Classical.choice`/`Quot.sound`
  only.
* **`compactifySelf`** (`Compactify.lean` §6) — the same-type
  empty-band compactification. `compactify` changes the carrier
  (`α ↦ ↥S`); the bridge needs the carrier *fixed* and the empty
  bands removed, so the re-pinned cap 2
  (`∀ k ∈ [1, K], (bandSet k).Nonempty`) holds. `compactifySelf` is
  `compactify` specialised to `S := Finset.univ`, kept on `α`; it
  reuses the `compactBand` machinery verbatim. `compactifySelf_w`
  (width preserved), `compactifySelf_K_le` (depth contracts),
  `compactifySelf_bandSet_nonempty` (the cap).
* **`excPerturbLift_of_bridge_output`** — the A–D integration
  boundary: the bridge output carrier `↥((Xexc cld)ᶜ)` is *exactly*
  the carrier S7-F-D's perturbation lift
  `not_isGammaCounterexample_of_exc_balanced_compl` consumes.
* **non-vacuous instantiation** on the concrete R1 witness
  `gridChainLiftData` (`§5`): `grid_lem_layered_from_step7` fires the
  bridge; `gridLayeredFromStep7` is a genuine `LayeredDecomposition`
  on the 8-element `Grid ∖ {(0,0)}` with `w = 3`, depth `K ≥ 2`, a
  non-constant band map; `grid_excPerturbLift_of_bridge` runs the
  whole A–D pipeline carrier-to-carrier.

**The non-triviality bar is cleared (§6).** The bridge genuinely
delivers the 3-cap output — `Xexc` and `L` are constructed, not
asserted; `C_exc T` and `L.w ≤ 4` are genuine quantities, not inert
literals; band-nonemptiness is *earned* by `compactifySelf`. Every
hypothesis is load-bearing. The output is non-vacuous against the
genuine R1 witness, and the obligations genuinely *fail* on `Δ_ℓ`.

**`#print axioms`** (`scripts/PrintAxiomsLayeredFromStep7.lean`):
`lem_layered_from_step7`, `compactifySelf`,
`compactifySelf_bandSet_nonempty`, `grid_lem_layered_from_step7`, the
grid non-degeneracy certificates — `propext`, `Classical.choice`,
`Quot.sound` only. `excPerturbLift_of_bridge_output` and
`grid_excPerturbLift_of_bridge` additionally carry
`brightwell_sharp_centred` — **inherited** from the S7-F-D
`exc_perturb` lift (F6b already carries it; `AXIOMS.md` already
documents it). No `sorryAx`, **no new project axiom**; `AXIOMS.md`
unchanged.

---

## §1. What S7-F-Z is

Piece 3 (the S7-F bridge) was decomposed into sub-arcs A–D + Z
(scoping §2.3). A–D each delivered one ingredient of paper
`lem:layered-from-step7` (`step8.tex:2009-2089`):

| Sub-arc | File | Delivers |
|---|---|---|
| A (mg-08d7) | `ExceptionalSet.lean` | `Xexc`, `C_exc`, `ExcBudget`, `Xexc_card_le` — item (i) |
| B (mg-120d) | `SyncMaps.lean` | wired sync maps, decidable orphans |
| C (mg-bcc9) | `BridgeLayered.lean` | `bridgeLayered : LayeredDecomposition ↥(Xexcᶜ)`, `(L1)`–`(L4)`, `w ≤ 4` — item (ii) |
| D (mg-876f) | `ExcBalancedLift.lean` | the perturbation lift — item (iii) |

**S7-F-Z = the integration.** It wires A–D into the single finalised
theorem `lem_layered_from_step7` and discharges QA. The bridge body
is A (the `Xexc` + `C_exc` bound) ⊕ C (`bridgeLayered`), with B
consumed *transitively* (the exceptional set `Xexc cld` folds in
`Xexc_sync`, built from B's orphan index sets, and `bridgeLayered`
uses B's `anchor_not_refOrphan`). D is wired at the *output boundary*:
the carrier the bridge emits is the carrier D consumes.

---

## §2. The signature — QA finding on the `hCex` domain pin

This is the load-bearing QA finding; it is recorded in full because
it is a genuine refinement of the `MA-Sig §4.2 §E` pinned contract.

### §2.1. The finalised signature

```lean
theorem lem_layered_from_step7 (T : ℕ) (cld : ChainLiftData α)
    (hKbw : cld.K_bw ≤ 2)
    (hMono : cld.PotPosetMono)        -- S7-F-C Resolution-A obligation (prop:71)
    (hBudget : ExcBudget cld T) :     -- S7-F-A Resolution-A obligation (item (i))
    ∃ (Xexc : Finset α) (L : LayeredDecomposition ↥(Xexcᶜ)),
      Xexc.card ≤ C_exc T ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) ∧
      L.w ≤ 4
```

**Every hypothesis is load-bearing.** `cld` / `T` thread everywhere;
`hKbw` is consumed by `Xexc_card_le` *and* `bridgeLayered_w_le_four`;
`hMono` builds `bridgeLayered`; `hBudget` discharges the `C_exc T`
bound. Drop any one and the proof fails — there is no inert
hypothesis.

### §2.2. Why `hCex` is **not** a bridge-body input — the QA finding

`MA-Sig §4.2 §E` pins `lem_layered_from_step7` with `hCex :
IsGammaCounterexample α γ` (plus `γ, hγ_pos, hP, hI, ih`), tagging
`hCex` "LOAD-BEARING under the R2 reconciliation". **Under the
Resolution-A design crystallised by S7-F-A/B/C, that is no longer
accurate** — and carrying `hCex` unused would itself be an inert
hypothesis (exactly what the `mg-02cd` non-triviality bar forbids).
The precise status:

* §4.2 §E's claim that `hCex` is load-bearing is made for a bridge
  taking `cld + hKbw` **without** explicit soundness obligations:
  such a bridge is *false* on the `Δ_ℓ` family (3 disjoint chains —
  the bare `ChainLiftData` is inhabited there, yet the conclusion
  fails), and `hCex` rescues it by being false on `Δ_ℓ` (`§11.3`).
* But that bridge is also **not provable** — the bare `ChainLiftData`
  + `hCex` does not yield `PotPosetMono` / `ExcBudget` (deriving them
  needs the *genuine Steps-1-7 cascade*, which is not ported). This
  is the §11.3 bare-structure caveat. S7-F-A/B/C therefore took
  **Resolution A**: name the missing soundness facts as the explicit,
  decidable obligations `ExcBudget` (A), `BoundedSyncOrphans` (B),
  `PotPosetMono` (C).
* Under Resolution A the `Δ_ℓ`-exclusion role is played by the
  **obligations themselves**: `ExcBudget cld T` and `cld.PotPosetMono`
  both provably *fail* on `Δ_ℓ` (S7-F-A §3, S7-F-C §1.2). So the
  finalised bridge — conditional on `hMono ∧ hBudget` — is already
  vacuously inapplicable on `Δ_ℓ`. `hCex` adds nothing to the bridge
  *body*; it is genuinely redundant there.
* Hence `lem_layered_from_step7` consumes `cld, hKbw, hMono, hBudget`
  and **not** `hCex`. This satisfies "no free hypotheses beyond the
  documented call-site contract": `hKbw` is `§4.2 §E`; `hMono` is the
  documented S7-F-C obligation; `hBudget` is the documented S7-F-A
  obligation. No undocumented hypothesis; no `sorry`.

**Where `hCex` still lives.** `hCex` remains the genuine domain pin
of the *call site* — the `MA-Sig §4.2 §D′` constructor
`chainLiftData_of_cascade` and the §4.3 headline body. The honest
reading of "discharge the obligations at the bridge call site"
(S7-F-A/B/C §3) is: a future **Piece-1** `chainLiftData_of_cascade`,
fed `hCex` + the genuine Steps-1-7 cascade, produces the `cld`
**together with** proofs of `hMono` and `hBudget`, and hands all
three to `lem_layered_from_step7`. The bridge consumes what that
constructor produces. S7-F-Z does not — and cannot — port that
constructor (the cascade is not in tree); it finalises the bridge
*against the obligations*, which is the correct Piece-3 boundary.

**Recommended MA-Sig follow-on (documentation, not Lean).** `§4.2 §E`
should be re-pinned to the signature in §2.1 — drop `γ, hγ_pos, hP,
hI, hCex, ih` from the bridge (none is used), add `hMono` / `hBudget`
— and `§4.2 §D′` re-pinned so `chainLiftData_of_cascade` emits
`∃ cld, cld.K_bw ≤ 2 ∧ cld.PotPosetMono ∧ ExcBudget cld T`. This is a
mechanical pseudo-Lean edit for whoever owns MA-Sig / ports Piece 1;
it does not affect any in-tree Lean file.

### §2.3. The `ih` parameter

`§4.2 §E` also pins a recursion hypothesis `ih`. The 3-cap output is
a pure existence statement about `Xexc` / `L`; it does **not**
recurse. `ih` is dropped for the same reason as `hCex` — it would be
inert. (The strong-induction recursion lives in Piece 6
`lem_layered_balanced_full`, which already carries its own.)

---

## §3. The deliverable — `LayeredFromStep7.lean`

Namespace `OneThird.Step8`. Three sections.

* **§1 — `lem_layered_from_step7`.** The finalised bridge (§2.1).
  Proof: `refine ⟨Xexc cld, compactifySelf (bridgeLayered cld hMono),
  …⟩`; cap 1 = `Xexc_card_le cld T hKbw hBudget` (S7-F-A); cap 2 =
  `compactifySelf_bandSet_nonempty`; cap 3 = `compactifySelf_w` ▸
  `bridgeLayered_w_le_four cld hMono hKbw` (S7-F-C).
* **§2 — `excPerturbLift_of_bridge_output`.** The A–D wiring: threads
  S7-F-A's `Xexc cld` into S7-F-D's `↥(Tᶜ)`-carrier lift
  `not_isGammaCounterexample_of_exc_balanced_compl`. The Piece-6
  balanced pair is the explicit hypothesis `hBP` (Piece 6 is a
  separate piece of the refactor); the theorem's content is that the
  **carrier types line up** — the bridge emits, and S7-F-D consumes,
  the *same* `↥((Xexc cld)ᶜ)`.
* **§3 — grid instantiation** (`namespace GridChainLift`):
  `grid_lem_layered_from_step7` (the bridge fires on the R1 witness),
  `gridLayeredFromStep7` (the genuine output object),
  `gridLayeredFromStep7_w = 3`, `_band_nonconstant`, `_K_ge_two`,
  `grid_excPerturbLift_of_bridge` (the full A–D pipeline).

### §3.1. The band-nonempty cap — why `compactifySelf`

`bridgeLayered` (S7-F-C) sets `L.band z := (chain potential of z,
normalised) + 1` and `L.K := (potMax − potMin) + 1`. Its bands are
potential **level sets**, which can *skip values*: a `ChainLiftData`
whose potential image is `{0, 5}` has `K = 6` but bands `2, 3, 4, 5`
empty. The re-pinned cap 2 demands every index in `[1, K]` be
non-empty. So the integration post-composes with `compactifySelf`,
which renumbers band indices densely (band `k ↦` rank of `k` among
non-empty bands), preserving `w` exactly and contracting `K`. The
cap is then `compactifySelf_bandSet_nonempty`, proved by the same
`Nat.find`-sandwich argument as the existing `compactify_bandSet_nonempty`.

`compactifySelf` is a genuine generalisation tool, not a one-off: it
reuses every `compactBand` lemma of `Compactify.lean` (with `S :=
Finset.univ`), so its structural correctness rests on the same
machinery `compactify` is already verified against.

---

## §4. Non-triviality / satisfiability discipline (the `mg-02cd` QA bar)

The ticket: *"type-checks-clean is not sufficient; the assembled
bridge must genuinely deliver the 3-cap output."* The checks run:

1. **No `sorry`, no new axiom.** `#print axioms` confirms (§0, §7).
2. **No inert bounds.** `C_exc T = c₁ T + 6` is a genuine `O_T(1)`
   function of `T`; `L.w ≤ 4` reduces to the genuine `K_bw ≤ 2`
   (`lem:bandwidth`), *not* a literal `4 ≤ 4` — `forced_lt` genuinely
   consumes `w`; band-nonemptiness is *earned* by `compactifySelf`'s
   dense renumbering, not asserted.
3. **No inert hypotheses.** Every parameter of
   `lem_layered_from_step7` is load-bearing (§2.1); `hCex` / `γ` /
   `ih` are *excluded* precisely because they would be inert (§2.2).
4. **The output is satisfiable** — the re-pinned 3-cap form is the
   `mg-faf8` correction of the `mg-0bd1` 8th-vacuity 5-cap form; it
   is satisfiable for unbounded `|α|` (paper `def:layered`: bands
   `≤ 3`, depth `K ≥ |X|/6`). The bridge *constructs* a witness, so
   satisfiability is demonstrated, not assumed.
5. **The hypotheses are satisfiable** — `hMono ∧ hBudget` holds for
   `gridChainLiftData` (`grid_PotPosetMono`, `grid_excBudget`); the
   bridge fires non-vacuously (`grid_lem_layered_from_step7`). They
   genuinely *fail* on `Δ_ℓ`, so they are real soundness filters, not
   disguised `True` (and not disguised `False` — the grid witnesses
   satisfiability).
6. **Non-degenerate output.** `gridLayeredFromStep7` has `w = 3`
   (genuinely `K_bw + 2`, not the cap `4`), depth `K ≥ 2`, a
   non-constant band map (`gridLayeredFromStep7_band_nonconstant`,
   proved structurally via `compactBand_inj_on_S` from S7-F-C's
   `grid_bridgeLayered_band_nonconstant`).

---

## §5. Grid discharge — the R1 witness, end to end

On `gridChainLiftData` (the 3×3 grid, `ConcreteChainLiftData.lean`):

| Theorem | Content |
|---|---|
| `grid_lem_layered_from_step7` | the finalised bridge fires — 3-cap output for every `T`, no free hypothesis |
| `gridLayeredFromStep7` | the genuine output `LayeredDecomposition` on the 8-element `Grid ∖ {(0,0)}` |
| `gridLayeredFromStep7_w` | `w = 3` — genuinely `K_bw + 2`, tight `K_bw = 1` |
| `gridLayeredFromStep7_K_ge_two` | depth `K ≥ 2` — non-trivial layering |
| `gridLayeredFromStep7_band_nonconstant` | the band map is real, not inert |
| `grid_excPerturbLift_of_bridge` | the **full A–D pipeline**: `Grid ∖ X^exc` has a balanced pair (S7-F-D's swap witness) → routed through `excPerturbLift_of_bridge_output` → refutes the `(2/9)`-counterexample |

`grid_excPerturbLift_of_bridge` exercises the Piece-3 pipeline
carrier-to-carrier on the concrete R1 witness: S7-F-A's
`Xexc gridChainLiftData = {(0,0)}` is *exactly* the finset S7-F-D's
lift deletes — no carrier shuffling. (Piece 6 — turning the bridge's
`L` into the balanced pair — is bypassed here because the grid's
ground set has a balanced pair directly via the coordinate swap;
the carrier-type identity is the integration content.)

---

## §6. Scope boundary — what S7-F-Z does *not* do

* **Discharge `ExcBudget` / `PotPosetMono` from `hCex` + cascade.**
  Not possible in tree — the genuine Steps-1-7 cascade is not ported
  (Piece 1). S7-F-Z finalises the bridge *against* the obligations;
  Piece 1's `chainLiftData_of_cascade` will produce them (§2.2).
* **Port Piece 6** (`lem_layered_balanced_full` is already in tree,
  mg-65de) **or the §4.3 headline body.** The headline body is a
  separate ticket; `excPerturbLift_of_bridge_output` (§3 §2) records
  the exact Piece-3↔headline boundary.
* **Re-pin `MA-Sig §4.2 §E/§D′/§F` pseudo-Lean.** That is a
  documentation edit for the MA-Sig owner; the recommended re-pin is
  in §2.2. No in-tree Lean file depends on it.

---

## §7. Build / axioms

* `lake build OneThird.Step8.LayeredFromStep7` — clean (only the
  pre-existing `push_neg` deprecation / `show`-linter style warnings
  inherited from `Compactify.lean`).
* `lake build OneThird` — green, **1448 jobs** (1447 + the new file).
* `scripts/PrintAxiomsLayeredFromStep7.lean` — the axiom audit.
  `lem_layered_from_step7` / `compactifySelf` /
  `compactifySelf_bandSet_nonempty` / `grid_lem_layered_from_step7`
  and the grid non-degeneracy certificates:
  `propext`/`Classical.choice`/`Quot.sound` only. The two D-pipeline
  theorems additionally carry `brightwell_sharp_centred`, inherited
  from `exc_perturb` (F6b) — pre-existing, **not new**. No `sorry`,
  no new project axiom; `AXIOMS.md` unchanged.

---

## §8. Acceptance bars

- [x] Read-first set consumed: onboarding doc; scoping §2.3; the
  S7-F-A through S7-F-D deliverables + state docs; MA-Sig §4.2/§4.3/§11.
- [x] S7-F-A through S7-F-D wired into the single finalised theorem
  `lem_layered_from_step7` — consuming a `ChainLiftData α`.
- [x] Output is the re-pinned **3-cap** form: `Xexc.card ≤ C_exc T`,
  band-nonempty on `[1, L.K]`, `L.w ≤ 4`.
- [x] Genuinely concrete — no free hypothesis beyond the documented
  call-site contract (`hKbw` §4.2 §E; `hMono` S7-F-C; `hBudget`
  S7-F-A); the `hCex` domain-pin status is the §2.2 QA finding.
- [x] No inert bounds; no `sorry`; no new `axiom`; `AXIOMS.md`
  unchanged.
- [x] Non-vacuous instantiation against the concrete R1
  `ChainLiftData` `gridChainLiftData` — `grid_lem_layered_from_step7`
  + the non-degeneracy certificates (`w = 3`, `K ≥ 2`, non-constant
  band) + the full A–D pipeline `grid_excPerturbLift_of_bridge`.
- [x] Satisfiability discipline run — §4; the obligations are real
  soundness filters (hold on the grid, fail on `Δ_ℓ`).
- [x] File builds; imported into `OneThird.lean`; full `OneThird`
  build green (1448 jobs).
- [x] **Piece 3 is complete.**

---

## §9. Forward action — Piece 3 done, what is next

* **Piece 3 (the S7-F bridge) is COMPLETE.** Sub-arcs A, B, C, D, Z
  are all landed; `lem_layered_from_step7` is the finalised in-tree
  bridge theorem.
* **Piece 1** — port the Steps-1-7 cascade + `chainLiftData_of_cascade`
  (§4.2 §D′), which discharges `hMono` / `hBudget` (and `ExcBudget`'s
  `c₁ T` becomes the genuine Step-5 constant) from `hCex`.
* **The §4.3 headline body** — wires `lem_layered_from_step7` → Piece 6
  (`lem_layered_balanced_full`) → S7-F-D's lift; the
  `excPerturbLift_of_bridge_output` boundary is the recorded
  hand-off.
* **MA-Sig owner** — apply the §2.2 pseudo-Lean re-pin of §4.2
  §E/§D′ (documentation only).

---

## §10. Cross-reference index

### §10.1. Lean (this session)

* `lean/OneThird/Step8/LayeredFromStep7.lean` (NEW) — namespace
  `OneThird.Step8`.
  * `lem_layered_from_step7` — the finalised bridge.
  * `excPerturbLift_of_bridge_output` — the A–D integration boundary.
  * `GridChainLift.grid_lem_layered_from_step7`,
    `gridLayeredFromStep7`, `gridLayeredFromStep7_{w,band_nonconstant,
    K_ge_two}`, `gridQ01`, `gridQ22`, `grid_excPerturbLift_of_bridge`
    — the §5 grid discharge.
* `lean/OneThird/Step8/LayeredDecomposition/Compactify.lean` — §6
  added: `compactifySelf`, `compactifySelf_{K,w,band}`,
  `compactifySelf_K_le`, `compactifySelf_bandSet_nonempty`.
* `lean/OneThird.lean` — adds the `LayeredFromStep7` import.
* `lean/scripts/PrintAxiomsLayeredFromStep7.lean` (NEW) — axiom audit.

### §10.2. Lean (consumed, unmodified)

* `Step8/ExceptionalSet.lean` — `Xexc`, `C_exc`, `ExcBudget`,
  `Xexc_card_le`, `grid_excBudget` (S7-F-A).
* `Step8/SyncMaps.lean` — sync wiring (S7-F-B, transitive).
* `Step8/BridgeLayered.lean` — `bridgeLayered`,
  `ChainLiftData.PotPosetMono`, `bridgeLayered_w_le_four`,
  `gridBridgeLayered`, `grid_PotPosetMono`,
  `grid_bridgeLayered_{w,K,band_nonconstant}` (S7-F-C).
* `Step8/ExcBalancedLift.lean` —
  `not_isGammaCounterexample_of_exc_balanced_compl`,
  `hasBalancedPair_orderIso`, `complNotMemOrderIso`,
  `ExcBalancedLiftGrid.{gridMinusCorner_hasBalancedPair,grid_exc_eps}`
  (S7-F-D).
* `Step8/ConcreteChainLiftData.lean` — `gridChainLiftData`,
  `gridChainLiftData_K_bw_le_two` (R1).
* `Step8/LayeredReduction.lean` — `LayeredDecomposition`, `bandSet`.

### §10.3. Predecessor docs / work items

* `docs/state-S7F-A-Session1.md` (mg-08d7) — `Xexc`, `ExcBudget`.
* `docs/state-S7F-B-Session1.md` (mg-120d) — sync wiring.
* `docs/state-S7F-C-Session1.md` (mg-bcc9) — `bridgeLayered`,
  Resolution A, `PotPosetMono`.
* `docs/state-S7F-D-Session1.md` (mg-876f) — the perturbation lift.
* `docs/state-S7F-R1-Session1.md` (mg-974c) — `gridChainLiftData`.
* `docs/state-MA-Sig-Session1.md` §4.2 §E/§D′/§F, §4.3, §11 — the
  contract; §2.2 above is the QA refinement.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 — Piece 3.
* `step8.tex:2009-2089` — paper `lem:layered-from-step7`.

---

## §11. Maintenance contract

This file is the state record for FULL REFACTOR Phase-2 Piece-3
sub-arc Z (mg-02cd) — the integration that **completes Piece 3**. It
owns `lean/OneThird/Step8/LayeredFromStep7.lean` and the §6
`compactifySelf` block of `Compactify.lean`. Supersede it only if a
later session changes those deliverables. If Piece 3 is ever
re-scoped to MA-Sig §11.3 resolution (B) (a strengthened
`ChainLiftData` carrying `PotPosetMono` / `ExcBudget` as fields),
`lem_layered_from_step7`'s `hMono` / `hBudget` parameters become
field projections of the strengthened structure and §2.2 should be
re-evaluated; record that in the same commit.
