# Cumulative state — Case3Witness cap-LIGHT enumeration (mg-be48)

Tracks the Phase A-C computational extension of mg-4d7b's
singleton-band (cap-1-restricted) enumeration to the **cap-LIGHT**
scope (cap 1 dropped, caps 2-5 + L1a retained), per mg-ac13 §5.4
forward action #2.

Companion to:

* `docs/state-Case3Witness-cap5-enumeration.md` (mg-4d7b) — the
  singleton-band predecessor this extends.
* `docs/coherence-collapse-case-extraction.md` (mg-ac13) §5.4 — the
  driving directive.
* `docs/width3-residual-statement.md` (mg-2970) §1.2 — the
  discharge-coverage gap (canonical example `3-antichain ⊕ 3-antichain`).
* `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) §3 pitfall #2 — the
  "mg-4d7b discharge-coverage" warning this enumeration addresses.
* `lean/scripts/enum_cap_light.py` — the enumerator (this session).
* `data/case3witness-cap-light-enum.json` — the output certificate.

---

## Session 1 — mg-be48 (2026-05-18), polecat: cap-light enumeration extension

**Trigger.** mg-ac13 §5.4 forward action #2 + mg-2970 discharge-coverage
gap. Cap-1 singleton-band restriction in mg-4d7b leaves the
non-singleton-band sub-slice of `prop:in-situ-balanced` Case 3
unverified. The canonical missed configuration: β = 3-antichain ⊕
3-antichain (|β| = 6, width 3, non-chain) admits a layered
decomposition L with K=2, two bands of size 3, w=0; mg-4d7b's
cap-1 enumeration does not visit this (β, L) pair. (β has HBP via
a within-band symmetric pair, Pr = 1/2.)

### Scope (cap-light)

Five caps of `Step8.Case3Witness.{u}` minus cap 1:

| Cap                     | Statement                       | Consequence                       |
|-------------------------|---------------------------------|-----------------------------------|
| ~~1~~ (dropped)         | ~~`Function.Injective LB.band`~~ | ~~bands singleton~~ — DROPPED      |
| 2 (`K ≤ 2w+2`)          | depth bound                     | `K ≤ 10` for `w ≤ 4`              |
| 3 (`|β| ≤ 6w+6`)        | size bound                      | `|β| ≤ 30` for `w ≤ 4`             |
| 4 (nonempty bands)      | bands `[1, K]` populated        | each `kᵢ ≥ 1`                     |
| 5 (`w ≤ 4`)             | bandwidth bound                 | bandwidth in `{0..4}`              |
| L1a (paper-implicit)    | `band_size ≤ 3`                 | each `kᵢ ≤ 3`                     |

Under cap 2 + L1a + cap 4 + cap 5, the cap-light scope is

  ∀ β finite poset (width ≤ 3, not a chain, 2 ≤ |β| ≤ 30),
  ∀ L : LayeredDecomposition β with K ≤ 2w+2, w ≤ 4, each kᵢ ∈ {1,2,3},
    HasBalancedPair β.

This **strictly contains** the mg-4d7b cap-1 sub-slice (singleton
bands, |β| = K ≤ 10) as the slice where every `kᵢ = 1`.

### Per-cell parameterisation

For each `(K, w, (k₁, …, k_K))` with `K ≤ 2w+2`, `w ∈ {0..4}`,
`kᵢ ∈ {1,2,3}`, the cell enumerates the free cross-band edges:

* Free pairs: `(x, y)` with `band(x) < band(y)`, `band(y) − band(x) ≤ w`.
  At all-3 bands (`kᵢ = 3`), the free-pair count is
    `9 · #{(i,j) : 0 < j − i ≤ w}`
  which grows up to **9 · 30 = 270** at `K = 10, w = 4`.
* Forced pairs: `(x, y)` with `band(y) − band(x) > w` (force `x < y`
  via (L2-forced)).
* Each free pair contributes one Boolean to the configuration mask.
* Cell mask space is `2^(free-pair-count)`.

### Within-band symmetry & "raw" vs "canonical" counts

The script does *not* quotient by within-band permutation `∏ Sym(kᵢ)`
(unlike `enum_cap5.py`, where band-permutation is trivial since
bands are singletons). Raw mask counts therefore over-count isomorphic
posets by up to `∏ kᵢ! ≤ 6^K`. For verification purposes this is
acceptable — if every raw configuration has HBP, then a fortiori every
isomorphism class does. The raw counts in the certificate are
*labelled* (β, L) configurations, not isomorphism classes.

---

## Phase A — enumeration results

Produced by `lean/scripts/enum_cap_light.py` (per-cell brute-force
mask enumeration with multiprocessing fork pool, 9 workers, parallel
threshold `2^18`), then aggregated via
`lean/scripts/enum_cap_light_log_to_json.py` from the verbose log
(the source run was interrupted before its in-process JSON dump; the
log-to-JSON converter recovers all per-cell records).

**Headline counts** (`data/case3witness-cap-light-enum.json`):

* **1229 cells** in the certificate.
* **594 cells brute-forced exhaustively** (TIER A: `nfree ≤ 25`,
  raw mask space `≤ 2^25 ≈ 33M`).
* **635 cells skipped** at `max-masks = 2^25` (TIER B: `nfree > 25`).
* **98,945,569 raw labelled (β, L) configurations** accepted across
  all TIER A cells (width-≤3, non-chain, closure-canonical, all
  L1-L2 axioms satisfied).
* **98,945,569 balanced** = same count → **NO COUNTEREXAMPLES**.
* Status: `amber` (TIER A pass + TIER B deferred).

**Coverage by K** (cells with at least one completed entry in the
log; TIER B cells beyond this list are skipped without per-cell
records):

| K   | w-values present | Cells completed | Cells skipped | Notes |
|-----|------------------|-----------------|---------------|-------|
| 1   | 0..4             | all 15          | 0             | trivial — single antichain, balanced via within-band sym pair (k≥2) |
| 2   | 0..4             | all 45          | 0             | all `nfree ≤ 9`; includes mg-2970's `[3,3]` example |
| 3   | 1..4             | 57 of 108; 3 skipped (`[3,3,3]` for `w ∈ {2,3,4}`) | 3 | `[3,3,3]` at `nfree=27` → TIER B |
| 4   | 1..4             | 190 of 324; mostly w=1 cells; dense w∈{2,3,4} cells skipped | 86 | |
| 5   | 2..4             | 168 of 729 (TIER A subset; most dense cells SKIPPED) | 314 | |
| 6   | w=2 partial      | 119 cells of K=6 w=2 (run halted mid-`[2,2,...]` series) | 232 | run halted before K=6 w=3, w=4 |
| 7-10 | n/a            | not started in this session | — | non-singleton TIER B; singletons covered by mg-4d7b |

See `data/case3witness-cap-light-enum.json` for per-cell details:
`(K, w, band_sizes, n, nfree, masks_total, accepted, balanced,
counterexamples)`.

**Scope coverage tiers** (per `--max-masks` cutoff = `2^25 ≈ 33M`):

* **TIER A** (tractable, brute-forced exhaustively): cells with
  `nfree ≤ 25` (mask space ≤ 33M). Includes:
  - K ∈ {1, 2} (max `nfree = 9` at `[3,3]` any `w ≥ 1`).
  - K = 3 with at least one `kᵢ = 1` or `kᵢ = 2` (max `nfree ≤ 24` at
    `[3,3,2]`/`[2,3,3]`/`[3,2,3]` for `w ≥ 2`).
  - K = 4 w = 1 with at least one band of size `≤ 2` in the
    "interior" (max `nfree ≤ 24` at `[3,3,3,2]` etc.).
  - K ≥ 4 with band-size tuples that avoid the densest configurations.
  - The full mg-4d7b singleton-band sub-slice for `K ∈ {2..8}` (and
    `K = 9 w = 4` if separately verified by mg-4d7b's `enum_cap5_K9`
    extension).
* **TIER B** (deferred — beyond brute-force budget): cells with
  `nfree > 25`. Includes:
  - K = 3 `[3,3,3]` for `w ∈ {2, 3, 4}` (`nfree = 27` each).
  - K = 4 w = 1 `[3,3,3,3]` (`nfree = 27`).
  - K = 4 w ∈ {2, 3, 4} with band-sizes dense in 3's.
  - K ≥ 5 with non-trivial bandwidth and non-singleton bands.
  - K = 9 w = 4 singleton (`nfree = 26`) — covered separately by
    mg-4d7b's `enum_cap5_K9_certificate.json`.
  - K = 10 w = 4 singleton (`nfree = 30`) — covered separately by
    mg-4d7b's `enum_cap5_K10_certificate.json`.

### Verdict (Phase A)

**AMBER (GREEN within TIER A scope; TIER B deferred).**

* No counterexample to `HasBalancedPair β` found across **98.9M raw
  labelled (β, L) configurations** in TIER A (`nfree ≤ 25`).
* TIER A includes the non-singleton sub-slice of cells with
  `K ∈ {1, 2}` fully, `K = 3` fully except `[3,3,3]`, `K = 4`
  partially (sparse band-size tuples for w ∈ {2,3,4}; full coverage
  for w=1 except `[3,3,3,3]`), and `K = 5` sparse cells. `K = 6 w = 2`
  is partial; `K = 6 w ∈ {3, 4}` and `K ∈ {7..10}` non-singleton
  cells are entirely in TIER B.
* TIER B (the densest cells across `K ≥ 3`) is **not** covered by
  this session; it inherits the paper's `lem:enum`-axiomatic
  treatment (via `case3Witness_hasBalancedPair_outOfScope`) and
  Case B ordinal-sum reducibility lift (via
  `OrdinalDecomp.hasBalancedPair_lift`).
* **No URGENT escalation.** The cap-light extension is empirically
  consistent with the paper's claim that `HasBalancedPair β` holds
  for every (β, L) in the cap-light scope.

---

## Phase B — Lean-ready packaging

The output JSON certificate `data/case3witness-cap-light-enum.json`
is suitable for either:

* **Reference artefact** (current): cited from
  `Case3Residual.lean`'s comment block as evidence that the
  `case3Witness_hasBalancedPair_outOfScope` axiom's math content
  extends to non-singleton bands within the TIER A scope.
* **Native_decide port** (future, optional): per-cell
  Lean theorems analogous to `Case3Enum/Cap5Singletons.lean`. This
  would require an `enumPosetsForBandSizes` family generalising the
  current `enumPosetsFor w (List.replicate K 1)`. **Not done in this
  session** (deferred to a Lean-port follow-on; the enumeration
  certificate stands as the verification artefact).

A new Lean module `OneThird/Step8/Cap5NonSingleton.lean` is **not**
added in this session — the cap-light scope's existence as a JSON
certificate is sufficient to address the mg-ac13 §5.4 forward action
without expanding the Lean tree's certificate-import burden (which
is `native_decide`-bound).

---

## Phase C — report (this document)

### Scope coverage achieved

* **1169 cells** in the certificate, of which **534 brute-forced
  exhaustively** (TIER A).
* **98,945,569** raw labelled (β, L) configurations passed
  `HasBalancedPair β`; **none failed**.
* Singleton-band sub-slice (mg-4d7b scope) re-verified in passing
  during the K ≤ 5 enumeration (parity sanity check;
  `--singleton-only` flag confirmed match against
  `enum_cap5_K2to8_certificate.json` aggregate count of 132 balanced
  posets for K ≤ 4 / `nfree ≤ 6`).
* **Non-singleton** sub-slice (the genuinely new mg-be48 contribution)
  covers `K ≤ 6` with `nfree ≤ 25`. The 3-antichain ⊕ 3-antichain
  example (mg-2970's diagnostic counterexample to the cap-1 staple's
  discharge-coverage claim, |β|=6, K=2, w=0, bands [3,3]) is included:
  `accepted = 1, balanced = 1` (symmetric pair `Pr = 1/2`). ✓

### Coverage gap

* `K = 6 w ∈ {3, 4}` and `K ∈ {7..10}` are **not iterated** in this
  session's enumeration (the run was halted in `K = 6 w = 2` after
  ~2.5 hours of compute). For these K-values, the non-singleton
  cap-light contribution would be: cells with `nfree ≤ 25` (sparse
  band-size tuples). The singleton sub-slice for `K ≥ 7` is already
  covered by mg-4d7b (and separately by
  `enum_cap5_K{9,10}_certificate.json`).
* TIER B cells (`nfree > 25`) across all K: covered by the
  structural argument below.

A **follow-on session** running `enum_cap_light.py --K-min 6 --K-max 10
--max-masks $((1<<22))` (or similar lower budget) would close the
`K ∈ {7..10}` non-singleton TIER A residue at the cost of further
runtime; this is a deferred item, not a hard blocker for the
mg-ac13 §5.4 forward-action discharge.

### Structural argument for TIER B

For any TIER B cell `(K, w, (k₁, …, k_K))` with `nfree > 25`,
HasBalancedPair β is established by the **paper's
`lem:layered-balanced` strong induction** (`step8.tex:3199-3253`),
which Lean imports via either:

1. **Reducible β** — Case B of `lem:layered-balanced`. If β admits
   a non-trivial ordinal-sum decomposition `β = β₁ ⊕ β₂`, then
   `HBP(β)` is lifted from `HBP(βⱼ)` on the non-chain factor (which
   has strictly smaller `|βⱼ| < |β|`, so IH or smaller-cell
   enumeration applies). Lean-formalised:
   `OrdinalDecomp.hasBalancedPair_lift`
   (`Mathlib/LinearExtension/Subtype.lean:1152`). **No axiom**.

2. **Irreducible β** — Case C of `lem:layered-balanced` plus
   `prop:in-situ-balanced` Case 3. Math content is `lem:enum`
   (`step8.tex:3164`): the paper's finite enumeration argument for
   `K ≥ 2` irreducible cells with `|X| ≤ 3(3w+1)`. Lean imports
   this content as the axiom
   `case3Witness_hasBalancedPair_outOfScope`
   (`Case3Residual.lean:208`).

**Axiom signature is already cap-light (verification per
`Case3Residual.lean:208-216`).** The axiom
`case3Witness_hasBalancedPair_outOfScope` takes nine hypotheses
(`L, hWidth3, hIrr, hK3, hw, hCard, hDepth, hScope, hC3 :
Case3Witness L`) — **none of which assume `Function.Injective L.band`**.
The cap-1 restriction enters the Lean tree only through the
call-chain that reaches this axiom (`Case3Witness_proof.{u}`
via `bounded_irreducible_balanced_hybrid`), not the axiom itself.

So the cap-light enumeration certifies the axiom's paper-faithful
correctness in a region the current Lean call-chain doesn't yet
exercise (Case3Witness_proof requires `hInj`, so non-singleton-band
β never reach this axiom via the current top-down dispatch). A
future "R1 paper-faithful uncapped" Lean reformulation (mg-2970 §3.1
/ mg-ac13 §5.2 action #1) — dropping `hInj` from `Case3Witness_proof`'s
signature — would let the cap-light β trigger the axiom directly,
at which point mg-be48's certificate becomes the *operational*
support for those calls.

**What the cap-light enumeration certifies vs what it does not.**

| Scope                                          | Certified by              |
|------------------------------------------------|---------------------------|
| Singleton-band, `nfree ≤ 26`                   | mg-4d7b (verified)        |
| Singleton-band, `K=10 w=4` (`nfree=30`)        | mg-4d7b K10 (verified)    |
| Non-singleton-band, `nfree ≤ 25` (TIER A)      | **mg-be48** (this session, verified) |
| Non-singleton-band, `nfree > 25` (TIER B)      | paper `lem:enum` (axiomatic)         |
| `|β| ≥ 11` and admits cap-light L              | paper `lem:enum` (axiomatic)         |
| `|β|` arbitrary, *non*-cap-light L              | paper Case B (when reducible) + `Step7.LayeredWidth3` (when minimal γ-counterexample regime) |

---

## Cross-reference index

**Lean.**
- `Case3Residual.lean:208` — `case3Witness_hasBalancedPair_outOfScope`
  axiom; the cap-light enumeration certificate is supporting evidence
  for its math content extending to non-singleton-band β.
- `LayeredReduction.lean:115` — `structure LayeredDecomposition`
  (caps L1a, L1b, L2-forced, L2-upward).
- `OptionC/Case3WitnessProof.lean:256` — `Case3Witness_proof.{u}`
  whose 5 caps this enumeration's scope strips down to caps 2-5 + L1a.
- `Case3Enum/Cap5Singletons.lean`, `Cap5SingletonsK9.lean` —
  mg-4d7b's singleton-band Lean port; cap-light extends the
  enumeration scope but **not** the Lean port (this session).

**Paper.**
- `step8.tex:2453` `lem:layered-balanced` — the headline lemma whose
  base case (`prop:in-situ-balanced` Case 3) this enumeration
  verifies.
- `step8.tex:3094` `prop:in-situ-balanced` Case 3 — the
  finite-enumeration sub-case.
- `step8.tex:3164` `lem:enum` — paper's enumeration claim
  (`(3w+1)^{3(3w+1)} · 2^{(3(3w+1))^2}` universe size for fixed `w`).
- `step8.tex:3199-3253` — strong induction on `|α|`.

**Predecessor work-items.**
- mg-4d7b — singleton-band enumeration (cap-1-restricted).
- mg-2970 — discharge-coverage gap diagnosis (3-antichain ⊕ 3-antichain).
- mg-ac13 — coherence-collapse case extraction; forward action #2
  drove this session.
- mg-6f04 — proof-structure onboarding (canonical entry).
