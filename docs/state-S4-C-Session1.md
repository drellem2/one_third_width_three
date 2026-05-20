# State — S4-C — Session 1: Step 4 assembly and integration — land `thm:step4`, verify Step 6 consumability

**Ticket:** mg-3bca (OneThird-S4-C: Step 4 assembly and integration —
land `thm:step4`, verify Step 6 consumability).
**Branch:** `polecat-mg-3bca`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.1 Piece 1,
Wave-3.
**Depends:** mg-1c08 (S4-B per-pair bound + Markov aggregation); merged
at `c9ee834`.

**Scope.** Wave-3, third (final) ticket of the Step 4 sub-arc of the
Piece-1 (Steps 1-6 cascade port) decomposition. Assembles the complete
`thm:step4` two-interface incompatibility lemma, integrates it into the
cascade scaffold, and confirms the output is consumable by Step 6.
Consumes the S4-B per-pair bound (`step4_perPair_bound`) and Markov
aggregation (`incoherent_mass_lower_bound`).

---

## §0. Verdict — **GREEN-S4-C-delivered**

`lean/OneThird/Step4/Assembly.lean` (NEW, ~330 LoC) assembles the
complete grounded `thm:step4` and grounds the Step 6 overlap-counting
interface; `lean/OneThird/Step6/Assembly.lean` gains a `§2a G7Grounded`
section (~95 LoC) verifying Step 6's `lem:sum-step4` consumes the
grounded Step 4 output.

* `thm_step4_assembled` — **the complete grounded `thm:step4`**
  (`step4.tex:93`). S4-B's `step4_perPair_bound` discharged the
  `thm:step4` conclusion from four named hypotheses, of which
  `hMarkov : δ·|Ω°| ≤ 2·M_inc` was the operative incoherent-mass bound.
  The assembled form closes that last gap: it takes the genuine
  per-block pointwise-disagreement counts `dis B` and block masses
  `m B` and discharges `hMarkov` **internally** via the S4-B Markov
  split `incoherent_mass_lower_bound`, plus the sub-mass fact
  `M_inc ≤ |Ω°|`. The only remaining inputs are the genuine structural
  ones: the per-block rectangle incompatibility (`lem:rect-stable-area`),
  the block-disjointness (`prop:G1.2`), and the cleared-denominator
  incoherence calibration `δ·|Ω°| + |Ω°| ≤ 2·∑ dis`.
* `witnessFamilyOfPairs` — **the BK-edge witness family indexed by
  ordered rich pairs** (`step4.tex:1167`): per ordered pair, the S4-A
  `witnessFamily` of that pair's conflict-square data. This is the
  concrete `witness : Pair → Pair → Finset Edge` object the Step 6
  overlap-counting double-counts.
* `pairWeight_eq_card_of_subset` / `pairWeight_witnessFamilyOfPairs` —
  **the grounding bridge**: since every witness family lies inside the
  BK boundary (`witnessFamily_subset_bkBoundary`), the Step 6 pair
  weight `w_{α,β} = |∂_BK S ∩ E_{α,β}|` is exactly the witness-family
  cardinality `|E_{α,β}|` — the quantity the S4-B per-pair bound
  `prop_G5_witnessFamily` actually lower-bounds.
* `lem_G6_bkEdge` — **`lem:G6` (witness-edge multiplicity,
  `step4.tex:1177`) grounded** on the concrete BK edge type
  `Sym2 (LinearExt α)`.
* `cor_step6_input_grounded` / `cor_step6_input_witnessMass` —
  **`cor:step6-input` (`step4.tex:1269`) grounded** on the genuine BK
  boundary `bkBoundary S` of `bkGraph α`:
  `∑_{(α,β)} |∂_BK S ∩ E_{α,β}| ≤ M · |∂_BK S|`, and in witness-mass
  form `∑_{(α,β)} |E_{α,β}| ≤ M · |∂_BK S|` — the paper's display
  verbatim, the overlap-counting lemma Step 6 consumes.
* `Step6.lem_sum_step4_grounded` — **the Step 6 consumability check**:
  Step 6's G7 `lem_sum_step4` (`step6.tex:270`) sums the Step 4 per-pair
  bound against the overlap-counting multiplicity; this theorem confirms
  the grounded `witnessFamilyOfPairs` (on the genuine `bkBoundary S`)
  feeds it directly, the per-pair input stated on `|E_{α,β}|` and
  converted to the abstract `pairWeight` via the grounding bridge.
* `thm_step4_assembled_nonvacuous` / `corStep6Input_nonvacuous` /
  `lem_sum_step4_grounded_nonvacuous` — the S4-C non-vacuity acceptance
  witnesses at the genuine width-3 non-chain grid poset `Fin 3 × Fin 3`
  (see §5).

`lake build OneThird` (full library) is clean, exit 0, 1432 jobs. The
new file `Step4/Assembly.lean` produces no warnings; the
`Step6/Assembly.lean` `G7Grounded` section produces no warnings.

**No `sorry`, no new axiom.** `#print axioms` confirms all nine S4-C
theorems (`thm_step4_assembled`, `cor_step6_input_grounded`,
`cor_step6_input_witnessMass`, `lem_G6_bkEdge`,
`pairWeight_eq_card_of_subset`, `lem_sum_step4_grounded`, and the three
non-vacuity witnesses) depend on exactly
`[propext, Classical.choice, Quot.sound]` — the three standard mathlib
axioms. No `sorryAx`, no project axiom.

---

## §1. What S4-C assembles, and how

`thm:step4` (`step4.tex:93`) is the two-interface incompatibility lemma
`|∂_BK S| ≥ c·(δ − C·ε)·|Ω°|`. Its paper proof (`step4.tex:1135-1160`)
is: block-decompose `Ω°` (`prop:G1`); Markov ⇒ incoherent blocks carry
`≥ δ/2·|Ω°|`; `prop:G5` density regularization sums the per-block
rectangle incompatibility into the global bound; the `½` factor absorbs
the Markov loss.

The grounded port split across three Wave-3 tickets:

| paper content | ticket | grounded as |
|---|---|---|
| `thm:step4` statement + `E_{α,β}` construction | S4-A | `Step4Conclusion`, `thm_step4_grounded_witness`, `witnessFamily` |
| `prop:G5` + Markov split + per-pair discharge | S4-B | `prop_G5_witnessFamily`, `markov_incoherent_mass`, `step4_perPair_bound` |
| **`thm:step4` assembly + `lem:G6` + `cor:step6-input`** | **S4-C** | **`thm_step4_assembled`, `lem_G6_bkEdge`, `cor_step6_input_witnessMass`** |

The S4-C assembly closes the loop. S4-B's `step4_perPair_bound` took
`hMarkov : δ·|Ω°| ≤ 2·M_inc` as a *named* hypothesis;
`thm_step4_assembled` discharges it from the genuine per-block
disagreement counts: with `dis B`/`m B` and the cleared-denominator
calibration `δ·|Ω°| + |Ω°| ≤ 2·∑ dis`, the S4-B Markov split
`incoherent_mass_lower_bound` delivers exactly `hMarkov`, and
`Finset.sum_le_sum_of_subset` delivers the sub-mass `hMass`. The block
is incoherent exactly when `m B ≤ 2·dis B` — the S4-A `BlockIncoherent`
`½`-threshold. After the assembly, the only inputs of
`thm_step4_assembled` are the genuine structural ones of the paper's
proof.

---

## §2. The Step 6 integration (`lem:G6` + `cor:step6-input`)

`step4.tex` §"Witness-edge multiplicity for Step 6" delivers the
bookkeeping Step 6 consumes:

* `lem:G6` (`step4.tex:1177`) — each BK edge lies in at most `M = 2·M₁`
  ordered rich-interface witness families.
* `cor:step6-input` (`step4.tex:1269`) — `∑_{(α,β)} w_{α,β} ≤ M·|∂_BK S|`
  where `w_{α,β} = |∂_BK S ∩ E_{α,β}|`.

The abstract `OneThird.Step4.Step4Theorem` already proves `lem_G6` and
`cor_step6_input` over an opaque edge type `Edge`. S4-C **grounds
`Edge`** to the concrete BK edge type `Sym2 (LinearExt α)` and
`boundary` to the genuine BK boundary `bkBoundary S` of `bkGraph α`:

* `lem_G6_bkEdge` instantiates `lem_G6` at `Edge := Sym2 (LinearExt α)`.
* `cor_step6_input_grounded` instantiates `cor_step6_input` at
  `boundary := bkBoundary S`.
* `cor_step6_input_witnessMass` rewrites the abstract `pairWeight`
  (`|∂_BK S ∩ E_{α,β}|`) to the witness-family cardinality `|E_{α,β}|`
  via the grounding bridge `pairWeight_witnessFamilyOfPairs` — the
  witness family lives inside the BK boundary, so the intersection is
  the whole family. This gives the paper's `cor:step6-input` display
  verbatim: `∑ |E_{α,β}| ≤ M·|∂_BK S|`.

**Step 6 consumability — verified.** Step 6's `lem:sum-step4` (G7,
`step6.tex:270`) sums the Step 4 per-pair bound `w_{α,β}` against the
overlap-counting multiplicity `M`. `Step6.lem_sum_step4_grounded`
(new `§2a` of `Step6/Assembly.lean`) confirms the grounded
`witnessFamilyOfPairs` feeds `lem_sum_step4` directly: it states the
per-pair input on the grounded witness-family cardinality `|E_{α,β}|`
(the quantity the S4-B `prop_G5_witnessFamily` lower-bounds), converts
it to the abstract `pairWeight` via `pairWeight_witnessFamilyOfPairs`,
and discharges `lem_sum_step4` to obtain
`c_n·∑_{bad active} w_{α,β} ≤ c_d·M·|∂_BK S|` on the genuine BK
boundary. The integration is therefore end-to-end: S4-A statement →
S4-B per-pair discharge → S4-C assembly → S4-C grounded
`cor:step6-input` → Step 6 `lem:sum-step4`.

---

## §3. Scope boundary (honest)

This ticket assembles the **complete `thm:step4`** and grounds the
**Step 6 overlap-counting interface** — all grounded, 0-sorry, no new
axiom. Out of scope, faithfully so:

* **The width-3 local-fiber bound of `lem:G6` Step 4**
  (`step4.tex:1221-1256`) — the `O(1)` count of partner interfaces — is
  carried as the abstract `LocalFiberBound` hypothesis of
  `lem_G6_bkEdge`, exactly as in the abstract
  `Step4Theorem.lem_G6`. The paper itself (`step4.tex` `rem` after
  `cor:step6-input`) flags that an explicit numerical `M` is **not
  needed** by any downstream step — only that `M` depends on the width
  alone — so this abstraction is faithful, **not a paper-side rigour
  gap newly surfaced by the assembly** (see §6).
* **The Step 1 swap-pair pinning** (`step4.tex:1190-1196`, "the swap
  pair of a witness edge equals `α` or `β`") is the `hpin` hypothesis
  of `lem_G6_bkEdge`. S4-A's `witnessEdge_bkAdj` already grounds the
  *existence* of a BK swap pair for every witness edge; that the swap
  pair equals one of the two interfaces is the rectangle-block-model
  structural input, carried as a named hypothesis here.
* **The per-block rectangle incompatibility** (`lem:rect-stable-area`)
  and **block-disjointness** (`prop:G1.2`) enter `thm_step4_assembled`
  as the named hypotheses `hPerBlock` / `hdisj` — the same
  abstract-hypothesis style as S4-B; the non-vacuity (§5) discharges
  `hPerBlock` concretely via the S4-A `lem:22`.

The abstract Step 4 files (`RectangleModel.lean`,
`DensityRegularization.lean`, `Step4Theorem.lean`), the S4-A
`WitnessGrounded.lean`, and the S4-B `PerPairBound.lean` are
**unchanged**. `Step4/Assembly.lean` is purely additive; the only
non-additive change is the `§2a G7Grounded` section appended to
`Step6/Assembly.lean` (plus its `import OneThird.Step4.Assembly` line)
and the `+1` import line in `lean/OneThird.lean`.

---

## §4. What this port consumes

* **S4-B** (`OneThird.Step4.PerPairBound`) — `step4_perPair_bound` (the
  full witness discharge of `thm:step4`) and `incoherent_mass_lower_bound`
  (the Markov aggregation arithmetic). These are the two named
  consumables of the ticket.
* **S4-A** (`OneThird.Step4.WitnessGrounded`) — `bkBoundary`,
  `witnessFamily`, `witnessFamily_subset_bkBoundary`,
  `witnessFamily_nonempty_of_conflict`, `cutEdgesOfSquare`,
  `Step4Conclusion`, `BKSquare`, `lem22_bk`, `IsConflictSquare`, and the
  non-vacuity scaffold (`gridSquare`, `witnessGrounded_nonvacuous`).
* **Step 4 abstract scaffold** (`OneThird.Step4.Step4Theorem`) — the
  abstract `lem_G6`, `cor_step6_input`, `witnessCount`, `pairWeight`,
  `LocalFiberBound`; S4-C grounds the abstract `Edge` type to the
  concrete BK edge type `Sym2 (LinearExt α)`.
* **Step 6** (`OneThird.Step6.Assembly`) — `lem_sum_step4` (G7), for the
  consumability check.

**Self-assessment — vacuous-scaffold check (per mg-3bca mayor mail).**
S4-C does **not** build against the vacuous `Step1/Corollaries.lean`
scaffolds. No S4-C theorem references `bounded_interaction`,
`cor:overlap`, or `cor:triple-overlap` by name (grep: zero hits).
`Step1.Corollaries` appears in the transitive *import* closure of
`Step4.Assembly` only — inherited from the pre-existing chain
`Step4.PerPairBound → Step4.WitnessGrounded → Step1.BKMoves →
Step1.GroundSet → Step1.Corollaries`, identical to S4-B's own closure
(which self-assessed clean). S4-C introduces no new path to
`Corollaries`. `#print axioms` on every S4-C theorem is
`[propext, Classical.choice, Quot.sound]` — no project axiom, no
`sorryAx`.

---

## §5. Non-vacuity (mg-3bca acceptance bar)

Three acceptance witnesses, all at the genuine width-3 non-chain grid
poset `Fin 3 × Fin 3` — no `Subsingleton`-on-empty baseline:

* `thm_step4_assembled_nonvacuous` — the assembled `thm:step4` fires on
  a *one-block* decomposition whose single block carries the genuine
  conflict square `gridSquare`. The block is genuinely incoherent
  (`m = 1 ≤ 2·dis = 2`), so the incoherent-block filter is non-empty;
  `hPerBlock` is discharged **concretely** via the S4-A `lem22_bk` — the
  genuine conflict square contributes a real BK cut edge; the assembled
  theorem delivers `Step4Conclusion` with strictly positive `δ = 1`,
  `|Ω°| = 1`.
* `corStep6Input_nonvacuous` — the grounded `witnessFamilyOfPairs` over
  a one-pair index (`Pair := Unit`) has a non-empty witness family (a
  real BK cut edge from `gridSquare`); the overlap-counting bound
  `∑ |E_{α,β}| ≤ M·|∂_BK S|` fires with `M = 1` and a strictly positive
  left-hand side.
* `lem_sum_step4_grounded_nonvacuous` — the Step 6 consumption fires:
  the bad-active-pair set is non-empty (one pair), the per-pair weight
  `w = 1` is strictly positive, the per-pair bound is discharged by the
  genuine non-empty witness family, and `lem_sum_step4_grounded`
  delivers `1·∑ w ≤ 1·1·|∂_BK S|`.

A genuine `2×2` BK conflict square requires a poset with at least four
elements supporting two disjoint incomparable pairs; `Fin 3 × Fin 3`
carries one and the 3-element antichain structurally cannot — so the
assembly fires on a *genuine* square, and the per-block / per-pair
bounds are discharged by real BK cut edges, not degenerate ones.

---

## §6. Paper-side rigour: no new gap surfaced by the assembly

The S4-C ticket directive includes "block-and-report if assembly
surfaces a paper-side rigor gap." The assembly surfaced **no new gap**:

* The `thm:step4` proof (`step4.tex:1135-1160`) ports cleanly — the
  Markov split, density regularization, and the `½` Markov-loss factor
  are all genuine and discharged (S4-B + the S4-C assembly).
* The one hand-wavy passage in `step4.tex` — the `lem:G6` Step 4
  width-3 local-fiber `O(1)` count (`step4.tex:1221-1256`, "Summing
  over adjacent positions ... would naively give an unbounded count,
  but the coordinate-convexity clause (S1.1) together with richness
  rules this out") — was **already abstracted** by the existing
  `Step4Theorem.lem_G6` as the named `LocalFiberBound` hypothesis,
  *before* S4-C. The paper itself (`step4.tex` `rem` after
  `cor:step6-input`) explicitly states an explicit numerical `M` is
  not needed downstream — only the width-dependence. S4-C inherits
  this documented abstraction; it does not newly surface it.

This is consistent with the mg-8b95 Checkpoint-1 audit (AMBER on S1's
`thm:interface`): the S4-C-relevant abstraction (`LocalFiberBound` /
`hpin`) is a *deliberate, documented* hypothesis-threading, not a
silent gap.

---

## §7. Files

* `lean/OneThird/Step4/Assembly.lean` — NEW (~330 LoC).
* `lean/OneThird/Step6/Assembly.lean` — `+1` import line + `§2a
  G7Grounded` section (`lem_sum_step4_grounded` +
  `lem_sum_step4_grounded_nonvacuous`).
* `lean/OneThird.lean` — `+1` import line (`OneThird.Step4.Assembly`).
* `docs/state-S4-C-Session1.md` — this file.
