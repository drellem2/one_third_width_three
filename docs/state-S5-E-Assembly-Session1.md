# OneThird-S5-E Session 1 state report — Step 5 assembly landed

**Ticket:** mg-14b0 (FULL REFACTOR Phase 2, Wave-1; Piece-1 Steps-1-6
cascade port; scoped by mg-d8c7 §2.1 / §5.2 under S5-E; depends on
mg-faf8 / mg-be3e).
**Verdict:** **GREEN — substantively landed.** The Step 5 assembly
integrates the S5-A, S5-B, S5-C, S5-D ports and lands the `thm:step5`
endpoint (`step5.tex:74`) **cleanly**: the three G4 closures that the
S5-D `thm_step5_grounded` carried as *opaque hypotheses* are now
**discharged** from the grounded G4 port. The assembled endpoint is
instantiated **non-vacuously** on a concrete width-3 non-chain poset,
with **both** the richness and the collapse witnesses verified. Full
`lake build` clean; no new axioms, no `sorry`, no `native_decide`.

---

## §0. TL;DR

* **What S5-A–D delivered.** S5-A (`mg-b21f`) grounded G1+G2; S5-B
  (`mg-f268`) grounded G3 (Dilworth decomposition selection); S5-C
  (`mg-be3e`) grounded G4+G5; S5-D (`mg-d4bb`) the Rich-or-Collapse
  dichotomy `dichotomy_grounded` / `thm_step5_grounded`.
* **The gap S5-E closes.** S5-D's `thm_step5_grounded` already routes
  the dichotomy into the paper's (R) and (C) conclusions, but it
  carries the three **G4 closures** (`hG4_AB/AC/BC :
  SingleTripleMany … → Step5Richness …`) as **opaque hypotheses** — it
  never *constructs* them. They are the exact slot where the grounded
  G4 of S5-C must plug in. S5-E supplies that plug.
* **The assembly.** New file `Step5/Assembly.lean`:
  * **`richness_of_manyRich`** — the G4 integration step: a
    `SingleTripleMany` outcome (the dichotomy's "many rich pairs"
    branch) together with the Step-1 interface partition data yields
    the genuine `Step5Richness` conclusion (R), via S5-C's
    `fiber_mass_richness_grounded`. This *is* the discharge of
    `thm_step5_grounded`'s opaque G4 closure.
  * **`TripleFiberData`** — a structure bundling, per ordered triple,
    the Step-1 interface partition data (I1 `LP = goodFiber ⊔
    badFiber`, I2 thin bad sets, the activation threshold). These are
    genuine Step-1 outputs — the *input* to Step 5's G4, not something
    Step 5 proves (`step5.tex:86`).
  * **`thm_step5_assembled`** — the integrated `thm:step5` endpoint.
    For a width-3 poset presented by three monotone Dilworth chains
    (the G3 output) and the Step-1 interface data, it emits the genuine
    Rich-or-Collapse disjunction: (R) some triple yields a genuine
    `Step5Richness`, or (C) all three triples are banded. **No opaque
    richness hypothesis** — each G4 closure is discharged in-line by
    `richness_of_manyRich`.
  * **`thm_step5_collapse_layering`** — the (C)-branch G5 integration:
    S5-C's `global_layering_grounded` re-exposed as the named Step-5
    collapse endpoint (pointwise height bounds + the cyclic-compat
    `|fA − fB| ≤ 2K + 1`).
* **Non-vacuity bar met.** `thm_step5_assembled_concrete` instantiates
  the whole assembly on `W3 := Fin 3 × Fin 3` and verifies **both**
  witnesses: the (R) witness fires with genuine non-zero constants
  (`c_R = 9`, `|LP| = 6`, fiber mass `648`), the (C) witness is the
  genuine three-banded conjunction, and G5 fires the cyclic-compat
  bound `|2 − 0| ≤ 2·2 + 1` on the genuine incomparable pair
  `chainA 2 ∥ chainB 1`. G3 (`decomp_selection_groundSet`) is
  exercised explicitly. No `Subsingleton`/empty baseline anywhere.
* **No new axioms, no `sorry`, no `native_decide`, no headline-path
  change.** `Step5/Assembly.lean` is a new import-only leaf; the
  abstract and grounded Step-5 files are untouched.

## §1. Inventory delta

```
Assembly.lean   new, ~340 LoC   (assembly endpoint + concrete instance)
OneThird.lean   +1 import line
```

The four predecessor files (`G1G2Grounded.lean`, `GroundSet.lean`,
`G4G5Grounded.lean`, `DichotomyGrounded.lean`) and all abstract Step-5
files are **not modified** — `Assembly.lean` is purely additive, an
import-only leaf, keeping the merge surface minimal.

## §2. What the assembly does

| Symbol | Role (`step5.tex`) |
|---|---|
| `richness_of_manyRich` | G4 integration: `SingleTripleMany → Step5Richness` via grounded G4; discharges `thm_step5_grounded`'s opaque G4 closure (`step5.tex:218-237`, Step 3 case (i)) |
| `TripleFiberData` | Step-1 interface partition data per triple — the input to G4 (`thm:interface` (ii)+(iv), `step5.tex:668-689`) |
| `thm_step5_assembled` | **the integrated `thm:step5` endpoint** (`step5.tex:74`): width-3 Dilworth chains → genuine (R) ∨ (C), G4 closures discharged |
| `thm_step5_collapse_layering` | (C)-branch G5 integration: grounded Global Layering Lemma (`lem:global-layering`, `step5.tex:866`) as the named collapse endpoint |

### §2.1. Why the integration is genuine, not a re-routing

The load-bearing observation: a `SingleTripleMany richCount cT m n`
outcome unfolds to `cT · (m·n) ≤ richCount`. With `richCount :=
|richPairs|`, this is **exactly** the positive-density hypothesis
`hrich : c5 · sigma ≤ |richPairs|` of the grounded G4 port
`fiber_mass_richness_grounded`, with rich-density constant `c5 = cT`
and single-triple count `sigma = m·n = |A|·|B|`. The paper makes this
identification explicitly (`step5.tex:225-229`: *"This is precisely the
'in particular' hypothesis of Lemma~\ref{lem:fiber-mass} … the output
of Step 2 is literally the input to G4"*). So `richness_of_manyRich`
is a faithful port of Step 3 case (i) of the `thm:step5` proof, not a
typed-routing shell — it consumes the genuine interface partition and
emits the genuine cleared-denominator (R) bound.

The dichotomy itself (`dichotomy_grounded`, S5-D) is grounded on S5-A's
genuine `alphaIdx`/`betaIdx` incomparability-interval geometry, so the
`SingleTripleMany`/`SingleTripleBanded` outcomes the assembly routes
are themselves geometric, not opaque.

### §2.2. Scope of the G5 integration

`thm_step5_collapse_layering` re-exposes S5-C's
`global_layering_grounded` as the Step-5 (C) endpoint. The paper's G5
(`lem:global-layering`, `step5.tex:866`) is **stated** with explicit
IC-interval band hypotheses (`IC(a_i) ⊆ [f(i)−K, f(i)+K]`); the
grounded G5 discharges the combinatorial `IntervalsTouch` from genuine
poset incomparability (S5-C's substantive contribution) and packages
the three height-difference cases. Building the *global* height
function `h : P → ℤ` (`step5.tex:884-893`) is, per the abstract
`Layering.lean` docstring and the S5-C state doc §3 scope note, the
**Step 7 assembly level** — it is correctly downstream of Step 5. The
S5-scope collapse endpoint is the three packaged cases, which is what
`thm_step5_collapse_layering` delivers.

### §2.3. The richness disjunction shape

`thm_step5_assembled`'s (R) conclusion is a **three-way disjunction** —
one `Step5Richness` per ordered triple `(A,B|C)`, `(A,C|B)`, `(B,C|A)`
— faithful to the paper's "for at least one ordered triple" phrasing
(`step5.tex:81`). Each disjunct's richness is discharged from that
triple's own `TripleFiberData`, with single-triple count `σ = p·q`,
`p·r`, `q·r` respectively (matching the dichotomy's per-triple index
ranges). The (C) conclusion is the genuine three-banded conjunction
emitted verbatim by `dichotomy_grounded`.

## §3. Non-vacuous instantiation (`mg-14b0` acceptance bar)

`W3 := Fin 3 × Fin 3` (product order) — the genuine width-3, non-chain,
9-element poset of S5-A — with its Dilworth triple `(chainA, chainB,
chainCenum)`. `thm_step5_assembled_concrete` bundles, all proved (not
assumed):

1. `HasWidthAtMost W3 3` and `¬ IsChainPoset W3` — the `thm:step5`
   precondition;
2. **G3 (S5-B)** — `decomp_selection_groundSet` fires at `W3`,
   selecting the Dilworth decomposition `X = A ⊔ B ⊔ C` (Step 1 of the
   `thm:step5` proof);
3. **(R), G4 (S5-C) + dichotomy (S5-D)** — the genuine `Step5Richness`
   witness, with constant `c_R = 1·9 = 9`, universe `|LP| = 6`, total
   fiber mass `2·9·36 = 648`. The interface data `fiberData9` is a
   genuine `9`-element rich set with a genuine disjoint partition
   (`4`-element good fibers, `2`-element thin bad fibers). Density
   `cT = 1` — a **genuine, non-zero** density, not the `cT = 0`
   vacuous baseline (`richness_witness_nonvacuous` spells out the
   non-zero constants `9 / 6 / 648`);
4. **(C), dichotomy (S5-D)** — the genuine three-banded collapse
   output for the three ordered triples;
5. **G5 (S5-C)** — the grounded Global Layering Lemma fires the
   cyclic-compatibility bound `|2 − 0| ≤ 2·2 + 1` on the genuine
   incomparable pair `chainA 2 ∥ chainB 1`, with the `IntervalsTouch`
   discharged from real incomparability;
6. the rich set is genuinely populated — `(2 : Fin 3)` is in the rich
   row of `(A,B|C)`.

Additionally `thm_step5_assembled_fires` shows the integrated endpoint
`thm_step5_assembled` itself produces a genuine term when applied to
the `W3` data and `fiberData9` for all three triples. No
`Subsingleton`-on-empty baseline is used: `p = q = r = 3`, the poset
has `9` elements, the rich set and `LE(P)` are genuinely populated.

## §4. No gap-discovery

Default-skeptical re-read of `step5.tex:74-246` (`thm:step5` + its
proof) and `step5.tex:864-962` (G5 + `lem:cyclic-compat`) against the
assembled Lean port, applying `PROOF-STRUCTURE-ONBOARDING.md` §3
pitfall #2's three checks:

1. **Satisfiability under caps.** `thm_step5_assembled`'s hypotheses
   (three monotone Dilworth chains + three `TripleFiberData` bundles)
   are satisfiable at the headline range — explicitly witnessed by the
   `W3` instance with `fiberData9`. The conclusion's (R) disjuncts and
   (C) conjuncts are genuine non-trivial propositions (verified
   numerically: `Step5Richness 6 648 9`, the three banded facts with
   genuine band data).
2. **Discharge-coverage of cited artefacts.** The only cited grounded
   artefacts are `fiber_mass_richness_grounded` (S5-C),
   `global_layering_grounded` (S5-C), `dichotomy_grounded` (S5-D),
   `decomp_selection_groundSet` (S5-B) — each used within its stated
   scope. `richness_of_manyRich` consumes the `SingleTripleMany`
   outcome in exactly the shape the dichotomy emits and feeds it to G4
   in exactly the shape G4 consumes (`step5.tex:225-229` makes this
   identification authoritative).
3. **Universal-quantifier truthfulness.** `thm_step5_assembled` is
   `∀ (chains, interface data), (R) ∨ (C)` — no problematic `∃ L`
   existence claim. The (R) ∨ (C) disjunction is the paper's
   `thm:step5` conclusion verbatim; the (C) branch is the genuine
   three-banded conjunction (S5-D §4 confirms this is the genuine,
   non-trivial collapse output — *not* the weak `Step5Collapse`
   packaging).

The port surfaced **no ill-posed target** and **no missing mathlib
dependency** — the block-and-report condition is **not** triggered.

One scope clarification (not blocking, consistent with S5-C §3 and
S5-D §4): the paper's `thm:step5` proof Step 3 case (ii)
(`step5.tex:240-246`) transitions from the dichotomy's *rich-row*
banding to G5's *IC-interval* band hypotheses with the terse phrasing
"the three monotone maps … together express P as a band". This is not
a rigour gap — `thm:step5` conclusion (C) (`step5.tex:98`) explicitly
admits `O_T(1)` slack ("each element is incomparable to only `O_T(1)`
elements outside the corresponding band"), which absorbs the
rich-vs-IC discrepancy. The grounded G5 (`global_layering_grounded`,
S5-C) is correctly stated taking the IC-interval band as its
hypothesis, faithful to `lem:global-layering`'s own statement; the
assembly wires it as the (C) endpoint without inventing a
rich-row-to-IC bridge (which would be exactly the vacuity trap of
pitfall #2).

## §5. Build

`lake build OneThird` (full tree) clean. `Assembly` and all downstream
modules compile; the new file is an import-only leaf, so nothing else
recompiles beyond the added import. No new `sorry`, no new axioms, no
`native_decide`. `#print axioms` on `thm_step5_assembled`,
`thm_step5_assembled_concrete`, `richness_of_manyRich`,
`thm_step5_collapse_layering`: `[propext, Classical.choice, Quot.sound]`
only — no project axioms, no `sorryAx`, no `Lean.ofReduceBool`.
