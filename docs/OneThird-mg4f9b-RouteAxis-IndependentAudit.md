# INDEPENDENT AUDIT of mg-4f9b — the route-axis restoration and the PROVENANCE negative (mg-56be)

**Target.** `docs/OneThird-mg4f9b-RouteAxis.md` (mg-4f9b), the gate it repairs
(`scripts/onethird_mg2c34_n7_overlap_test.py`), and — as the author itself asked — mg-4f9b's **negative
claim** that the gate *cannot* close the one-character-selector class.

**Lineage, because it sets the bar.** mg-09ea found two controls passing while blind; mg-60d3 repaired those
two instances; mg-5ad1 showed the repair closed two instances and not the class; mg-75f0 widened the field
axis and silently narrowed the route axis; mg-bd53 measured that and returned RED. mg-4f9b is generation
five. **Every previous generation looked like a fix to its author.**

**Instrument.** `scripts/onethird_mg56be_provenance_audit.py`, built from scratch. mg-4f9b's own probe
(`scripts/onethird_mg4f9b_route_axis_probe.py`) asks that an auditor not validate its result by re-running
it; that request is honoured — it was **not run**. mg-bd53's probe **was** run, unchanged and byte-verified,
on both trees, because it is the instrument that found the regression.

---

## §0 — Verdict: **RED**, on one axis only, and the rest is **GREEN**

RED is not a reversal of mg-4f9b's repairs. **Every one of them holds**, two are confirmed by mg-bd53's own
unmodified instrument going `0 → 1`, and its central provenance measurement reproduces exactly. The RED is on
the **negative** — the thing mg-4f9b asked to have attacked — and on two new defects in structure it added.

| | |
|---|---|
| **Did mg-4f9b modify mg-bd53's probe — the instrument that found the regression?** | **NO.** `md5 a97218cb1a39cfabaf0fd9ec3bd97e1d` on both trees, byte-identical. §1 |
| **Field axis, before → after** | **No loss anywhere.** `22 of 23` compared per `n=7` row on both trees, plus `24 of 25` at the new `fam:N (2+2)`; one declared exclusion (`name`). §2 |
| **Route axis, before → after** | **Restored, and the restoration is real.** `lambda_std` and `delta` regained a gated second route; `bk_lambda2` kept its. §2 |
| **Is the `lambda_std` flip (`np.max`→`np.min`) caught again?** | **YES**, exit 1 at `#3/#20/#600`, via `lambda_std=False` — i.e. through the **restored route**, not a special case. §3 |
| **Is the fix a route restoration or a `lambda_std` special case?** | **A route restoration**, applied uniformly to all three two-route quantities from one declaration table. §3 |
| **The `frozen_pair` class (G3), still open?** | **Open, and mg-4f9b says so unambiguously**, with the exact numbers, in §3.3 and in the gate's own header. §4 |
| **The population claim ("22 of 23")** | **Correct, and the corrected claim names its population.** Counted from the JSON: 1091 rows, 25 field names, 54 carry the two `h_bk_*` fields, no duplicate-name collapse. §5 |
| **The AMBER (G5)** | **Correctly repaired.** The claim was scoped, the Aldous/CLR justification is intact, and **no behaviour was reverted** — `_antichain_row_ok` still carries mg-75f0's third conjunct and was not touched by mg-4f9b. §6 |
| **PROVENANCE, measured mechanically** | **5 controls THEOREM-referenced, 1 STORED.** Perturb the store by `1e-6` and see whose verdict moves; agrees with mg-4f9b's hand-authored ledger on every row. §7 |
| **Does mg-4f9b's mutate-and-regenerate experiment reproduce?** | **YES, exactly, rebuilt from scratch.** `M3` exit 1 → `M3+regen` exit **0**; `M4` exit 1 → `M4+regen` exit **1**. The `M4` control is what makes it a measurement. §8.1 |
| **THE RED — "the gate CANNOT close this class"** | **REFUTED BY CONSTRUCTION.** Three corpus-independent references exist for `frozen_pair_overlap_with_U`, are ~15 lines, and close **both** open instances — mg-bd53's C2 *and* mg-5ad1's M3-under-regeneration. mg-4f9b considered one candidate, rejected it correctly, and generalised. §8 |
| **A defect in mg-bd53's probe, found in flight** | **YES.** Part 1's `still_gated` column — the one the lineage reads as the route-axis measurement — is a **hardcoded dict**. It cannot detect a route restoration and prints the same table forever. §1.2 |
| **A new defect in mg-4f9b's own new structure** | **YES.** The per-dataset census is a **field-NAME** statement being read as coverage: `h_bk_exhaustive` is compared at exactly one poset, `\|L\|=6`, and the identity population has **no poset with `6 < \|L\| ≤ 15`**. §9 |
| **A second new defect, route axis** | **YES.** The route **declaration** is a gate condition; the route **WIRING** is not. mg-75f0's regression can be re-committed in two lines with every gate condition in the file still green. §10 |

**Why RED rather than AMBER.** mg-4f9b's own framing is the right one: *"A 'no' is a comfortable thing for an
author to write because nothing can then be shown to have failed."* Something can now be shown to have
failed. The negative is the ticket's headline — it is the reason the ticket did not attempt a fourth
widening — and it is wrong in the direction that leaves work undone. §9 and §10 are each independently
enough for RED on the *repairs* as well: both are new, both are in structure mg-4f9b added or restored, and
neither was measured by anybody.

---

## §1 — The instrument, and a defect in it

### 1.1 mg-bd53's probe is unmodified

The brief's first instruction was to treat modification of mg-bd53's probe as suspicious. It was not
modified:

```
md5 -q wt-pre/scripts/onethird_mgbd53_widening_audit_probe.py   a97218cb1a39cfabaf0fd9ec3bd97e1d
md5 -q wt-post/scripts/onethird_mgbd53_widening_audit_probe.py  a97218cb1a39cfabaf0fd9ec3bd97e1d
git log 91fa25f..HEAD -- scripts/onethird_mgbd53_widening_audit_probe.py   (empty)
```

Run unchanged on a pristine `91fa25f` (pre-repair) and on `HEAD` (post-repair), in two detached worktrees,
BLAS pinned to one thread. **Exactly two rows changed, both `0 → 1`:**

| mutation | pre-repair | post-repair | |
|---|---|---|---|
| `none` | exit 0 | exit 0 | |
| `A1` `standard_block_and_lambda` argmax→argmin | exit 1 | exit 1 | unchanged |
| `A2` `bk_frozen_pair` max-bias max→min | exit 1 | exit 1 | unchanged |
| **`B1` mg-4a86's own `lambda_std` `np.max`→`np.min`** | **exit 0** | **exit 1** | **REPAIRED** |
| **`C1` `bk_cheeger_exhaustive` volume normalisation** | **exit 0** | **exit 1** | **REPAIRED** |
| `C2` `frozen_pair_indicator` loses its centring | exit 0 | exit 0 | **still open** |
| `M3` mg-5ad1's frozen-pair selector | exit 1 | exit 1 | unchanged |
| `M4` mg-5ad1's rank filter | exit 1 | exit 1 | unchanged |

**No row went `1 → 0`.** The repair is monotone on this instrument: `+2` caught, `−0` lost. mg-4f9b's
before/after claim reproduces exactly, including that `C1` was not one of its targets and was caught by the
population fix anyway.

`B1` is caught at `enum-n7-#3/#20/#600` with the diagnostic reading
`(num_LE=True lambda_std=False delta=True lambda2_BK=True)` — the restored route naming itself. `C1` is
caught at `fam:N (2+2)`, the poset mg-4f9b added.

### 1.2 …and its route-axis column is not a measurement

Part 1 of mg-bd53's probe prints the table the whole lineage has been reading as the route-axis
measurement, and it printed **byte-identical output on both trees** — still reporting `lambda_std` and
`delta` as having lost their gated second route *after* mg-4f9b restored them.

That is not a regression. It is a defect in the instrument:

```python
    still_gated = {"num_LE": False, "lambda_std": False, "delta": False,
                   "bk_lambda2": True}
```

`still_gated` is a **hardcoded dict**. Nothing derives it from the gate. `lost_second_route` — the probe's
headline list — is computed from it, so the probe will report `['delta', 'lambda_std']` as permanently lost
no matter what any future ticket does. The two things part 1 *does* measure (`legacy_match_keys_are_inert`,
`row_wide_comparison_decides`) are real and both still True, correctly: mg-4f9b kept the four `match_*` keys
as aliases and ANDed the routes into `field_matches` rather than beside it.

**Consequence for the brief.** "Run mg-bd53's probe unchanged on both trees and diff its output" is
necessary and not sufficient: on the route axis the diff is empty *by construction*. The route axis had to
be re-measured from the gate's source, which §2 does.

**This is not a finding against mg-4f9b** — it inherited the instrument. It is a finding against the
instrument, and it is the reason a fourth generation could have "restored the route axis" in a commit
message while changing nothing, and no committed probe in this repo would have contradicted it.

---

## §2 — The 2×2, measured from the gate rather than from a table

| | FIELD axis (fields compared) | ROUTE axis (gated independent recomputations) |
|---|---|---|
| **pre-repair `91fa25f`** | **22 of 23** per `n=7` row, 1 declared exclusion (`name`), at **7** posets | `num_LE` **1** · `lambda_std` **1** · `delta` **1** · `bk_lambda2` **2** |
| **post-repair `HEAD`** | **22 of 23** at the same seven, plus **24 of 25** at the new `fam:N (2+2)` — **8** posets | `num_LE` **1** · `lambda_std` **2** · `delta` **2 (half)** · `bk_lambda2` **2** |

Field counts read off the gate's own printed identity lines on an unmutated run of each tree, not from a
table:

```
post-repair, unmutated:  fields compared 22/23 (excluded: name)  ... mismatched: none    x7
                         fields compared 24/25 (excluded: name)  ... mismatched: none    (fam:N (2+2))
```

**Nothing was traded.** The field axis did not narrow anywhere and the route axis rose at two of four
quantities. This is the check mg-bd53's RED demanded and it passes.

Verified from source, not from `IDENTITY_SECOND_ROUTES`:

```
quantity      declares 2nd route  computes it  ANDs it in
bk_lambda2                  True         True        True
delta                       True         True        True
lambda_std                  True         True        True
num_LE                     False        False       False
```

Cross-checked against the pre-repair tree, where the count of named route keys is **0**: mg-75f0's surviving
`bk_lambda2` route was ANDed *inline*, with no `second_route_*_ok` key at all
(`91fa25f:.../onethird_mg2c34_n7_overlap_test.py:784-787`). mg-4f9b's form names all three, which is the
reason a source-level check is now possible — and §10 is that it is not performed.

`num_LE`'s single route is honestly labelled and the reason is right: both sides call the same
`Poset.linext_count` and a second copy of that DP would be a second copy, not a second route. `delta`'s is
labelled a **half** second route because `before_prob_dp` is shared and only the aggregation differs — also
right, and the kind of qualifier this arc has repeatedly lost.

---

## §3 — The `lambda_std` flip, reproduced independently, and *how* it is caught

Reproduced in an isolated tree with an anchor-count assertion (`np.max(w)` → `np.min(w)` in
`onethird_mg4a86_standard_dominance_target_audit.lambda_std`, 1 occurrence required, 1 found):

```
CASE  B1   gate=widened   --> exit 1
  GATE FAILURE: enum-n7-#3:   ... (num_LE=True lambda_std=False delta=True lambda2_BK=True)
  GATE FAILURE: enum-n7-#20:  ... (num_LE=True lambda_std=False delta=True lambda2_BK=True)
  GATE FAILURE: enum-n7-#600: ... (num_LE=True lambda_std=False delta=True lambda2_BK=True)
```

**It exits 1.** And the brief's real question — *how*:

```python
rec["second_route_lambda_std_ok"] = bool(abs(rec["lambda_std"] - ref["lambda_std"]) < IDENTITY_FLOAT_TOL)
rec["match_lambda_std"]           = bool(rec["match_lambda_std"] and rec["second_route_lambda_std_ok"])
rec["field_matches"]["lambda_std"] = rec["match_lambda_std"]
```

This is **not** a `lambda_std` special case. Three properties make it a class fix rather than an instance
fix, and each is the thing mg-60d3 lacked:

1. **The same three lines exist for all three two-route quantities**, from one table, with one shape.
2. **The route is ANDed *into* `field_matches`**, not asserted beside it — so
   `scripts/onethird_mg5ad1_gate_blindspot_probe.py` part B2, which perturbs one field at a time and calls
   `_identity_row_ok` on `field_matches` alone, still sees it. A route wired beside the predicate would
   have been invisible to the probe that enforces the gate. That placement is deliberate and documented.
3. **`_identity_routes_declared()` is a gate condition**, so a fifth compared quantity with no declaration,
   or a reason that decays to a stub, fails the gate.

The caveat is §10: property 3 enforces the *declaration* and nothing enforces the *wiring*.

---

## §4 — The `frozen_pair` class (G3): still open, and stated so

Dropping one line from `frozen_pair_indicator` (mg-bd53's `C2`, `f -= f.mean()` → `f -= 0.0 * f.mean()`)
still exits **0**, on both trees, and the moved values are printed by the gate on the way past. Reproduced
independently, in-process:

| poset | baseline `frozen_pair_overlap_with_U` | under C2 |
|---|---|---|
| `enum-n7-#3` | 0.807168 | **0.903584** |
| `enum-n7-#20` | 0.809421 | **0.907598** |
| `enum-n7-#600` | 0.809650 | **0.904825** |

These match mg-bd53's `0.8072/0.8094/0.8096 → 0.9036/0.9076/0.9048` to every printed digit.

**Was it left ambiguous?** No. mg-4f9b's §3.3 states it with the numbers, the gate's header states it under
`WHAT THIS GATE CANNOT SEE`, and the reproducibility note at the end of the header states the mechanism
(the gate writes `data/onethird-mg2c34-n7-overlap.json` and never reads it back). **Disclosure is GREEN and
is the best in the arc.** What is RED is the conclusion drawn from it — §8.

---

## §5 — The population claim, counted from the JSON

Counted directly from `data/onethird-mg8b64-L1b-bk-transport-transfer.json`, not read from any document:

```
rows                                            1091
distinct field names over ALL rows                25
rows carrying h_bk_exhaustive                     54
rows carrying h_bk_argmin_is_pair_cut             54
every other field name                          1091 rows
duplicate row names                                 0
fam:N (2+2) present, carries 25 fields            yes
```

Every number in mg-4f9b's corrected claim is right, and the corrected claim **names its population** —
*"1091 committed rows, 25 distinct field names, 24 compared at ≥1 of the 8 identity posets, 1 excluded with
a reason, compared NOWHERE: none"*. The per-dataset census is a genuine gate condition
(`if dataset_uncompared: failures.append(...)`), not a printed sentence.

One hazard checked and clear: the census builds `ref_rows` as a dict keyed on `name`, so a duplicated row
name would silently collapse rows and could drop a field from `dataset_schema`. There are **0** duplicate
names, and `sorted({k for r in rows for k in r})` gives the same 25 either way. The check is sound *on this
dataset*; it is one duplicated name away from under-counting, which is worth a comment and is not a defect
today.

§9 is where this claim's *reach* is measured rather than its arithmetic.

---

## §6 — The AMBER (G5): claim corrected, behaviour intact

Three things had to be true and all three are.

1. **The correction is to the CLAIM.** Ledger row 7 and §5 of `docs/OneThird-mg75f0-GateClassClosure.md`
   now read `~~docstring only, no behaviour change~~ — the JUSTIFICATION is docstring-only; the COMMIT
   added a third conjunct (dim_U == dim_U_known)`. The strikethrough is on the wording, not on the work.
2. **The Aldous/CLR justification is not weakened.** It survives verbatim: CLR gives the gap *eigenvalue*;
   `c_min = 1` is the strictly stronger eigenspace-containment statement; the licence is therefore a
   verified property of these specific matrices, not the theorem; and a future failure narrows the
   *population* rather than loosening the *assertion*. That last clause is the load-bearing one and it is
   still there, in both the doc and `_antichain_row_ok`'s own docstring.
3. **No behaviour was reverted alongside the wording.** `_antichain_row_ok` still returns all three
   conjuncts, and `git log -L` over that function shows its last modification is **`e8e70c1` (mg-75f0)** —
   mg-4f9b did not touch the predicate at all. The correction is purely to the record.

---

## §7 — PROVENANCE, measured mechanically rather than declared

mg-4f9b's third axis asks, per control, whether its reference is a theorem the corpus cannot produce or a
number the corpus produced and committed. Its ledger answering that is hand-authored. This audit measures
it instead, and the measurement needs no docstring: **perturb the store and see whose verdict moves.** Every
float field in the committed dataset scaled by `1 + 1e-6`; one gate run.

```
  perturbed 16398 float values in the committed dataset by a relative 1e-6

  control                                          verdict moved  reference
  CONTROL A  graded analytic, c = cos^2(theta)             False    THEOREM
  CONTROL B  antichain c = 1, dim U = (n-1)^2+1            False    THEOREM
  CONTROL C  broken projector must NOT return 1            False    THEOREM
  CONTROL E  dim U <= (n-1)^2+1 and dim U < |L|            False    THEOREM
  CONTROL F  two-sided reading-dependence on real data      False    THEOREM
  IDENTITY   recomputed row vs the committed row            True     STORED
```

The partition agrees with mg-4f9b's hand-authored ledger on **every** row. **CONTROL A / B / C / E / F are
theorem-referenced; the IDENTITY check is the only stored-reference control in the gate.** mg-4f9b named
A/B/C/E; this measurement adds F to the theorem side, which is right — its reference is `dim_E > 1` and a
`1e-9` tolerance, both literals.

This is worth having as an *instrument* rather than only as a result: it is one gate run, it needs no
docstring, and it will keep classifying controls added by later tickets. A control whose author believes it
is theorem-referenced and which moves when the store moves is a defect this catches for free.

**Reported as an upper bound, in the terms the brief requires.** The identity check's coverage figure — 22
of 23 fields per row, 24 of 25 at `fam:N (2+2)`, three of four quantities two-routed — is not a durable
number. It holds *only until somebody re-runs the probe that wrote the store*. §8's `M3+regen` row is that
sentence as a measurement.

---

## §8 — THE RED: the negative is refuted by construction

### 8.1 What mg-4f9b claims, and how narrowly

Two statements, and they are not the same statement.

> **(i)** *"Widening cannot [close the class]. … A mutation that moves the computation and its own
> reference together is invisible to any number of comparisons against that reference."*

> **(ii)** *"Can the gate close the class? **No.** … Where the class is detected: the independent audit
> stage … That is not a gap to be closed by this file; it is the division of labour."*

**(i) is correct, important, and this audit confirms it independently.** Rebuilt from scratch, eleven gate
runs, anchor counts asserted, 8 rows regenerated per `+regen` case and the count asserted:

| case | exit | |
|---|---|---|
| `none` | 0 | 22/23 fields at the seven `n=7` posets, 24/25 at `fam:N (2+2)`, `mismatched: none` |
| `M3` | **1** | caught, as mg-4f9b reports |
| **`M3+regen`** | **0** | **absorbed — the stored reference moved with the mutation** |
| `M4` | **1** | caught |
| **`M4+regen`** | **1** | **still caught — regeneration cannot move `(n−1)²+1`** |
| `C2` | 0 | never compared |
| `C2+regen` | 0 | never compared, so regeneration is irrelevant |

**mg-4f9b's central measurement reproduces exactly.** The `M3` / `M3+regen` pair is the provenance effect and
the `M4` / `M4+regen` pair is its control, and the control is what makes the pair a measurement rather than
an anecdote.

**(ii) does not follow from (i), and is false.** (i) is a statement about *comparisons against the stored
reference*. It says nothing about controls that are not such comparisons — and mg-4f9b's own §3.2 states
the correct design rule three sentences later: *"A new control is worth more than a wider comparison exactly
when its reference is one the corpus cannot regenerate."* **That rule, applied to the one quantity mg-4f9b
names as open, closes it.**

### 8.2 The adversarial question, settled

mg-4f9b names the question it most wants attacked: *does some cheap independent reference exist for
`frozen_pair_overlap_with_U`, and did mg-4f9b talk itself out of looking for one?*

**It exists. Five of them. And yes — mg-4f9b evaluated exactly one candidate and generalised from its
rejection.** The candidate it considered was *having the gate read its own committed output back*; it
rejected that correctly, on the grounds that a read-back only relocates the mutation into the `R1` row
above. Every candidate below is **not a comparison against a stored number at all**, so the rejection does
not reach them.

Let `f = gate.frozen_pair_indicator(P, x, y)` over `L(P)` and `P_U` the projector onto the one-particle
span. The gate reports `f᷀ᵀP_U f` and never reads it back.

| | invariant | reference | is it a stored number? |
|---|---|---|---|
| **I1** | `Σ_σ f(σ) = 0` | the integer **0**, from *"a mean-centred vector sums to zero"* | no |
| **I2** | `‖f‖ = 1` | the integer **1**, from *"the function returns `f/‖f‖`"* | no |
| **I3** | `0 ≤ fᵀP_U f ≤ ‖f‖²` | the interval **[0,1]**, from *"`P_U` is an orthogonal projector"* | no |
| **I4** | `fᵀP_U f ≥ ⟨f, ĝ⟩²` for `g(σ) = pos_σ(y) − pos_σ(x)` | **Bessel's inequality**, with a constructible witness | no |
| **I5** | `fᵀP_U f` recomputed by least squares against the `\|L\|×n²` position-indicator matrix | a second **route**, never forming the SVD projector | no |
| **I6** | `fᵀP_U f < 1 − ε` | the integer **1** — the same vacuity floor `_projector_row_ok` already applies to `dim U` | no |

**I4 deserves a sentence of its own, because it is a real theorem about this specific quantity and not
floating-point hygiene.** `g = Σ_a a·(e_{y,a} − e_{x,a})` is a linear combination of position indicators, so
`g ∈ U` **by construction** — verified, not assumed: `‖P_U ĝ − ĝ‖ ≤ 5.1e-15` at every measured poset.
Bessel then bounds the overlap from below by `⟨f, ĝ⟩²`. Measured, and it is **tight**:

| poset | `frozen_pair_overlap_with_U` | I4 lower bound | bound/value |
|---|---|---|---|
| `enum-n7-#3` | 0.807168 | 0.788086 | **0.9764** |
| `enum-n7-#20` | 0.809421 | 0.787622 | **0.9731** |
| `enum-n7-#600` | 0.809650 | 0.787772 | **0.9730** |

The frozen-pair indicator is within **2.4%** of being explained by a single rank-difference observable. That
is a fact about the corpus's own mechanism claim, obtained from a control that compares against nothing the
corpus produced.

### 8.3 Both open instances close, and they close *under regeneration*

| variant | I1 | I2 | I3 | I4 | I5 | I6 | caught by |
|---|---|---|---|---|---|---|---|
| baseline, 3/3 posets | ok | ok | ok | ok | ok | ok | — (no false positives) |
| **C2** (uncentred), 3/3 posets | **FIRE** | ok | ok | ok | ok | ok | **I1** |
| **M3** (max-ratio pair), 3/3 posets | ok | ok | ok | ok | ok | **FIRE** | **I6** |

- **C2** — the instance that has survived four generations. `|Σf|` moves from `≤ 2.3e-16` to **8.12 / 10.10 /
  13.42**. It fires by twelve orders of magnitude against a reference of exactly `0`.
- **M3 under regeneration** — the case mg-4f9b measured as exit 0 everywhere. The max-ratio selector drives
  the overlap to **exactly 1.000000** at 3 of 3 off-regime posets (`1 − ov = 2.2e-15`, `−2.9e-15`, `0.0`).
  A floor at `1 − 1e-6` fires.

**Neither reference can be regenerated, because neither is a number the corpus produced.** No re-run of any
probe moves `0`, `1`, or Bessel's inequality. That is the whole point, and it is mg-4f9b's own design rule
being applied to mg-4f9b's own open instance.

**Cost:** I1 and I6 together are about fifteen lines inside `measure()`, on quantities the gate already
computes. No new gate runs, no new imports, no new dataset.

### 8.4 The honest scope of the refutation

Stated plainly, because a control whose stated reason is wider than its real one is this arc's named defect.

- **I6 needs its population scoped.** It is a statement about the **off-regime measured posets**, where the
  corpus's own claim is that the overlap is `~0.81` and emphatically not 1. There are posets where `f ∈ U`
  legitimately. If it ever fires legitimately the fix is to narrow the population, not to loosen the number
  — the same rule `_antichain_row_ok`'s docstring already states for CONTROL B.
- **These six do not close the class in general.** They close `frozen_pair_overlap_with_U`, which is the
  quantity ledger claim 8 rests on and the one mg-4f9b names as the open instance. A selector flip that
  lands on a legitimately-different pair without driving the overlap to 1 would pass all six. **The general
  class remains open** and mg-4f9b's diagnosis of *why* remains the right one.
- **What is refuted is the specific proposition** that the gate cannot close this class and must hand it to
  the audit stage. It can close both named instances, cheaply, with theorem-grade references. That is not a
  small correction: it is the difference between a residual and a division of labour.

---

## §9 — NEW DEFECT: the per-dataset census is field-NAME coverage, read as coverage

This is in the structure mg-4f9b **added**, and it is the brief's target 7 — *"what did it add beyond its
brief, and treat that as a primary target."*

The census guarantees that every field name in the committed dataset is compared at **≥1** poset. For
`h_bk_exhaustive` and `h_bk_argmin_is_pair_cut` that is **exactly one** poset — `fam:N (2+2)`, `|L| = 6` —
out of the **54** rows that carry them. And the identity population has a gap exactly where it matters:

```
the gate's 8 identity posets, |L|:  6, 21, 25, 132, 180, 198, 288, 360
any poset with 6 < |L| <= 15 ?      NO
```

`bk_cheeger_exhaustive` returns a value only for `|L| ≤ BK_CHEEGER_CAP = 15`. So the window `7…15`, which is
where **36 of the 47 reconstructible field-carrying rows live**, is compared nowhere — while the census
prints `compared NOWHERE: none`.

**My mutation `mg56be-A`, used by none of the fifteen mutations across the three prior generations:**

```python
BK_CHEEGER_CAP = 15   ->   BK_CHEEGER_CAP = 6
```

One token, on a named tuning constant of exactly the kind an author edits to speed up a sweep. It destroys
`h_bk_exhaustive` and `h_bk_argmin_is_pair_cut` on **36 of 47** rows and is a **no-op on the one poset the
gate compares them at**, because that poset has `|L| = 6`.

**Measured, on the repaired gate:**

| case | exit | census line the gate printed |
|---|---|---|
| `mg56be-A` | **0** | `... 24 compared at >=1 of the 8 identity posets, 1 excluded with a reason, compared NOWHERE: none` |
| `mg56be-A+regen` | **0** | identical |

The gate is silent, and **its census prints a clean bill on the way past** — the same sentence, verbatim, that
mg-4f9b added to close the zero-comparison gap. The `+regen` row is there to show the blindness is not a
provenance effect: this mutation needs no regeneration to hide, because the one poset that compares the field
is the one poset the mutation does not reach.

**The repair is one line, and it is a population statement rather than a check.** Add one poset with
`6 < |L| ≤ 15` to the identity population. `fam:N (2+2)` was chosen for cost (`|L| = 6`); a second small
poset above the parity of the cap costs almost as little and turns one-poset name coverage into two-poset
value coverage. Alternatively, and more in the spirit of §8: `h_bk` is a conductance and satisfies
`0 ≤ h_bk ≤ 1` with an achievable pair-cut upper bound — a theorem-referenced control, immune to
regeneration, on a quantity that currently has a one-row stored reference.

**This does not make mg-4f9b's G4 repair wrong.** Comparing the two fields somewhere is strictly better than
the zero comparisons it found, and choosing to compare rather than declare an exclusion was the right call
for the stated reason. The defect is that the census's *printed statement* — the thing a later reader
consults — does not distinguish "compared" from "covered", which is the same shape as the per-row / per-
dataset confusion mg-4f9b was created to fix, one level in.

---

## §10 — NEW DEFECT: the route DECLARATION is enforced, the route WIRING is not

Also in structure mg-4f9b added, and it is the mg-75f0 regression re-armed.

`_identity_routes_declared()` is a gate condition. It checks that every legacy field **has an entry** with a
non-stub reason. Nothing in the gate checks that a declared route is **computed** or **ANDed in**. The gate
says so itself:

> *It does NOT verify that a declared route is wired, nor that the two implementations are still distinct —
> that needs to import three other modules and diff their source, so it lives in
> `scripts/onethird_mg4f9b_route_axis_probe.py` part 1 (seconds, not wired to every run).*

**Two different checks are being priced as one.** Verifying the two implementations are still *distinct*
does need three imports and a source diff — that justification is correct. Verifying a declared route is
**wired at all** does not: it is a key-presence check on the record the identity loop already builds, and it
costs nothing:

```python
for field, d in IDENTITY_SECOND_ROUTES.items():
    if d["second_route"] is not None and f"second_route_{field}_ok" not in rec:
        failures.append(f"IDENTITY ROUTES: {field} DECLARES a second route that is not wired "
                        f"into field_matches -- the declaration and the check have separated")
```

Three lines. **And it is exactly the check that would have turned mg-75f0's silent route drop into a gate
failure** instead of an audit finding two generations later.

**My mutations `mg56be-B` and `mg56be-B+B1`**, on a line no prior generation touched:

```python
rec["match_lambda_std"] = bool(rec["match_lambda_std"] and rec["second_route_lambda_std_ok"])
   ->  rec["match_lambda_std"] = bool(rec["match_lambda_std"])
```

`IDENTITY_SECOND_ROUTES["lambda_std"]` still declares **TWO ROUTES** with a 300-character reason.
`_identity_routes_declared()` still returns clean. The per-dataset census still prints
`compared NOWHERE: none`.

**Measured, on the repaired gate:**

| case | edits applied | exit | |
|---|---|---|---|
| `mg56be-B` | gate ×1 | **0** | the gate does not notice that a declared route has stopped being computed |
| **`mg56be-B+B1`** | gate ×1, `mg4a86` ×1 | **0** | **the regression is back** |

`mg56be-B+B1` is the decisive row, and it exits 0. **The regression mg-4f9b exists to repair is reinstated by
a two-line edit that every gate condition in the file passes** — `_identity_routes_declared()` clean,
`compared NOWHERE: none`, `All controls and identity checks PASSED` — and the only artifact in the repo that
would contradict it is a probe that runs nowhere.

For scale: mg-bd53 needed a fourteen-run audit to find that mg-75f0 had dropped this route. After mg-4f9b,
dropping it again is still a silent edit; what mg-4f9b added is a *declaration* that would then be false, and
nothing reads the declaration against the code.

**mg-4f9b's disclosure is honest** — the commit message says plainly *"the new probe is NOT wired into CI …
What IS enforced on every gate run is the route declaration and the per-dataset census, which are the cheap
halves."* The defect is that "the cheap halves" was drawn in the wrong place: the wiring check is cheaper
than either of the two things that were wired.

---

## §11 — Other things checked, and one thing tried that did nothing

**Tried and it did nothing, reported because a negative is data.** `bk_cheeger_exhaustive`'s argmin
tie-break, `phi < best - 1e-15` → `phi <= best + 1e-15` (report the *last* argmin among ties rather than the
first). A genuine one-line change to a real semantic choice, affecting `h_bk_argmin_is_pair_cut`. Measured
across all **47** reconstructible field-carrying rows: **0 moved**. It is a genuine invariance of this
computation, not a blind spot. My reimplementation reproduces the committed `h_bk_exhaustive` and
`h_bk_argmin_is_pair_cut` on **47 of 47** rows, which is what licenses reading the 0 as invariance rather
than as a broken harness.

**The data refresh (`4515cdb`).** mg-4f9b regenerated `data/onethird-mg60d3-gate-mutation-demo.json` — a
probe's committed output, refreshed by its author after a code change, which is precisely the act §3 of its
own deliverable identifies as what blinds the gate. It flagged this itself, in the commit message, with the
correct distinction: *"It is safe HERE only because nothing compares this file against anything — it is a
record, not a reference."* Verified: nothing reads that file. The diff is confined to the recorded failure
text (the eighth poset appearing, and the second route naming itself), and the demo still exits 0. **Clean,
and the self-flagging is the standard the rest of the arc should be held to.**

**mg-bd53's probe now exits 1 on `HEAD`,** and mg-4f9b deliberately left it that way so a later reader can
reproduce the before/after. Checked: neither mg-bd53's probe nor mg-4f9b's is wired into
`.github/workflows/*.yml` or `scripts/refinery_gate.sh`, so nothing automated is red, and mg-bd53's own
docstring says a `0 → 1` flip is *"good news reported as a failure"*. Defensible; the rows should be
re-pointed by whoever lands §9/§10.

**A defect in THIS audit's own harness, recorded because it nearly produced a false RED against mg-4f9b's
headline.** The first version of `regenerate()` read the small-`|L|` poset's name off the gate module, where
it is a **local of `main()`** and not a module attribute. The subprocess raised `AttributeError`, the caller
returned `{"ok": False}` — and did not fail. Every `+regen` case then ran against an **unregenerated**
dataset and reproduced the mutation-alone exit code exactly, so `M3+regen` read `exit 1` where mg-4f9b
measured `exit 0`. Had that been reported, it would have been an audit claiming mg-4f9b's central
provenance measurement does not reproduce, on the strength of a regeneration that never happened. It is now
fatal on failure **and** asserts that exactly 8 rows were rewritten. The general lesson is the arc's own:
*a negative control that silently becomes a no-op reports the absence of an effect it never looked for.*

**`fam:N (2+2)` joining the identity population** does not disturb the other controls: CONTROL E's
population is scoped to `report["measured"]` and CONTROL F's to `DEGENERATE_LAMBDA2`, neither of which the
new poset enters.

**mg-4f9b's own `D1`/`D2` claims** are on lines (`delta`'s aggregation; `phi = boundary/((n-1)*mn)`) that no
prior generation used, so the "mine" column is accurate. Not independently re-run — they are the author's
acceptance rows, and this audit's job was to choose its own.

---

## §12 — Findings ledger

| # | finding | severity | § |
|---|---|---|---|
| 1 | **mg-4f9b's negative — *"the gate cannot close this class"* — is refuted by construction.** Three corpus-independent references (`I1`, `I6`, plus `I4` as a tight theorem-grade bound) close both named open instances, `C2` and `M3`-under-regeneration, in ~15 lines. mg-4f9b evaluated one candidate, rejected it correctly, and generalised | **RED** | §8 |
| 2 | **The per-dataset census is field-NAME coverage.** `h_bk_*` is compared at 1 poset of 54; the identity population has no poset with `6 < \|L\| ≤ 15`; `BK_CHEEGER_CAP 15 → 6` destroys the field on 36 of 47 rows and is a no-op where the gate looks | **RED** | §9 |
| 3 | **The route DECLARATION is a gate condition; the route WIRING is not.** mg-75f0's regression is re-armable in two lines with every gate condition green. The three-line fix was priced as if it were the expensive distinctness check | **RED** | §10 |
| 4 | **mg-bd53's probe part 1 reports a hardcoded dict as the route-axis measurement.** It cannot see a route restoration and will report `['delta','lambda_std']` lost forever. Not mg-4f9b's defect; it is why the brief's diff test is insufficient | **RED**, against the instrument | §1.2 |
| 5 | The route axis is genuinely restored, uniformly, from one declaration table, ANDed into `field_matches` where the enforcing probe can see it. `B1` exits 1 via `lambda_std=False` | **GREEN** | §2, §3 |
| 6 | Field axis lost nothing; mg-bd53's unmodified probe moves `+2 / −0` | **GREEN** | §1.1, §2 |
| 7 | The population claim is arithmetically exact and names its population; the census is a real gate condition | **GREEN** | §5 |
| 8 | The AMBER correction is to the claim; the Aldous/CLR justification is intact; `_antichain_row_ok` was not touched | **GREEN** | §6 |
| 9 | The `frozen_pair` class is disclosed as open, with numbers, in three places. Best disclosure in the arc | **GREEN** | §4 |
| 10 | The provenance ledger, measured mechanically by perturbing the store, agrees with mg-4f9b's hand-authored partition on every row | **GREEN** | §7 |
| 11 | The `4515cdb` data refresh is a record, not a reference, and mg-4f9b flagged it as the pattern it is | **GREEN** | §11 |
| 12 | `ref_rows` is keyed on `name`; 0 duplicates today, one duplicate away from under-counting the schema. Worth a comment | **note** | §5 |
| 13 | The tie-break mutation moved 0 of 47 rows — a genuine invariance, reported so nobody re-spends the effort | **note** | §11 |

---

## §13 — Suggested repairs, in the order they matter

1. **Land `I1` and `I6` in `measure()`** (§8). Fifteen lines, no new imports, closes both instances mg-4f9b
   records as open. Scope `I6` to the off-regime population and say why in the predicate, per
   `_antichain_row_ok`'s own precedent.
2. **Add the three-line route-wiring assertion** (§10). It is cheaper than either check mg-4f9b did wire,
   and it is the check that would have caught mg-75f0.
3. **Add one identity poset with `6 < |L| ≤ 15`** (§9), or give `h_bk` a theorem-referenced bound. Then
   correct the census's printed sentence to say *compared*, not *covered*.
4. **Replace `still_gated` in mg-bd53's probe part 1 with a derivation** (§1.2), and re-point its `B1`/`C1`
   rows per its own instruction.
5. **Consider `I4` as a measurement, not only a control** (§8.2). That the frozen-pair indicator is within
   2.4% of a single rank-difference observable is a statement about the corpus's mechanism claim, and it
   came out of building a control.

---

## §14 — Reproduction

```bash
# the invariants and the route declared-vs-wired table, no gate runs      ~40 s
/usr/bin/python3 scripts/onethird_mg56be_provenance_audit.py --part3-only

# everything: provenance perturbation + 11 gate runs incl. regeneration  ~10 min
/usr/bin/python3 scripts/onethird_mg56be_provenance_audit.py

# the two rows that carry §9 and §10, on their own                       ~3 min
/usr/bin/python3 scripts/onethird_mg56be_provenance_audit.py --only mg56be-A,mg56be-B+B1

# mg-bd53's probe, UNCHANGED, on both trees -- the §1.1 diff             ~8 min each
git worktree add --detach /tmp/wt-pre 91fa25f && cd /tmp/wt-pre
/usr/bin/python3 scripts/onethird_mgbd53_widening_audit_probe.py
```

Output: `data/onethird-mg56be-provenance-audit.json`. Interpreter matters — bare `python3` on this host has
no numpy. The probe pins BLAS to one thread for the same reason mg-bd53's does: the compared float fields
move in the last digit between threading regimes, six orders under the `1e-9` tolerance, but the
"regeneration moved nothing" reading is taken from printed output.

**mg-4f9b's own probe was not run.** It asked not to be the instrument that validates its own result, and
that request is the correct one for this stage of the arc.
