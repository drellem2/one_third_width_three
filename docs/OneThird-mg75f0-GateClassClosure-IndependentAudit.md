# INDEPENDENT AUDIT of the mg-75f0 gate widening (mg-bd53)

**Target.** `docs/OneThird-mg75f0-GateClassClosure.md` and the five commits behind it (`e8e70c1`,
`f589307`, `b3cfb25`, `9fa4aaa`, `4ea1d45`), which widen the mg-2c34 CI gate's identity check from four
hand-listed fields to the whole committed mg-8b64 reference row and add CONTROL E and CONTROL F.

**Why this audit was pre-filed.** This is the third generation of one defect. mg-09ea found two controls
passing while blind; mg-60d3 repaired those two; mg-5ad1 measured that the repair closed two instances
and not the class, exhibiting a one-character selector flip that sailed through. mg-75f0 is the class
fix. The only question worth asking of a class fix is whether it catches a mutation **it was not built
from**, chosen by somebody who did not build it.

**Method, deliberately not mg-75f0's.** Six mutations of my own — none of them in mg-75f0's `M3…M9`,
none of them in mg-7db4's battery — plus an independent reproduction of mg-5ad1's M3 and M4. Each is one
source-level edit in an isolated tree with an anchor-count assertion, the gate run there as a
subprocess. Fourteen full `--no-sweep` gate runs.
`scripts/onethird_mgbd53_widening_audit_probe.py`, `data/onethird-mgbd53-widening-audit.json`.

---

## §0 — Verdict: **RED**

The widening is real and it generalises: it catches mutations I chose that mg-75f0 never saw, in fields
mg-75f0's own acceptance run never moved. That half of the ticket is met and §1.1 is the evidence.

It is RED because of what came with it.

| | |
|---|---|
| **Does the widened gate catch a mutation it was not built from?** | **YES**, twice, chosen by me: `transport_gap` (A1) and `max_bias` (A2) — fields no row of mg-75f0's `M3…M9` moves. Exit 1 at 7/7 identity posets each; the pre-widening gate was blind to both. §1.1 |
| **Did the widening COST any coverage?** | **YES, and this is the finding.** A one-character flip in mg-4a86's own `lambda_std` — `np.max(w)` → `np.min(w)` — makes the **pre-widening gate exit 1** and the **widened gate exit 0**. The widened gate prints `lam_std=-0.048288466 (ref 0.7850482917286934)` and `match=True/True/True` **on the same line** and passes. §1.2 |
| **How many of the four pre-widening comparisons kept an independent second route?** | **One of four.** `bk_lambda2` — kept deliberately, with a comment saying why. `lambda_std` and `delta` had the identical two-route structure and lost it silently. `num_LE` never had one. §1.2 |
| **Is the class closed at the quantity mg-5ad1 named?** | **NO.** Dropping one line from the gate's own `frozen_pair_indicator` moves `frozen_pair_overlap_with_U` — the quantity **ledger claim 8** rests on — from `0.8072/0.8094/0.8096` to `0.9036/0.9076/0.9048`. The gate prints the moved values and exits **0**, on **both** gate columns. §1.3 |
| **Is `22 of 23` right?** | **Right for the seven identity rows, which have 23 fields — counted from the JSON, not read off the doc.** The dataset also holds 54 rows with **25** fields; `h_bk_exhaustive` and `h_bk_argmin_is_pair_cut` are compared at **zero** posets. The census is per-ROW, so "0 silently uncompared" is true per row and false per dataset. §1.4, §2 |
| **The one exclusion's stated reason — is it TRUE?** | **Yes.** `analyze_poset(P, name)` copies the same string the row was fetched by, so comparing `name` cannot fail. Verified in source, both sides. §2 |
| **Did the census stay coupled to the gate?** | **YES, and it got tighter, not looser.** Part B imports the gate and calls `identity_field_comparisons` / `_identity_row_ok`. No hand-maintained list, no hardcoded count anywhere in the probe. This was the likeliest way the fix could rot and it did not. §3 |
| **The AMBER (CONTROL B's Aldous/CLR justification)** | **Correct, and it does not under-claim** — confirmed independently, including the representation-theoretic reason `dim U = (n−1)²+1` is exact on `S_n`. One wording defect: ledger row 7 and §5 say *"docstring only, no behaviour change"* while the same commit added a third conjunct to `_antichain_row_ok`. §4 |
| **Duplication with mg-7db4** | **Neither doubled nor dropped.** The closure demo is wired exactly once; the probe is wired twice **on purpose**, in two different enforcement layers. Watchlist check green on this tree: 16 paths, 10 modules, 1 dataset, 5/5 self-test drifts caught. §5 |
| **M3 / M4 on report?** | **No — reproduced.** Both reproduce exactly, including M4's `dim U` figures `49/49/49/21/25` and the three controls that fire. §6 |

**The one-sentence verdict.** mg-75f0 widened the identity check along the **field** axis and, in the same
edit, narrowed it along the **route** axis without saying so; the class is not closed, and the gate is now
blind to a mutation it used to catch.

---

## §1 — The only question that matters

**The measured matrix**, fourteen full `--no-sweep` runs, pre-widening column pinned at `af7fc2df`:

| mutation | mine? | pre-widening | widened | verdict on the widened gate |
|---|---|---|---|---|
| — unmutated | — | exit **0** | exit **0** | no false positive |
| **A1** `standard_block_and_lambda` argmax→argmin | **mine** | exit **0** | exit **1**, 7/7 | CAUGHT |
| **A2** `bk_frozen_pair` max-bias selector max→min | **mine** | exit **0** | exit **1**, 7/7 | CAUGHT |
| **B1** mg-4a86's `lambda_std` `np.max`→`np.min` | **mine** | exit **1**, 5/5 | exit **0** | **EXERCISED AND ABSORBED** |
| **C1** `bk_cheeger_exhaustive` normalisation min→max | **mine** | exit **0** | exit **0** | never exercised |
| **C2** gate's `frozen_pair_indicator` loses centring | **mine** | exit **0** | exit **0** | **EXERCISED AND ABSORBED** |
| **M3** mg-5ad1's frozen-pair selector | reproduced | exit **0** | exit **1**, 7/7 | CAUGHT |
| **M4** mg-5ad1's rank filter | reproduced | exit **0** | exit **1** | CAUGHT |

*(B1's left column is 5/5 rather than 7/7 because the pre-widening gate's identity population is the five
named posets; `#52` and `#88` join only with CONTROL F.)*

### 1.1 The positives: it does catch mutations it was not built from

Both were written down before the widened gate was run against them, and neither appears in mg-75f0's
`M3…M9` or in mg-7db4's battery.

| | mutation | one line | moves | pre-widening | widened |
|---|---|---|---|---|---|
| **A1** | `standard_block_and_lambda`'s eigenvalue selector | `np.argmax(w)` → `np.argmin(w)` (mgb0a6) | `lambda_std`, `transport_gap` | exit **0** | exit **1**, 7/7 |
| **A2** | `bk_frozen_pair`'s **max-bias** selector | `max(pairs, …)` → `min(pairs, …)` (mg-8b64) | `max_bias` | exit **0** | exit **1**, 7/7 |

Both are chosen to be hostile in a specific way.

- **`transport_gap` and `max_bias` are moved by none of mg-75f0's seven rows.** M3/M8 move the `frozen_*`
  block and `ratio_of_sums`; M5 moves the `min_phi_*` block; M6 `phi_t_min_prefix`; M7 `phi_t_cheeger`;
  M9 `width`. So A1 and A2 are field coverage the acceptance run did not measure, and the widening
  reaches it.
- **A2 is the third selector in the function M3 and M5 already mutate.** If the widening had covered two
  lines of `bk_frozen_pair` rather than the function, this is where it would show. It does not.
- A1's pre-widening run is **byte-identical** to the unmutated pre-widening run — the old gate never
  reached the code at all. A2's likewise.

That is the honest positive answer to the ticket's first question, and it is not a small one.

### 1.2 The regression: the widened gate is blind to a mutation the pre-widening gate caught

**B1 — `onethird_mg4a86_standard_dominance_target_audit.py:175`, one character:**

```python
-    return float(np.max(w))
+    return float(np.min(w))
```

| gate | exit | what it printed at `enum-n7-#3` |
|---|---|---|
| **pre-widening** (`af7fc2df`) | **1**, at 5/5 posets | `lam_std=-0.048288466 (ref 0.7850482917286934) … match=True/False/True` |
| **widened** (this tree) | **0** | `lam_std=-0.048288466 (ref 0.7850482917286934) … match=True/True/True` |

The widened gate computes the wrong number, **prints it beside the reference it disagrees with**, calls
it a match, and passes. This is mg-5ad1's class in its strict sense — *exercised, printed, absorbed* —
and it is a **regression**, not a pre-existing gap: the gate this ticket set out to strengthen used to
catch it.

**The mechanism, and it is one line of the diff.** Before mg-75f0:

```python
rec["match_lambda_std"] = abs(rec["lambda_std"] - ref["lambda_std"]) < 1e-9
```

where `rec["lambda_std"] = float(lambda_std(P))` is mg-4a86's own implementation. After:

```python
# the four legacy keys, now ALIASES of four of the 22 comparisons
for key, field in IDENTITY_LEGACY_FIELDS:
    rec[key] = matches.get(field, False)
```

`matches["lambda_std"]` compares mg-8b64's `analyze_poset` → `transport_summary` → **mgb0a6's**
`standard_block_and_lambda`. That is a different implementation in a different module. mg-4a86's
`lambda_std` is still called, still printed, still written into `report["identity_check"]` and into
every `measured` row of the deliverable's own dataset — and compared against nothing.

**mg-75f0 saw this hazard and fixed it for exactly one of the four quantities.** From the gate, in the
same block:

> *"Kept as a **SECOND, independent route** to `bk_lambda2`: this one goes through mg-4a86's
> `bk_walk_matrix`, the row-wide comparison below goes through mg-8b64's, so a mutation in EITHER walk
> matrix is fatal."*

`lambda_std` has the identical structure. `delta` has a weaker version of it (shared `before_prob_dp`,
separate aggregation on each side). Neither got the treatment, and nothing in the commit message, the
deliverable, or the CI comment records that any comparison was removed.

**Part 1 of the audit probe measures this structurally**, in milliseconds, so it does not depend on
anyone thinking of B1:

| quantity | independent 2nd route existed | still gated after mg-75f0 |
|---|---|---|
| `num_LE` | no (both `Poset.linext_count`) | — |
| `lambda_std` | **yes** (mg-4a86 vs mgb0a6) | **NO** |
| `delta` | **yes** (separate aggregations) | **NO** |
| `bk_lambda2` | yes | **yes**, explicitly |

**What this does to the claims.**

- §0 of the deliverable — *"the class is closed for the mg-8b64 identity surface"* — is **false as
  worded**. `lambda_std` is on that surface.
- Ledger **claim 28**'s scope sentence (*"a mutation that moves no committed reference field … is
  covered only as far as CONTROL A/B/C/D/F reach"*) is technically satisfied by B1 only if
  *"committed reference field"* is read as *"the field as recomputed by `analyze_poset`"*. Under that
  reading the sentence silently absorbs a regression instead of describing a limit. It needs to say
  which route.
- §4.1 / §4.2 / §4.3 repeatedly offer the printed `num_LE=True lambda_std=True delta=True
  lambda2_BK=True` as evidence that *"the four fields it used to compare were not the ones that moved"*.
  Three of those four flags no longer measure the routes that sentence is about.

### 1.3 The class is still open, at the quantity mg-5ad1 named

**C2 — the gate's own `frozen_pair_indicator` loses its centring**, one line:

```python
-    f -= f.mean()
+    f -= 0.0 * f.mean()
```

| | `#3` | `#20` | `#600` | `#945` | `#809` |
|---|---|---|---|---|---|
| `frozen_pair_overlap_with_U` unmutated | `0.8072` | `0.8094` | `0.8096` | `1.0000` | `1.0000` |
| **C2** | `0.9036` | `0.9076` | `0.9048` | `1.0000` | `1.0000` |
| `frozen_pairmode_capture` unmutated | `0.3920` | `0.4303` | `0.6114` | `0.3456` | `0.4656` |
| **C2** | `0.1960` | `0.2086` | `0.3057` | `0.0823` | `0.1304` |

Exit **0** on the widened gate and **0** on the pre-widening gate, with the moved values printed in the
measurement table both times. `frozen_pair_overlap_with_U` is the quantity **ledger claim 8** rests on,
and it is the quantity mg-5ad1 gave as the *reason M3 mattered* — *"moves `frozen_pair_overlap_with_U`
from `0.807/0.809/0.810` to exactly `1.0000`"*. The widening secured **which pair is chosen**. It did not
secure **the number computed from it**.

**The residual as §7.2 states it does not cover this case.** §7.2 reads:

> *"A quantity the corpus computes but never COMMITS has no reference to be compared against, and this
> mechanism cannot manufacture one."*

`frozen_pair_overlap_with_U` **is** committed — in `data/onethird-mg2c34-n7-overlap.json`, written by
this same gate, and quoted in §5/§6 of the deliverable and in the ledger. What is missing is not a
reference; it is that **the gate never reads its own committed output back**. The honest successor
residual is *"quantities the gate commits and never reads back"*, which is strictly larger than what
§7.2 names and which points at a repair (`--no-sweep` compares the measured rows against the committed
ones) that §7.2's wording makes look impossible.

### 1.4 The census is per-ROW, not per-DATASET

**C1 — `bk_cheeger_exhaustive`'s volume normalisation**, M7's shape in a different function:

```python
-        mn = min(k, m - k)
+        mn = max(k, m - k)
```

Exit **0** on both columns, and the stdout is **byte-identical** to the unmutated run on both — the gate
never reaches the mutated line. It moves `h_bk_exhaustive` and `h_bk_argmin_is_pair_cut`, which appear in
**54 of the 1091** committed mg-8b64 rows and in **none** of the seven the gate compares.

`identity_field_comparisons` iterates *one committed row*, and part B1's census reads
`ref_rows[NAMED[0]]` — a 23-field row. So both the gate and the probe report **0 silently uncompared**
while two fields of the same committed dataset are compared nowhere. This is the weaker sibling of the
class (never exercised rather than absorbed), but it is the exact shape the ticket said to look for: an
exclusion nobody declared, sitting where the census structurally cannot see it.

---

## §2 — The field count, counted rather than read

Enumerated from `data/onethird-mg8b64-L1b-bk-transport-transfer.json` directly:

| | |
|---|---|
| rows in the committed dataset | **1091** |
| rows with 23 fields | 1037 |
| rows with 25 fields | 54 (they carry `h_bk_exhaustive`, `h_bk_argmin_is_pair_cut`) |
| the seven identity rows (`#3 #20 #600 #945 #809 #52 #88`) | **23 fields each** |
| compared by the gate | **22** |
| excluded | **1** (`name`) |
| excluded without a stated reason | **0** |

So `22 of 23` is right for the population the gate uses, and the gate docstring's *"22 of 22 fields, one
declared exclusion"* and `_identity_row_ok`'s *"gates on all 22"* are the same count phrased two ways.
(mg-5ad1's original *"4 of the row's 22 fields"* is off by one against the row, which has 23; harmless,
and inherited rather than introduced here.)

**The one exclusion's reason, checked rather than accepted.** It reads: *"the lookup key itself. The row
is FETCHED BY this value (`ref_rows[name]`), so comparing it is a tautology that cannot fail."* Verified
on both sides: the gate does `ref = ref_rows.get(name)` and `rec_row = mg8b64_analyze_poset(P, name)`,
and `analyze_poset` stores that same parameter as `row["name"]`. The two strings are the same object's
value by construction. **The reason is TRUE.** It is also the only field for which it is true — every
other field of the row is recomputed from `P`.

**Modulo §1.4**: the census's *scope* is one row, so "0 uncompared" is a statement about the 23-field
schema and not about the dataset.

---

## §3 — Did the census stay coupled to the gate? **Yes, more tightly**

This was the ticket's named "likeliest way a correct-looking fix rots", and it did not happen.

mg-5ad1's part B parsed the field list out of the gate source. mg-75f0 replaced parsing with **importing
the gate and calling its own comparison function**:

```python
import onethird_mg2c34_n7_overlap_test as gate
excluded = dict(gate.IDENTITY_EXCLUDED_REF_FIELDS)
compared = sorted(gate.identity_field_comparisons(ref, ref)[0])
...
fires = not gate._identity_row_ok({"field_matches": matches})
```

Checked specifically, since a retreat here would have been the finding:

- **No hand-maintained field list** anywhere in `part_B`. The census is `identity_field_comparisons(ref,
  ref)`; the exclusions are read from the gate's own dict.
- **No hardcoded field count.** `grep`ed for one; there is none. The printed `22/23` is `len(compared)`
  and `len(present)`.
- **B2 measures firing** rather than inferring it: each field is perturbed and the gate's own
  `_identity_row_ok` must go `False`. 22/22 on this tree.
- **B3 is the anti-drift canary** — a field name the gate has never seen must be picked up automatically
  **and fail**, because the row builder does not produce it. It is, and it does.
- **Stale exclusions fail too**: an entry naming a field the row no longer has is a B1 failure, as is an
  exclusion whose reason is under 20 characters.

This is strictly stronger than parsing — there is no second representation of the census left to
disagree with the first — and it is the correct response to mg-7db4's measured N2 defect. **Green, and
the ticket's suspicion is answered in mg-75f0's favour.**

A caveat that costs nothing to state: calling the gate makes the census immune to *source-layout* drift
but not to *population* drift, which is §1.4.

---

## §4 — The AMBER: CONTROL B's Aldous/CLR justification

**The corrected wording is right.** Aldous' spectral-gap conjecture, as proved by
Caputo–Liggett–Richthammer, gives the gap **eigenvalue**: `gap(interchange on the path) =
gap(one-particle)`. `c_min = 1` asserts that the whole gap **eigenspace** lies in the one-particle
sector, which additionally requires that no other `S_n`-irrep component attains that eigenvalue. CLR
does not supply that. The docstring now says exactly this and no more.

**Confirmed independently, and it strengthens rather than weakens the control.** `U = span{σ ↦ 1[σ(a) =
x]}` is the span of the matrix coefficients of the permutation representation `C^n` of `S_n`, and
`C^n = trivial ⊕ standard`. So

```
dim U = 1² + (n−1)² = (n−1)² + 1
```

**exactly** on `S_n`, which is simultaneously (i) why CONTROL E's structural bound `dim U ≤ (n−1)²+1`
holds on every poset — restriction to `L(P) ⊆ S_n` can only lower the rank — and (ii) why the
"one-particle sector" in the corrected docstring is precisely the standard-isotypic component.
CONTROL E's stated relation count `2n−2` is also right: the kernel of the map from `R^{n×n}` onto `U` is
spanned by the `n−1` row-sum differences and the `n−1` column-sum differences, and
`n² − (2n−2) = (n−1)²+1`.

**It does not under-claim.** The assertion is unchanged and unweakened: `|c_max − 1| < 1e-8` **and**
`|c_min − 1| < 1e-8`, same tolerance, and the docstring adds the standing instruction that a future
failure on a larger antichain narrows the **population**, not the **assertion**. mg-5ad1's part A
measurements (`dim_E = n−1`, `1 − c_min ≤ 2.7e-15`, nearest excluded eigenvalue `3.0e7–1.1e8 × EIG_TOL`
away) reproduce on this tree, 4-for-4 at `n = 4,5,6,7`.

**One wording defect.** §5 and ledger row 7 say *"docstring only, no behaviour change"* about CONTROL B.
The same commit added a **third conjunct** to `_antichain_row_ok`:

```python
return (abs(row["c_max"] - 1.0) < 1e-8 and abs(row["c_min"] - 1.0) < 1e-8
        and row["dim_U"] == row["dim_U_known"])
```

That is a strengthening and is documented elsewhere (§3.1, the predicate's own docstring, and the new
`dim_U_known` key), so nothing is at risk. But the ledger row is the artifact a later reader consults to
decide whether `_antichain_row_ok` changed, and it says it did not. **AMBER, wording only** — the fix is
to scope the phrase to the justification.

---

## §5 — Duplication with mg-7db4: neither doubled nor dropped

The dangerous outcome here is **zero** — two tickets each assuming the other wired it. Checked in the
merged state of both:

| instrument | `script-controls.yml` | `refinery_gate.sh` (blocking) | `gate-mutation-demo.yml` |
|---|---|---|---|
| widened mg-2c34 gate | ✔ every commit | — | — |
| mg-7db4 watchlist check | ✔ | ✔ | ✔ |
| **mg-5ad1 blindness probe** | ✔ | ✔ | — |
| mg-60d3 demo | — | ✔ | ✔ |
| mg-7db4 battery | — | — | ✔ |
| **mg-75f0 closure demo** | — | — | ✔ **exactly once** |

The probe appearing twice is **deliberate and correct**: `script-controls.yml` informs (the refinery does
not read GitHub checks) and `refinery_gate.sh` blocks. They are different enforcement layers, not a
duplicate. The closure demo is wired once, and the four coupled edits mg-7db4's mechanism requires were
all made: the step, both `paths:` lists, `WATCHED` in `refinery_gate.sh`, and `ROOTS` in the watchlist
check. Verified by running it on this tree:

```
watchlist consistent: 16 paths; import closure 10 modules; datasets read 1
  shell WATCHED loses an entry the workflow still has        CAUGHT
  workflow loses its pull_request paths filter               CAUGHT
  gated instrument imports a module nobody watched           CAUGHT
  gated instrument reads a dataset nobody watched            CAUGHT
  watchlist grows a path unrelated to the gate               CAUGHT
```

**But mg-75f0 left a false description of its own change in that same workflow file.**
`.github/workflows/script-controls.yml:145–149`, still as mg-7db4 wrote it in `df7db8b`:

> *"Part B **parses** the gate's identity conjunction **OUT OF THE GATE SOURCE**, so the census cannot
> drift away from the thing it censuses; Part C compares the corpus's Theorem-E frozen-pair selector
> against the committed reference, which is the quantity ledger claim 8 rests on **and which the gate
> does not compare**."*

Both clauses were made false by mg-75f0, and both were made false **on purpose**: §3.2 of its own
deliverable is the argument for replacing parsing with calling, and *"the gate now compares
`frozen_pair`"* is its headline. mg-75f0 **edited this file** (`b3cfb25`) and went through mg-7db4's
*document* correcting the CONTROL E catch matrix — and left the CI file advertising the pre-mg-75f0
behaviour of the step directly below the comment. This is the arc's own named pattern: *the over-wide
statement lands where nobody was watching, in a file's own description of its coverage.*

---

## §6 — M3 and M4, reproduced rather than taken on report

Same route as the rest of this audit (my harness, not mg-75f0's), same pinned `af7fc2df` left column.

| | pre-widening | widened | agrees with §4.1? |
|---|---|---|---|
| **M3** frozen-pair selector | exit **0**, stdout moved (exercised and absorbed) | exit **1** at **7 of 7** identity posets | ✔ same posets, same mismatched-field lists |
| **M4** rank filter | exit **0**, stdout moved | exit **1** via CONTROL B **and** CONTROL E **and** CONTROL F | ✔ |

M4's figures reproduce exactly: `dim U = 49` against the bound `(n−1)²+1 = 37` at `#3`/`#20`/`#600`, and
`dim U = 21 = |L|` at `#945`, `25 = |L|` at `#809` with `null = 1.0000` — the properness clause, firing
on the vacuity case. `mismatched: none` at all seven posets, confirming §4.1's point that **the widening
is not what catches M4**.

---

## §7 — Other claims checked

- **"Every compared float field reproduces to `0.00e+00` at 7/7 against a `1e-9` tolerance"** (§2, ledger
  row 8) — **true on the host configuration measured, not a property of the computation.** With
  single-threaded BLAS (`OMP_NUM_THREADS=1`) on this same tree, `max |diff|` is `8.88e-16` at `#52` and
  `9.99e-16` at `#88`. Six orders of margin either way, so **nothing is at risk** — but §2 offers the
  `0.00e+00` as evidence that *"the tolerance exists so a different BLAS cannot fail the gate spuriously,
  not because anything needs it"*, and the second half of that sentence is what the measurement
  contradicts. The tolerance is load-bearing at the `1e-15` scale; it is simply enormously generous.
- **CONTROL E's citation of `sector_leakage`'s docstring** — verified present and verbatim: *"rank =
  (n-1)^2 + 1 on S_n, not n^2"*. The claim that the bound is the corpus's own and not reverse-engineered
  from M4 stands.
- **CONTROL F's non-vacuity** — `dim_E = 2` at `#52` and `#88` reproduces, and `_two_sided_row_ok`
  asserts `dim_eigenspace > 1`, so the control cannot silently become the vacuous one it replaces.
  Part D's `CONTROL F / coverage gone` row rejects `dim_eigenspace = 1`. Sound.
- **Part D** — 10 probes, 10 agree on this tree, and each rejection row is a real mutation's signature.
- **mg-60d3's harness fix (§6.1)** — the `_rebind` signature-crossing diagnosis is correct on
  inspection: `bk_walk_matrix` returns `W` in mg-4a86 and `(W, index)` in mg-8b64, and the M1
  replacement was a copy of the former. Not re-run here (11 min, and mg-5ad1 already confirmed the 2×3
  matrix by a disjoint route); flagged as **inspected, not re-measured**.
- **The battery docstring's run count** — *"~5 min — ten probe runs, mg-75f0 added two"*, revised from
  *"~6 min — eight probe runs"*. Two runs were added and the stated cost went **down**. Probably a
  re-measurement on a quieter host, but it is stated as though it followed from the change. Cosmetic.

---

## §8 — Findings ledger

| # | finding | severity | site |
|---|---|---|---|
| **1** | **The widening removed a comparison.** `lambda_std` (and, more weakly, `delta`) had an independent second route into `_identity_row_ok` and lost it; only `bk_lambda2` kept one, deliberately. A one-character flip in mg-4a86's `lambda_std` makes the **pre-widening gate exit 1 and the widened gate exit 0**, with both values printed on the same line and `match=True/True/True` beside them. Strict class, and a regression | **RED** | §1.2 |
| **2** | **The class is still open at ledger claim 8's quantity.** One line out of the gate's own `frozen_pair_indicator` moves `frozen_pair_overlap_with_U` `0.807/0.809/0.810 → 0.904/0.908/0.905`, printed, exit 0 on both columns. §7.2's residual (*"a quantity the corpus … never COMMITS"*) does not describe it: the quantity **is** committed, in the gate's own output file, which the gate never reads back | **RED** | §1.3 |
| **3** | **The widening does generalise.** Two mutations I chose, in fields (`transport_gap`, `max_bias`) that no row of mg-75f0's acceptance run moves, are caught at 7/7 and were invisible before. A2 is the third selector in the function M3 and M5 mutate, so the widening covers the function and not two lines of it | **GREEN, and it is the ticket's first question answered** | §1.1 |
| **4** | **The census is per-ROW.** `h_bk_exhaustive` and `h_bk_argmin_is_pair_cut` are committed on 54 rows and compared at zero posets; both the gate and part B1 report "0 silently uncompared" because they census a 23-field row. Demonstrated with a mutation that both gate columns pass byte-identically | **AMBER** | §1.4, §2 |
| **5** | **`.github/workflows/script-controls.yml:145–149` describes the probe as it was before mg-75f0** — *"Part B **parses** … OUT OF THE GATE SOURCE"* and *"the quantity … **which the gate does not compare**"*. Both were made false deliberately by this ticket, which edited this file and corrected mg-7db4's *document* but not mg-7db4's *CI comment* | **AMBER** | §5 |
| **6** | **Ledger row 7 and §5 say the CONTROL B change was *"docstring only, no behaviour change"*** while the same commit added a third conjunct (`dim_U == dim_U_known`) to `_antichain_row_ok`. A strengthening, documented elsewhere, so nothing is at risk — but the ledger row is what a later reader consults | **AMBER, wording** | §4 |
| **7** | **§0's *"the class is closed for the mg-8b64 identity surface"* is false as worded**, and claim 28's scope sentence absorbs finding 1 only under a reading (*"reference field" = "field as recomputed by `analyze_poset`"*) that the sentence does not state | **AMBER, and it is the sentence finding 1 hides behind** | §1.2 |
| **8** | **The census stayed coupled to the gate and got tighter** — imports the gate, calls its comparison function, no hand-maintained list and no hardcoded count anywhere. The ticket's named rot mode did not occur | **GREEN** | §3 |
| **9** | **The AMBER repair is correct and does not under-claim.** Confirmed independently, including `dim U = 1 + (n−1)²` exactly on `S_n` from `C^n = trivial ⊕ standard`, which is the same fact CONTROL E asserts as a bound | **GREEN** | §4 |
| **10** | **No duplication and no gap with mg-7db4.** Closure demo wired exactly once; probe wired twice across two enforcement layers by design; watchlist green, 5/5 drifts caught | **GREEN** | §5 |
| **11** | **M3 and M4 reproduce exactly**, including M4's `dim U = 49/49/49/21/25` and `mismatched: none` at 7/7 | **CONFIRMED** | §6 |
| **12** | *"Every compared float field reproduces to `0.00e+00`"* is host-configuration-dependent: `8.88e-16` / `9.99e-16` under single-threaded BLAS. No risk at a `1e-9` tolerance; the claim that nothing needs the tolerance is what is wrong | **note** | §7 |

---

## §9 — Suggested repairs, in the order they matter

1. **Restore the second routes.** `match_lambda_std` and `match_delta` should be ANDed with the gate's own
   recomputation, exactly as `match_bk_lambda2` already is. Three lines. Then B1 goes red again.
2. **Make the gate read its own committed output back** under `--no-sweep`: compare `report["measured"]`
   against the committed `data/onethird-mg2c34-n7-overlap.json` rows the same way the identity check
   compares the mg-8b64 rows. That is the repair §7.2's wording makes look impossible, and it closes
   finding 2 and the whole *"quantities the gate commits and never reads back"* family with it.
3. **Widen the census's population, or declare it.** Either add one small-`|L|` poset to the identity
   population so the 25-field schema is covered, or record `h_bk_exhaustive` /
   `h_bk_argmin_is_pair_cut` as declared exclusions with a reason — the point of
   `IDENTITY_EXCLUDED_REF_FIELDS` is that an exclusion nobody wrote down is the defect.
4. **Fix `script-controls.yml:145–149`**, ledger row 7's *"no behaviour change"*, and §0's *"closed for
   the mg-8b64 identity surface"*.

## §10 — Reproduction

```bash
# the structural half -- which of the four pre-widening comparisons survived   ~2 s
/usr/bin/python3 scripts/onethird_mgbd53_widening_audit_probe.py --part1-only

# the full matrix: 14 gate runs, 6 mutations of mine + M3/M4 reproduced      ~8 min
/usr/bin/python3 scripts/onethird_mgbd53_widening_audit_probe.py

# the two rows that carry the verdict, on their own                          ~2 min
/usr/bin/python3 scripts/onethird_mgbd53_widening_audit_probe.py --only B1,C2
```

Output: `data/onethird-mgbd53-widening-audit.json`. Interpreter matters: bare `python3` on this host has
no numpy. The probe pins BLAS to one thread, deliberately — the stdout digest that separates *"absorbed"*
from *"never exercised"* is a byte comparison, and unpinned threads move the last digits run to run.

**Out of scope, not re-litigated, per the ticket:** mg-60d3's repair and ledger claim 27 as worded; the
`dim_E = 1` vacuity observation, which is correctly reported as a coverage observation and is now
addressed by CONTROL F.
