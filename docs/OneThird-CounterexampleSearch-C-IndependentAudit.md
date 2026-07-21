# Independent audit — mg-0eac §9 (onethird δ-search), merged at `a90f0f7`

*Auditor: polecat `aud0eac`, fresh context, **not** the author of the audited work. Date 2026-07-21.*
*Audited: commit `a90f0f7` (and predecessor `172546c`) against `origin/main`.*
*Audited artifacts: [`docs/OneThird-CounterexampleSearch-C.md`](OneThird-CounterexampleSearch-C.md), `scripts/onethird_mg0eac_*.py`, `data/onethird-mg0eac-*.json`.*

---

## 0. Verdict

> ## **PASS-WITH-FINDINGS**

**Every headline quantitative claim reproduced exactly**, most of them on a from-scratch δ
engine that shares no code with the merged work. No finding changes a numeric result. The two
substantive findings are a **commit-subject overstatement relative to the doc's own text** (F1)
and a **control-coverage gap that is structurally real but empirically closed** (F2).

This deliverable was audited as an **empirical** one, per its originating ticket: δ-engine
correctness, search completeness, and scope honesty — not a proof ledger.

**General note on the audited document: its scope discipline is unusually good.** It labels every
row `exhaustive` vs `bounded`, states its compute walls, reports two search misses it could have
quietly dropped (§4.5 `n=15`, §9.3c `n=10`), and says of its own §9 "*It narrows the gap; it does
not close it.*" Findings F1/F5 below are precisely where surrounding text drifted *looser* than
that body text — not where the body text overclaimed.

### The precise proven statement

The commit subject and §0 one-liner are both broader than what was established. Stated honestly:

> Over primitive posets of **width exactly 3** with **`n ≤ 11`**, the minimum `δ` is
> **`6/17 ≈ 0.352941`**, attained at `n = 10`. This is a **proven minimum** (exhaustive
> enumeration, prune independently re-certified by this audit). It lies **below** Olson–Sagan's
> `14/39 ≈ 0.358974` — which they established only for `n ≤ 9`, so this **extends** rather than
> contradicts them — and it remains **`4.10·10⁻³` ABOVE `β`**.
>
> For **`12 ≤ n ≤ 16`** at width ≥ 3, nothing below `β` was found by a **bounded beam that is
> demonstrably incomplete** (it misses the true optimum at `n = 10` in its own validation).
> **Width ≥ 4 received no coverage at any `n ≥ 10`.** Nothing below `1/3` was found anywhere.

"Nothing below β" is therefore **proven** only on width exactly 3 at `n ≤ 11`, and is a
**bounded-search observation** at `12 ≤ n ≤ 16`.

---

## 1. δ-engine correctness — re-run, not read off the table

I did **not** read the controls off the doc's tables. I wrote an independent engine
(`scripts/audit_mg0eac_independent_delta.py`) that enumerates linear extensions directly by
recursion over currently-minimal elements, and computes `δ` as
`max` over incomparable pairs of `min(Pr[x<y], Pr[y<x])` in exact `Fraction` arithmetic. It
shares **no code** with the merged scripts.

### 1.1 Mandated controls — all reproduce independently

| control | `n` | `e(P)` | `δ` (my engine) | expected | primitive | result |
|:--|--:|--:|:--|:--|:--|:--|
| `T = ({a,b,c}, a<b)` | 3 | 3 | `1/3` | `1/3` | **yes** | **PASS** |
| antichain `A₃` | 3 | 6 | `1/2` | `1/2` | yes | **PASS** |
| antichain `A₄` | 4 | 24 | `1/2` | `1/2` | yes | **PASS** |
| antichain `A₅` | 5 | 120 | `1/2` | `1/2` | yes | **PASS** |
| ordinal sum `T ⊕ T` | 6 | 9 | `1/3` | `1/3`, reduces | **no** | **PASS** |

The doc's **§0 correction is correct**: `T` is primitive (incomparability graph = path `a—c—b`,
connected) *and* attains `δ = 1/3`. Independently confirmed. "Primitive ⟹ `δ ≥ β`" is indeed
false as stated, and scoping every threshold claim to `n ≥ 4` is the right repair.

### 1.2 External control — all seven of Peczarski's published pairs

I rebuilt the ladder `L_{n;S}` **from the doc's prose spec** (§3.3: rails `j ⋖ j+2`, rungs
`j ⋖ j+3` except broken, transitive closure), not from their code — so this tests the doc's
construction and my engine simultaneously:

| poset | `e(P)` | `δ` (my engine) | published | result |
|:--|--:|:--|:--|:--|
| `L₆;₁` | 14 | `5/14` | `5/14` | **PASS** |
| `L₉;₁,₂,₃,₄` | 85 | `6/17` | `6/17` | **PASS** |
| `L₁₀;₁,₅` | 106 | `37/106` | `37/106` | **PASS** |
| `L₁₁;₁,₆` | 171 | `20/57` | `20/57` | **PASS** |
| `L₂₀;₁,₅,₈,₁₁,₁₅` | 17 366 | `6059/17366` | `6059/17366` | **PASS** |
| `L₂₁;₁,₅,₈,₉,₁₂,₁₆` | 30 970 | `5402/15485` | `5402/15485` | **PASS** |
| `L₂₅;₁,₅,₈,₉,₁₂,₁₃,₁₆,₂₀` | 256 308 | **`7451/21359`** | `7451/21359` | **PASS** |

Seven independent `(δ, e)` pairs including exact denominators, reproduced from the doc's written
construction on an unrelated engine. **The ladder reconstruction is sound and the doc specifies it
completely enough to rebuild.**

### 1.3 Can a control FAIL? — yes, demonstrated

Per the remit: *"If a control cannot be made to FAIL on a deliberately broken input, it is not a
control."* I corrupted the engines and re-ran the gate:

| deliberate break | gate response |
|:--|:--|
| `Q_primary` (M1) returns `δ + 10⁻⁶` | **CAUGHT** — `AssertionError: T: Q M1=1000003/3000000 M2=1/3` |
| `Q_brute` (M4) returns `δ + 1/7919` | **CAUGHT** — `AssertionError: T: Q M1=1/3 M4=7922/23757` |
| force `δ = 1/4` inside the width-≤3 sweep | **CAUGHT** — `SubBetaHalt` raised, search halted, not silent |
| `fast_Q` returns `δ + 10⁻⁶` | **NOT CAUGHT** — see **Finding F2** |

The control gate is a **real** control (it fails on broken input) and the `δ ≤ 1/3` halt genuinely
fires rather than passing a candidate through silently. The fourth row is Finding F2.

---

## 2. Search completeness — hunting for false negatives

A negative result is only as good as the enumeration behind it. I re-certified each layer by a
route that shares as little as possible with the merged code.

| layer | how I checked it | result |
|:--|:--|:--|
| canonical augmentation complete? | unpruned enumeration vs **OEIS A000112**, `n ≤ 8` | 1, 2, 5, 16, 63, 318, 2045, **16999** — exact match |
| width oracle correct? | `width_value_bitmask` vs **brute-force largest antichain**, all 19 448 posets `n ≤ 8` | **0 disagreements** |
| does the width prune drop posets? | width-≤3 counts from *unpruned enumeration + my own width* vs the pruned enumerator | `15, 55, 245, 1285, **7790**` — exact match at every `n ≤ 8` |
| primitivity filter over-excludes? | `is_primitive` vs **brute-force search for a proper ordinal-sum splitting**, all 2 449 posets `n ≤ 7` | **0 disagreements** (doc claimed only `n ≤ 5`; I extended it) |
| sweep engine == control engines? | `fast_Q` vs `Q_primary` on all 9 397 width-≤3 posets `n ≤ 8`; vs **my independent engine** `n ≤ 7` | **0 disagreements** |

**The width-prune completeness argument is also sound as stated.** Width is monotone under
deletion of a maximal element (an induced subposet's antichains are antichains of the parent), and
every finite non-empty poset has a maximal element; combined with `children_max` being complete
(A000112-certified above), pruning each level to width ≤ `W` provably cannot drop a width-≤`W`
poset. Both premises verified, not assumed.

**No false-negative channel was found.** The width-3 `n ≤ 11` enumeration is genuinely exhaustive.

---

## 3. The quantitative claims in the commit message

### 3.1 `min 6/17 at n=10` — REPRODUCED

I re-ran the production command end to end
(`--exh-nmax 11 --beam-nmax 16 --beam 400 --keep 30`), regenerating the full 397 222-class
`n = 10` level from scratch:

```
[width<=3] n=10  classes=  397,222  prim= 279,618  min delta = 37/106 |  width==3: prim= 277,180 min = 6/17
```

**Every §9.3a row through `n = 10` regenerated exactly** — class counts
(`55, 245, 1285, 7790, 53108, 397222`), primitive width-3 counts
(`18, 106, 681, 4715, 35057, 277180`), and minima
(`4/11, 15/37, 14/39, 19/50, 50/139, 6/17`). This covers the headline claim, which is at
`n = 10`.

The `n = 11` level (3 195 182 iso-classes, ~1 430 s) is the one row I did **not** independently
regenerate end to end within the audit window; I verified it two other ways instead — its record
witness on my independent engine (`below = [0,0,1,1,3,7,47,127,111,39,895]` → `e = 750`,
`δ = 134/375`, width 3, primitive), and against the committed certificate. Since `n = 11` is
neither the headline nor the minimum, this does not affect the verdict.

The committed certificate `data/onethird-mg0eac-width3-gap.json` **fully backs the §9.3a table**,
field by field, for every `n` including 11.

The record witness verified on my independent engine:
`below = [0,0,1,1,7,11,43,107,111,255]` → `e = 187`, `δ = 6/17`, **width exactly 3**, **primitive**,
transitively closed. Likewise the `n = 11` witness → `e = 750`, `δ = 134/375`.

### 3.2 `below Olson-Sagan's 14/39` — CORRECT, and correctly scoped

`6/17 = 0.352941… < 14/39 = 0.358974…` ✓. I fetched the actual paper (arXiv:1706.04985) and
extracted §6 verbatim:

> "*the three posets have balance constants δ(A)=6/17≈0.35294, δ(B)=60/171≈0.350877, and
> δ(C)=37/106≈0.349057. The smallest known balance constant for a poset with width strictly
> greater than 2 is 14/39≈0.3590, as described in [Bri99]. It belongs to the poset with 7 elements
> in Figure 12. A computer search of all posets with up to 9 elements revealed no posets with
> balance constant smaller that 14/39 and width greater than 2.*"

**Olson–Sagan is cited for exactly what it says.** Three independent confirmations:
`A, B, C = 6/17, 60/171, 37/106` ✓; `14/39` belongs to a **7-element** poset — and §9.3a
independently recovers `14/39` at exactly `n = 7` ✓; their search covered `n ≤ 9` ✓. The doc's
framing — `n = 10` is *past* their range, so this **extends** their datum rather than contradicting
it — is correct. Consistency check: at `n = 9` the width-3 minimum is `50/139 ≈ 0.35971 > 14/39`,
exactly as Olson–Sagan require.

### 3.3 `exhaustive to n=11` vs `bounded beam to n=16` — word discipline CLEAN

I grepped every occurrence of "exhaustive" in the doc. **It is never attached to a beam row.**
§9.3b is headed "*upper bounds only*" and opens "**These are NOT minima.**"; §6 and §9.0 both
carry explicit claimed/not-claimed tables. The beam **states the bound it covered**
(`beam = 400`, `keep = 30`, plus per-`n` `evaluated` counts: 76 940 / 24 645 / 34 552 / 34 060 /
48 658), and the certificate records `seeds`, `depths`, and `seconds` as well.

I re-ran the beam validation and **reproduced the documented `n = 10` miss**: the beam reaches
`47/130 ≈ 0.361538` where the exhaustive truth is `6/17 ≈ 0.352941`. The doc reports this miss
itself rather than dropping it — the correct behaviour, and it is what justifies the
upper-bound labelling.

All five beam witnesses (`n = 12…16`) verified on my independent engine as real, transitively
closed, primitive, width-exactly-3 posets with the claimed `δ`, none below `β`.

### 3.4 The `β` threshold — pinned from exact radicals, correct value operative

The ticket flagged a Chen-vs-Peczarski/Sah discrepancy. The doc resolves it correctly, and I
verified the resolution algebraically:

| | Chen `κ` | **Sah/Peczarski `β`** |
|:--|:--|:--|
| radical | `(93 − √6697)/32` | `(5864893 + 27√57)/16812976` |
| min poly (I derived) | `32x² − 186x + 61` ✓ matches doc | `33625952x² − 23459572x + 4091717` ✓ matches doc |
| field | `ℚ(√6697)`, 6697 = 37·181 squarefree | `ℚ(√57)`, 57 = 3·19 squarefree |
| decimal (20 dp) | `0.34889999217940426135` | `0.34884346742240945893` |

Distinct squarefree radicands ⟹ **distinct quadratic fields** ⟹ `β ≠ κ` provably. `κ − β =
5.652476·10⁻⁵` ✓ matches the doc's `5.65·10⁻⁵`. **`β` (the smaller, stronger threshold) is the one
used** — confirmed in code: `BETA_THRESHOLD = min(BETA_CHEN, BETA_PECZARSKI_SAH) = β`.

Comparisons are **exact integer arithmetic**, not float: `q < β ⟺ (16812976q − 5864893)² < 27²·57`
(with the sign branch). I re-derived both predicates independently; **all verdicts agree**.

Sah's abstract (arXiv:1811.01500), fetched and read, confirms the doc's citations verbatim:
`β ≈ 0.348843`, the width-2 bound `(−3+5√17)/52 ≈ 0.33876`, the "cannot be formed from the
singleton poset and the three element poset with one relation using direct sum" hypothesis (the
basis of the §0 correction), and that it is "*an improvement over a construction of Chen*" — which
is the doc's supersession argument.

Margins confirmed: `6/17 − β = 4.0977·10⁻³` (doc: `4.1·10⁻³`) ✓;
`7451/21359 − β = 2.4523·10⁻⁶` (doc: `2.45·10⁻⁶`) ✓.

---

## 4. Findings

### F1 — MEDIUM: the commit subject says "close out"; the doc says "does not close" ✋

**Claim.** Commit `a90f0f7` subject: "*close out the width>=3, n>=12 gap*".

**Observed.** The audited document says of the very same work, at line 396:

> "This section attacks that region. **It narrows the gap; it does not close it.**"

and §9.0's not-claimed row rules out "*any exhaustive statement at width ≥ 3 for `n ≥ 12`*".
**The doc is right and the commit subject is wrong.** At `n ≥ 12` the only coverage is a bounded
beam which, by its own validation, **misses the true optimum at 1 of 3 tested sizes**.

**Does it change the headline?** It changes the *commit-message* headline, not any number. But
this is exactly the failure pattern the audit brief warned about — a hedge present in the body
vanishing from the subject line. Recommend the ledger/subject record "**narrow**", not "close out".

### F2 — MEDIUM: the sweep's δ engine is not one of the five engines the controls validate

**Claim.** §3.1/§9.2: the engine is gated by five-engine agreement, "*so it never trusts a `δ` it
did not itself verify*".

**What I ran.** Patched each engine at its definition site and re-ran `positive_controls()`.

**Observed.** `five_engine_check` calls `Q_primary`, `ap0_Q_via_dp`, `IndPoset`, `ehrhart_Q`,
`Q_brute`. It does **not** call `fast_Q`. But `delta_of` — which computes `δ` for **every poset in
every sweep** — calls `fast_Q`, and `fast_Q is not Q_primary`. Corrupting `Q_primary` or `Q_brute`
is caught; **corrupting `fast_Q` passes the control gate untouched.**

The risk is **asymmetric**: only the *argmin* is re-verified through five engines. A `fast_Q` bug
that *understates* `δ` yields a bogus argmin that five-engine check would catch — but one that
*overstates* `δ` **on the true minimiser** hides it as a **silent false negative**, and nothing in
the pipeline would ever look at it.

**Mitigation — I closed this empirically.** Exhaustive cross-check of `fast_Q` vs `Q_primary` over
all **9 397** width-≤3 posets to `n = 8`, and vs my **independent** engine to `n = 7`:
**0 disagreements**. So there is **no actual bug** — but the *stated* control does not cover the
load-bearing code path, and a future edit to `fast_Q` would not be caught by it.

**Does it change the headline?** No. Recommend adding `fast_Q` to `five_engine_check` (a one-line
assert) so the control covers the path the sweep actually runs.

### F3 — LOW: the width-prune certification is partly self-referential

**Claim.** §9.2: "*Two independent routes, same set ⟹ the prune is sound.*"

**What I ran.** Corrupted `width_value_bitmask` (inflate width by 1 for `n ≥ 5`) and re-ran
`certify_width_prune`.

**Observed.** Both sides collapsed to 1 class at every `n ≥ 5` and the certification still printed
`MATCH` / `CERTIFIED`. The reason: `certify_width_prune` filters `width2_families` through **the
same width oracle** it uses for the prune, so the two "independent routes" share it. **The
certification cannot detect a width-oracle bug.**

**Mitigation — I closed this empirically.** Validated `width_value_bitmask` directly against
brute-force largest-antichain over all **19 448** posets to `n = 8`: **0 disagreements**; and
independently reproduced the width-≤3 counts (`7790` at `n = 8`) via unpruned enumeration + my own
width function. **No actual bug.**

**Does it change the headline?** No. Recommend the certification compare against an oracle-free
width, or state that it certifies the *prune logic* conditional on the oracle.

### F4 — LOW: one β comparison is float, against a blanket "exact" claim

**Claim.** §0 line 30: "*Every comparison against `β` in this document is exact rational-vs-algebraic
arithmetic, not floating point.*"

**Observed.** In the §§0–8 script the `sub_beta_records` flag uses
`float(d) < BETA_THRESHOLD` (line 663), a float comparison. The §9 script uses exact `lt_beta_sah`
throughout (`BETA_THRESHOLD` is an unused import there), and the safety-critical `δ ≤ 1/3` halt is
exact `Fraction`.

**Does it change the headline?** **No.** The tightest margin in play is `2.45·10⁻⁶` against double
precision `≈10⁻¹⁶` — ten orders of magnitude of headroom, so no verdict could flip. Every *reported*
`< β` verdict in both docs and certificates comes from the exact predicate. Flagged only because the
blanket wording is marginally stronger than the code.

### F5 — LOW: "width ≥ 3 arena" is really "width exactly 3"

**Observed.** §0's one-line §9 summary says §9 "*extends this to the width ≥ 3 arena*". In fact
§9.3a is width **exactly** 3, and **every beam argmin at `n = 12…16` has width exactly 3**
(I verified all five). **Width ≥ 4 received no coverage at any `n ≥ 10`.**

§9.0 and §6 both state this correctly ("*any statement at width ≥ 4 for `n ≥ 12` beyond what the
beam happened to visit*"; "*widths ≥ 4, `n ≥ 12` — NOT COVERED*"). Only the §0 one-liner is loose.

**Does it change the headline?** No, but it is the honest boundary of the residual gap: **width ≥ 4
is essentially untouched**, and it is where a wide low-`δ` poset would have to hide.

### F6 — INFO: prior-work boundary respected, but the two artifacts are pitched differently

The ticket bound new effort to `n ≥ 12` and forbade redoing Peczarski's `n ≤ 11` verification.

**Observed.** §9.3a is entirely `n ≤ 11`, inside Peczarski's GPC-verified range. The **script's own
stdout** says so plainly — "*n <= 11 lies INSIDE Peczarski's exhaustively verified range —
reported as a positive control + certified seed harvest, **NOT as a new result***" — while the
**doc** calls each §9.3a row "*a proven minimum*" and presents `n = 10`'s `6/17` as extending
Olson–Sagan.

**Both are defensible and reconcilable**: Peczarski's `n ≤ 11` work verifies the *Gold Partition
Conjecture* (⟹ `δ ≥ 1/3`), **not** a width-stratified min-`δ` profile; and Olson–Sagan covered only
`n ≤ 9` at width > 2, so `n = 10, 11` **is** new relative to them. **No misrepresentation** — the
boundary is respected. Worth noting only that the genuinely-new-territory contribution at
`n ≥ 12` is the bounded beam alone.

---

## 5. What I ran

| script | purpose |
|:--|:--|
| `scripts/audit_mg0eac_independent_delta.py` | from-scratch δ engine; all controls, 7 published pairs, both §9.3a witnesses, exact β/κ predicates re-derived |
| `scripts/audit_mg0eac_negative_controls.py` | deliberate engine/prune/guard corruption — proves the controls can fail |
| `scripts/audit_mg0eac_completeness.py` | A000112, width oracle vs brute force, prune vs unpruned, primitivity vs ordinal-sum splitting, `fast_Q` vs control engines |

Plus a full re-run of the production command
(`--exh-nmax 11 --beam-nmax 16 --beam 400 --keep 30`), regenerating §9.3a from scratch.

## 6. Recommendations (for pm-onethird — non-blocking)

1. **F1** — record this work as **narrowing** the width≥3/`n≥12` gap, not closing it. The doc
   already says this; only the commit subject and any ledger entry derived from it need the fix.
2. **F2** — add `fast_Q` to `five_engine_check` so the gate covers the path the sweep runs.
3. **F3** — note that the prune certification is conditional on the width oracle (which this
   audit has now independently validated to `n = 8`).
4. **F4/F5** — soften two sentences: the blanket "every β comparison is exact", and "width ≥ 3
   arena" → "width exactly 3".
5. Nothing here blocks the merge. The mathematics and the search results stand as reported.
