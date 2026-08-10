# Closing the class: the CI gate now compares the whole reference row (mg-75f0)

**Target.** The RED finding of `docs/OneThird-mg60d3-GateRepair-IndependentAudit.md` (mg-5ad1, merged
`c48d238b`), finding 1: *the repair is a patch on two instances, not a fix for the class.* The class,
in that audit's words:

> *a quantity the document asserts, computed by code the CI gate exercises, with no control that can
> fail.*

**Instruction taken literally.** Close the class, not two more instances. mg-60d3 repaired the two
mutations that had beaten the gate, which is exactly why the class survived: a repair derived **from**
a known failure carries no information about the class. So the acceptance bar here is not "does the
gate now catch M3 and M4" — it is "does it catch a mutation of the same family that nobody used to
build it". §4 is that test, and it was specified before it was run.

**What was NOT touched, per the ticket.** The mg-60d3 repair reproduces exactly and is not
re-litigated; ledger claim 27 stands as worded and is not struck; the audit's note that the
`dim_eigenspace > 1` two-sided check is vacuous on real data is treated as a coverage observation, not
a bug — and §3.3 gives it real coverage rather than arguing about it.

---

## §0 — Verdict

| | |
|---|---|
| **Fields of the committed mg-8b64 reference row now compared** | **22 of 23** (`name` excluded, reason in the source). Was **4 of 22 non-key fields**. |
| **Silent exclusions** | **0.** The one exclusion carries its reason in the code, and the probe fails if any exclusion lacks one. |
| **Per-field firing** | **22/22.** Perturbing any single compared field makes the gate's own `_identity_row_ok` return `False`. |
| **Field-census drift** | **Closed behaviourally, not by a list.** A field newly added to the reference row is compared automatically and, if the row builder does not produce it, **fails**. Tested (§3.2, B3). |
| **Does the widened gate fire on M3?** | **YES — exit 1**, 7 of 7 identity rows, 5–6 mismatched fields each, with all four previously-compared fields still `True`. §4.1 |
| **Does it fire on M4?** | **YES — exit 1**, via the new CONTROL E, 5 of 5 measured posets. §4.1 |
| **Does it fire on a mutation neither mg-60d3 nor mg-5ad1 used?** | **YES — 4 of 4** (M5, M6, M7, M8), each invisible to the pre-widening gate (exit 0) and fatal to the widened one (exit 1). **This is the finding**, and M8 was authored by mg-7db4, not by the author of the widening. §4 |
| **False positives** | **None.** Unmutated: exit 0, and every compared float field reproduces to `0.00e+00` against a `1e-9` tolerance. |
| **Is the proof-of-firing run by anything now?** | **The cheap half, yes** — wired into `script-controls.yml`. The 12- and 35-minute demonstrations are still unscheduled; that gap is **mg-7db4's**, and §6 says which of us owns what — including that `script-controls.yml` *informs* and does not *block*, which is mg-7db4's finding and mg-7db4's fix. |
| **The AMBER (audit finding 3)** | **FIXED, docstring only, no behaviour change.** §5 |
| **Overall** | **The class is closed for the mg-8b64 identity surface and for `projector_U`'s rank, and demonstrated so against unseen mutations. §7 states precisely what is still not covered.** |

---

## §1 — The hole, restated so the fix can be checked against it

The gate opens `data/onethird-mg8b64-L1b-bk-transport-transfer.json`, looks up the row for each named
poset, and — before mg-75f0 — compared four values out of it: `num_LE`, `lambda_std`, `delta`,
`bk_lambda2`. The row has 23 fields. Eighteen non-key fields were opened and not looked at:

```
bk_gap  frozen_p  frozen_pair  frozen_phi_bk  frozen_phi_t_image  frozen_ratio
frozen_sep_k  max_bias  min_phi_bk  min_phi_bk_pair  minphi_phi_t_image  n
num_incomp_pairs  phi_t_cheeger  phi_t_min_prefix  ratio_of_sums  transport_gap  width
```

That is not an oversight in one field, it is a *shape*: the comparison was a hand-written conjunction,
and a hand-written conjunction is a list that has to be maintained. mg-09ea's F3 defect was one
missing entry in that list; mg-5ad1's M3 was another. Adding entries one audit at a time is a process
that produces exactly this document again next quarter.

**So the repair is not additive.** `identity_field_comparisons` iterates the **committed row** and
compares everything in it. What is *not* compared has to be named, in code, with a reason:

```python
IDENTITY_EXCLUDED_REF_FIELDS = {
    "name": "the lookup key itself.  The row is FETCHED BY this value "
            "(`ref_rows[name]`), so comparing it is a tautology that cannot "
            "fail.  This is the only exclusion.",
}
```

One exclusion, and it is the only field for which "compare it" is meaningless — the row was *found* by
that value. Eighteen silent exclusions are not reviewable; one with a stated reason is.

**Why comparing a recomputation against a committed JSON is a real control.** The reference file is
static on disk: nothing in the gate's run can move it. The recomputation goes through mg-8b64's own
row builder (`analyze_poset`), which is the code the mutations live in. So the comparison is
*frozen ground truth vs. live code*, which is the same shape the F3 repair used, applied to the whole
row instead of one field.

**A bonus that fell out of it.** `bk_lambda2` is now compared **twice, by two independent
implementations**: the identity block still recomputes it through mg-4a86's `bk_walk_matrix` (the F3
repair, kept), and the row-wide comparison recomputes it through mg-8b64's own. Both must agree with
the committed value, so a mutation in *either* walk matrix is fatal.

---

## §2 — What the widened gate compares, measured

Unmutated, `--no-sweep`, this host:

| poset | fields compared | excluded | mismatched | `max \|diff\|` over float fields |
|---|---|---|---|---|
| `enum-n7-#3` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#20` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#600` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#945` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#809` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#52` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#88` | 22/23 | `name` | none | `0.00e+00` |

Two things worth stating rather than assuming:

- **The identity population is now seven posets, not five.** `#52` and `#88` come in with CONTROL F
  (§3.3) and get the same full-row treatment. mg-5ad1's §7 finding was that §2.6 said "three" where
  the loop ran over five; the number is now **seven**, and it is the loop that says so.
- **The tolerance has infinite margin here.** Every one of the compared float fields reproduces
  *bit-identically* — `max |diff| = 0.00e+00` at 7 of 7 posets — against a `1e-9` comparison
  tolerance. The tolerance exists so a different BLAS cannot fail the gate spuriously, not because
  anything needs it. Non-float fields (`frozen_pair`, `min_phi_bk_pair`, `width`, `frozen_sep_k`,
  `num_incomp_pairs`, `n`, `num_LE`) are compared **exactly**: "nearly the same pair of labels" is not
  a thing.

---

## §3 — The three additions, and why each is not derived from a known failure

### 3.1 CONTROL E — `dim U` has a structural bound and must stay proper

`U = span{σ ↦ 1[σ(a) = x]}` is spanned by the `n²` position indicators, which satisfy `2n−2`
independent homogeneous relations: the `n` row-sums all equal the constant function `1`, and so do the
`n` column-sums. Hence **always**

```
dim U  ≤  n² − (2n−2)  =  (n−1)² + 1
```

This is not new mathematics and it is not derived from M4 — the corpus already states it, in
`onethird_mg4a86_sector_leakage_and_tempering.sector_leakage`'s own docstring: *"rank = (n-1)^2 + 1 on
S_n, not n^2"*. It was stated in a comment and never asserted anywhere.

Verified against the committed sweep before being asserted: **0 violations** over 946 sweep rows + 29
family rows + 10 iso-gap rows. Saturated exactly on the antichains (`10/17/26/37` at `n = 4,5,6,7`),
which is why `_antichain_row_ok` can assert equality there rather than an inequality.

The second half is a **vacuity floor**, and it is the document's own criterion, not an aesthetic one:
if `dim U = |L(P)|` then `U` is the whole function space, `c ≡ 1` identically, and §2 of the
deliverable says *"c near `null` is NO signal in either direction"*.

**Population, stated because scoping a control is a claim.** CONTROL E runs on
`report["measured"]` — the five named posets. Not the family block: on hosts with `|L| ≤ n` (the
`fam:1||chain*` family) `U` legitimately *is* everything, `null = 1.0000` is correct, and those rows
are a falsification probe rather than a measurement. Not CONTROL F's two either — `projector_U` is
global, so a rank-filter mutation cannot hide from five posets and surface at a sixth; adding them
would be more lines and no more coverage. Both reasons are in the predicate's docstring, so the
scoping is reviewable rather than implicit.

### 3.2 The probe is now the standing control, and it takes its census from the gate

`scripts/onethird_mg5ad1_gate_blindspot_probe.py` is wired into `script-controls.yml`. Its part B was
already the right design — the ticket's reason for preferring it is that it derives the census from the
gate rather than from a list — and mg-75f0 strengthened it from *parsing* the gate's source to
*calling the gate's own comparison function*.

**That is not a stylistic preference; the parsing route had a measured defect.** mg-7db4, working the
same file concurrently, found it — and *how* it found it is the part worth keeping: not by reading the
code, but by building a mutation battery over the probe and running it. Row **N2** (delete
`match_bk_lambda2` from the gate — the mg-09ea F3 repair, reverted, one line) was expected CAUGHT and
came back **NOT CAUGHT** on the first run. The cause: part B's 240-character scan ran past the end of
the assignment it was reading and into the *next* `rec["match_*"] = …` line, so the window opened at
`match_delta` swept up `ref["bk_lambda2"]` from the line below. The census therefore still reported
`bk_lambda2` as COMPARED with the repair deleted, and the probe exited 0.

The one assertion part B made was that the F3 repair was present, and it could not see that repair
being removed. **A census that parses the thing it censuses can be defeated by that thing's source
layout, silently, in the exact case it exists to detect.** Calling the gate's own function has no
window to get wrong, so mg-7db4's fix to the regex is **superseded, not reverted** — the finding is
what justifies the redesign, and it is written up as a measured defect of the parsing approach in
`docs/OneThird-mg7db4-GateDemo-Trigger.md` §2.1a rather than as a comment on code that no longer
exists.

Three checks, increasing in strength:

| | check | result |
|---|---|---|
| **B1** | every reference field is COMPARED or excluded-with-a-reason; stale exclusions and reasonless exclusions both fail | 22 compared, 1 excluded, **0 silent** |
| **B2** | for EACH field, perturb it alone and require the gate's own `_identity_row_ok` to go `False` | **22/22 fire** |
| **B3** | hand the comparison a reference row with a field name it has never seen | **compared automatically, and FAILS** (the row builder does not produce it) |

**B3 is the one that closes the class rather than the instances.** The failure mode a hand-maintained
census has is not "it is wrong today" — it is "someone adds a field to the mg-8b64 row and the census
silently keeps passing". B3 is that scenario, executed. And note which way it resolves: an
*unrecomputed* reference field is a **failure**, not a pass. Defaulting the other way is how F3
happened.

A new **part D** asks the same question of every other predicate: each of CONTROL B, CONTROL E and
CONTROL F is handed a row it must accept and a row it must reject — **10 probes, 10 agree**. This is
the part of a mutation demonstration that costs milliseconds, so it can be in CI, which is the
difference between a control with a mechanism and a control with an instruction addressed to a future
reader.

### 3.3 CONTROL F — the two-sided check now has real coverage

mg-5ad1 finding 4, recorded as a coverage observation: `dim_E = 1` at all five measured posets, so the
gate's `dim_eigenspace > 1 and |c_max − c_min| > 1e-9` branch is **vacuous on real data**, and
mg-60d3's F4 repair bought two-sided coverage on three *synthetic* antichains only.

The coverage was available and unused. The committed sweep has `dim_eigenspace = 2` at exactly four of
the 946 posets — `#52`, `#88`, `#209`, `#420` — and `#209/#420` measure identically to `#52/#88`. So
CONTROL F measures `#52` and `#88`:

| poset | `\|L\|` | `dim U` | `dim_E` | `c_max` | `c_min` | `\|c_max − c_min\|` |
|---|---|---|---|---|---|---|
| `enum-n7-#52` | 288 | 25 | **2** | `0.994818990` | `0.994818990` | `8.88e-16` |
| `enum-n7-#88` | 180 | 17 | **2** | `0.978492428` | `0.978492428` | `1.11e-16` |

`dim_E > 1` is **asserted**, not hoped for, so this control cannot quietly become the vacuous one it
replaces.

And it is non-vacuous in the way that matters — it can fail on a real mutation. Measured directly:
under mg-09ea's M2 (`U` shrunk by the element-0 and element-1 position blocks) the two readings
**split** at both posets, `|c_max − c_min| = 7.58e-02` at `#52` and `4.30e-02` at `#88`, with `c_max`
surviving at its unmutated value — M2's exact signature, now visible on **real posets** and not only
on synthetic antichains.

---

## §4 — ACCEPTANCE: does it fire, and does it fire on something unseen?

Route, and it is deliberately not the mg-60d3 demo's route (which reconstructs the gate in process and
monkeypatches loaded modules — reproducing that would have audited nothing). Following mg-5ad1's
audit: **one isolated tree per case**, holding a copy of `scripts/` plus the reference dataset the gate
reads; **one source-level edit** applied there with an **anchor-count assertion**, so a silent
no-match is impossible; the gate run in that tree. The pre-widening gate is the **real source** at
`af7fc2df` (mg-60d3's merge — the exact file mg-5ad1 measured M3 and M4 against), pinned by SHA rather
than derived from branch topology, so the left column does not silently become the widened gate once
this lands.

`scripts/onethird_mg75f0_gate_class_closure_demo.py`, fourteen full `--no-sweep` gate runs:

| mutation | one-line change | first used by | pre-widening gate | widened gate |
|---|---|---|---|---|
| — | unmutated | — | exit **0** | exit **0** |
| **M3** | `bk_frozen_pair`'s Theorem-E selector `min` → `max` | mg-5ad1 | exit **0** ← the residual | exit **1** |
| **M4** | `projector_U`'s rank filter `s > max(tol,1e-10)` → `s > 0.0` | mg-5ad1 | exit **0** ← the residual | exit **1** |
| **M5** | `bk_frozen_pair`'s MIN-PHI selector `min` → `max` | **UNSEEN** | exit **0** | exit **1** |
| **M6** | `transport_summary`'s prefix selector `min` → `max` | **UNSEEN** | exit **0** | exit **1** |
| **M7** | `_transport_label_cheeger`'s volume normalisation `min(r,n−r)` → `max(r,n−r)` | **UNSEEN** | exit **0** | exit **1** |
| **M8** | `bk_pair_cut`'s Bernoulli variance `p(1−p)` → `p` | **mg-7db4's row N1 — NOT chosen by this author** | exit **0** | exit **1** |

The left column is what makes the right one mean anything: each mutation is shown to have been
**invisible** before, so `exit 1` is the widening firing and not a pre-existing control doing its job.

### 4.1 M3 and M4 — the two the audit exhibited

**M3** fails the identity check at **7 of 7** posets, and the gate names the moved fields in its
failure message:

| poset | mismatched fields (of the 22 compared) | count |
|---|---|---|
| `enum-n7-#3` | `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |
| `enum-n7-#20` | + `frozen_p` | 6 |
| `enum-n7-#600` | `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |
| `enum-n7-#945` | `frozen_p` `frozen_pair` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |
| `enum-n7-#809` | `frozen_p` `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 6 |
| `enum-n7-#52` | `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |
| `enum-n7-#88` | `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |

`max |diff|` over float fields goes from `0.00e+00` unmutated to `2.22e-01` / `2.35e-01` at `#3` / `#20`.

**Note what did *not* move**, printed by the gate in the same line: `num_LE=True lambda_std=True
delta=True lambda2_BK=True` — **all four fields the pre-widening gate compared**, at every one of the
seven posets. That is the residual, stated by the failure message itself.

**M4** moves **no mg-8b64 reference field at all** — the identity check reports `mismatched: none` and
`max |diff| = 0.00e+00` at all seven posets, so the widening is *not* what catches it. This is the
worked example of §7.1: widening the identity comparison does not cover a mutation that moves no
identity field. **Three independent controls fire:**

| control | how it fires under M4 |
|---|---|
| **CONTROL E** — bound | `dim U = 49 > (n−1)²+1 = 37` at `#3`, `#20`, `#600` |
| **CONTROL E** — properness | `dim U = |L|` exactly at `#945` (21) and `#809` (25), i.e. `null = 1.0000` — `U` is the whole function space and `c ≡ 1` is vacuous by §2's own criterion |
| **CONTROL B** — known rank | the antichains' `dim U` goes `10/17/26 → 16/25/36 = n²`, off the known `(n−1)²+1` |
| **CONTROL F** — two-sided | `\|c_max − c_min\|` at `#52`/`#88` splits to `5.54e-04`/`1.37e-03`, over the `1e-9` bar |

Five of five measured posets, three of three antichains, two of two CONTROL F posets. The
pre-widening gate reported no failure at all.

### 4.2 M5, M6, M7 — the ones that decide whether the class is closed

These were chosen and written down **before** the widened gate was run against them, and none of them
appears in mg-60d3's demo or mg-5ad1's audit. They are also not all the same shape, which matters: a
widening that only catches `min → max` in one function has not generalised.

- **M5** — `bk_frozen_pair`'s `minphi` selector `min` → `max`. This is the honest one, and the one to
  look at first: it is **M3's structural twin, one line down in the same function**. If the widening
  were a patch on its own witnesses, M5 is where that would show.

  Measured: **pre-widening gate exit 0, no failure reported at all**; widened gate **exit 1** at
  **6 of the 7** identity posets, on exactly `min_phi_bk`, `min_phi_bk_pair` and
  `minphi_phi_t_image` — three fields uncompared until mg-75f0 — with `num_LE`, `lambda_std`, `delta`
  and `bk_lambda2` all still `True`. `frozen_pair` is untouched, so the comparison that catches M3 is
  **not** what catches this. `max |diff|` reaches `1.11e-01`.

  **6 of 7, not 7 of 7, and that is worth stating.** At `enum-n7-#945` the argmax-`Φ` pair coincides
  with the argmin, so the flip is not a mutation there at all — the same phenomenon part C measures for
  the frozen-pair selector. One poset where a mutation is a no-op is coverage arithmetic, not a miss.
- **M6** — `transport_summary`'s expected-rank prefix selector `min` → `max`, so `phi_t_min_prefix`
  reports the *worst* transport prefix cut instead of the best. Different side of the probe: transport,
  not BK.

  Measured: pre-widening **exit 0**, widened **exit 1** at **7 of 7** posets, and its entire visible
  footprint is **one field of the 22** — `phi_t_min_prefix`, and nothing else, at every poset
  (`max |diff|` `3.70e-01` / `3.55e-01`). This is the narrowest catch in the set and therefore the
  strongest evidence the widening is not a patch: there was no neighbourhood of related fields to
  stumble over, just the single one the mutation touched.
- **M7** — `_transport_label_cheeger`'s volume normalisation `min(r, n−r)` → `max(r, n−r)`. A
  **normalisation, not a selector**, so it is not the same edit shape as M3/M5/M6 at all. Pre-widening
  **exit 0**, widened **exit 1** at **7 of 7** posets on exactly one field, `phi_t_cheeger`.

All three: **invisible to the pre-widening gate (exit 0), fatal to the widened one (exit 1).** And note
the spread of the evidence: 5–6 fields (M3), 3 fields at 6 of 7 posets (M5), exactly 1 field at 7 of 7
(M6), and a normalisation rather than a selector, again 1 field at 7 of 7 (M7). A widening that had
merely covered its own witnesses would not have produced that spread — and in all four the printed
`num_LE=True lambda_std=True delta=True lambda2_BK=True` says, in the gate's own words, that the four
fields it used to compare were not the ones that moved.

### 4.3 M8 — the row this author did not choose, which is the one that counts

M5/M6/M7 share a weakness that has to be said out loud rather than left for a reader to notice: **the
person who wrote the widening also chose them.** An author picks around the cases their own fix misses
without meaning to, so three-for-three from a single author is weaker evidence than the count suggests.
That is the same circularity mg-5ad1 identified in mg-60d3's repair, one level up — and being aware of
it is not the same as escaping it.

**M8 escapes it.** `bk_pair_cut`'s Bernoulli variance `p(1−p) → p`, so Theorem E's ratio
`E(f_xy)/Var(f_xy)` is divided by the wrong variance. It is **mg-7db4's**, row `N1` of
`scripts/onethird_mg7db4_probe_mutation_battery.py`, written for a different instrument, for a different
purpose, by an author who had not seen this widening. It is the only row in the table selected by nobody
who built the thing under test. Measured here: pre-widening **exit 0**, widened **exit 1**.

**And mg-7db4's own result on it is the stronger statement of the property, so it is recorded as
mg-7db4's and not as this document's.** Running N1 through GitHub Actions on a branch carrying nothing
else, mg-7db4 measured `Script controls` **failure**: the pre-existing mg-2c34 gate step **succeeded**
— blind to N1 — and the mg-5ad1 probe step **caught it**. The check that caught it is mg-5ad1's
*original* part C comparison, written by an author who had never seen that mutation. That is the only
place in either ticket where **the guard demonstrably predates the mutation**, which is the
non-circular form of what both tickets were asked to establish. mg-75f0 adds that the *widened gate*
also catches N1; mg-7db4's is the cleaner claim.

**The bar the ticket set is met.** If any of these had passed, the correct report would have been "the
class is still open" — the demonstration is written so that outcome exits non-zero and says so in
those words, rather than being papered over.

---

## §5 — The AMBER: CONTROL B's justification (audit finding 3), docstring only

The docstring said:

> *"L(P) = S_n, the BK chain is the interchange process on the path, and by Aldous/CLR the slowest
> mode **IS** the single-particle mode, which lies in U."*

Aldous' spectral-gap conjecture, as proved by Caputo–Liggett–Richthammer, gives the gap
**eigenvalue**: `gap(interchange on the path) = gap(one-particle)`. `c_min = 1` is the strictly
stronger claim that the **whole gap eigenspace** lies in the one-particle sector, which additionally
requires that no other `S_n`-irrep component of the generator attains that eigenvalue. **CLR does not
supply that.**

The control is **not wrong today** — the hazard is latent, verified 4-for-4 at `n = 4,5,6,7` (mg-5ad1
part A: `dim_E = n−1`, `1 − c_min ≤ 2.7e-15` against a `1e-8` assertion, nearest *excluded* eigenvalue
`3.0e7–1.1e8 × EIG_TOL` away). What was wrong was the *reason*, and an over-strong stated reason has a
predictable consequence: whoever extends the control to a larger antichain and hits a legitimate
cross-irrep coincidence will read "by Aldous/CLR this must hold", conclude the assertion is too tight,
and loosen it — at which point the repair is gone.

The docstring now cites Aldous/CLR **for the eigenvalue equality alone**, cites the eigenspace
containment as a **verified property of these specific matrices** with the measurements and the
probe that produces them, and states the consequence explicitly: if it ever fails on a larger
antichain, narrow the control's **population**, do not loosen the **assertion**. No behaviour changed.

---

## §6 — Wiring, and who owns which trigger (mg-7db4)

mg-7db4 was in flight and had not merged when this was written (`mg show mg-7db4` → `claimed`; no
commit on `main`; its work staged-but-uncommitted in its own worktree). It is working the **same two
files** — `script-controls.yml` and the probe — so ownership is stated rather than assumed, and both
mails are in mg-7db4's inbox:

- **mg-75f0 owns the wiring of the probe.** `script-controls.yml` gains one step running
  `scripts/onethird_mg5ad1_gate_blindspot_probe.py` (parts A–D). **Cost, measured properly:
  30.8 s** uncontended on this host; mg-7db4 measured the whole workflow going `41–64 s → 1m12s`
  with both new steps on a hosted runner. An earlier draft raised the job's `timeout-minutes`
  10 → 20 on a **2m33s reading taken while this ticket's own 25-minute demonstration was saturating
  the same host** — a mismeasurement of a factor of five. The raise is reverted and the revert is
  commented in the workflow rather than done silently: a bound loosened on a bad measurement is worse
  than one left alone, because it stops being a wedge detector.
- **mg-7db4 owns the expensive demonstrations' trigger.** `onethird_mg60d3_gate_mutation_demo.py`
  (~12 min, six gate runs) is run by nothing on this branch, and mg-5ad1 finding 2 stands in full: it
  would not have caught M3 or M4 even if it were scheduled. mg-75f0 adds a **third** expensive artifact
  to that problem — `onethird_mg75f0_gate_class_closure_demo.py`, ~25 min, twelve gate runs —
  deliberately *not* wired into CI here for the same order-seconds reason. mg-7db4's paths-filtered job
  should trigger both.
- **`script-controls.yml` INFORMS; it does not BLOCK — and that is mg-7db4's finding, not this
  document's.** `main` has no branch protection and no ruleset, and the refinery fast-forwards without
  reading GitHub check runs, so *every* step in that file reports and nothing stops a merge. This is
  the same shape as the defect this ticket exists to close, relocated to the enforcement layer: a
  control that fires into a check nobody consults is not distinguishable from a control that cannot
  fire. mg-7db4's MR adds this repo's first refinery gate (`.pogo/refinery.toml` +
  `scripts/refinery_gate.sh`) and **already runs the probe inside it**, cheapest-first — verified from
  that MR's own gate output, not from its description. So the enforcement half is mg-7db4's and is
  already correct; nothing is left for mg-75f0 to add there.
- **Two enforcement decisions recorded rather than taken silently.** (i) The 25-minute closure demo
  goes in the *informational* workflow and in the watchlist ROOTS, **not** in the blocking gate:
  mg-7db4's 11 minutes plus mg-75f0's 25 would make a gate-touching merge ~37 minutes, and a blocking
  gate long enough to invite bypass has a shorter life expectancy than the defect it guards. (ii) The
  mg-2c34 gate itself (~2 min) is **not** mirrored into the blocking layer either — the probe cannot
  pass if the identity comparison has narrowed and the probe *is* blocking, so the marginal enforcement
  is small against a cost paid by every gate-touching merge.
- **Merge order: mg-75f0 volunteered to be second.** mg-7db4's first MR (`mr-d9lcsk2tjv1tur4p9bf0`)
  came back **`cancelled`** with the probe reporting `signal: killed`. **That was mg-7db4 cancelling its
  own MR deliberately**, ~90 s in, to fold its acceptance demonstration into the same MR rather than a
  follow-up it might not have lived to make — the `signal: killed` is its own SIGTERM reaching the probe
  through the process-group kill, and *"cancelled by operator"* is literally accurate. Recorded because
  this document's first draft speculated about host contention instead, and that was wrong: nothing was
  wrong with the gate, and its watchlist check had already passed with all five self-test drifts CAUGHT.
  That MR and its successor were cancelled by mg-7db4 as well — **mid-iteration, not wedged**; the live
  one is `mr-d9ld8m2tjv1tur4p9bh0`, whose gate is cheaper because mg-7db4 moved its own battery out of
  the blocking path applying this document's split argument to its own instrument, and raised its gate
  timeout to 90m so contention cannot produce a false failure. Whichever branch is second rebases, **keeping mg-7db4's part C column, its `gate-mutation-demo.yml`,
  `refinery_gate.sh`, `.pogo/refinery.toml` and watchlist-consistency script, collapsing the duplicated
  probe step to one, adding the closure demo to the three places mg-7db4 named, and re-pointing its
  battery row N2** — whose anchor is the four-conjunct `_identity_row_ok` that mg-75f0 replaces, so its
  anchor-count assertion will fire with *"occurs 0 times"*. That is the assertion working, not a break.
- **Two statements in mg-7db4's MR that CONTROL E makes stale, to be corrected in whichever rebase
  happens** — at mg-7db4's own request, so they are recorded here rather than left to memory:
  (i) `docs/OneThird-mg7db4-GateDemo-Trigger.md` §3.1 says *"M4 is caught by nothing"*, true of `main`
  today and false the moment CONTROL E lands — replace with §4.1's measured result, **keeping the sting
  that the identity widening does not catch M4** (`mismatched: none` at all seven posets), which is why
  CONTROL E had to exist separately; (ii) the battery's M4 row **stays** expected-exit-0 and is still
  correct, because it measures the *probe*, which does not import `projector_U` — but its docstring's
  *"caught by nothing here and nothing in `script-controls.yml`"* needs its second half struck, and a
  sentence saying that expected-0 means *"the probe is blind"*, not *"the repo is blind"*.
  (iii) **The `timeout-minutes` revert is mg-75f0's to make, and is made here.** mg-7db4 carried the
  10 → 20 raise on mg-75f0's reasoning, then declined to cancel a third MR to change one integer of
  pure headroom — a judgement this document agrees with and records rather than leaves implicit. If
  mg-7db4 lands first the revert survives the rebase; if mg-75f0 lands first, mg-7db4's copy of that
  hunk conflicts and is dropped.
- **mg-7db4 owns one defect fix inside part C that mg-75f0 keeps verbatim, and it is not a nicety.**
  Measured by mg-7db4 before it wired anything in: **the probe as mg-5ad1 committed it caught neither
  M3 nor M4** — both exit 0. M3 got through because part C recomputed `argmin` over the pair *list* and
  never read what `bk_frozen_pair` *returns*, so it printed *"a comparison IS available"* and did not
  make it. That is the F3 shape inside the file written to report the F3 shape. M4's row is on
  mg-7db4's record as expected-exit-0; **that is now out of date** — §4.1 measures M4 firing on CONTROL
  E at 5 of 5, and mg-7db4 has been told.

**One consequence for a merged artifact, stated plainly.** `apply_pre_repair_gate` in
`onethird_mg60d3_gate_mutation_demo.py` reconstructs the 87f0424 gate by substituting two predicates.
The gate has since acquired two more failure conditions, so that function was reconstructing "today's
gate minus two predicates" rather than the gate mg-09ea measured. Two lines were added to neutralise
CONTROL E and CONTROL F in the reconstruction. **`EXPECTED` is unchanged, the 2×3 matrix is unchanged,
and ledger claim 27 is untouched** — the substitutions still live in the demonstration and not in the
gate, which has no switch that weakens it and must not acquire one. The demo's committed JSON is
regenerated because the widened gate reports more in its failure messages; no asserted value changed.

---

## §7 — What is NOT closed, stated rather than implied

1. **The class is closed for the mg-8b64 identity surface and for `projector_U`'s rank — not for
   everything the gate touches.** Anything that moves *no* field of the committed reference row and
   *no* dimension of `U` is still only covered to the extent CONTROL A/B/C/D/F reach it. M4 is the
   worked example of that gap being real: it needed a purpose-built control, not the widening.
2. **The expensive demonstrations are still unscheduled** (mg-7db4). The cheap half now has a
   mechanism; the 12- and 25-minute halves have an owner and no trigger.
3. **CONTROL F's population is two posets, both `n = 7`.** It is real-data coverage where there was
   none, not broad coverage.
4. **`data/onethird-mg2c34-n7-overlap.json` was not regenerated.** The committed dataset predates the
   new per-field keys and the CONTROL F block, because regenerating it means a full sweep and the doc's
   §5/§6 tables are sourced from it. Nothing in this document depends on those keys being in the
   committed file; the gate writes them on any full run.
5. **`(n−1)²+1` is asserted as a bound, and verified, not proved here.** The relation count `2n−2` is
   stated in the predicate's docstring and is the corpus's own; the assertion's licence in this
   document is the 985-row check plus exact saturation at `n = 4,5,6,7`.

---

## §8 — Reproduction

```bash
# the standing control, now in CI (parts A-D; order-tens-of-seconds)
/usr/bin/python3 scripts/onethird_mg5ad1_gate_blindspot_probe.py

# the widened gate itself (~2 min)
/usr/bin/python3 scripts/onethird_mg2c34_n7_overlap_test.py --no-sweep

# the acceptance test: 12 gate runs, 5 mutations, 3 of them unseen (~25 min)
/usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py
/usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py --only M5,M6,M7

# mg-60d3's 2x3 matrix, still exact after the widening (~12 min)
/usr/bin/python3 scripts/onethird_mg60d3_gate_mutation_demo.py
```

`data/onethird-mg75f0-gate-class-closure.json` is the acceptance run's committed output;
`data/onethird-mg5ad1-gate-blindspot-probe.json` the probe's. Interpreter matters: bare `python3` on
this host has no numpy.

---

## §9 — Findings ledger

| # | finding | severity | site |
|---|---|---|---|
| **1** | **The identity comparison is now the whole row**: 22 of 23 fields, one exclusion with a stated reason, 0 silent. Iterating the committed row means a field ADDED to it is compared automatically — the defect one turn later is closed behaviourally, not by a list | **CLOSED** (audit finding 1) | §1, §2 |
| **2** | **The widened gate fires on 4 of 4 mutations that neither mg-60d3 nor mg-5ad1 used**, each invisible to the pre-widening gate. M5 is M3's twin one line down; M6's whole footprint is 1 field of the 22; M7 is a normalisation, not a selector; and **M8 was chosen by mg-7db4, not by the author of the widening** — the only row here free of that circularity | **the acceptance result** | §4.2, §4.3 |
| **3** | **CONTROL E**: `dim U ≤ (n−1)²+1` and `dim U < \|L\|`. Analytic, the corpus's own stated rank, 0 violations in 985 committed rows. Catches M4 at 5/5 measured posets, which the identity widening does not | **new control** | §3.1 |
| **4** | **CONTROL F**: the two-sided check now has real-data coverage (`#52`, `#88`, `dim_E = 2`), with non-vacuity asserted. It splits under M2 by `7.6e-2` / `4.3e-2`, so the coverage is real and not decorative | **CLOSED** (audit finding 4, as a coverage gap) | §3.3 |
| **5** | **The probe is in CI, and its census comes from the gate's own comparison function** — 22/22 fields fire when perturbed, and part D proves every gate predicate can reject | **CLOSED, cheap half** (audit finding 2) | §3.2, §6 |
| **6** | **CONTROL B's Aldous/CLR justification corrected**, docstring only, no behaviour change: CLR gives the gap eigenvalue; eigenspace containment is a verified property of these matrices | **CLOSED** (audit finding 3, AMBER) | §5 |
| **7** | The expensive demonstrations remain unowned-by-a-trigger; mg-75f0 adds a third one. mg-7db4's, and mailed there | **open, assigned** | §6, §7.2 |
| **8** | Every compared float field reproduces to `0.00e+00` at 7/7 posets against a `1e-9` tolerance — the widening introduces no tolerance risk | **note** | §2 |
| **9** | **CONTROL B's failure message misattributed its own cause**, found by running M4 against the widened gate: it read *"antichain c != 1 (Aldous/CLR)"* while `c` was exactly 1 and `dim U` was what had failed — naming the one conjunct that held, and citing a theorem that does not license the assertion. It now prints all three conjuncts per failing row. A diagnostic that misdirects is the same genre as a control that cannot fail | **fixed, found in flight** | §5 |
| **10** | **`script-controls.yml` INFORMS, it does not BLOCK** — `main` has no branch protection and the refinery fast-forwards without reading GitHub check runs (mg-7db4 verified both). mg-7db4's MR adds this repo's first refinery gate; mg-75f0 puts the **probe** in it (paths-filtered, so an ordinary commit pays milliseconds) and deliberately keeps the 25-minute closure demo **out** of the blocking layer — a blocking gate long enough to invite bypass has a shorter life than the defect it guards | **enforcement, decided not assumed** | §6 |
