# Closing the class: the CI gate now compares the whole reference row (mg-75f0)

**Target.** The RED finding of `docs/OneThird-mg60d3-GateRepair-IndependentAudit.md` (mg-5ad1, merged
`c48d238`), finding 1: *the repair is a patch on two instances, not a fix for the class.* The class, in
that audit's words:

> *a quantity the document asserts, computed by code the CI gate exercises, with no control that can
> fail.*

**Instruction taken literally.** Close the class, not two more instances. mg-60d3 repaired the two
mutations that had beaten the gate, which is exactly why the class survived: a repair derived **from** a
known failure carries no information about the class. So the acceptance bar here is not "does the gate
now catch M3 and M4" — it is "does it catch mutations of the same family that nobody used to build it".
§4 is that test, and the mutations were written down before the widened gate was run against them.

**What was NOT touched, per the ticket.** The mg-60d3 repair reproduces exactly and is not
re-litigated; ledger claim 27 stands as worded and is not struck; the audit's note that the
`dim_eigenspace > 1` two-sided check is vacuous on real data is treated as a coverage observation, not a
bug — and §3.3 gives it real coverage rather than arguing about it.

**Coordination.** mg-7db4 merged (`df7db8b`, `245085e`) while this ticket was between attempts. It owns
the trigger mechanism; this ticket owns what is triggered. §6 states the split and what each side
corrected in the other's artifacts.

---

## §0 — Verdict

| | |
|---|---|
| **Fields of the committed mg-8b64 reference row now compared** | **22 of 23** (`name` excluded, reason in the source). Was **4 of 22 non-key fields**. |
| **Silent exclusions** | **0.** The one exclusion carries its reason in the code, and the probe fails if any exclusion lacks one. |
| **Per-field firing** | **22/22.** Perturbing any single compared field makes the gate's own `_identity_row_ok` return `False` — measured, not inferred from the source. |
| **Field-census drift** | **Closed behaviourally, not by a list.** A field newly added to the reference row is compared automatically and, if the row builder does not produce it, **fails**. Tested (§3.2, B3). |
| **Does the widened gate fire on M3?** | **YES — exit 1**, 7 of 7 identity rows, 5–6 mismatched fields each, with all four previously-compared fields still `True`. §4.1 |
| **Does it fire on M4?** | **YES — exit 1**, and **not** via the widening: M4 moves *no* reference field. CONTROL E at 5/5 measured posets, plus CONTROL B and CONTROL F. §4.1 |
| **Does it fire on mutations neither mg-60d3 nor mg-5ad1 used?** | **YES — 5 of 5** (M5, M6, M7, M8, M9), each fatal to nothing before the widening. **This is the finding.** One of the five, M8, was authored by mg-7db4 rather than by the author of the widening. §4.2, §4.3 |
| **False positives** | **None.** Unmutated: exit 0, and every compared float field reproduces to `0.00e+00` against a `1e-9` tolerance, at all 7 posets. |
| **Is the proof-of-firing run by anything?** | **Yes, at three tiers, all mg-7db4's mechanism.** The ~27 s probe on every commit; the ~11 min mg-60d3 demo blocking at the refinery; this ticket's ~13 min closure demo in the paths-filtered Actions job. §6 |
| **The AMBER (audit finding 3)** | **FIXED, docstring only, no behaviour change.** §5 |
| **Overall** | **The class is closed for the mg-8b64 identity surface and for `projector_U`'s rank, demonstrated against five unseen mutations. §7 states precisely what is still not covered, including a distinction §4.2 measures rather than assumes.** |

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
and a hand-written conjunction is a list that has to be maintained. mg-09ea's F3 defect was one missing
entry in that list; mg-5ad1's M3 was another. Adding entries one audit at a time is a process that
produces exactly this document again next quarter.

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
static on disk: nothing in the gate's run can move it. The recomputation goes through mg-8b64's own row
builder (`analyze_poset`), which is the code the mutations live in. So the comparison is *frozen ground
truth vs. live code* — the same shape the F3 repair used, applied to the whole row instead of one field.

**A consequence worth stating, because it is the reason the widening had to call `analyze_poset`.** The
pre-widening gate never called mg-8b64's row builder at all. It recomputed four quantities by four
separate routes. So eighteen fields were not merely uncompared — most of the code that produces them was
never **executed** by the gate. §4.2 measures which mutations fall on which side of that line, because
they are findings of different strength and an exit code alone averages them together.

**And a bonus that fell out of it.** `bk_lambda2` is now compared **twice, by two independent
implementations**: the identity block still recomputes it through mg-4a86's `bk_walk_matrix` (the F3
repair, kept), and the row-wide comparison recomputes it through mg-8b64's own. Both must agree with the
committed value, so a mutation in *either* walk matrix is fatal.

---

## §2 — What the widened gate compares, measured

Unmutated, `--no-sweep`, this host, 45 s:

| poset | fields compared | excluded | mismatched | `max \|diff\|` over float fields |
|---|---|---|---|---|
| `enum-n7-#3` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#20` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#600` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#945` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#809` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#52` | 22/23 | `name` | none | `0.00e+00` |
| `enum-n7-#88` | 22/23 | `name` | none | `0.00e+00` |

Three things worth stating rather than assuming:

- **The identity population is now seven posets, not five.** `#52` and `#88` come in with CONTROL F
  (§3.3) and get the same full-row treatment. mg-5ad1's §7 finding was that §2.6 said "three" where the
  loop ran over five; the number is now **seven**, and it is the loop that says so.
- **The tolerance has enormous margin here.** Every compared float field reproduces *bit-identically* —
  `max |diff| = 0.00e+00` at 7 of 7 posets — against a `1e-9` comparison tolerance. The tolerance exists
  so a different BLAS cannot fail the gate spuriously, not because anything needs it.
- **Non-float fields are compared EXACTLY.** `frozen_pair`, `min_phi_bk_pair`, `width`, `frozen_sep_k`,
  `num_incomp_pairs`, `n`, `num_LE`: "nearly the same pair of labels" is not a thing. That is not
  pedantry — M9 (§4.2) moves `width` from 4 to 1 and leaves `max |diff|` over the *float* fields at
  `0.00e+00`, so a float-only comparison would have missed it entirely.

---

## §3 — The three additions, and why none is derived from a known failure

### 3.1 CONTROL E — `dim U` has a structural bound and must stay proper

`U = span{σ ↦ 1[σ(a) = x]}` is spanned by the `n²` position indicators, which satisfy `2n−2` independent
homogeneous relations: the `n` row-sums all equal the constant function `1`, and so do the `n`
column-sums. Hence **always**

```
dim U  ≤  n² − (2n−2)  =  (n−1)² + 1
```

This is not new mathematics and it is not derived from M4 — the corpus already states it, in
`onethird_mg4a86_sector_leakage_and_tempering.sector_leakage`'s own docstring: *"rank = (n-1)^2 + 1 on
S_n, not n^2"*. It was stated in a comment and asserted nowhere.

Verified against the committed sweep **before** being asserted: **0 violations** over 946 sweep rows + 29
family rows + 10 iso-gap rows. Saturated exactly on the antichains (`10/17/26/37` at `n = 4,5,6,7`),
which is why `_antichain_row_ok` can assert *equality* there rather than the inequality.

The second half is a **vacuity floor**, and it is the document's own criterion rather than an aesthetic
one: if `dim U = |L(P)|` then `U` is the whole function space, `c ≡ 1` identically, and §2 of the
deliverable says *"c near `null` is NO signal in either direction"*.

**Population, stated because scoping a control is itself a claim.** CONTROL E runs on
`report["measured"]` — the five named posets. Not the family block: on hosts with `|L| ≤ n` (the
`fam:1||chain*` family) `U` legitimately *is* everything, `null = 1.0000` is correct, and those rows are
a falsification probe rather than a measurement. Not CONTROL F's two either — `projector_U` is global, so
a rank-filter mutation cannot hide from five posets and surface at a sixth; adding them would be more
lines and no more coverage. Both reasons are in the predicate's docstring, so the scoping is reviewable
rather than implicit.

### 3.2 The probe takes its census from the gate, and now proves each field fires

`scripts/onethird_mg5ad1_gate_blindspot_probe.py` has been a step in `script-controls.yml` since mg-7db4.
Its part B was already the right design — the ticket's reason for preferring it is that it derives the
census from the gate rather than from a list — and mg-75f0 strengthened it from *parsing* the gate's
source to *calling the gate's own comparison function*.

**That is not a stylistic preference; the parsing route had a measured defect.** mg-7db4 found it, and
*how* it found it is the part worth keeping: not by reading the code, but by building a mutation battery
over the probe and running it. Row **N2** (delete `match_bk_lambda2` from the gate — the mg-09ea F3
repair, reverted, one line) was expected CAUGHT and came back **NOT CAUGHT** on the first run. The cause:
part B's 240-character scan ran past the end of the assignment it was reading and into the *next*
`rec["match_*"] = …` line, so the window opened at `match_delta` swept up `ref["bk_lambda2"]` from the
line below.

The one assertion part B made was that the F3 repair was present, and it could not see that repair being
removed. **A census that parses the thing it censuses can be defeated by that thing's source layout,
silently, in the exact case it exists to detect.** Calling the gate's own function has no window to get
wrong — there is no second representation of the census left to disagree with the first. So mg-7db4's
regex fix is **superseded rather than reverted**, and its finding is quoted verbatim inside the new
`part_B` docstring, where it is the argument for the redesign.

Three checks, increasing in strength:

| | check | result |
|---|---|---|
| **B1** | every reference field is COMPARED or excluded-with-a-reason; stale exclusions and reasonless exclusions both fail | 22 compared, 1 excluded, **0 silent** |
| **B2** | for EACH field, perturb it alone and require the gate's own `_identity_row_ok` to go `False` | **22/22 fire** |
| **B3** | hand the comparison a reference row with a field name it has never seen | **compared automatically, and FAILS** (the row builder does not produce it) |

**B3 is the one that closes the class rather than the instances.** The failure mode of a hand-maintained
census is not "it is wrong today" — it is "someone adds a field to the mg-8b64 row and the census
silently keeps passing". B3 is that scenario, executed. And note which way it resolves: an *unrecomputed*
reference field is a **failure**, not a pass. Defaulting the other way is how F3 happened.

A new **part D** asks the same question of every other predicate: each of CONTROL B, CONTROL E and
CONTROL F is handed a row it must accept and a row it must reject — **10 probes, 10 agree**. The rows to
reject are not arbitrary; each is the signature of a mutation that has actually beaten this gate. This is
the part of a mutation demonstration that costs milliseconds, so it can run on every commit, which is the
difference between a control with a mechanism and a control with an instruction addressed to a future
reader.

Whole probe, uncontended on this host: **26.5 s**.

### 3.3 CONTROL F — the two-sided check now has real coverage

mg-5ad1 finding 4, recorded as a coverage observation: `dim_E = 1` at all five measured posets, so the
gate's `dim_eigenspace > 1 and |c_max − c_min| > 1e-9` branch is **vacuous on real data**, and mg-60d3's
F4 repair bought two-sided coverage on three *synthetic* antichains only.

The coverage was available and unused. The committed sweep has `dim_eigenspace = 2` at exactly four of
the 946 posets — `#52`, `#88`, `#209`, `#420` — and nowhere else; `#209/#420` measure identically to
`#52/#88`. So CONTROL F measures `#52` and `#88`:

| poset | `\|L\|` | `dim U` | `dim_E` | `c_max` | `c_min` | `\|c_max − c_min\|` |
|---|---|---|---|---|---|---|
| `enum-n7-#52` | 288 | 25 | **2** | `0.994818990` | `0.994818990` | `8.88e-16` |
| `enum-n7-#88` | 180 | 17 | **2** | `0.978492428` | `0.978492428` | `1.11e-16` |

`dim_E > 1` is **asserted**, not hoped for, so this control cannot quietly become the vacuous one it
replaces.

**And it can fail on real mutations, which is the part that makes it a control rather than a
decoration.** Measured directly, on the same two posets:

| | `#52` `dim U` | `#52` `\|c_max − c_min\|` | `#88` `dim U` | `#88` `\|c_max − c_min\|` |
|---|---|---|---|---|
| unmutated | 25 | `8.88e-16` | 17 | `1.11e-16` |
| **M2** (`U` shrunk by the element-0 and element-1 blocks) | 21 | **`7.58e-02`** | 15 | **`4.30e-02`** |
| **M4** (rank filter `s > 0.0`) | 49 | **`5.54e-04`** | 49 | **`1.37e-03`** |

Under M2, `c_max` survives at its unmutated value to nine decimals while `c_min` collapses — M2's exact
signature, now visible on **real posets** and not only on synthetic antichains. That is the coverage
mg-5ad1 finding 4 said mg-60d3 had not bought.

---

## §4 — ACCEPTANCE: does it fire, and does it fire on something unseen?

Route, and it is deliberately not the mg-60d3 demo's route (which reconstructs the gate in process and
monkeypatches loaded modules — reproducing that would have audited nothing). Following mg-5ad1's audit:
**one isolated tree per case**, holding a copy of `scripts/` plus the reference dataset the gate reads;
**one source-level edit** applied there with an **anchor-count assertion**, so a silent no-match is
impossible; the gate run in that tree. The pre-widening gate is the **real source** at `af7fc2df`
(mg-60d3's merge — the exact file mg-5ad1 measured M3 and M4 against), **pinned by SHA** rather than
derived from branch topology, so the left column does not silently become the widened gate once this
lands.

`scripts/onethird_mg75f0_gate_class_closure_demo.py`, eighteen full `--no-sweep` gate runs, ~13 min:

| mutation | one-line change | first used by | pre-widening gate | widened gate |
|---|---|---|---|---|
| — | unmutated | — | exit **0** | exit **0** |
| **M3** | `bk_frozen_pair`'s Theorem-E selector `min` → `max` | mg-5ad1 | exit **0** ← the residual | exit **1** |
| **M4** | `projector_U`'s rank filter `s > max(tol,1e-10)` → `s > 0.0` | mg-5ad1 | exit **0** ← the residual | exit **1** |
| **M5** | `bk_frozen_pair`'s MIN-PHI selector `min` → `max` | **UNSEEN** | exit **0** | exit **1** |
| **M6** | `transport_summary`'s prefix selector `min` → `max` | **UNSEEN** | exit **0** | exit **1** |
| **M7** | `_transport_label_cheeger`'s volume normalisation `min(r,n−r)` → `max(r,n−r)` | **UNSEEN** | exit **0** | exit **1** |
| **M8** | `bk_pair_cut`'s Bernoulli variance `p(1−p)` → `p` | **mg-7db4's row N1 — NOT chosen by this author** | exit **0** | exit **1** |
| **M9** | `_width`'s antichain search direction `range(n,0,−1)` → `range(1,n+1)` | **UNSEEN** | exit **0** | exit **1** |

The left column is what makes the right one mean anything: each mutation is shown to have been fatal to
nothing before, so `exit 1` is the widening firing and not a pre-existing control doing its job.

**But "fatal to nothing" has two forms, and this demonstration separates them** rather than reporting one
number. For every case it digests the pre-widening gate's **entire stdout** and compares it against the
unmutated pre-widening run:

| mutation | pre-widening stdout moved? | what that means |
|---|---|---|
| **M3** | **yes** | **EXERCISED AND ABSORBED.** The pre-widening gate computed a moved quantity, *printed* it, and exited 0. |
| **M4** | **yes** | EXERCISED AND ABSORBED. |
| **M8** | **yes** | EXERCISED AND ABSORBED. |
| **M5** | no | **NEVER EXERCISED.** Not one printed byte moved: the pre-widening gate did not reach the mutated code. |
| **M6** | no | NEVER EXERCISED. |
| **M7** | no | NEVER EXERCISED. |
| **M9** | no | NEVER EXERCISED. |

**This is the honest reading of the acceptance result and it is weaker than the raw 5-of-5.** Three
mutations (M3, M4, M8) are the class exactly as mg-5ad1 defined it — *"a quantity the document asserts,
computed by code the CI gate exercises, with no control that can fail"* — the gate computed the wrong
number, printed it, and passed. Four (M5, M6, M7, M9) are the class's weaker sibling: the quantity is
committed, the document asserts it, and the gate did not compute it at all. Both are blind spots the
widening closes, but only for the first three was the word *exercises* satisfied before.

**Which does not weaken the finding, and the reason is M8.** Of the three genuinely-exercised-and-absorbed
mutations, two (M3, M4) are the audit's own witnesses and one (M8) is mg-7db4's — so there is exactly one
row here that is *both* the class in its strict sense *and* not chosen by anyone who built the widening,
and it is caught. §4.3.

### 4.1 M3 and M4 — the two the audit exhibited

**M3** fails the identity check at **7 of 7** posets, and the gate names the moved fields in its failure
message:

| poset | mismatched fields (of the 22 compared) | count |
|---|---|---|
| `enum-n7-#3` | `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |
| `enum-n7-#20` | + `frozen_p` | 6 |
| `enum-n7-#600` | `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |
| `enum-n7-#945` | `frozen_p` `frozen_pair` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |
| `enum-n7-#809` | `frozen_p` `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 6 |
| `enum-n7-#52` | `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |
| `enum-n7-#88` | `frozen_pair` `frozen_phi_bk` `frozen_phi_t_image` `frozen_ratio` `frozen_sep_k` | 5 |

`max |diff|` over float fields goes from `0.00e+00` unmutated to `2.22e-01` at `#3`.

**Note what did *not* move**, printed by the gate in the same line: `num_LE=True lambda_std=True
delta=True lambda2_BK=True` — **all four fields the pre-widening gate compared**, at every one of the
seven posets. That is the residual, stated by the failure message itself.

**M4 moves no mg-8b64 reference field at all.** The identity check reports `mismatched: none` and
`max |diff| = 0.00e+00` at all seven posets, so **the widening is not what catches it.** This is the
worked example of §7.1: widening the identity comparison does not cover a mutation that moves no identity
field. Three independent controls fire:

| control | how it fires under M4 |
|---|---|
| **CONTROL E** — bound | `dim U = 49 > (n−1)²+1 = 37` at `#3`, `#20`, `#600` |
| **CONTROL E** — properness | `dim U = 21 = \|L\|` at `#945` and `25 = \|L\|` at `#809`, i.e. `null = 1.0000` — `U` is the whole function space and `c ≡ 1` is vacuous by §2's own criterion |
| **CONTROL B** — known rank | the antichains' `dim U` goes `10/17/26 → 16/25/36 = n²`, off the known `(n−1)²+1` |
| **CONTROL F** — two-sided | `\|c_max − c_min\|` at `#52`/`#88` splits to `5.54e-04`/`1.37e-03`, over the `1e-9` bar |

Five of five measured posets, three of three antichains, two of two CONTROL F posets. The pre-widening
gate reported no failure at all.

### 4.2 M5, M6, M7, M9 — the ones that decide whether the class is closed

These were chosen and written down **before** the widened gate was run against them, and none appears in
mg-60d3's demo or mg-5ad1's audit. They are deliberately not all the same shape: a widening that only
catches `min → max` in one function has not generalised.

- **M5** — `bk_frozen_pair`'s `minphi` selector `min` → `max`. This is the honest one, and the one to
  look at first: it is **M3's structural twin, one line down in the same function**. If the widening were
  a patch on its own witnesses, M5 is where that would show.

  Measured: pre-widening **exit 0, and not one printed byte moved**; widened gate **exit 1** at **6 of
  the 7** identity posets, on exactly `min_phi_bk`, `min_phi_bk_pair` and `minphi_phi_t_image` — three
  fields uncompared until mg-75f0 — with `num_LE`, `lambda_std`, `delta` and `bk_lambda2` all still
  `True`. `frozen_pair` is untouched, so the comparison that catches M3 is **not** what catches this.
  `max |diff|` reaches `1.11e-01`.

  **6 of 7, not 7 of 7, and that is worth stating.** At `enum-n7-#945` the argmax-`Φ` pair coincides with
  the argmin, so the flip is not a mutation there at all — the same phenomenon part C measures for the
  frozen-pair selector. One poset where a mutation is a no-op is coverage arithmetic, not a miss.
- **M6** — `transport_summary`'s expected-rank prefix selector `min` → `max`, so `phi_t_min_prefix`
  reports the *worst* transport prefix cut instead of the best. Different side of the probe: transport,
  not BK.

  Measured: pre-widening **exit 0**, widened **exit 1** at **7 of 7** posets, and its entire visible
  footprint is **one field of the 22** — `phi_t_min_prefix`, and nothing else, at every poset
  (`max |diff| = 3.70e-01`). This is the narrowest catch in the set and therefore useful evidence the
  widening is not a patch: there was no neighbourhood of related fields to stumble over, just the single
  one the mutation touched.
- **M7** — `_transport_label_cheeger`'s volume normalisation `min(r, n−r)` → `max(r, n−r)`. A
  **normalisation, not a selector**, so it is not the same edit shape as M3/M5/M6 at all. Pre-widening
  **exit 0**, widened **exit 1** at **7 of 7** posets on exactly one field, `phi_t_cheeger`
  (`max |diff| = 1.00e-01`).
- **M9** — `_width`'s antichain search direction `range(n, 0, −1)` → `range(1, n+1)`, so the max-antichain
  scan returns the *first* `r` admitting an antichain rather than the last and `width` collapses to `1` on
  every poset. Neither a selector nor a normalisation, and the only row here that touches **no spectral
  or transport quantity at all** — `width` is the parameter the whole width-3 programme is indexed by.

  Pre-widening **exit 0**, widened **exit 1** at **7 of 7** posets on exactly one field, `width`. **And
  `max |diff|` over float fields stays at `0.00e+00`**, because `width` is an integer compared exactly.
  That is the row which shows why §2's exact-comparison rule earns its keep: a comparison that only
  tracked float distances would have reported this mutation as a perfect match.

Spread of the evidence: 5–6 fields (M3), 3 fields at 6 of 7 posets (M5), exactly 1 field at 7 of 7 (M6,
M7, M9), across a selector, a normalisation, and a search direction, on the BK side and the transport
side and a purely combinatorial field. In all of them the printed `num_LE=True lambda_std=True
delta=True lambda2_BK=True` says, in the gate's own words, that the four fields it used to compare were
not the ones that moved.

**The weakness in this subsection, stated because a reader should not have to find it.** All four were
chosen by the author of the widening, and — per the stdout digest above — all four were **never
exercised** by the pre-widening gate. So what they establish is that the widening generalises across
edit shapes and across fields, not that it catches mutations the old gate had computed and absorbed. For
that, see M8.

### 4.3 M8 — the row this author did not choose, which is the one that counts

M5/M6/M7/M9 share a weakness that has to be said out loud rather than left for a reader to notice: **the
person who wrote the widening also chose them.** An author picks around the cases their own fix misses
without meaning to, so four-for-four from a single author is weaker evidence than the count suggests.
That is the same circularity mg-5ad1 identified in mg-60d3's repair, one level up — and being aware of it
is not the same as escaping it.

**M8 escapes it, on both axes at once.** `bk_pair_cut`'s Bernoulli variance `p(1−p) → p`, so Theorem E's
ratio `E(f_xy)/Var(f_xy)` is divided by the wrong variance. It is **mg-7db4's**, row `N1` of
`scripts/onethird_mg7db4_probe_mutation_battery.py`, written for a different instrument, for a different
purpose, by an author who had not seen this widening. It is the only row in the table selected by nobody
who built the thing under test — **and it is also one of the three the pre-widening gate genuinely
computed, printed, and absorbed.** So it is simultaneously the strict form of mg-5ad1's class and the row
free of author bias.

Measured: pre-widening **exit 0** with printed output demonstrably moved; widened **exit 1** at **7 of 7**
posets, on **7 fields** at six of them (`frozen_p`, `frozen_pair`, `frozen_phi_bk`, `frozen_phi_t_image`,
`frozen_ratio`, `frozen_sep_k`, `ratio_of_sums`) and 2 at `#945` (`frozen_ratio`, `ratio_of_sums`).
`max |diff| = 4.00e-01`. Note `ratio_of_sums` among them: a field no other mutation in this table moves.

**mg-7db4's own result on N1 is the stronger statement of the property, so it is recorded as mg-7db4's
and not as this document's.** Running N1 through GitHub Actions on a branch carrying nothing else,
mg-7db4 measured `Script controls` **failure**: the pre-existing mg-2c34 gate step **succeeded** — blind
to N1 — and the mg-5ad1 probe step **caught it**, via mg-5ad1's *original* part C comparison, written by
an author who had never seen that mutation. That is the only place in either ticket where **the guard
demonstrably predates the mutation**, which is the non-circular form of what both tickets were asked to
establish. mg-75f0 adds that the *widened gate* also catches N1; mg-7db4's is the cleaner claim.

**The bar the ticket set is met.** If any of these had passed, the correct report would have been "the
class is still open" — the demonstration is written so that outcome exits non-zero and says so in those
words, rather than being papered over.

---

## §5 — The AMBER: CONTROL B's justification (audit finding 3), docstring only

The docstring said:

> *"L(P) = S_n, the BK chain is the interchange process on the path, and by Aldous/CLR the slowest mode
> **IS** the single-particle mode, which lies in U."*

Aldous' spectral-gap conjecture, as proved by Caputo–Liggett–Richthammer, gives the gap **eigenvalue**:
`gap(interchange on the path) = gap(one-particle)`. `c_min = 1` is the strictly stronger claim that the
**whole gap eigenspace** lies in the one-particle sector, which additionally requires that no other
`S_n`-irrep component of the generator attains that eigenvalue. **CLR does not supply that.**

The control is **not wrong today** — the hazard is latent, verified 4-for-4 at `n = 4,5,6,7` (mg-5ad1
part A: `dim_E = n−1`, `1 − c_min ≤ 2.7e-15` against a `1e-8` assertion, nearest *excluded* eigenvalue
`3.0e7–1.1e8 × EIG_TOL` away). What was wrong was the *reason*, and an over-strong stated reason has a
predictable consequence: whoever extends the control to a larger antichain and hits a legitimate
cross-irrep coincidence will read "by Aldous/CLR this must hold", conclude the assertion is too tight,
and loosen it — at which point the repair is gone.

The docstring now cites Aldous/CLR **for the eigenvalue equality alone**, cites the eigenspace
containment as a **verified property of these specific matrices** with the measurements and the probe
that produces them, and states the consequence explicitly: if it ever fails on a larger antichain, narrow
the control's **population**, do not loosen the **assertion**. No behaviour changed.

**One diagnostic defect found while running M4 against the widened gate, and fixed.** CONTROL B's failure
message read *"antichain c != 1 (Aldous/CLR)"*. Under a broken rank filter `c` **is** exactly 1 and it is
`dim U` that has failed — so the message named the one conjunct that held, and cited a theorem that does
not license the assertion anyway. It now prints all three conjuncts for every failing row. A diagnostic
that misdirects the reader is the same genre of defect as a control that cannot fail.

---

## §6 — Wiring, and who owns which trigger

**mg-7db4 owns the trigger mechanism; mg-75f0 owns what is triggered.** mg-7db4 merged while this ticket
was between attempts, so mg-5ad1's finding 2 — *the proof-of-firing has no owner and no mechanism* — was
closed by mg-7db4 and **not** by this ticket. What it built, and what mg-75f0 added to it:

| tier | runs | on what | owner |
|---|---|---|---|
| **fast gate**, `script-controls.yml` | mg-8489, mg-8ff1, the **widened mg-2c34 gate** (45 s), the watchlist check, the **mg-5ad1 probe** parts A–D (26.5 s) | every commit under `scripts/`, `data/`, `docs/` | mechanism mg-7db4 / mg-4ad1; gate + probe parts B/D mg-75f0 |
| **blocking**, `scripts/refinery_gate.sh` via `.pogo/refinery.toml` | watchlist check, mg-5ad1 probe, **mg-60d3 demo** (~11 min) | merges touching any watched path | mg-7db4 |
| **informational**, `gate-mutation-demo.yml` | + mg-7db4 battery (~5 min), + **mg-75f0 closure demo** (~13 min) | pushes touching any watched path | mg-7db4's job; mg-75f0's step |

Four points recorded rather than left implicit:

- **`script-controls.yml` INFORMS; it does not BLOCK — mg-7db4's finding, not this document's.** `main`
  has no branch protection and no ruleset, and the refinery fast-forwards without reading GitHub check
  runs, so every step in that file reports and nothing stops a merge. That is the same shape as the
  defect this ticket exists to close, relocated to the enforcement layer: a control that fires into a
  check nobody consults is not distinguishable from a control that cannot fire. mg-7db4's refinery gate
  is the fix, and it already runs the probe blockingly. Nothing was left for mg-75f0 to add there.
- **The closure demo goes in the informational tier deliberately.** mg-7db4's split — *the blocking layer
  gets the cheap total check, the informational layer gets the expensive complete one* — is right, and it
  applies to this instrument at least as much as to mg-7db4's own. 11 minutes of blocking demonstration
  plus 13 more would make a gate-touching merge ~24 minutes and hold the refinery queue for every other
  author; a blocking gate long enough to invite bypass has a shorter life expectancy than the defect it
  guards. A proof *about* the checks is not a check on the change.
- **Adding it took the four edits mg-7db4's mechanism requires, in one commit**: the step, the path in
  both `paths:` lists, the same path in `WATCHED`, and the script in `ROOTS` in the watchlist check. The
  last is **enforced, not trusted**: a watched path reachable from nothing in `ROOTS` is rejected as
  *"watched but not part of the gate"*, and the converse too. Verified after the edit: watchlist
  consistent, 16 paths, import closure 10 modules, **5/5 self-test drifts CAUGHT**. The job's
  `timeout-minutes` went `45 → 75` in the same commit, so the bound tracks the work rather than lagging.
- **The fast gate's `timeout-minutes` is back to 10, and that correction is mg-75f0's own to make.** The
  `10 → 20` raise was carried on mg-75f0's reasoning — mg-7db4 landed it here only to avoid a conflict on
  the file, which was the right call — but the reasoning was wrong. It rested on a `2m33s` probe reading
  taken while a multi-gate demonstration was saturating the same host (mg-1b8c: concurrent heavy jobs here
  inflate each other by roughly 10×). Uncontended and measured for this document: the probe is **26.5 s**
  and the gate is **45 s**; mg-7db4 measured the whole workflow going `41–64 s → 1m12s` on a hosted
  runner. 10 minutes was never close to tight, and a bound loosened on a bad measurement is worse than
  one left alone — it stops being a wedge detector, which is the only thing a timeout on an
  order-seconds job is for.

**What mg-75f0 corrected in mg-7db4's merged artifacts**, at mg-7db4's explicit request in its own MR:

1. `docs/OneThird-mg7db4-GateDemo-Trigger.md` §3.1 *"M4 is caught by nothing"* — true of `main` when
   written, false once CONTROL E landed. Struck, with the reasoning kept because it was right, and with
   **the sting kept**: the identity widening does *not* catch M4, which is why CONTROL E had to exist
   separately. What survives is the narrower true statement — *the probe* is blind to M4.
2. The battery's **M4 row stays expected-exit-0** and is still correct, because it measures the *probe*,
   which never imports `projector_U`. Its docstring's *"caught by nothing here and nothing in
   `script-controls.yml`"* had its second half struck, plus a sentence saying expected-0 means *"the probe
   is blind"*, not *"the repo is blind"*.
3. Battery rows **N2 and N3 re-pointed** as their own notes instructed. N2's old anchor — the four-key
   `match_*` conjunction — dropped to **zero occurrences** and `apply_mutation` refused to run rather than
   reporting an untested blind spot. **That refusal is the mechanism working**, and it is the reason the
   re-pointing was safe to do mechanically. N2 now mutates `all(...)` → `any(...)`, which reverts the
   widening *wholesale* and which no census of "which fields are compared" can see, since all 22 still
   are. **N3's expectation moved `0 → 1`** because part D now catches it: coverage improved, and the
   battery's own rule is that a table which improves silently is a table that is wrong.
4. Two rows **added**, so the controls mg-75f0 introduced are held to the standard they inherited: **N6**
   (`frozen_pair` moved into the exclusion list with a plausible-sounding reason — M3 made green by
   *policy* rather than by mutation, which is the realistic way this defect returns) and **N7** (CONTROL
   E's properness clause dropped).

**One consequence for another merged artifact, stated plainly.** `apply_pre_repair_gate` in
`onethird_mg60d3_gate_mutation_demo.py` reconstructs the `87f0424` gate by substituting two predicates.
The gate has since acquired two more failure conditions, so without a change that function would
reconstruct "today's gate minus two predicates" rather than the gate mg-09ea measured, and the left
column of its 2×3 matrix would stop being a statement about the pre-repair gate. Two lines were added to
neutralise CONTROL E and CONTROL F in the reconstruction. **`EXPECTED` is unchanged, the 2×3 matrix is
unchanged, and ledger claim 27 is untouched** — the substitutions still live in the demonstration and not
in the gate, which has no switch that weakens it and must not acquire one.

---

## §7 — What is NOT closed, stated rather than implied

1. **The class is closed for the mg-8b64 identity surface and for `projector_U`'s rank — not for
   everything the gate touches.** Anything that moves *no* field of the committed reference row and *no*
   dimension of `U` is still covered only to the extent CONTROL A/B/C/D/F reach it. M4 is the worked
   example of that gap being real: it needed a purpose-built control, not the widening.
2. **A quantity the corpus computes but never COMMITS has no reference to be compared against**, and this
   mechanism cannot manufacture one. The widening's reach is exactly the set of fields
   `analyze_poset` writes into the committed dataset. That is the narrower residual which replaces
   mg-5ad1's "4 of 22", and it is the honest successor statement.
3. **Four of the five unseen mutations were never *exercised* by the pre-widening gate** (§4.2), so for
   those the widening's achievement is that the gate now runs mg-8b64's row builder at all, rather than
   that it now compares a number it previously computed wrongly. Only M3, M4 and M8 are mg-5ad1's class
   in its strict sense. This is measured in the committed JSON, not argued.
4. **CONTROL F's population is two posets, both `n = 7`.** It is real-data coverage where there was none,
   not broad coverage.
5. **`data/onethird-mg2c34-n7-overlap.json` was not regenerated.** The committed dataset predates the new
   per-field keys and the CONTROL F block, because regenerating it means a full sweep and the deliverable's
   §5/§6 tables are sourced from it. Nothing in this document depends on those keys being in the committed
   file; the gate writes them on any full run.
6. **`(n−1)²+1` is asserted as a bound, and verified rather than proved here.** The relation count `2n−2`
   is stated in the predicate's docstring and is the corpus's own; the assertion's licence in this
   document is the 985-row check plus exact saturation at `n = 4,5,6,7`.

---

## §8 — Reproduction

```bash
# the standing control, in CI (parts A-D)                                ~27 s
/usr/bin/python3 scripts/onethird_mg5ad1_gate_blindspot_probe.py

# the widened gate itself                                                ~45 s
/usr/bin/python3 scripts/onethird_mg2c34_n7_overlap_test.py --no-sweep

# the acceptance test: 18 gate runs, 7 mutations, 5 of them unseen        ~13 min
/usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py
/usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py --only M5,M6,M7,M9

# the probe's own mutation battery (mg-7db4), ten probe runs              ~5 min
/usr/bin/python3 scripts/onethird_mg7db4_probe_mutation_battery.py

# mg-60d3's 2x3 matrix, still exact after the widening                    ~11 min
/usr/bin/python3 scripts/onethird_mg60d3_gate_mutation_demo.py
```

`data/onethird-mg75f0-gate-class-closure.json` is the acceptance run's committed output;
`data/onethird-mg5ad1-gate-blindspot-probe.json` the probe's. Interpreter matters: bare `python3` on this
host has no numpy.

---

## §9 — Findings ledger

| # | finding | severity | site |
|---|---|---|---|
| **1** | **The identity comparison is now the whole row**: 22 of 23 fields, one exclusion with a stated reason, 0 silent. Iterating the committed row means a field ADDED to it is compared automatically — the defect one turn later is closed behaviourally, not by a list | **CLOSED** (audit finding 1) | §1, §2 |
| **2** | **The widened gate fires on 5 of 5 mutations that neither mg-60d3 nor mg-5ad1 used**, each fatal to nothing before it. M5 is M3's twin one line down; M6's and M7's entire footprint is 1 field of the 22; M7 is a normalisation, not a selector; M9 is a search direction in a purely combinatorial field; and **M8 was chosen by mg-7db4, not by the author of the widening** | **the acceptance result** | §4.2, §4.3 |
| **3** | **Only 3 of the 7 mutations were EXERCISED by the pre-widening gate** (M3, M4, M8 — the other four never reached the mutated code). Measured by digesting stdout, not asserted. This is a *weakening* of the raw 5-of-5 and is reported as such; M8 is the row that is both strict-class and author-independent | **honest scope** | §4, §7.3 |
| **4** | **CONTROL E**: `dim U ≤ (n−1)²+1` and `dim U < \|L\|`. Analytic, the corpus's own stated rank, 0 violations in 985 committed rows. Catches M4 at 5/5 measured posets, which the identity widening does **not** | **new control** | §3.1 |
| **5** | **CONTROL F**: the two-sided check now has real-data coverage (`#52`, `#88`, `dim_E = 2`), with non-vacuity asserted. It splits under M2 by `7.58e-02`/`4.30e-02` and under M4 by `5.54e-04`/`1.37e-03`, so the coverage is real and not decorative | **CLOSED** (audit finding 4, as a coverage gap) | §3.3 |
| **6** | **The probe's census comes from the gate's own comparison function, not from its source** — 22/22 fields fire when perturbed, an unseen field is picked up and fails, and part D proves every gate predicate can reject. The parsing route it replaces had a *measured* defect (mg-7db4's N2) | **strengthened** (audit finding 2's cheap half, wired by mg-7db4) | §3.2 |
| **7** | **CONTROL B's Aldous/CLR justification corrected**, docstring only, no behaviour change: CLR gives the gap eigenvalue; eigenspace containment is a verified property of these matrices, so a future failure narrows the *population* rather than loosening the *assertion* | **CLOSED** (audit finding 3, AMBER) | §5 |
| **8** | Every compared float field reproduces to `0.00e+00` at 7/7 posets against a `1e-9` tolerance — the widening introduces no tolerance risk. And non-float fields are compared exactly, which is what catches M9, whose float distance is `0.00e+00` | **note** | §2, §4.2 |
| **9** | **CONTROL B's failure message misattributed its own cause**, found by running M4 against the widened gate: it read *"antichain c != 1 (Aldous/CLR)"* while `c` was exactly 1 and `dim U` was what had failed. It now prints all three conjuncts per failing row | **fixed, found in flight** | §5 |
| **10** | mg-5ad1 finding 2 was **closed by mg-7db4**, not by this ticket. mg-7db4 owns the trigger, mg-75f0 owns what is triggered; the closure demo sits in the informational tier by mg-7db4's own cost split, and the fast gate's `timeout-minutes` is back to 10 on a corrected measurement | **ownership, stated** | §6 |
