# Axiom inventory verification (Validation C, mg-5cd8)

**Audit date.** 2026-05-06.
**HEAD audited.** `0df0bc4` (`docs: root README — reflect
unconditional headline after Option-C Stage 2B (mg-0dd2)`).
**Audited by.** `cat-mg-5cd8` polecat (forum-readiness validation
pass; ticket text and protocol per `mg-5cd8`).
**Verdict.** **GREEN.** The axiom inventory at current main HEAD
matches the disposition-B-amendment expectation, modulo a
cosmetic `#print axioms` rendering difference (5 individual
`_native.native_decide.ax_1_1` instances vs. a single rolled-up
`Lean.ofReduceBool` — same trust surface). No new project axioms
have been introduced since `mg-b846`/`mg-b699`. Zero `sorry`. Zero
`admit`. The headline `OneThird.width3_one_third_two_thirds` is
**unconditional** (no `hC3` hypothesis) after Option-C Stage 2B
(`mg-8c72`).

## Disposition-B-amendment expected inventory

Per `mg-5cd8` ticket "DISPOSITION B AMENDMENT (2026-05-06)" and the
`pm-onethird` mail 1778024525633630000:

> Forum-readiness validation must verify the CURRENT main HEAD
> state, NOT the hypothetical post-port state.
>
> Updated expected axiom inventory for `#print axioms
> width3_one_third_two_thirds`:
> ```
> [propext, Classical.choice, Quot.sound,
>  brightwell_sharp_centred,
>  case3Witness_hasBalancedPair_outOfScope,  ← STAYS, honestly disclosed
>  Lean.ofReduceBool]
> ```
>
> Validation C passes if all 6 are present and no NEW project
> axioms have been added.

## Actual inventory at HEAD (`0df0bc4`)

`lean/PRINT_AXIOMS_OUTPUT.txt` (last touched by Option-C Stage 2B
commit `16d26ef`, 2026-05-05):

```text
'OneThird.width3_one_third_two_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OneThird.LinearExt.brightwell_sharp_centred,
 OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope,
 OneThird.Step8.Case3Enum.case3_balanced_w1._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_w2._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_w3._native.native_decide.ax_1_1,
 OneThird.Step8.Case3Enum.case3_balanced_w4._native.native_decide.ax_1_1,
 OneThird.Step8.OptionC.case2_certificate._native.native_decide.ax_1_1]
```

The Stage 2B commit message (commit `16d26ef`,
"lean+docs: Option-C Stage 2B — Candidate A'' tightening +
Case3Witness_proof + drops hC3 (mg-8c72)") declares this same set
verbatim:

> `#print axioms width3_one_third_two_thirds` =
> `[propext, Classical.choice, Quot.sound, brightwell_sharp_centred,
> case3Witness_hasBalancedPair_outOfScope,
> case3_balanced_w{1..4}._native.native_decide.ax_1_1,
> case2_certificate._native.native_decide.ax_1_1]`. **No new project
> axioms introduced**; the existing
> `case3Witness_hasBalancedPair_outOfScope` axiom (mg-b846) and the
> five `_native.native_decide` instances of `Lean.ofReduceBool` are
> now transitively reachable from the unconditional headline
> (previously hidden behind the `hC3` hypothesis).

## Match analysis

The disposition-B-amendment spec lists 6 entries; the actual
`#print axioms` output expands to 10 entries. The expansion is
purely cosmetic — every `<def>._native.native_decide.ax_1_1` is an
**instance of `Lean.ofReduceBool`**, the standard compiler-trust
axiom for `native_decide`. Lean 4.29 prints these as separate
named axioms (one per `native_decide` invocation), but they share
the same underlying trust assumption: that the compiled native
code's `Bool` evaluation matches the Lean kernel's reduction.

Mapping:

| Disposition-B entry | Actual `#print axioms` entry | Same? |
|---|---|---|
| `propext` | `propext` | ✓ identical |
| `Classical.choice` | `Classical.choice` | ✓ identical |
| `Quot.sound` | `Quot.sound` | ✓ identical |
| `brightwell_sharp_centred` | `OneThird.LinearExt.brightwell_sharp_centred` | ✓ same axiom (full-qualified vs. short name) |
| `case3Witness_hasBalancedPair_outOfScope` | `OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope` | ✓ same axiom |
| `Lean.ofReduceBool` | `case3_balanced_w{1..4}._native.native_decide.ax_1_1` (×4) + `case2_certificate._native.native_decide.ax_1_1` (×1) | ✓ same trust surface (5 instances of `Lean.ofReduceBool`) |

**Trust surface match.** ✅ The five `native_decide` invocations
introduce exactly one underlying compiler axiom (`Lean.ofReduceBool`);
their per-invocation expansion in `#print axioms` does not add
trust beyond what disposition B's "Lean.ofReduceBool" entry
captures.

**`case3Witness_hasBalancedPair_outOfScope` STAYS.** ✅
(`Case3Residual.lean:208`, axiom declaration intact.)

**No NEW project axioms.** ✅ Direct verification:

```
$ grep -rnE '^\s*axiom\s+[A-Za-z_]' lean/OneThird /lean/OneThird.lean
lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159:
  axiom brightwell_sharp_centred
lean/OneThird/Step8/Case3Residual.lean:208:
  axiom case3Witness_hasBalancedPair_outOfScope
```

Exactly the two expected project axioms; no others. (The
`Case3Residual.lean:57` and `:226` matches in a coarser search are
docstring references inside the existing axiom's surrounding
documentation, not declarations.)

**Zero `sorry` / zero `admit`.** ✅ A `git grep -nE '\bsorry\b|\badmit\b'
lean/` returns only docstring / comment references (e.g.
`MainAssembly.lean:77` reading "discharges the `sorry` of …" inside
a doc-comment). A stricter search for proof-term occurrences

```
grep -rnE ':=.*\bsorry\b|by\s+sorry\b|^\s*sorry\b|\bexact\s+sorry\b|by\s+admit\b'
```

returns no matches.

## Headline shape change since the disposition-B-amendment text was written

The disposition-B-amendment text in `mg-5cd8` was prepared on
2026-05-06 and assumes the headline still carries `hC3` as a
Prop-level hypothesis (per the `lean-forum-publication-readiness.md`
and `lean-forum-post-template.md` framing as of `mg-457c`).

**Current state (`0df0bc4`, post-Stage-2B `mg-8c72`):** the headline
is **unconditional** (no `hC3`):

```lean
-- lean/OneThird/MainTheorem.lean (current)
theorem width3_one_third_two_thirds.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α) :
    HasBalancedPair α
```

The `hC3 : Step8.Case3Witness.{u}` hypothesis was discharged by
Stage 2B's `OptionC.Case3Witness_proof` (a strong induction on
`Fintype.card β` with K-dispatch, see
`OptionC/Case3WitnessProof.lean:231-499`). The discharge consumes
the existing `case3Witness_hasBalancedPair_outOfScope` axiom plus
the five `native_decide` certificates plus the Brightwell axiom —
so the **trust surface is unchanged**, only the public signature
has tightened.

This is a **substantive improvement** over the disposition-B
amendment's framing — the headline is now strictly stronger (drops
a hypothesis) without any new trust assumption — but it does mean
some pre-Stage-2B disclosure documents
(`docs/lean-forum-publication-readiness.md`,
`docs/lean-forum-post-template.md`) describe the headline shape as
hC3-gated, which is now stale. **This drift is recorded under
Validation D**; it does not affect Validation C's GREEN verdict.

## Cross-references

* Headline theorem: `lean/OneThird/MainTheorem.lean`.
* Stage 2B closure: `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean`,
  commit `16d26ef`.
* Project axioms:
  - `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159`
    (`brightwell_sharp_centred`) — `mg-b699` decision: retained
    as transcription of Brightwell 1999 §4 + Kahn–Saks 1984.
  - `lean/OneThird/Step8/Case3Residual.lean:208`
    (`case3Witness_hasBalancedPair_outOfScope`) — `mg-b846`,
    QA-audited `mg-7377`; per `mg-5cd8` disposition-B amendment,
    port deferred indefinitely.
* Compiler-trust axiom: `Lean.ofReduceBool` (5 `native_decide`
  instances, audited per-invocation in `native-decide-audit.md`).
* Inventory snapshot: `lean/PRINT_AXIOMS_OUTPUT.txt`.
* Existing disclosure: `lean/AXIOMS.md` (entries for both project
  axioms).

## Verdict

**GREEN.** The current main HEAD axiom inventory of
`OneThird.width3_one_third_two_thirds` matches the
disposition-B-amendment expectation (modulo cosmetic
`Lean.ofReduceBool` expansion). No NEW project axioms have been
added; `case3Witness_hasBalancedPair_outOfScope` STAYS as
specified; zero `sorry`/`admit`. The headline is now unconditional
(Stage 2B `mg-8c72`); trust surface unchanged.
