# Forum-readiness validation pass — aggregate verdict (mg-5cd8)

**Audit date.** 2026-05-06.
**HEAD audited.** `0df0bc4` (`docs: root README — reflect
unconditional headline after Option-C Stage 2B (mg-0dd2)`).
**Audited by.** `cat-mg-5cd8` polecat.

## Aggregate verdict — **AMBER**

The forum-readiness validation pass is **AMBER, not RED**.
Substantively the formalization is forum-ready: the build is clean,
the axiom inventory is exactly what disposition B expects, and all
five `native_decide` invocations are faithful Bool encodings of
the math claims they support. The AMBER comes entirely from a
**doc-drift** issue (per `mg-5cd8` trip-wire 5): two of the four
forum-disclosure documents
(`docs/lean-forum-publication-readiness.md` and
`docs/lean-forum-post-template.md`) were last touched on 2026-05-04
and frame the headline as carrying an `hC3 : Step8.Case3Witness`
Prop-level hypothesis. After Option-C Stage 2B (`mg-8c72`,
2026-05-05), `hC3` was discharged as a theorem, the public headline
is now unconditional, and these two docs need a refresh before
forum send.

**Path to GREEN.** A single small PM-filed doc-refresh ticket
(scope outlined in [`doc-consistency.md`](doc-consistency.md) §
"Recommended PM follow-on ticket") flips this verdict to GREEN.
No Lean source changes are needed.

## Per-validation summary

| Validation | Verdict | Notes |
|---|---|---|
| **A — Fresh-clone build** | **GREEN** | 1409 lake jobs, 552 s build wall (632 s including clone + cache get); zero errors; 5 style/deprecation warnings (non-blocking); fresh-build `#print axioms` matches `lean/PRINT_AXIOMS_OUTPUT.txt` byte-for-byte. See [`build-verification.md`](build-verification.md). |
| **B — `native_decide` audits** | **GREEN** | All 5 invocations (`case3_balanced_w{1,2,3,4}` + `case2_certificate`) are faithful: Bool predicates encode exactly the math claims, parameter ranges `(1,9), (2,7), (3,7), (4,7)` for Case 3 / `(1,6)` for Case 2 cover the F5a / Stage-1 sub-case bounds, Bool→Prop bridges close cleanly via the per-mask iteration theorem + band-major OrderIso transport, no Bool-predicate-vs-math mismatch. See [`native-decide-audit.md`](native-decide-audit.md). |
| **C — Axiom inventory** | **GREEN** | Live `#print axioms width3_one_third_two_thirds` (run on the fresh-clone build) matches the disposition-B-amendment expectation modulo cosmetic `Lean.ofReduceBool` expansion (5 individual `_native.native_decide.ax_1_1` instances). `case3Witness_hasBalancedPair_outOfScope` STAYS as specified. No new project axioms. Zero `sorry`/`admit`. The headline is unconditional after Stage 2B; trust surface unchanged. See [`axiom-inventory-verification.md`](axiom-inventory-verification.md). |
| **D — Documentation consistency** | **AMBER** | `README.md` (root) and `lean/README.md` are current (post-Stage-2B). `lean/AXIOMS.md` is faithful on its core scope (named project axioms) with one minor polish item (Forum-post disclosure subsection lacks a sentence noting the `_native.native_decide` entries). `docs/lean-forum-publication-readiness.md` and `docs/lean-forum-post-template.md` are pre-Stage-2B and reference the now-discharged `hC3` hypothesis throughout — substantive disclosure drift per trip-wire 5. See [`doc-consistency.md`](doc-consistency.md). |

## Trip-wire status

Per `mg-5cd8` ticket "Trip-wires":

| # | Trip-wire | Status |
|---|---|---|
| 1 | Build fails at HEAD | **CLEAR** — fresh-clone build returns 0, 1409/1409 jobs succeed |
| 2 | `case3Witness_hasBalancedPair_outOfScope` STILL present (disposition B says it stays) | **CLEAR — present as expected.** The disposition-B amendment specifies the axiom STAYS; the live `#print axioms` confirms it is in the headline closure. |
| 3 | NEW project axiom not on the expected list | **CLEAR** — `grep -rE '^\s*axiom\s+'` confirms exactly two project axioms (`brightwell_sharp_centred` + `case3Witness_hasBalancedPair_outOfScope`), both expected |
| 4 | `native_decide` Bool-predicate-vs-math mismatch (mg-a79e pattern) | **CLEAR** — all 5 invocations audited; Bool encodings match math claims |
| 5 | Doc drift surfaces a substantive disclosure issue | **TRIGGERED, AMBER** — two pre-Stage-2B disclosure docs reference `hC3` as an active headline hypothesis |
| 6 | Token overrun > 450k (150% of 300k cap) | **CLEAR** — well under cap |

## Disposition-B amendment note (sub-case interpretation)

The `mg-5cd8` ticket carries a "DISPOSITION B AMENDMENT (2026-05-06)"
clarifying that the case3 axiom port is deferred indefinitely. The
amendment-specified expected inventory:

```
[propext, Classical.choice, Quot.sound,
 brightwell_sharp_centred,
 case3Witness_hasBalancedPair_outOfScope,  ← STAYS, honestly disclosed
 Lean.ofReduceBool]
```

The actual current main HEAD inventory expands `Lean.ofReduceBool`
into 5 per-`native_decide` instances, but the **trust surface is
identical** — each `_native.native_decide.ax_1_1` axiom is an
instance of `Lean.ofReduceBool`. The disposition-B intent is
therefore satisfied: the axiom STAYS, no new project axioms have
been added, and the headline-closure `#print axioms` carries
exactly the expected six trust line items (mathlib trio +
Brightwell + outOfScope + compiler-trust for `native_decide`).

The disposition-B-amendment text was prepared on 2026-05-06 and
appears to assume the headline still carries `hC3`. The actual
current state (post-Stage-2B `mg-8c72`, 2026-05-05) is **strictly
stronger**: the headline is unconditional, while the trust surface
remains the same. This is a substantive improvement, not a
regression.

## Forum-readiness recommendation

Substantively, **the formalization is forum-ready**. The
structural argument, the residual axioms, and the computational
certificates are all in their final state, faithfully audited, and
honestly disclosed at the per-axiom level. The build is
reproducible from a clean clone in ~10 minutes after cache get on
Apple Silicon.

**Required before forum send.** Refresh
`docs/lean-forum-publication-readiness.md` and
`docs/lean-forum-post-template.md` to reflect the post-Stage-2B
unconditional headline and the corresponding shift in trust
surface from "`hC3` parked" to "`outOfScope` axiom retained,
honestly disclosed, replacement deferred indefinitely per
disposition B." This is a single PM-filed doc-refresh ticket
(~150-300 lines of doc edits across two files plus a minor
`lean/AXIOMS.md` polish item); the substantive content of these
docs (the F3 obstruction discussion, the cleanup-track audits, the
A8-S2-cont infrastructure framing) all remains accurate and
should be preserved.

**Not required before forum send (but recommended for polish).**
Single small ticket for the 5 style / deprecation warnings
(`push_neg` migration to `push Not`; `show` → `change` cleanup;
remove unused `hNonempty`). These do not affect correctness, the
trust footprint, or the headline closure; the forum post can
either include them as expected innocuous warnings or treat them
as a follow-on polish item.

**Daniel-side decision point.** The `mg-fb16` unhold question
("can we send the forum post yet?") is now substantively
unblocked — the validation pass returns AMBER on doc consistency
only. PM should surface the doc-refresh follow-on to Daniel
together with the unhold decision; Daniel can then either (i)
greenlight the doc refresh + send the forum post, or (ii) hold
the forum post pending some other unrelated decision and the
doc refresh becomes opportunistic.

## Cross-references

* `build-verification.md` — Validation A.
* `native-decide-audit.md` — Validation B.
* `axiom-inventory-verification.md` — Validation C.
* `doc-consistency.md` — Validation D.
* `mg-5cd8` ticket text (this directory's parent ticket).
* `lean/PRINT_AXIOMS_OUTPUT.txt` — committed baseline (matches
  fresh build).
* `lean/AXIOMS.md` — named project axioms catalog (faithful).
* Stage 2B closure: `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean`,
  commit `16d26ef` (`mg-8c72`).
