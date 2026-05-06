# Fresh-clone build verification (Validation A, mg-5cd8)

**Audit date.** 2026-05-06.
**HEAD audited.** `0df0bc4` (`docs: root README — reflect
unconditional headline after Option-C Stage 2B (mg-0dd2)`).
**Audited by.** `cat-mg-5cd8` polecat (forum-readiness validation
pass; ticket text and protocol per `mg-5cd8`).
**Verdict.** **GREEN.** A clean fresh clone of
`drellem2/one_third_width_three` builds end-to-end on Lean 4.29.1
with mathlib cache from
`leanprover-community/mathlib4`. Build completes in **552 s**
(~9.2 min) after `lake exe cache get` (78 s); total wall
including clone is **632 s** (~10.5 min). All 1409 lake jobs
succeed with exit code 0; 5 style-linter warnings observed but no
`error` lines.

## Procedure

```sh
git clone https://github.com/drellem2/one_third_width_three.git \
    /tmp/lean-fresh-validation
cd /tmp/lean-fresh-validation/lean
cat lean-toolchain                  # leanprover/lean4:v4.29.1
lean --version                       # 4.29.1, arm64-apple-darwin24.6.0
lake exe cache get                   # mathlib cache (8229 files)
lake build OneThird                  # full build of 1409 targets
lake env lean scripts/PrintAxiomsAudit.lean
```

All commands run from a clean tmpdir (`/tmp/lean-fresh-validation`)
with no shared `.lake` state from the polecat's source repo;
`PATH="$HOME/.elan/bin:$PATH"` for `elan`-managed `lean` /
`lake` binaries.

## Environment

| Field | Value |
|---|---|
| Host | macOS Darwin 24.6.0 (arm64) |
| Lean toolchain | `leanprover/lean4:v4.29.1` (per `lean-toolchain`) |
| Lean version | `Lean (version 4.29.1, arm64-apple-darwin24.6.0, commit f72c35b3f637c8c6571d353742168ab66cc22c00, Release)` |
| Lake version | `Lake version 5.0.0-src+f72c35b (Lean version 4.29.1)` |
| Mathlib cache origin | `leanprover-community/mathlib4` (Azure cloud release) |
| Cache size | 8229 files; 3 already-decompressed (toolchain match), 8226 newly decompressed |
| Audit start | 2026-05-05T23:50:08Z |
| Audit end | 2026-05-06T00:00:40Z |

## Results

### Clone

| Metric | Value |
|---|---|
| `git clone` exit | 0 |
| `git clone` wall | 1 s |
| Cloned HEAD | `0df0bc405c797e06572b51040e7396e1d5f50c70` |

The cloned HEAD matches the local polecat worktree HEAD
(`0df0bc4`) and `origin/main` (`git ls-remote
https://github.com/drellem2/one_third_width_three.git
refs/heads/main` returns the same SHA).

### `lake exe cache get`

| Metric | Value |
|---|---|
| Wall time | 78 s |
| Result | `Completed successfully!` |
| Files decompressed | 8229 / 8229 (3 already up-to-date, 8226 newly decompressed in 9241 ms) |
| Files downloaded | 0 (all from local mathlib4 cache) |

### `lake build OneThird`

| Metric | Value |
|---|---|
| Lake jobs | 1409 |
| Successful builds | 1409 / 1409 |
| Build wall time | 552 s (~9.2 min) |
| Total wall (clone + cache + build) | 632 s (~10.5 min) |
| `error` lines | **0** |
| Final tail line | `Build completed successfully (1409 jobs).` |
| Final two olean targets | `[1407/1409] Built OneThird.MainTheorem (1.9s)`, `[1408/1409] Built OneThird (1.8s)` |

**Note on wall time.** The ticket's "~3-5 min" estimate predates
Option-C Stage 2B's expansion of the headline transitive closure
to include `OptionC.Case3WitnessProof` and the Stage-2A
`LayeredDecomposition.Compactify` infrastructure. The single
slowest target is `OneThird.Step8.Case3Enum.W1` (the `w = 1, |Q| ≤
9` Bool certificate, ~344243 enumerated configurations after the
filter cascade), whose `native_decide` evaluation accounts for
roughly 7-8 minutes of the build wall. This is consistent with
the Python ground-truth enumerator's `~13 s` for the same slice
(Python is interpreted but uses native bigint operations
directly; Lean `native_decide` runs through compiled `Id.run do`
foldl over `1 << nfree` masks, which is constant-factor slower).
**Forum-post template should set the wall-time expectation
accordingly** (suggested: "build completes in ~10-15 minutes after
cache get on Apple Silicon").

### Warnings (non-blocking)

5 style / deprecation warnings from `lake build` (no errors):

| File:line | Type | Message |
|---|---|---|
| `OneThird/Step8/Case2Rotation.lean:382:2` | deprecation | `push_neg` has been deprecated. Prefer using `push Not` instead. |
| `OneThird/Step8/BipartiteEnumGeneral.lean:116:6, 130:6` | style.show | The `show` tactic should only be used to indicate intermediate goal states for readability. |
| `OneThird/Step8/OptionC/Case3WitnessProof.lean:110:5` | unusedVariables | unused variable `hNonempty` |
| `OneThird/Step8/OptionC/Case3WitnessProof.lean:282:10, 469:10` | deprecation | `push_neg` has been deprecated. Prefer using `push Not` instead. |
| `OneThird/Step8/OptionC/Case3WitnessProof.lean:352:14, 484:14` | style.show | The `show` tactic should only be used to indicate intermediate goal states for readability. |

These are **upstream Lean / Mathlib deprecations and style
linter notices** introduced in recent Lean releases; they affect
code style, not correctness. None of them block the build, none
of them touch the proof's trust footprint, and none of them appear
in the headline transitive closure's `#print axioms` output. They
**should be cleaned up at some point** for a polished forum
post (or annotated in the post template as expected innocuous
warnings), but they are non-blocking for the validation pass and
out of scope for `mg-5cd8`. Recommended PM follow-on item:
single small ticket for `push_neg` migration + `show` →
`change` cleanup + remove unused `hNonempty`.

### `#print axioms` cross-check

Run on the fresh build:

```sh
lake env lean scripts/PrintAxiomsAudit.lean > /tmp/fresh-axioms.txt
diff /tmp/fresh-axioms.txt lean/PRINT_AXIOMS_OUTPUT.txt
```

**Result.** `diff` reports zero output (rc=0) — the fresh build's
`#print axioms` output matches `lean/PRINT_AXIOMS_OUTPUT.txt`
**byte-for-byte**.

The matched headline inventory:

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

This is the **live confirmation** for Validation C: the axiom
inventory is what the in-tree baseline file claims, the disposition-B
amendment expectations are met, and `case3Witness_hasBalancedPair_outOfScope`
is present in the headline closure as expected.

The `#print axioms` audit also confirms the secondary inventory
checkpoints (`width3_one_third_two_thirds_assembled`,
`width3_one_third_two_thirds_via_step8`, `mainAssembly`, etc.) are
unchanged from the committed baseline.

## Verdict

**GREEN.** The proof builds cleanly from a fresh clone using
mathlib cache, completes in 632 s wall, and the resulting `#print
axioms` matches the committed baseline exactly. No errors, no
sorrys, no admits, no surprises.

The 5 style/deprecation warnings are non-blocking and recommended
as a small PM follow-on cleanup ticket; they do not affect the
forum-post readiness verdict.

## Cross-references

* Build log: `/tmp/fresh-build.log` (full transcript with timestamps).
* `#print axioms` output: `/tmp/fresh-axioms.txt` (== `lean/PRINT_AXIOMS_OUTPUT.txt`).
* Audit script: `lean/scripts/PrintAxiomsAudit.lean`.
* Lean toolchain: `lean/lean-toolchain`.
* Mathlib cache origin: `leanprover-community/mathlib4` (Azure cloud release).
