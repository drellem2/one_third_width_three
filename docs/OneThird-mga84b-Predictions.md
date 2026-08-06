# mg-a84b — PRE-REGISTERED PREDICTIONS

Committed **before any audit code exists**. Written from three inputs only: the
`mg show mg-a84b` brief, the dispatch body, and the commit message + diff of
`41ef4ee` (the mg-ba2a repair). No control has been run, no grep for the digest
class has been issued, no Actions run has been read.

Everything below is falsifiable and names the instrument that would falsify it.
Where a number appears I also name the POPULATION and the GRAIN I expect it to
be over, because the audit is required to and a prediction that does not is
unscoreable.

## Framing I am inheriting, and whose it is

The dispatch retracts pm-onethird's original diagnosis (ROTTED PIN) and replaces
it with pm-onethird's own corrected one: the 22-character literal is the tail of
a line-wrapped sha256 digest. **That corrected diagnosis is still the parent's,
not mine.** Predictions P1, P8, P9, P11 are re-derivations of parent numbers and
are marked as such. I have not verified any of them at the time of writing.

The reasoning error named in the dispatch — excluding one branch of a two-branch
disjunction does not establish the other, and both branches shared a false
unstated premise — is the standard I am holding the repair to, and it is also a
standard I can fail myself. P5 and P13 are where I expect to be at risk of it.

---

### P1 — main is green, and green because of this commit

- **P1a** The `script-controls.yml` run on `main` at or after `41ef4ee`
  concludes `success`. *(parent's claim, re-derived)*
- **P1b** The same workflow concluded `failure` on `fc8115d` (the commit
  immediately before the repair).
- **P1c** The green is attributable: the step that failed on `fc8115d` is the
  one that runs `onethird_mg3934_ci_history_depth_control.py`, and that same
  step RAN and passed on `41ef4ee`. **I predict it is not green because a step
  was skipped, a matrix leg was dropped, a `continue-on-error` was added, or the
  workflow file changed.**
- **Instrument:** `gh run list --branch main --workflow script-controls.yml`,
  then `gh run view <id> --log` for the step-level record on both commits. A log
  that shows the step *present and passing* is the only thing that can
  distinguish P1c from "green for another reason"; a run-level `success` alone
  cannot, and I will say so if the log is unavailable.
- **P1d** `41ef4ee` touches no file under `.github/`. *(mechanical; `git show
  --stat` already suggests this, so this one is nearly free and I score it as
  such.)*

### P2 — the repair is against the actual defect, not the asserted one

- **P2a** `scripts/onethird_mg76d0_partial_report_audit.py` is **unmodified** by
  `41ef4ee`. A repair written against "rotted pin" would have re-pointed or
  deleted that literal; a repair written against "wrapped digest" leaves the
  subject alone and fixes the reader.
- **P2b** Checking out the **pre-repair** control (`fc8115d` version) and running
  it against the **current** tree reproduces exit 1 naming the 22-character
  literal. The post-repair control against the same tree exits 0.
- **P2c** The delta between those two runs is exactly the one literal — no other
  finding appears or disappears.
- **Instrument:** `git show fc8115d:scripts/onethird_mg3934_ci_history_depth_control.py`
  into a scratch path, run both against the worktree, diff the outputs.

### P3 — the defect is a CLASS; the class is bigger than one

- **P3a** The pattern "a 64-hex-character sha256 digest split across two or more
  adjacent Python string literals" occurs in **more than one file** under
  `scripts/`.
- **P3b** Population/grain I will report: *occurrences* (grain = one joined
  64-hex literal) over the population *all `.py` files in `scripts/` at
  `41ef4ee`*. I predict that count is **≥ 3 and ≤ 40**.
- **P3c** Only a strict subset of those files also mentions `git`, and it is
  that subset that (B) could ever have tripped on. I predict that subset has
  **exactly 1** member before the repair — `onethird_mg76d0_partial_report_audit.py`
  — which is why exactly one instance went red rather than nine.
- **P3d** Therefore: **the repair does fix the class, not the instance**, because
  it changed the reader rather than the one file. But P3c is the load-bearing
  check — if the git-mentioning subset has more than one member and only one
  fired, my model of the mechanism is wrong and I must say so.
- **Instrument:** a scanner that joins adjacent literals and reports every joined
  run whose text is 64 hex characters, plus, separately, every joined run of
  ANY length ≥ 41 hex characters (the superset — a digest that is not sha256, a
  128-char sha512, a truncated hash). Reporting only 64 would be an instrument
  that cannot show the positive it is looking for.

### P4 — the join has residual holes, and I predict which ones

`_ADJACENT_LITERAL_RE` is `([\"'])([^\"'\\\n]*)\1\s*([\"'])([^\"'\\\n]*)\3`.
Reading it alone, before running anything, I predict it does **not** join:

- **P4a** literals carrying a prefix — `f"..."`, `r"..."`, `b"..."`, `rb"..."` —
  because after the first closing quote the pattern allows only `\s*` before the
  next quote, and a prefix letter is not whitespace. **A wrapped digest whose
  second fragment is prefixed still leaks a 7–40 tail.**
- **P4b** literals containing a backslash escape (excluded by the character
  class), and triple-quoted strings (the inner `""` of `"""` matches as an
  empty literal and the join will mangle rather than concatenate them).
- **P4c** fragments separated by a `\`-continuation or by a comment between them.
- **P4d** the join is applied to the **whole source text including comments and
  docstrings**, so prose containing two adjacent quoted words is silently
  concatenated. I predict this produces **no new false positive on the current
  tree** (it would need to yield 7–40 hex characters), but that it is an
  unbounded exposure rather than a bounded one, and the control does not say so.
- **P4e** I predict the repair's own docstring/comment does **not** enumerate
  P4a. (It does state the escape/triple-quote exclusion — I have read that — so
  P4b is already disclosed and I score it as disclosed, not as a finding.)
- **Instrument:** construct each shape as a fixture, feed it to the shipped
  `revs_in()`, and check whether the tail survives the window. A prediction of
  "still leaks" that I test only by reading the regex is not tested.

### P5 — the disjunction is probably still not exhaustive

This is the one the dispatch says matters most, and the one where I am most
likely to repeat the parent's error in reverse (concluding "still broken"
because I did not find the fix rather than because I found its absence).

- **P5a** The (B) failure message still offers the reader a **two-branch**
  choice — shallow clone or rotted pin — with no third branch for "this literal
  is not a revision at all".
- **P5b** However, I predict the repair makes the disjunction **sound where it
  is now reachable**: the join removes the population that made the third branch
  necessary, so a literal that reaches (B) after the repair genuinely is a
  7–40-char hex string in a git-calling file. The disjunction can still be
  non-exhaustive (a 7–40 hex string can be a truncated digest, a test fixture, a
  blob/tree object rather than a commit, an object in another repo) — so I
  predict **the message is still wrong, but less often reached wrongly**.
- **P5c** I predict I will find at least one concrete non-exhaustive residual:
  **a hex literal naming a git object that is not a commit** (blob or tree).
  `git cat-file -t` distinguishes these and `git rev-parse --verify` does not
  cleanly; if the control uses a commit-shaped resolver on a blob it will print
  "rotted" for an object that exists.
- **Instrument:** read the exact message string in the shipped control; then
  construct a literal in each residual category and observe what the control
  prints. A negative here ("the disjunction is fine now") is only reportable if
  I built a case it should have mis-called and it did not.

### P6 — the parent's self-test cases are real instruments

- **P6a** Case 8 (`_WRAPPED_DIGEST_SRC`) **fails** against the pre-repair
  `revs_in()` and passes against the post-repair one. *(parent's claim,
  re-derived — this is the "RED before" the parent asserts.)*
- **P6b** Case 9 (`_WRAPPED_REV_SRC`, a real 40-char rev wrapped 20+20) passes
  **both** before and after. *(parent's claim.)* If case 9 also passed before
  *trivially* — i.e. for a reason unrelated to the join, such as the 20-char
  fragments already landing in the 7–40 window — then it is a weaker
  anti-blind-spot guard than the commit message implies, and I predict **that is
  exactly what is going on**: 20 is inside 7–40, so the un-joined reading finds
  it too. Case 9 would then pass before the fix for the wrong reason and after
  the fix for the right one, and cannot distinguish them.
- **Instrument:** run the shipped `_selftest()` with `join_implicit_concat`
  monkey-patched to the identity, which isolates the join from everything else.

### P7 — no silent cap in the repair

- I predict the shipped control still reports **all** (B) findings rather than a
  top-N, and that nothing in `41ef4ee` introduces sampling or truncation.

### P8 — parent's counts re-derive *(parent's numbers, all four)*

- **P8a** (B) population **11 → 10** literals across the repair. Grain: distinct
  quoted-hex strings in the 7–40 window inside git-mentioning files. Population:
  the whole tree as the control walks it.
- **P8b** The one removed is the 22-char tail and nothing else.
- **P8c** "All 5 distinct real pins resolve AND are ancestors of `origin/main`" —
  I predict 5 distinct, 5/5 resolving, 5/5 ancestors.
- **P8d** I predict the gap between 10 findings and 5 distinct pins is
  duplication (the same rev pinned in several places), not five unresolved ones,
  and that the parent's report says which.

### P9 — the digest identity re-derives

- The concatenation of the 42-char and 22-char fragments in
  `onethird_mg76d0_partial_report_audit.py` equals
  `sha256(data/onethird-mg75f0-gate-class-closure.json)` **byte-exactly**.
  *(parent's claim; `shasum -a 256` is the instrument, and I predict it matches
  the file's current bytes, which is a stronger statement than "matched when
  written".)*

### P10 — the eleven-hour gap answer is argued and still open

- **P10a** The parent's claim that `refinery_gate.sh` names this control at line
  54 and never executes it is **true and re-derivable**.
- **P10b** `41ef4ee` does **not** close that gap — it fixes the control without
  making the gate run it. So the same class of red-main-for-hours remains
  possible for any *other* control the gate watches but does not run.
- **P10c** Per the dispatch this is an out-of-scope coverage boundary. I predict
  I will report it and not fix it, and P10b is a prediction about the repair's
  scope, not a criticism of it.

### P11 — the repair does not reproduce its own defect class

- **P11a** `41ef4ee` adds **no new hardcoded hex constant**: both `_FAKE_REV`
  and `_FAKE_DIGEST` are *computed* at import time, never written down.
- **P11b** Therefore the standing target "a fix that pins a new literal is a
  candidate for exactly the same rot" does **not** land on this repair.

### P12 — where I expect to find something the parent did not

Naming this in advance so a null result is scoreable rather than quietly
dropped. I expect the most likely genuine new finding to be, in order:

1. **P4a** — prefixed string literals (`f"" r"" b""`) defeat the join.
2. **P5c** — a hex literal naming a non-commit object mis-called as rotted.
3. **P3c being wrong** — more than one git-mentioning file carrying a wrapped
   digest, meaning the pre-repair control should have fired more than once and
   something else was suppressing it.

If none of these three produces anything, I predict I will report **no new
defect in the repair** rather than manufacture one, and will say which
instruments were run and could have shown the positive.

### P13 — my own most likely error

The symmetric version of the parent's mistake. The parent excluded one branch
and concluded the other. **My available failure is to find the repair sound on
the axis I checked and report it sound overall** — a negative over the
population I happened to instrument, presented as a negative over the class.
Every negative in my report must therefore name the instrument and the
population it swept, and any category I did not instrument goes in WHAT I DID
NOT DO rather than being absorbed into a clean bill.

---

## Scoring

Every prediction above is scored HIT / MISS / UNRESOLVED in the final report,
with UNRESOLVED reserved for ones whose instrument could not be run (and the
reason named). Predictions marked *(parent's claim)* are scored on whether my
independent re-derivation agrees, not on whether the parent said it.
