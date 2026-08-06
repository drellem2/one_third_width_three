# mg-ba2a — main was red for eleven hours over a literal that was never a revision

**Verdict: the pin did not rot. It was never a git object.** The 22-character
literal the gate named is the TAIL of a 64-character sha256 content digest,
line-wrapped into two adjacent Python string literals. The gate's own
40-character cap was written to exclude sha256 digests and was defeated by the
wrap, because the cap was applied per quoted piece instead of per Python string.

Repaired in `scripts/onethird_mg3934_ci_history_depth_control.py`. Whole-tree
exit code **1 before, 0 after**. Two new self-test cases, one of which is RED
on the pre-repair code.

This report is written for **mg-a84b** to verify rather than re-derive. Every
population size below is a count I ran, and the command is given.

---

## 1. What the gate said, and why its disjunction was not exhaustive

    PROBLEMS (1):
      - scripts/onethird_mg76d0_partial_report_audit.py pins revision
        8fc785f76e225ec6c97318, which does not resolve in this checkout
        (no such object). If this is CI, the checkout is shallow and the pin is
        unreachable rather than wrong; if it is a full clone, the pin has rotted.

pm-onethird's inference is **valid and I am not re-opening it**: section (A) of
the same run prints `gate-mutation-demo.yml  fetch-depth 0`, that is a full
clone, so the shallow-checkout branch does not apply. I confirmed it
independently — `.github/workflows/gate-mutation-demo.yml` sets `fetch-depth: 0`
and my own full-clone worktree reproduces the identical failure. **Shallowness
is excluded.**

What is wrong is not the inference, it is the **disjunction the inference runs
on**. "Shallow, or rotted" is exhaustive only under an unstated premise: *that
the literal is a revision*. It is not. There is a third branch — **not a
revision at all** — and the gate has no way to see it, because the only question
it asks of the literal is whether `git rev-parse` resolves it, and "no" is
returned identically for a rotted pin and for a fragment of a hash that was
never in the object database.

pm-onethird flagged the tell in the ticket: twenty-two hex characters is not 7,
not 40. That is the whole finding.

## 2. The mechanism, exactly

`scripts/onethird_mg76d0_partial_report_audit.py:65`:

```python
ASSERTED_CANON_SHA = ("39a4ca340ffeb74f2a9d78c60b4b147813b739633e"
                      "8fc785f76e225ec6c97318")
```

42 + 22 = **64 characters**, and Python concatenates them into one string. It is
the sha256 of `data/onethird-mg75f0-gate-class-closure.json`, verified by
recomputation:

    $ /usr/bin/python3 -c "import hashlib; print(hashlib.sha256(
        open('data/onethird-mg75f0-gate-class-closure.json','rb').read()).hexdigest())"
    39a4ca340ffeb74f2a9d78c60b4b147813b739633e8fc785f76e225ec6c97318   # exact match

The detector in `onethird_mg3934_ci_history_depth_control.py` is

```python
_HEX = r"[0-9a-f]{7,40}"
_REV_INLINE_RE = re.compile(r"[\"'](%s)[\"']" % _HEX)
```

`_REV_INLINE_RE` anchors on the **quote characters**, so it sees two strings, not
one. The head is 42 — over the cap, not matched. The tail is 22 — inside the
7-40 window, matched. The file shells out to git, so `revs_in()`'s file-level
branch admits every hex literal in it, and the tail is handed to
`git rev-parse --verify 8fc785f76e225ec6c97318^{commit}`, which fails, forever.

The control's own docstring already claimed the defence:

> The 40-character cap keeps a sha256 digest literal (64 characters) from being
> mistaken for a revision.

That claim was true of the intent and false of the code. A 64-character constant
does not fit this corpus's 79-column line, so **every** digest in it is wrapped;
the cap therefore never once saw a 64-character quoted string.

## 3. The two hypotheses the brief told me to test first

### 3a. "The refinery rebases before merging, so pins to pre-merge SHAs rot by construction" — **the premise is TRUE, the conclusion does not apply here, and the class is currently empty**

The refinery does rebase. Committer dates on `origin/main` are rewritten away
from author dates in a block-per-merge pattern:

    c64fe68  author 08-05T23:35   committer 08-06T01:19
    a99c970  author 08-05T23:24   committer 08-06T01:19
    1ef4c79  author 08-05T23:17   committer 08-06T01:19   <- one rebase, three commits

So the hazard the brief describes is real: **a pin written on a polecat branch,
naming a commit on that same unmerged branch, rots the moment the refinery
rebases it.** That is a class, and it is worth naming even though it did not
cause this.

It did not cause this, on two independent grounds:

1. **The literal is not a revision** (§2), so no history operation could have
   removed it.
2. **No pin in the corpus is exposed to it today.** All five distinct real
   revision literals resolve *and* are ancestors of `origin/main` —
   permanent, not merely present:

   | pin | resolves | ancestor of `origin/main` |
   |---|---|---|
   | `9fa4aaa`  | yes | yes |
   | `af7fc2df` | yes | yes |
   | `91fa25f`  | yes | yes |
   | `9072f34`  | yes | yes |
   | `c64fe68`  | yes | yes |

   `c64fe68` is the interesting row: it is itself a commit that transited the
   refinery from a polecat branch, and it is pinned by
   `onethird_mga266_split_phrase_control.py`, which landed *later*. The corpus's
   idiom is **pin after landing**, and that idiom is what makes it immune.

   Reproduce: `git merge-base --is-ancestor <rev> origin/main`.

**A caution I am handing forward rather than acting on:** ancestry of
`origin/main` is the strong property. `fetch-depth: 0` fetches every *surviving*
branch, so a pin reachable only from an unmerged branch would resolve on a
developer's box and in CI right up until that branch is deleted. Nothing in the
control distinguishes those two cases. It is not exposed today (5/5 are
ancestors) and I did not add the check — see §7.

### 3b. "Truncated or mis-transcribed when written" — **excluded**

A mis-transcription would produce a 22-character string with no other meaning.
This one reconstructs, character for character, as the second half of a digest
that recomputes exactly against the file it names. It was transcribed
correctly; it was *read* wrongly.

### 3c. Patch-id — **not used, and here is why**

The brief warns that patch-id is not an oracle (1 of 234 pairs in this arc share
content under different patch-ids). I did not need it and did not run it. Patch-id
answers "did this content survive a rewrite?", and that question presupposes
something was rewritten away. Nothing was: the object never existed, and all
five real pins are present and reachable. Reaching for patch-id here would have
been adjudicating a disappearance that did not happen.

## 4. Population sizes — all of them, with commands

| population | size | command |
|---|---|---|
| literals reported by (B) **before** the repair | **11**, in 7 files | `python3 scripts/onethird_mg3934_ci_history_depth_control.py` |
| of those, UNRESOLVABLE | **1** | same run, `PROBLEMS (1)` |
| literals reported by (B) **after** the repair | **10**, in 7 files | same command |
| distinct real revision pins | **5** (`9fa4aaa`, `af7fc2df`, `91fa25f`, `9072f34`, `c64fe68`) | dedup of the 10 |
| of those, resolving | **5 / 5** | `git cat-file -e <rev>^{commit}` |
| of those, ancestors of `origin/main` | **5 / 5** | `git merge-base --is-ancestor <rev> origin/main` |
| adjacent-hex-literal pairs in `scripts/` (the exposure) | **1** — `mg76d0_partial_report_audit.py`, 42+22 | regex sweep over `scripts/*.py`, below |
| unwrapped 64-char hex literals in `scripts/` | **0** | `grep -rnoE "[0-9a-f]{64}" scripts/` |
| files in `scripts/` computing sha256 | **9** | `grep -rlE "sha256\|hexdigest" scripts/*.py` |

The sweep for the exposure:

```python
PAIR = re.compile(r"[\"']([0-9a-f]+)[\"']\s*\n?\s*[\"']([0-9a-f]+)[\"']")
# scripts/onethird_mg76d0_partial_report_audit.py  42+22=64  git=True
#     fragments_flagged=['8fc785f76e225ec6c97318']
# pairs found: 1
```

**Read the last three rows together.** The live instance count is 1, so nothing
else is red right now — but zero unwrapped 64-character literals is not luck, it
is the 79-column style, and **nine** files already compute sha256 digests. Each
becomes a new instance of this defect the first time it hard-codes an expected
digest next to a git call. That is why the repair is in the control and not in
the subject file. Repairing the subject would have made main green and left the
class loaded.

## 5. The repair

`scripts/onethird_mg3934_ci_history_depth_control.py` only. **The subject file
was correct and is untouched.**

1. `join_implicit_concat(src)` collapses runs of adjacent string literals to a
   fixpoint (`"a" "b" "c"` needs two passes), and `revs_in()` runs it first. The
   7-40 window is now applied to the whole Python string, which is what the
   docstring always said it did. Contents exclude quotes, backslashes and
   newlines — an escaped or triple-quoted literal is simply not joined, leaving
   the old per-literal reading for those, which is the conservative direction.
2. Docstring KNOWN LIMITS amended: the cap is stated over the joined string, with
   this incident named. A second bullet records that the cap also blinds the
   control in a sha256-object-format repository, where 64 hex characters *is* a
   revision. This one is sha1.
3. Two self-test cases, fixtures **built not written down**, per the existing
   note (a quoted hex literal in this file would make the control report itself):
   - **case 8** — a wrapped 64-char digest (42+22) beside a git call, under the
     *shallow* workflow and a resolver that refuses everything, must produce no
     problem. Shallow on purpose: if the digest were wrongly a pin, (A) fires as
     well as (B), so the case is covered from both sides.
   - **case 9** — a real 40-char revision wrapped 20+20 must **still** be seen.
     The join must not buy §2 at the price of a blind spot.

### RED before the repair

Case 8 on the pre-repair detector, verbatim:

```
  8. a WRAPPED sha256 digest is not a revision (the mg-ba2a defect) FAILED
      expected problem=False, got: [".github/workflows/a.yml runs code that reads
      historical revisions -- scripts/onethird_d.py (6d4b2907e5c3a18f6d4b29) --
      but its actions/checkout sets fetch-depth unset (=1). ...",
      'scripts/onethird_d.py pins revision 6d4b2907e5c3a18f6d4b29, which does not
      resolve in this checkout (stub refuses every literal). ...']
  9. a WRAPPED 40-char revision is still seen (the join has no hole) ok
SELF-TEST FAILED
```

The synthetic fragment `6d4b2907e5c3a18f6d4b29` is 22 characters — the same
shape as the real one, from a digest this control has never seen. Case 9 passes
before *and* after: it is a regression guard, not a RED.

### GREEN after

    SELF-TEST PASSED           (10 cases: undrifted + 1-9)
    === (B) pinned revisions in scripts/ (10 literal(s) in 7 file(s))
      ... all ok ...
    OK -- every workflow that reads history fetches it, and every pinned
    revision checked here resolves.

Whole-tree exit code, measured both ways on the real tree:

    pre-repair  (git show HEAD:...)  exit 1
    post-repair                      exit 0

`--static-only` (the `script-controls.yml` invocation) is clean. `--selftest`
alone is clean. `onethird_mg7db4_watchlist_consistency.py`, which names this
file in its watchlist, still exits 0 — the file's path and wiring are unchanged,
only its body.

## 6. Would anything cheap have caught the eleven hours sooner?

Not my ticket to fix, and I did not touch it. The answer is yes, and it is very
cheap:

The refinery gate does not run the Actions matrix, so a red Actions main is
invisible to it **by construction** — it merged four times through this.
`scripts/refinery_gate.sh` already knows about this control: line 54 has
`onethird_mg3934_ci_history_depth_control.py` in `WATCHED`. It watches the file
for changes but never runs it. The control's own docstring explains the
omission — the refinery has a full clone, so (A)'s shallow-checkout premise does
not apply there, and (B) "would pass and is left to Actions rather than added to
the blocking path."

That reasoning is exactly what failed. (B) would *not* have passed. It was the
thing that was red, it runs in seconds, and the refinery holds the only full
clone in the blocking path. **One line in `refinery_gate.sh` invoking this
control would have turned eleven hours and four merges into the first
submission bouncing.** Cheaper still, and orthogonal: one `gh run list
--branch main --limit 1` in the refinery preflight would refuse to merge onto a
red main whatever the cause.

I am naming both and doing neither, per the ticket.

## 7. WHAT I DID NOT DO

- **I did not modify `onethird_mg76d0_partial_report_audit.py`.** Its digest
  constant is correct and its wrapping is required by the line-length style.
  Rewriting the wrap would have gone green while leaving nine sha256-computing
  files loaded with the same defect.
- **I did not add a reachability check** (pin must be an ancestor of a surviving
  remote branch, not merely resolvable). All 5 are ancestors today, so it would
  be a new control with no live finding, and it is outside this ticket.
- **I did not touch the refinery/Actions boundary** — not `refinery_gate.sh`,
  not the workflows. §6 states the cheap fix and stops.
- **I did not run patch-id**, and §3c says why rather than leaving it silent.
- **I did not re-open the shallow-vs-full question.** pm-onethird's `fetch-depth
  0` reading is confirmed, independently, in §1. My finding is not that the
  inference was wrong but that the disjunction it ran on had a third branch.
- **I did not verify the four failing runs individually on GitHub.** I
  reproduced the identical single PROBLEM locally in a full clone at
  `origin/main`, which is the same tree those runs saw for this check.
- **I did not check `docs/` or `data/` for the same exposure.** The control
  scans `scripts/` only; the digest appears in three docs and one data file as
  prose and JSON, where nothing tries to resolve it.
