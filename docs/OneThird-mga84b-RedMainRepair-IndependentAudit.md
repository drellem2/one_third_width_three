# mg-a84b — INDEPENDENT AUDIT of the mg-ba2a red-main repair

**Verdict: the repair is sound, and it repairs the defect that actually
existed rather than the one first asserted.** Main is green, the green is
attributable to this commit, and the fix was made in the reader rather than in
the subject — which is the difference between fixing an instance and fixing a
class.

Three defects survive it. One is a residual hole in the new join (**F1**), one
is the two-branch disjunction that misled the parent in the first place and is
**still printed verbatim** (**F2**), and one is a coverage gap nobody has named
yet: **the pin check scans 128 files but is triggered by a 17-path allowlist,
and two pins have already landed on main without it ever running** (**F3**).

Subject: `41ef4ee` — *ci+docs: GET MAIN GREEN — the pin never rotted, it was
never a revision (mg-ba2a)*.
Predictions pre-registered in `e9e78c9` before any audit code existed;
scored in §8.
Instrument: `scripts/onethird_mga84b_wrapped_digest_audit.py`.
Record: `data/onethird-mga84b-wrapped-digest-audit.json`.

---

## 1. Whose claim is whose

The dispatch handed me a **retracted** diagnosis and its replacement. Keeping
those separate is most of this audit's job, so:

| Claim | Origin | This audit |
|---|---|---|
| "rotted revision pin" | pm-onethird, **retracted** | Independently **refuted** (§2) |
| "22 chars are the tail of a wrapped sha256" | pm-onethird (corrected) | **Re-derived byte-exactly** (§2) |
| "shallow was correctly excluded" | pm-onethird | Re-derived (`fetch-depth: 0`, §3) |
| "11 literals → 10" | mg-ba2a commit | **Re-derived** (§4) |
| "5 distinct pins, all resolve, all ancestors" | mg-ba2a commit | **Re-derived 5/5** (§4) |
| "case 8 RED before this commit" | mg-ba2a commit | **Re-derived** (§5) |
| "the gate watches this control and never runs it" | mg-ba2a commit | **Re-derived** (§7) |
| "eleven hours" | mg-ba2a commit | Reproducible only under one of two anchors; see §7 |
| "nine other files that compute sha256" | mg-ba2a commit | **8 compute; 9 mention.** See §6 |

Numbers marked *re-derived* were recomputed here from primary evidence, not
copied. Where I could not reproduce a number I say so rather than repeating it.

**Correcting the dispatch's own framing.** The dispatch says "main is green —
both workflows now passing". There are **three** workflow files
(`gate-mutation-demo.yml`, `lean.yml`, `script-controls.yml`). `lean.yml`
filters on `lean/**` and has not run on any commit in this window, so it is
neither passing nor failing here — it is absent. And `script-controls.yml`
**was never red**: it invokes the control with `--static-only`, which prints
"(B) skipped" and never checks a pin. The entire incident lived in
`gate-mutation-demo.yml`. That matters for §9.

---

## 2. Does the repair fix the actual defect, or the asserted one? (dispatch Q1)

**The actual one.** Two independent checks.

**The literal is a content hash, re-derived here:**

```
$ /usr/bin/python3 -c "import hashlib; print(hashlib.sha256(
    open('data/onethird-mg75f0-gate-class-closure.json','rb').read()).hexdigest())"
39a4ca340ffeb74f2a9d78c60b4b147813b739633e8fc785f76e225ec6c97318

scripts/onethird_mg76d0_partial_report_audit.py:65
    ASSERTED_CANON_SHA = ("39a4ca340ffeb74f2a9d78c60b4b147813b739633e"   # 42
                          "8fc785f76e225ec6c97318")                     # 22
```

Concatenation is 64 characters and matches **byte-exactly against the file's
current bytes** — a stronger statement than "matched when written", and the
one worth making, since the whole failure was an assertion about identity that
nobody re-ran.

**Provenance (dispatch Q2 of the original ticket).** `git log -S` puts the
literal's introduction at exactly one commit on main:

```
ced6861  docs+scripts+ci: INDEPENDENT AUDIT of the mg-a471 partial-report repair … (mg-76d0)
```

which is also the commit whose Actions run first went red, at
`2026-08-05T22:02:52Z`. The literal was **never** meant to name a revision.
Its own comment three lines above says so: *"The digest mg-a471's commit
message asserts for the committed acceptance record."* It is an integrity
check on `data/onethird-mg75f0-gate-class-closure.json`. There was no object
to rot, on day one or ever. **"Rotted pin" is refuted, not merely unproven.**

**The repair is in the reader.** `41ef4ee` touches two files — the control and
its report. `scripts/onethird_mg76d0_partial_report_audit.py` is **unmodified**
(verified: `git show --stat 41ef4ee`). Re-pointing or unwrapping that literal
would have turned main green in one line and left every future digest exposed.
This is the single most important thing the repair got right, and it is
directly downstream of the retraction: a repair written against "rotted pin"
would have edited the subject.

---

## 3. Main is green — is it the repair, or green for another reason? (dispatch Q4)

Green is **attributable**. The step-level record, not the run-level
conclusion, is what settles it — a run-level `success` cannot distinguish
"passed" from "skipped", and four steps *were* being skipped.

| Run | Head | Workflow | Conclusion | Step 5 (`mg-3934` control) |
|---|---|---|---|---|
| 31051199179 | `ced6861` | Gate mutation demo | failure | **failure** |
| 31059649976 | `c64fe68` | Gate mutation demo | failure | **failure** |
| — | `fc8115d` | Gate mutation demo | *(no run — see F3)* | — |
| **31098746315** | **`41ef4ee`** | **Gate mutation demo** | **success** | **success, ran** |
| 31098746207 | `41ef4ee` | Script controls | success | (`--static-only`) |

Same job, same step number, same step name, same runner image. Not skipped,
not `continue-on-error`, and `41ef4ee` touches nothing under `.github/`.

**And the pass is not vacuous.** The green run's step-5 output shows the
population it actually swept:

```
=== (B) pinned revisions in scripts/ (10 literal(s) in 7 file(s))
  … 10 rows, every one "ok" …
OK -- every workflow that reads history fetches it, and every pinned revision
     checked here resolves.
```

Ten rows, not zero. A green over an empty population is the failure mode
mg-a266 found one commit earlier in this same arc; it is not this one.

**Shallow was correctly excluded, re-derived.** `gate-mutation-demo.yml` sets
`fetch-depth: 0`, and the green run's own (A) section prints
`gate-mutation-demo.yml  fetch-depth 0`. The runner had full history. The
parent's exclusion of the shallow branch stands.

**What the red run also did, which nobody has mentioned.** On every red run,
steps 6–9 were **`skipped`** — `mg-7db4` watchlist consistency, the `mg-7db4`
probe mutation battery, the `mg-60d3` gate mutation demo, and the `mg-75f0`
class-closure demo. For the whole red window, four further controls did not
execute, and their state was unknown rather than good. They all pass on
`41ef4ee`, so nothing was hiding behind the false positive — but that is a
fact established *by the green run*, not something that was known at the time.
A false positive in step 5 is a **denial of service on every control behind
it**, and the one it masked longest was `mg-75f0`, whose committed acceptance
record is the very file the digest is a hash of.

---

## 4. The population, and the parent's counts

All three readings below are of **the same tree** (`41ef4ee`) so the only
variable is the control. Population: every `.py`/`.sh` file under `scripts/`
as the control's own lister walks it. Grain: **one quoted hex literal
occurrence**, not one file and not one distinct revision.

| Control | Literals | Files | Exit |
|---|---|---|---|
| pre-repair (`fc8115d` version) | **11** | 7 | 1 |
| post-repair (as landed) | **10** | 7 | 0 |

The delta is exactly one row — the 22-character tail — and nothing else moved.
**The parent's "11 → 10" re-derives.**

⚠️ **The dispatch's own "NINE literals in FIVE files" is stale.** That is the
red run's figure at `c64fe68`; `fc8115d` then added two more scripts carrying
pins. Same grain, different tree. Anyone comparing 9-in-5 against 10-in-7 and
reading it as growth-under-repair is comparing two trees, and the number to
compare against is 11.

**Distinct pins (grain: distinct revision literal), re-derived 5/5:**

| Literal | Resolves | Ancestor of `origin/main` |
|---|---|---|
| `9fa4aaa` | ✅ | ✅ |
| `af7fc2df` | ✅ | ✅ |
| `91fa25f` | ✅ | ✅ |
| `9072f34` | ✅ | ✅ |
| `c64fe68` | ✅ | ✅ |

The gap between 10 occurrences and 5 distinct revisions is duplication —
`af7fc2df` alone is pinned in five files. Not five unresolved pins. The
parent's claim holds, and its "pin AFTER landing" reading of the corpus idiom
is confirmed by 5/5 ancestry: nothing here pins an unmerged branch, so the
rebase-rot hypothesis is true in premise and inapplicable in fact, exactly as
the parent said.

---

## 5. Did the join buy the fix with a blind spot? (Q4 of the instrument)

No, on the real corpus, and the parent's self-test claims re-derive.

Neutering `join_implicit_concat` to the identity and re-running the shipped
self-test — which isolates the join and changes nothing else:

```
  8. a WRAPPED sha256 digest is not a revision (the mg-ba2a defect)  FAILED
  9. a WRAPPED 40-char revision is still seen (the join has no hole) ok
```

**Case 8 is RED before the repair, and fires both (A) and (B)** — precisely
what the commit message claims.

**Case 9 needs a caveat the commit message does not give it.** It passes with
the join *and* without it, so it does not discriminate the join at all: 20 is
already inside the 7–40 window, so the un-joined reading finds the two halves
and reports a pin anyway. It is a real guard against a join that *swallowed*
pins wholesale, but the commit message's "the join must not buy the fix with a
blind spot — passes before and after" reads as though passing-before is
evidence of care. Passing before is automatic here. The load-bearing guard is
case 8; case 9 is a weaker instrument than its framing suggests.

The corpus-level version, which does discriminate: every literal visible to
the pre-join reading and not to the post-join one — **exactly 1**, and it is
inside a 64-character hex run, so it is provably not a sha1 revision.
**0 unjustified drops.**

---

## 6. Are there other line-wrapped digests? (dispatch Q2)

**Population: 128 `.py` files under `scripts/` at `41ef4ee`. Grain: one
maximal run of adjacent string literals whose joined text is ≥ 41 hex
characters** — one past the control's cap, which is the population the cap
exists to exclude and therefore the only place a wrap can smuggle something
back in.

**Instrument.** Not a regex. A ground-truth join built from Python's own
`tokenize` module (handling `FSTRING_START/MIDDLE/END` explicitly so f-strings
are not silently dropped), run over every file, and compared against the
shipped regex join. *This is the instrument that could have shown the
positive*: if the shipped regex were flawless, tokenize would agree
everywhere, and it is that agreement — not the absence of a grep hit — that
makes the negative reportable.

**Result: exactly ONE.** The `mg-76d0` file, at line 65. `.sh` files: none.
Unwrapped ≥41-char literals elsewhere: none.

**So my prediction P3a/P3b was wrong** — I expected 3–40 and there is 1. The
class is real but currently instantiated once. Two consequences, and they cut
in opposite directions:

- **It does not weaken the repair.** The class-vs-instance argument was never
  about how many exist today; it is that the *next* one costs nothing to
  introduce. The repair fixed the reader, so the next one is free of charge.
- **It does weaken one sentence of the parent's.** "…left the class loaded on
  the nine other files that compute sha256" — re-derived, **8 files actually
  call `sha256()`** (9 merely mention the string, one of which is the control's
  own docstring). Of those 8, **6 also mention git** and so form the latent
  surface where a future hardcoded digest could reach (B):
  `mg4f9b`, `mg75f0`, `mg76d0`, `mga266_vacuity_enumeration`, `mga471`,
  `mgbd53`. Neither 8 nor 6 is nine. The argument survives; the number does not.

### F1 — the join has reachable holes, and they leak the same way

13 wrap shapes, 11 of them genuinely wrapped. **The shipped join disagrees
with Python on 5 of 11, and in all 5 the disagreement produces a wrong
verdict** — a 64-character digest is offered to the git resolver as a
22-character "pin":

| Wrap shape | Join = Python? | Verdict |
|---|---|---|
| 42 + 22 (the mg-ba2a shape) | ✅ | ok |
| 32 + 32 | ✅ | ok |
| three pieces, 22+21+21 | ✅ | ok |
| mixed quote styles `"…" '…'` | ✅ | ok |
| **raw prefix on the tail** `("…" r"…")` | ❌ | **MISVERDICT** |
| **f prefix on the tail** `("…" f"…")` | ❌ | **MISVERDICT** |
| **b prefix on the tail** `("…" b"…")` | ❌ | **MISVERDICT** |
| **`\`-continuation between fragments** | ❌ | **MISVERDICT** |
| **comment between the fragments** | ❌ | **MISVERDICT** |
| real 40-char rev wrapped 20+20 | ✅ | ok (still seen) |
| real 40-char rev wrapped 8+32 | ✅ | ok (still seen) |

Cause, from the regex itself
(`([\"'])([^\"'\\\n]*)\1\s*([\"'])([^\"'\\\n]*)\3`): after the first closing
quote it permits only `\s*` before the next quote. A prefix letter is not
whitespace; a `\` is not whitespace; a `# comment` is not whitespace.

The repair's comment **does** disclose the escape and triple-quote exclusions,
and calls them "the conservative direction". For escapes that is right — an
unjoined literal keeps the old reading. **For these five it is the opposite of
conservative**: not joining is precisely what re-exposes the tail. Same
failure, same false "rotted pin", same red main.

Severity: **latent, not live.** No file in the corpus is written this way
today, and nobody wraps a digest with a `b` prefix on purpose. But `f"…"`
adjacent to a plain literal is ordinary Python, and this control fails the
whole tree on a single hit. Minimal repair: tolerate `[A-Za-z]{0,3}` before
the second quote, and strip comments before joining. Not done here — see §10.

---

## 7. Is the gate's disjunction still wrong? (dispatch Q3)

### F2 — yes, and it is byte-identical to the sentence that misled the parent

`onethird_mg3934_ci_history_depth_control.py:363-366`, **unchanged by the
repair**:

> `…pins revision %s, which does not resolve in this checkout (%s).  If this
> is CI, the checkout is shallow and the pin is unreachable rather than wrong;
> if it is a full clone, the pin has rotted.`

Two branches. Both presuppose that the literal is a revision. That premise is
exactly what was false, and it is still unstated and still unquestioned. The
repair removed the *population* that made the unstated premise bite, and left
the *sentence* that will state it again to the next reader.

Constructed probe, 4 categories, resolved by the control's own
`git_resolver` against real objects in this repository:

| Literal is… | `git cat-file -t` | Control resolves | Both printed branches false? |
|---|---|---|---|
| a commit | `commit` | ✅ | — |
| **a tree that exists here** | `tree` | ❌ | **yes** |
| **a blob that exists here** | `blob` | ❌ | **yes** |
| no object at all | *(none)* | ❌ | no — "rotted" is fair |

**2 of 4 categories break the disjunction.** For an existing blob the control
prints "does not resolve in this checkout … shallow … or rotted", and the
checkout is not shallow and nothing rotted: the object is right there.

**A correction to my own prediction, which weakens this finding and should.**
I predicted the control would print a bare `no such object` for a blob. It
does not — `git rev-parse` returns `expected commit type, but the object
dereferences to blob type`, and the control passes that through in the
parenthetical. So a careful reader *does* get the evidence to catch it.

That sharpens rather than dissolves the point. Compare the historical case:
there the detail was `no such object` — true, and uninformative, because a
digest tail genuinely is not an object. **The disjunction is unsound exactly
where its accompanying evidence is weakest.** It reads as a complete
enumeration and it is not one, and it is at its most confidently wrong in the
case that actually occurred. Minimal repair: a third branch — *"or the literal
was never a revision; check whether it is a digest, a truncated hash, or a
non-commit object"*. One sentence.

### The eleven-hour gap (original ticket Q6)

The parent's cheap-catch answer is **argued and correct, and it would have
fired on this instance.** Re-derived: `scripts/refinery_gate.sh` lists
`onethird_mg3934_ci_history_depth_control.py` at **line 54**, inside the
`WATCHED` array — the set of paths that *invalidate* the demo — and the only
scripts it ever executes are at lines 92, 302 and 307
(`mg7db4_watchlist_consistency`, `mg5ad1_gate_blindspot_probe`,
`mg60d3_gate_mutation_demo`). The control is watched and never run. Since the
pre-repair control exits 1 on the offending tree (§4), executing it in the
gate would have failed `mg-76d0`'s branch **before** it merged. `41ef4ee` does
not close this, which is correct scoping, not an oversight.

**The number itself, with its anchor named — because it does not reproduce
under the anchor the commit message gives it:**

| Anchor | Interval | Length |
|---|---|---|
| first red run finishes → green finishes | `22:03:08Z` → `12:09:31Z` | **14 h 06 m** |
| last red-producing push → green finishes | `00:25:37Z` → `12:09:31Z` | **11 h 44 m** |

"Eleven hours" is the second. The commit message asserts the first anchor
("red … since 22:02") in the same paragraph. The two differ by 2 h 22 m and
the message does not say which it used. Minor, and it does not touch any
conclusion — flagged because this arc's standing target is that every printed
count names its grain, and this one does not.

---

## 8. F3 — the finding I did not predict, and the one I would act on first

**The (B) pin check scans 128 scripts and is triggered by a 17-path
allowlist. Pins have already landed on main without it ever running.**

(B) exists in exactly one place: step 5 of `gate-mutation-demo.yml`.
`script-controls.yml` runs the same control with `--static-only`, which prints
`(B) skipped`. And `gate-mutation-demo.yml` fires on a 17-entry `paths:`
allowlist that **does not include `scripts/**`** — it lists the gate's own
machinery, because it was designed to answer "did anything invalidate the
mutation demo?", not "did a pin break?". The pin check is a passenger on
somebody else's trigger.

Verified consequence, on this very window:

| Push | New pins added | Touches a watched path? | (B) ran? |
|---|---|---|---|
| `ced6861` | the wrapped digest | yes (3 of them) | yes → **red** |
| `c64fe68` | — | yes (`mg75f0`) | yes → red |
| **`fc8115d`** | **`c64fe68` and `af7fc2df`, in two new scripts** | **no** | **NO RUN** |
| `41ef4ee` | — | yes (the control) | yes → green |

`fc8115d` added `onethird_mga266_split_phrase_control.py` and
`onethird_mga266_vacuity_enumeration.py`, each carrying a pinned revision, and
`gate-mutation-demo.yml` **did not run on it at all**. Those two pins went
unchecked until `41ef4ee` happened to touch the control for unrelated reasons.
They are in the green run's 10 rows and they both resolve — so nothing broke.
It was not caught; it was lucky.

**This is the honest answer to dispatch Q4.** Main is green, the green is
real, and the green does not mean the pins are being checked going forward.
Any of the ~120 unlisted scripts can acquire a rotted pin and main will stay
green until something in the 17 happens to change.

**It applies to this very commit.** My branch touches `docs/`, `data/`, and
one new `scripts/` file — none of them in the 17. `gate-mutation-demo.yml`
will not run when this merges. Main will stay green **without (B) executing**.

I have run it locally against my worktree instead: the shipped control exits
`0` with 10 literals in 7 files, unchanged from `41ef4ee`. `script-controls.yml`
*does* filter on `scripts/**` and so will run on this branch, and all **21**
controls it invokes pass here — checked because several of them audit the
`docs/` corpus this report is about to join, and a new document is exactly the
kind of thing that trips a claim census. That is the substitute for (B), and
it is a weaker one than CI because it is my word for it.

Cheapest fix: add `'scripts/**'` to both `paths:` lists (the `mg-7db4`
watchlist-consistency control will require the same line in `WATCHED`, which is
the mechanism working). Not done here — §10.

---

## 9. Did the deliverable reproduce its own defect class?

**The parent's: no.** `41ef4ee` hardcodes no hex constant. Both fixtures are
*computed* — `_FAKE_DIGEST` and `_FAKE_REV` are built by arithmetic at import
time. The standing target "a fix that pins a new literal is a candidate for
exactly the same rot" does not land on it.

**Mine: yes, on the first draft, and the control caught me in seconds.** My
audit script needs a literal that is *not* a git object. I wrote one inline —
twelve hex characters, in a file that also mentions git. The shipped mg-3934
control immediately failed the whole tree:

```
=== (B) pinned revisions in scripts/ (11 literal(s) in 8 file(s))
  scripts/onethird_mga84b_wrapped_digest_audit.py  deadbeefcafe  UNRESOLVABLE: no such object
PROBLEMS (1): … the pin has rotted.
```

Note the message: **"the pin has rotted"**, about a string I had invented four
minutes earlier. F2, live, on me. Had I committed it, this audit would have
reproduced the exact incident it was dispatched to audit.

Now built, never written: `"".join("%x" % ((i * 5 + 3) % 16) for i in range(12))`.
Tree back to `exit 0`, 10 literals in 7 files.

This is the standing target answered by demonstration rather than by
assertion, and it is also the strongest single piece of evidence in this audit
that the control is load-bearing: it caught its own auditor, unprompted,
within seconds, on the first run.

---

## 10. Prediction scorecard

19 of 25 scored predictions HIT. The misses are recorded, not smoothed.

| # | Prediction | Result |
|---|---|---|
| P1a | `script-controls.yml` was the green/red workflow | **MISS** — it was never red; `--static-only` skips (B) |
| P1b | `script-controls.yml` failed on `fc8115d` | **MISS** — it succeeded; the demo workflow did not run at all |
| P1c | green is attributable, step ran and passed | HIT |
| P1d | `41ef4ee` touches no `.github/` file | HIT |
| P2a | subject file unmodified | HIT |
| P2b | pre-repair control → exit 1; post → exit 0 | HIT |
| P2c | delta is exactly one literal | HIT |
| P3a | more than one file carries a wrapped digest | **MISS** — exactly one |
| P3b | 3–40 wrapped hex runs | **MISS** — 1 |
| P3c | exactly one git-mentioning member | HIT |
| P3d | repair fixes the class, not the instance | HIT |
| P4a | `f"" r"" b""` prefixes defeat the join | **HIT** → F1 |
| P4b | escapes / triple quotes not joined | HIT (already disclosed by the repair) |
| P4c | continuation and comment gaps defeat the join | **HIT** → F1 |
| P4d | no new false positive on the current tree | HIT |
| P4e | the repair does not disclose the prefix hole | HIT |
| P5a | disjunction still two-branch | **HIT** → F2 |
| P5b | still non-exhaustive but less often reached wrongly | HIT |
| P5c | a non-commit object is mis-called "rotted" | HIT, **weakened** — git's detail string is truthful (§7) |
| P6a | case 8 RED with the join removed | HIT |
| P6b | case 9 non-discriminating for the join | HIT |
| P7 | no silent top-N cap | HIT |
| P8a–d | 11→10; delta is the tail; 5/5 pins; gap is duplication | HIT ×4 |
| P9 | digest identity re-derives byte-exactly | HIT |
| P10a–c | gate watches at line 54, never runs it; unclosed; out of scope | HIT ×3 |
| P11a–b | repair hardcodes no new literal | HIT ×2 |
| P12 | ranked my three likeliest findings | 1 of 3 top-ranked (P4a); P5c weakened; P3c inverted |
| P13 | my likeliest error is a scoped negative sold as a class negative | see §11 |

**P13 fired, and F3 is why.** I pre-registered that my characteristic failure
would be reporting a negative over the population I happened to instrument as
a negative over the class. My four planned checks all pass on the corpus, and
had I stopped at Q1–Q4 I would have written "the repair is sound, two minor
residuals". F3 was outside all four instruments — it is not about the literal,
the join, the disjunction, or the corpus, but about *when the check runs at
all* — and it is the most consequential thing in this report. The lesson
generalizes past this ticket: **the parent's error was excluding one branch of
a disjunction and concluding the other; the audit-shaped version is sweeping
four dimensions and concluding about the space.**

---

## 11. WHAT I DID NOT DO

- **I did not repair F1, F2, or F3.** This ticket is an audit; the standing
  instruction is to note and not fix. Minimal repairs are named in §6, §7 and
  §8. F3 is the one I would file first — it is one line in two `paths:` lists,
  and it is the difference between the pin check guarding the corpus and
  guarding seventeen files.
- **I did not sweep for wrapped digests outside `scripts/`.** `docs/`, `data/`
  and `.github/` were not tokenized. (B) does not read them, so nothing there
  can turn main red today — but "not currently read" is not "not present", and
  I did not measure it.
- **I did not tokenize `.sh` files.** I grepped them for hex runs ≥ 20
  characters and found none, which is a weaker instrument than the Python one.
  POSIX shell also concatenates adjacent quoted strings, so the class is
  expressible there and unmeasured by tokenizer.
- **I did not test the disjunction against every residual category.** Four
  constructed: commit, tree, blob, absent. Not covered: an ambiguous
  abbreviation, an annotated tag, a valid commit in a submodule or an
  alternate object store, or a literal that is a revision in a *different*
  repository. Each is a candidate for the same mis-call.
- **I did not verify the four masked controls (steps 6–9) would have passed
  during the red window.** They pass on `41ef4ee`. I did not check out each red
  commit and run them, so "nothing was hiding behind the false positive" is
  established at the endpoint, not across the interval.
- **I did not re-derive `fetch-depth: 0` on any runner other than the green
  one.** I read it from the workflow file and from the green run's (A) output.
- **I did not exercise the refinery-vs-Actions boundary.** Per the dispatch
  that is a known coverage limit and out of scope. F3 is *not* that boundary —
  it is an Actions-internal trigger gap — and I have reported it as separate.
- **I did not measure whether `41ef4ee`'s join slows the control.** It iterates
  a regex substitution to a fixpoint over whole source files, 128 of them. The
  green run's step 5 completed inside the normal window, so there is no visible
  problem; I did not benchmark it.
