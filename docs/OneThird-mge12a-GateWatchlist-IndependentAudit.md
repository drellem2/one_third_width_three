# mg-e12a — INDEPENDENT AUDIT of the gate-watchlist repair

**Tree audited:** `84f510a` (`origin/main`, 2026-08-06).
**Predictions:** `docs/OneThird-mge12a-GateWatchlist-AUDIT-PREDICTIONS.md`,
committed at `491220d` before any audit code of this ticket existed.
**Instruments:** `scripts/onethird_mge12a_watchlist_audit_probe.py`,
`scripts/onethird_mge12a_trigger_direction_control.sh`.
**Artifact:** `data/onethird-mge12a-watchlist-audit.json`.

---

## 0. THE FIRST FINDING IS ABOUT THE BRIEF: THERE IS NO REPAIR TO AUDIT

My dispatch says, verbatim, *"Pre-filed audit; its parent has landed."*
**It has not landed.**

    mg show mg-856d | grep '^Status:'          ->  Status:    available
    git log origin/main --format=%s | grep -c mg-856d
                                               ->  0   (over 424 commits)

`mg-856d` was never claimed and never done. The watchlist was not narrowed, no
duration figure was published, and nothing in the gate apparatus was changed by
it. So the briefed question — *"if the watchlist was narrowed, prove the mg-7db4
drift self-test still fires on all five drifts"* — **has no subject.**

Reporting "all five still fire" against a list nobody touched would be a PASS
over an empty population: the same defect `mg-a266` named at `fc8115d` and
`mg-9a59` refused at `c64fe68`, arriving one layer further out, in an audit
sent to look for exactly that.

**So I constructed the narrowing myself** (§4) and ran the five drifts against
it. That is the only way the briefed question has an answer at all, and it
turns out to answer something different and more useful than the brief expected.

One correction to my own prediction A3 while I am here. I predicted
`scripts/refinery_gate.sh` was byte-identical to its state when `mg-856d` was
filed. **It is not.** `ced6861` (mg-76d0) edited it at 2026-08-05 20:14:38, one
hour after filing. The edit changed `FIVE`→`SEVEN` and added six lines about
the wrap-blind grep; it added **no** duration figure and changed none. So A3 is
wrong as stated and right in substance, and both halves are recorded here.

---

## 1. THE COUNT, RE-DERIVED — 17, and what the 17 is made of

Three agents have now stated the size of this variable. Two were wrong (a peer
said five; pm-onethird adopted it without counting). pm-onethird then retracted
and re-derived seventeen. **I did not inherit that number.** Mine is a fourth,
independent statement:

| quantity | value | POPULATION | GRAIN |
|---|---|---|---|
| `WATCHED` rows | **17** | non-empty lines of the `WATCHED='…'` literal in `scripts/refinery_gate.sh` at `84f510a` | one line |
| `WATCHED` distinct | **17** | the same lines, `sort -u` | one path string |
| workflow `push` paths | **17** | `on.push.paths`, read with **PyYAML**, not the hand parser | one path string |
| workflow `pull_request` paths | **17** | `on.pull_request.paths`, PyYAML | one path string |
| import closure | **10** | transitive `onethird_*` modules from `ROOTS` | one module file |
| datasets read | **1** | `data/` files the closure reads | one dataset file |
| `MECHANISM` | **6** | the named non-derivable set | one path string |

Rows and distinct coincide, so the count is not a rows-vs-set trap here. Two
things follow that are worth writing down:

**1a. The 17 decomposes exactly and disjointly.**
`MECHANISM (6) ⊎ closure (10) ⊎ datasets (1) = 17`, verified pairwise disjoint,
and the union is set-equal to `WATCHED`. pm-onethird's retraction guessed this
("the import closure and datasets are what the checker validates the seventeen
AGAINST, not things summed into it"). That guess is **half right and I am
correcting it**: they are what the seventeen is validated against *and* the
seventeen is exactly their union. 6 + 10 + 1 = 17 is not a coincidence, it is
the invariant `check()` enforces in both directions.

**1b. The printed `17` is a row count under a label that says `paths`.**
`main()` prints `len(parse_shell_watchlist(...))` — a **list** length. A
duplicated entry would print 17 for 16 effective paths.
**FORCED, and here is the forcing:** `check()` raises
`"WATCHED has duplicate entries"` when `len(watch_set) != len(watch)`, and
`main()` returns 1 on any problem *before* reaching the print. So the
label/grain mismatch is **unreachable**. It is a real mismatch in the statement
and it cannot be exhibited. I flag it only so the next reader does not have to
re-derive that it is safe — and note in §2 that the check doing the forcing is
itself untested.

---

## 2. FINDING 1 (the load-bearing one) — THE FIVE-DRIFT SELF-TEST DOES NOT TEST THE PROPERTY THE FILE EXISTS FOR

All five drifts report `CAUGHT` on the current tree and the target exits 0. That
is true and it is not what the self-test is for.

**The self-test asserts only that `check()` returned a NON-EMPTY list.** It never
asks *which* problem fired. So I ablated each check in a copy of the target's own
source and re-ran all five drifts. A check whose deletion turns no drift MISSED
is a check the suite does not test.

    ablated check                                d1 d2 d3 d4 d5   self-test exit
    ---------------------------------------------------------------------------
    UNMUTATED (control)                          C  C  C  C  C    0
    check() blinded entirely                     M  M  M  M  M    1
    P1 agreement: workflow paths == WATCHED      C  C  C  C  C    0     <-- blind
    P1 both paths: blocks present                C  M  C  C  C    1
    P1 WATCHED has no duplicates                 C  C  C  C  C    0     <-- blind
    P3 completeness: reachable => watched        C  C  M  M  C    1
    P2 identity: watched => part of the gate     C  C  C  C  M    1
    P3 closure: no broken import target          C  C  C  C  C    0     <-- blind

**Three of the six ablatable checks can be deleted with the suite still green.**
The worst is the first:

> **Delete the agreement check — the comparison of the workflow's `paths:`
> against the shell's `WATCHED` — and the self-test still prints 5/5 CAUGHT and
> still exits 0.**

That check is *the entire stated reason the file exists*. Its own docstring:
*"Two copies of a list is exactly the shape that rots. This script is the reason
it cannot rot silently."* The reason it cannot rot silently is the one thing
that can be removed silently.

**Why:** drift 1 is over-determined. It raises **three** problems, not one —

    - workflow `paths:` block 1 disagrees with … WATCHED: only in workflow [mgb0a6…]
    - workflow `paths:` block 2 disagrees with … WATCHED: only in workflow [mgb0a6…]
    - scripts/onethird_mgb0a6_spectral_killshot_probe.py is reachable from the
      gate but NOT watched -- editing it would not re-run the mutation demo

— because removing an entry from `WATCHED` is *both* a disagreement *and* an
under-coverage. The third problem survives the ablation, `problems` stays
non-empty, and the suite calls it CAUGHT.

The duplicate check (§1b's forcing) and the broken-import-target check are blind
for the simpler reason that no drift exercises them at all.

**PREDICTION SCORECARD:** C3 predicted exactly this, and C8 **understated** it —
I predicted one blind check out of four, and measured three out of six.

**REPAIR, measured not guessed.** Two changes, both small:

1. **Add the converse drift** — *"workflow loses an entry the shell still has"*.
   I ran it: **CAUGHT**, and it is *uniquely* agreement's (coverage is
   unaffected, so nothing else fires). One case, and property 1 acquires a probe.
2. **Assert the problem, not its non-emptiness.** Give each case an expected
   substring and require it. Every drift above already produces a distinctive
   message; the suite simply does not look at them.

---

## 3. FINDING 2 — THE DRIFT SUITE IS A POPULATION CLAIM, AND SIX OF EIGHT REALISTIC DRIFTS ARE MISSED

The five drifts are described as the ways this can go wrong. I built eight more,
each a single realistic edit, and ran them against the **unmutated** checker:

    candidate drift                                                     verdict
    ----------------------------------------------------------------------------
    workflow loses an entry the shell still has (converse of drift 1)   CAUGHT
    workflow gains a DOUBLE-quoted path, FIRST in each block            CAUGHT
    workflow gains a DOUBLE-quoted path, LAST  in each block            MISSED
    workflow gains a BARE (unquoted) path, LAST in each block           MISSED
    gated instrument imports a local module not named onethird_*        MISSED
    gated instrument reads a dataset through a VARIABLE name            MISSED
    gated instrument reads a dataset with an explicit "r" mode          MISSED
    gated instrument reads a dataset with SINGLE quotes                 MISSED

**3a. The population is bounded by a quote character — and by POSITION.**
`parse_workflow_paths` admits only `- '…'`. I confirmed with PyYAML that
`- "x/y.yml"`, `- 'x/y.yml'` and `- x/y.yml` are the *same string* to YAML, so
GitHub honours all three and the hand parser sees only one.

The sharp part is that **the same edit has opposite outcomes depending on where
it sits.** At the *top* of a block the non-conforming line resets `current` to
`None`, the remaining 17 entries are dropped, the parser reports block sizes
`[0, 0]`, and the disagreement is enormous and loud — CAUGHT. At the *bottom*,
the 17 are already collected, the reset costs nothing, and the extra trigger
path is invisible: `check()` returns **no problems** and the gate prints
`watchlist consistent: 17 paths` while GitHub is triggering on eighteen.

**This refutes my own prediction E1**, which said flatly that a double-quoted
entry would be silently dropped and not caught. It is caught at one position and
not at the other, and I would have reported the wrong thing had I tested only
the position I first chose. The corrected, positional claim is the finding.

**3b. The closure is bounded by a name prefix.** `_IMPORT_RE` admits only
`onethird_\w+`, and captures only the first module on a line. The docstring's
claim *"The import scan has no such limit"* is therefore **false as written** —
refuted by construction above. In fairness: I measured the corpus and there is
**no live instance** (0 non-`onethird_*` sibling imports, 0 comma-carrying
`onethird_*` import lines across the closure and `MECHANISM`). It is a latent
hole and an overclaim, not a present gap.

---

## 4. FINDING 3 — THE DATASET DERIVATION IS 1-OF-4 BLIND ON READS, AND IS RIGHT BY COINCIDENCE

Property 3 is advertised as *"COMPLETENESS, derived rather than asserted."*
Here is the derivation's actual reach. Population: every
`os.path.join(REPO, "data", …)` site in the **10-module import closure**. Grain:
one call site.

| module | sites | matched by `_DATA_RE` | invisible | what they are |
|---|---|---|---|---|
| `onethird_mg2c34_n7_overlap_test.py` | 2 | 1 | 1 | 1 read (matched), 1 **write** |
| `onethird_mg5ad1_gate_blindspot_probe.py` | 3 | 0 | 3 | **2 reads via `REF`**, 1 write |
| `onethird_mg60d3_gate_mutation_demo.py` | 1 | 0 | 1 | 1 write |
| `onethird_mg75f0_gate_class_closure_demo.py` | 1 | 0 | 1 | **1 read via `fn`** |
| `onethird_mg7db4_probe_mutation_battery.py` | 1 | 0 | 1 | 1 write |
| **total** | **8** | **1** | **7** | **4 reads, 4 writes** |

Four of the seven invisible sites are writes, correctly excluded — no defect.
The other three **are reads of `data/` that the scanner cannot see**, because
the filename is a variable (`REF` at `mg5ad1:346` and `:550`, `fn` at
`mg75f0:362`) rather than a string literal.

**So the check that is "derived rather than asserted" sees 1 of the closure's 4
dataset reads.**

The watchlist is nonetheless **correct**: I resolved all three variables —
`REF = "onethird-mg8b64-L1b-bk-transport-transfer.json"` (`mg5ad1:153`) and
`DATASETS = ["onethird-mg8b64-L1b-bk-transport-transfer.json"]` (`mg75f0:209`)
— and every invisible read names the one dataset the visible read already put
on the list. **`datasets read 1` is the right answer, produced by a mechanism
that could not have found it.** A second dataset introduced through either
existing idiom would be unwatched and unreported.

Credit where due: the docstring **states** this limit for the data scan
(*"a module that reads a dataset some other way is invisible to it"*), which is
better than the corpus average. What it does not state is that the idiom it
names is already used, three times, inside the closure it is scanning.

---

## 5. THE NARROWING pm-onethird PROPOSED — CONSTRUCTED HERE, AND THE PRESCRIBED SAFETY TEST CANNOT FAIL

Item 2 proposes dropping `.github/workflows/script-controls.yml` from the
watchlist, with the warning: *"do not narrow the list without showing the
mg-7db4 drift self-test still fires on all five drifts."* I ran it.

**Arm 1 — edit the two watchlists only (17 → 16 paths, blocks `[16, 16]`):**

    check() -> 1 problem; the gate exits 1
      - .github/workflows/script-controls.yml is reachable from the gate but
        NOT watched -- editing it would not re-run the mutation demo

**The mechanism does not go blind under the proposed narrowing. It REFUSES it.**
`script-controls.yml` is a member of `MECHANISM` inside the consistency checker,
so the narrowing cannot be done in two files. It takes three.

**Arm 2 — also drop it from `MECHANISM` (16 paths):** consistent, exit 0, and

    drift 1  shell WATCHED loses an entry the workflow still has   CAUGHT
    drift 2  workflow loses its pull_request paths filter          CAUGHT
    drift 3  gated instrument imports a module nobody watched      CAUGHT
    drift 4  gated instrument reads a dataset nobody watched       CAUGHT
    drift 5  watchlist grows a path unrelated to the gate          CAUGHT

**5/5. And that is the correction to pm-onethird's framing.**

> **The safety test item 2 prescribes is structurally incapable of failing under
> any narrowing, so passing it is not evidence that a narrowing is safe.**

The five drifts probe the *structural consistency* of the two lists against the
closure. Narrowing removes one path from all three places at once and preserves
that consistency exactly. There is no narrowing — of this path or any other —
that turns a drift MISSED. The warning was right to be given and it names the
wrong instrument: it asks for a green light from a lamp that is wired on.

**What the narrowing would actually cost**, since the prescribed test will not
tell you: `script-controls.yml` is the file that *wires* the gated steps. After
the narrowing, this two-commit sequence merges without the demonstration ever
re-running — commit A edits `script-controls.yml` to change which controls run
or with what arguments; commit B is anything at all. The demo that proves those
controls can still fail is skipped on precisely the commit that changed them.
The workflow's own header anticipates this: *"Editing script-controls.yml itself
is watched, so adding a step is covered."* The narrowing removes that sentence's
truth-maker. Seventeen minutes against that is the actual trade, and it is
pm-onethird's call, not mine.

---

## 6. THE TRIGGER, BOTH DIRECTIONS — CORRECT, 6/6, AND THE CONTROL CAN FAIL

`scripts/onethird_mge12a_trigger_direction_control.sh` runs **the real gate**,
unmodified, on **real commits** in a throwaway branch. It does not reimplement
the trigger; a reimplementation can only agree with itself.

    case                                         want   got    consistency-ran
    ---------------------------------------------------------------------------
    unwatched path only (docs/*.md)              SKIP   SKIP   YES   PASS
    watched path only (mgb0a6 probe)             RUN    RUN    YES   PASS
    watched + unwatched together                 RUN    RUN    YES   PASS
    near miss (watched path + '.bak' suffix)     SKIP   SKIP   YES   PASS
    watched DATASET only (not a script)          RUN    RUN    YES   PASS
    empty diff (base=HEAD, no-op merge)          SKIP   SKIP   YES   PASS

**A negative needs an instrument that could have shown the positive.** Six
PASSes are worth nothing until the same cases are shown to fail against a gate
that is wrong. Two mutant arms, each one edit to a copy of the real gate:

    matcher -x dropped (substring match)          real=SKIP  mutant=RUN   CONTROL SEES IT
    trigger decision inverted (-z -> -n HITS)     real=RUN   mutant=SKIP  CONTROL SEES IT

The control changes its verdict in **both** directions — a gate that fires when
it should skip, and a gate that skips when it should fire. The 6/6 is over an
instrument that can distinguish right from wrong.

**This is the first time the fast path has been shown correct rather than fast.**

Two things a reader should take from the table beyond the verdicts:

- **`consistency-ran` is YES on every row, including the SKIPs.** The negative
  direction is not "the gate does nothing": the mg-7db4 consistency check runs
  *before* the trigger decision, so an unwatched-only commit still pays it and
  can still be failed by it. The cheap path is cheap, not absent.
- **The one committed dataset triggers the demo like any script.** Worth stating
  because it is the only non-`.py`, non-`.yml` entry on the list.

---

## 7. THE DURATION — 18 LITERALS, AND THE PARENT'S "SIX FIGURES" IS A COUNT OF LINES

Item 3's briefed target — *"if a new figure was published, check it carries the
load it was measured under"* — is **NOT APPLICABLE**, not PASS: §0 established
that no figure was published. Reporting it as a pass would be the vacuity again.

What I could do is re-derive the count the ticket rests on.

**POPULATION:** every duration literal in `scripts/refinery_gate.sh` at `84f510a`
— all 307 lines, comments and echoed branch text alike.
**GRAIN:** one regex match = one literal; a range (`~16-21 min`) and a composite
(`24 h 08 m 55 s`) each count as **one**. *That choice has to be stated or the
number is not defined, and the parent's "six" never stated it.*
**TOTAL: 18 literals**, hand-classified by subject (the classification is
printed per line by the probe and asserted complete — an unclassified literal is
a fatal error, so it cannot go stale silently):

| class | n | subject |
|---|---|---|
| A | **7** | this gate's own runtime, or a step of it |
| B | 2 | the GitHub Actions workflow's runtime |
| C | 1 | an end-to-end refinery MR wall-clock |
| D | 8 | the 2026-07-30/31 red window — an **outage**, not a runtime |

**7a. "Six different figures" is six LINES, not six figures.** Class A holds
**7 literals at 6 distinct lines**: line 289 carries two of them
(`~30 s on CI, ~2.5 min loaded`). The label says *figures* and the number counts
*lines* — the row-versus-grain mismatch this arc keeps finding, this time in the
ticket that was filed about mis-stated quantities. Correcting pm-onethird's
framing, as asked.

**7b. The bigger correction: less than half the file's durations are runtimes at
all.** Class D — eight literals, the largest class — is the duration of an
outage. A reader grepping this file for "how long does this take" meets
`24 h 08 m 55 s` five times before meeting `~11 min`.

**7c. Conditions.** 4 of 18 literals sit on a line carrying *any* load or regime
word (`idle`, `loaded`, `on CI`, `concurrent`). **0 of 18** state
what-is-timed **and** which-clock **and** under-what-load together. That zero is
by inspection, not by regex: no line in this file names a clock, a host, a date
or a load figure beside a duration. pm-onethird's three-clock diagnosis is
confirmed and it is if anything understated — the file also mixes runtimes with
an outage window on the same page.

**7d. And `17` is in this file as both a duration and a population size.**
`~17 minutes` (L21) and `17 paths` (the gate's first printed line). `grep 17`
returns both. I note it because the parent's item 1 was retracted over exactly
one agent's grep returning one line of a variable.

**What I am not offering:** a corrected duration. I did not time this gate.
pm-pogo's rule is right and stricter than substituting a quiet-box figure —
where a figure's conditions are unrecoverable the entry is NOT KNOWN with the
reason. I have added no measurement of my own to a file whose problem is
unconditioned measurements.

---

## 8. PREDICTION SCORECARD

**41** labelled predictions at `491220d` — 4 A, 4 B, 8 C, 4 D, 6 E, 6 F, 4 G,
5 H, counted by `grep -cE '^\*\*[A-H][0-9]'` over that file.

**My own pre-registration commit message says "30 predictions". It is wrong.**
I wrote a round number I had not counted, in the subject line of a commit whose
entire purpose is to fix claims before they can drift — and `H5` had predicted
exactly that failure for me: *"the single most likely way for this audit to be
WRONG overall is that I will assert a count without naming its population… If
the report contains a bare number, that is the finding against me."* It did.
That commit begins with `predictions:` and is not amended; the correction lives
here instead.

Held as stated (36): **A1 A2 A4 B1 B2 B3 B4 C1 C2 C3 C4 C5 C6 C7 D1 D2 D3 D4
E2 E3 E4 E5 E6 F1 F2 F3 F4 F5 G1 G2 G3 G4 H1 H2 H3 H4**.
Held against me (1): **H5**, above.

**Wrong, and how (4):**

- **E1 — REFUTED.** I predicted a double-quoted workflow path would be silently
  dropped and NOT caught. It is caught when it is first in the block (it
  truncates the block and the disagreement is loud) and missed when it is last.
  My prediction named the right hole and the wrong mechanism, and had I tested
  only my first position I would have reported the opposite of the truth.
- **C8 — UNDERSTATED.** I predicted five drifts probing four checks with one
  blind. Measured: six ablatable checks with **three** blind.
- **A3 — WRONG AS STATED.** `refinery_gate.sh` was not byte-identical; `ced6861`
  edited it an hour after `mg-856d` was filed. Right in substance: no duration
  figure was added or changed.
- **F6 — NOT TESTED.** I predicted a rename of a watched file triggers the demo
  and then did not build the case. A rename that leaves the tree's import
  closure broken fails the consistency check *before* the trigger decision, so
  the case needs a coordinated rename to be meaningful, and I did not build one.
  Recorded as untested, not as passed.

**H4 held against me, and it is the sharpest thing in this document.** My first
duration regex missed `~30-minute` (L178) and `25-minute` (L278) because it did
not handle the hyphenated compound form. That is the *identical* defect
documented at L171-176 **of the file I was measuring** — a sweep for a number in
a corpus that hyphenates and hard-wraps must handle those forms or its total
means "the forms I thought of". Two prior authors hit it with `grep "21 hours"`;
I hit it with a regex, in an audit whose premise is that inherited methods
reproduce inherited errors. It also split `24 h 08 m 55 s` into two literals and
read `~2.5 min` as `5 min`. Fixed, and the fix is commented in the probe at the
site so the next author meets the story where the code is.

Had I not caught it, this report would have said **14** literals with the two
hyphenated ones missing — a number I would have presented as a population.

---

## 9. WHAT I DID NOT DO

- **I did not run the demonstrations.** Not `mg-60d3` (~11 min), not `mg-75f0`,
  not the `mg-7db4` battery, not the Actions job. Every claim in §6 is about the
  **decision the gate reaches**, capped at 90 s; `rc=124` on the RUN rows is my
  cap, not a gate failure. Whether the demonstrations themselves are correct is
  other tickets' ground and I did not re-audit it.
- **I did not test against GitHub Actions.** §3a's claim that GitHub honours
  double-quoted and bare path entries rests on YAML equivalence, verified
  locally with PyYAML — not on a live Actions run. I have no run access here.
- **I did not measure any duration.** §7 counts literals; it times nothing. I
  have no unloaded-box figure to offer and I decline to import one.
- **I did not narrow the watchlist.** §5's narrowing exists only inside the
  probe's in-memory copy. **No watchlist file is changed by this branch**, and
  the recommendation in §5 is deliberately left as pm-onethird's call.
- **I did not repair anything.** §2's two-line fix is measured and specified and
  not applied: this is an audit branch, and a repair to `mg-7db4`'s self-test
  belongs to whoever picks up `mg-856d`.
- **I did not verify the `24 h 08 m 55 s` red window** against `gh run` history.
  It is class D and outside this ticket; I counted its literals, I did not
  re-derive its value.
- **I did not check the F6 rename case** (see §8).
- **I did not audit `script-controls.yml`'s own contents**, only its membership
  in the watchlist and `MECHANISM`.

---

## 10. IF THIS AUDIT FOUND NOTHING, HERE IS WHAT WOULD HAVE SHOWN IT

Stated because the brief requires a negative to carry its instrument, and
because three of the sections above **are** negatives.

- **§5 (narrowing is safe) would have been positive** if any of the five drifts
  had gone MISSED at 16 paths. The ablation table in §2 proves the harness *can*
  print MISSED: **9 of its 40 cells** (8 ablation rows × 5 drifts) are MISSED,
  across four different ablations, including one that turns all five at once. A
  5/5 CAUGHT from a harness that has never printed MISSED would mean nothing;
  and §3's eight candidate drifts add **6 more MISSED** from the *unmutated*
  checker, so the harness prints MISSED against the real target too, not only
  against sabotaged copies of it.
- **§6 (trigger correct) would have been positive** if either mutant arm had
  left the verdict unchanged. Both flipped it, in opposite directions.
- **§3b / §4 latency claims (no live instance)** would have been positive if the
  scanners had found a non-`onethird_*` sibling import, a comma-carrying import,
  or a dataset read naming a file other than the watched one. The scanners are
  the same ones that found **8** data sites and resolved **3** variables to a
  filename, so they were looking at the right places with working eyes.
- **§1 (the count is 17) would have been positive** if rows and distinct had
  disagreed, or if the PyYAML block sizes had disagreed with the hand parser's.
  I ran both parsers precisely so that a hand-parser bug could not hide inside
  its own answer — and §3a shows the hand parser *does* have such a bug, which
  is exactly why the cross-check was worth running.

---

## 11. FOR WHOEVER PICKS UP mg-856d

Ordered by what it buys:

1. **Add the converse drift** (`workflow loses an entry the shell still has`) to
   `_selftest`, and **assert the expected problem substring** per case instead of
   non-emptiness. Measured CAUGHT and uniquely attributable. Without this the
   agreement check, the duplicate check and the broken-import check are all
   removable in silence (§2).
2. **Do not treat "all five still fire" as clearance to narrow.** It cannot fail
   under a narrowing (§5). If you narrow, the thing to argue is the
   `script-controls.yml` two-commit gap, not the drift suite.
3. **The narrowing takes three edits, not two** — both watchlists *and*
   `MECHANISM` (§5). The consistency check will stop you at two, correctly.
4. **Anchor the workflow paths parser**, or drop the hand parser. Requiring
   `- '…'` makes an appended double-quoted or bare entry invisible while GitHub
   honours it (§3a). One cheap fix: after parsing, count the `- ` lines inside
   each `paths:` block and fail if it differs from the number parsed.
5. **The duration table** wants four row kinds (measured-with-conditions,
   historical-and-labelled, derived, NOT KNOWN) and a **subject** column before
   a load column — over half this file's duration literals are not runtimes at
   all (§7).
