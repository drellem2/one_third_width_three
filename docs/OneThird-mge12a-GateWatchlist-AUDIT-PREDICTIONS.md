# mg-e12a — pre-registered predictions for the INDEPENDENT AUDIT of the gate-watchlist repair

**Written 2026-08-06, committed BEFORE any audit code of this ticket exists.**
Tree audited: `84f510a` (`origin/main` at the time of writing; my worktree HEAD
is the same commit).

I have READ `scripts/refinery_gate.sh`,
`scripts/onethird_mg7db4_watchlist_consistency.py`,
`.github/workflows/gate-mutation-demo.yml`, `mg show mg-856d` and
`mg show mg-e12a` before writing these. I have written no script, run no
probe, and produced no measurement. Reading the target is not measuring it;
predictions made without reading the target would be predictions about a
different file.

Every prediction below is falsifiable and is written so that the measurement
that would refute it is obvious. Section H predicts against myself.

---

## A. THE PARENT — a structural prediction, and the first thing I will check

My dispatch brief says, in its own words, *"Pre-filed audit; its parent has
landed."*

**A1.** That sentence is FALSE. `mg-856d` is `Status: available` — never
claimed, never done — and **no commit in `origin/main` references `mg-856d`.**
I predict `git log origin/main --format=%s | grep -c mg-856d` is `0`.

**A2.** Therefore the watchlist was NOT narrowed. I predict `WATCHED` in
`scripts/refinery_gate.sh` at `origin/main` still contains
`.github/workflows/script-controls.yml` as its second line, and still has
seventeen entries.

**A3.** Therefore no new duration figure was published either. I predict the
duration literals in `scripts/refinery_gate.sh` are byte-identical to what they
were before `mg-856d` was filed (2026-08-05 19:13:54Z).

**A4.** So the audit as briefed — "if the watchlist was narrowed, prove the
self-test still fires" — has a **vacuously satisfiable** form: with no
narrowing, "the self-test still fires on all five" is true of a list nobody
touched, and reporting that as a PASS would be a PASS over an empty population.
I predict that the honest version of this audit is therefore not the briefed
one, and that I will have to CONSTRUCT the narrowing myself in order to have
anything to test. I pre-register that I will do exactly that.

## B. THE COUNT — re-derived by me, population and grain named

**B1.** `WATCHED` contains exactly **17** non-empty lines and **17 distinct**
path strings.
- POPULATION: the lines of the single-quoted `WATCHED='...'` literal in
  `scripts/refinery_gate.sh` at `84f510a`.
- GRAIN: one repo-relative path string per line.
- METHOD I will use: `git show 84f510a:scripts/refinery_gate.sh | awk` over the
  literal, `grep -c .` for rows and `sort -u | grep -c .` for distinct — two
  numbers, not one, so a rows-vs-set mismatch would be visible rather than
  assumed away.

**B2.** The gate's own printed `17` is
`len(parse_shell_watchlist(...))` — a **list length**, i.e. ROWS, under a label
that says `paths`. I predict rows and distinct paths coincide at this revision
(17 = 17), so the label is *accurate here* but is **not forced to be accurate
by the print statement**. I further predict the mismatch is UNREACHABLE at the
print site — a duplicate would be caught by the `len(watch_set) != len(watch)`
branch, `check()` would return a problem, and `main()` returns 1 before ever
reaching the print. So this is a label/grain mismatch that **cannot be
exhibited**, and I will label it FORCED with that forcing named.

**B3.** Both `paths:` blocks in `.github/workflows/gate-mutation-demo.yml`
contain 17 entries each, as identical sets to `WATCHED`. Total path strings in
the mechanism = **51 = 17 x 3**.

**B4.** pm-onethird's retraction states the variable "literally contains all
seventeen paths". I predict I will CONFIRM that by my own count, and that this
makes three consecutive agents to state a size for this variable of whom the
first two were wrong. My count is the fourth statement and is re-derived, not
inherited.

## C. THE FIVE DRIFTS AGAINST THE CURRENT (UN-NARROWED) LIST

**C1.** All five drift cases report `CAUGHT` on the tree at `84f510a`, and
`scripts/onethird_mg7db4_watchlist_consistency.py` exits 0.

**C2 — the one I expect to matter.** The self-test asserts only that
`check()` returns a **non-empty** list. It never checks WHICH problem fired.
I predict this is not a hypothetical weakness: I predict at least one drift is
caught by a check OTHER than the one it is named for, and therefore at least
one of the script's three stated properties can be **deleted outright with all
five drifts still reporting CAUGHT and the script still exiting 0**.

**C3 — the specific claim.** Drift 1, *"shell WATCHED loses an entry the
workflow still has"*, is the ONLY case that names property 1 (AGREEMENT). But
removing `scripts/onethird_mgb0a6_spectral_killshot_probe.py` from `WATCHED`
also removes it from `watch_set` while it remains in the import closure — so
the COMPLETENESS check (`"... is reachable from the gate but NOT watched"`)
fires on the same drift. I predict:

> If I delete the agreement comparison (the `for i, block in enumerate(blocks)`
> loop) from `check()`, the self-test still prints **5/5 CAUGHT** and
> `main()` still exits **0**.

That is: **property 1 — the entire stated reason this file exists, "Two copies
of a list is exactly the shape that rots" — has no drift case that uniquely
exercises it, and can die silently.**

**C4.** The converse drift is absent from the suite: no case removes an entry
from the WORKFLOW while the shell keeps it. I predict such a case IS uniquely
caught by agreement (nothing else would fire, because coverage is unaffected) —
so the repair for C3 is **one added case**, not a redesign.

**C5.** Drifts 3 and 4 share a single check. I predict deleting the
`expected - watch_set` loop makes **both** go MISSED simultaneously — they are
two probes of one mechanism, not two mechanisms.

**C6.** Deleting the `watch_set - expected` loop makes **exactly drift 5** go
MISSED.

**C7.** Deleting the `len(blocks) < 2` check makes **exactly drift 2** go
MISSED — agreement will NOT rescue it, because the surviving `push` block still
equals `WATCHED` as a set.

**C8 — the summary I expect to prove.** Five drift cases probe **four** checks;
one check (agreement) has no unique probe and one check (completeness) is
probed twice. The suite's advertised width (5) exceeds its attributive width
(4), and its attributive width over-counts by one.

## D. THE NARROWING THAT WAS PROPOSED BUT NEVER DONE

pm-onethird's surviving item 2 proposes dropping
`.github/workflows/script-controls.yml` from the watchlist. Nobody has done it.
I will do it, in a scratch copy, so that the briefed question has a subject.

**D1.** The narrowing CANNOT be done by editing the two lists alone.
`.github/workflows/script-controls.yml` is a member of the `MECHANISM` set
inside `onethird_mg7db4_watchlist_consistency.py`. Removing it from both
watchlists therefore makes `check()` report
`"... is reachable from the gate but NOT watched"` and the gate exits **1**.

**D2.** So the mg-7db4 self-test does not go BLIND under the proposed
narrowing — **it REFUSES it.** The parent's warning ("do not narrow the list
without showing the drift self-test still fires") is aimed at a failure mode
that this mechanism structurally cannot have for this particular path.

**D3.** After the *three*-file narrowing (both watchlists **and** `MECHANISM`),
I predict the tree is consistent again at **16** paths and **all five drifts
still report CAUGHT**. The five drifts are sensitive to the STRUCTURAL
consistency of the lists, not to their membership, so narrowing does not
disable any of them.

**D4.** I predict the real cost of the narrowing is elsewhere and is not a
blindness of the five: it is that `script-controls.yml` is the file that WIRES
the gated steps, so after the narrowing a commit that edits which controls run
no longer re-runs the demonstration that proves those controls can fail. I
predict I will be able to state that as a concrete two-commit scenario.

## E. THE MEMBERSHIP RULE — what the population is silently defined by

The arc's standing finding is that a population gets defined by an
unremarked character. I predict this mechanism has that shape in at least
two places.

**E1 — the quote character.** `parse_workflow_paths` admits only
`^\s*-\s*'([^']+)'\s*$` — **single**-quoted entries. A YAML-legal
`- ".github/workflows/foo.yml"` or bare `- .github/workflows/foo.yml` is
**invisible to the parser**. I predict: adding a double-quoted path to BOTH
`paths:` blocks and to neither watchlist copy is **NOT CAUGHT** — the agreement
check compares against a set that silently dropped the entry, so GitHub's
trigger and the shell's trigger genuinely disagree while the consistency
checker prints `watchlist consistent`. I predict this is a LIVE hole in the
admission rule, exercisable today, and that the current tree happens not to
exhibit it because every entry is single-quoted.

**E2 — the name prefix.** `_IMPORT_RE` admits only `onethird_\w+`. A gated
instrument importing a local helper not named `onethird_*` is outside the
closure and therefore unwatched, silently. I predict this is LATENT: no current
member of `ROOTS` or of the closure imports such a module. I will measure this
rather than assume it.

**E3 — one module per line.** `_IMPORT_RE` captures only the first module of
`import onethird_a, onethird_b`. I predict LATENT (no such line in the corpus)
and I will measure it.

**E4 — the data idiom.** `_DATA_RE` admits only
`open(os.path.join(REPO,"data","<name>"))` with **double** quotes and an
optional `,"w"`, after all whitespace is stripped. Single quotes, an explicit
`"r"` mode, an `encoding=` kwarg, or a variable filename are all invisible.
This limit is STATED in the docstring, which is to its credit. I predict the
docstring's neighbouring claim — *"The import scan has no such limit"* — is an
**OVERCLAIM**, refuted by E1/E2/E3. I predict at least one read of a `data/`
file somewhere in the closure is invisible to `_DATA_RE`; if there is none I
will say so and say what that means.

**E5 — the shell.** `for path in $WATCHED` is an unquoted expansion: it
word-splits on `IFS` and performs pathname expansion. A watched path containing
a space, `*`, `?` or `[` would not behave as written. I predict LATENT.

**E6.** I predict the count of DISTINCT admission rules that silently bound
this population is at least **four** (single-quote in the workflow parser,
`onethird_` prefix in the import scanner, double-quote-plus-idiom in the data
scanner, whole-line-exact `grep -qxF` in the shell matcher), and that none of
the four is stated at the place a reader meets the seventeen.

## F. THE TRIGGER, BOTH DIRECTIONS

**F1 (positive).** A commit touching ONLY
`scripts/onethird_mgb0a6_spectral_killshot_probe.py` makes the gate print
`=== watched paths changed:` and proceed into the demonstrations.

**F2 (negative).** A commit touching ONLY an unwatched path (a `docs/*.md`)
makes the gate print
`=== no watched path changed -- gate-mutation demo not required` and exit **0**.

**F3.** A commit touching one watched AND one unwatched path runs the demo —
the rule is ANY, not ALL.

**F4.** The negative direction is NOT "the gate does nothing": the mg-7db4
consistency check runs BEFORE the trigger decision, on every merge request. So
an unwatched-only commit still pays the consistency check and can still be
failed by it. I predict I will observe `=== mg-7db4 watchlist consistency` in
the negative-direction output.

**F5.** Matching is `grep -qxF` — whole line, fixed string. A changed path that
merely CONTAINS a watched path as a substring does not match. I predict correct
behaviour here.

**F6.** A pure RENAME of a watched file triggers the demo, because
`git diff --name-only` reports the old path too and the old path is watched.

## G. THE DURATION

**G1.** pm-onethird says the file "states its OWN runtime in six different
figures". I predict I will count **more than six** duration literals in
`scripts/refinery_gate.sh` alone, and that the "six" is itself an
un-populated count — the ticket never says over which file(s), nor what
counts as a figure (is `~16-21 min` one figure or two?). I predict I will have
to define the population before I can state a number, and that doing so is the
finding.

**G2.** No duration literal in `scripts/refinery_gate.sh` carries a MEASUREMENT
condition. Two carry a REGIME word (`~11 min idle, more under load`;
`~30 s on CI, ~2.5 min loaded`), which names a contrast without naming a load,
a date, a host or a clock. I predict zero literals in that file state all three
of what-is-timed / which-clock / under-what-load.

**G3.** The `~17 minutes` at line 21 is orphaned: it is not equal to, and not
reconcilable with, the cost table at lines 288-299 (ms + ~30 s + ~11 min) that
describes the same blocking path. I predict `17` appears in this file both as a
DURATION and as a WATCHLIST SIZE, and that a reader grepping `17` gets both.

**G4.** Since no repair landed (A3), the briefed target "if a new figure was
published, check it carries the load it was measured under" has **no subject**.
I predict I will report it as NOT APPLICABLE with the reason, not as a PASS.

## H. PREDICTIONS AGAINST MYSELF

**H1.** At least one prediction in A-G is WRONG. I will say which, in the
report, without softening it.

**H2.** A red I produce by mutation proves nothing unless the SAME harness
shows green on the unmutated tree in the same run. I predict my first cut of
the mutation harness will be capable of producing a red for a reason other than
the mutation (an import error, a path error, a copied tree that was already
inconsistent) and that I will have to add an explicit unmutated-control arm to
tell those apart.

**H3.** I will NOT run the `mg-60d3` demonstration (~11 min) or the ~30 min
Actions job to completion. Every trigger claim in F is a claim about the
DECISION the gate reaches, not about the demonstrations it then runs, and I
will label it that way everywhere it appears.

**H4.** I predict I will find at least one defect in the mechanism that my own
audit code initially reproduces — the standing target "does the deliverable
reproduce, in its own new code, the defect it was sent to repair" applies to me
and I expect to fail it once before I catch it.

**H5.** I predict that the single most likely way for this audit to be WRONG
overall is that I will assert a count (of duration figures, of admission rules,
of drifts) without naming its population, having spent this document insisting
on exactly that. If the report contains a bare number, that is the finding
against me.

---

### WHAT THESE PREDICTIONS DO NOT COVER

- I do not predict anything about whether the demonstrations themselves
  (`mg-60d3`, `mg-75f0`, the `mg-7db4` battery) are correct. That is other
  tickets' ground and I am not re-auditing it.
- I do not predict anything about the GitHub Actions run history or its
  timings; I have no run access here and will not infer one from a log.
- I do not predict whether the narrowing SHOULD happen. That is pm-onethird's
  call and their own item 2 says it is an opinion. I predict only what the
  mechanism does if it is attempted.
