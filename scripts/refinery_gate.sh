#!/bin/sh
# mg-7db4 -- the BLOCKING half of the gate-mutation trigger.
#
# WHY THIS FILE EXISTS AT ALL.  `.github/workflows/gate-mutation-demo.yml`
# expresses the trigger, but in this repo GitHub Actions cannot enforce it:
# `main` has no branch protection and no ruleset (checked, both empty), and
# merges are performed by the pogo refinery, which rebases and fast-forwards
# straight to `main` without ever reading a check run.  A branch that mutates
# the gate would therefore merge while its Actions run was still starting.
# Requiring the check on GitHub instead is not an option -- the refinery pushes
# to `main` directly rather than through a PR, so branch protection would block
# every merge in this repo, not just the ones this ticket is about.
#
# So the trigger is stated twice, once where it is visible (Actions) and once
# where the merge decision is actually made (here).  The two copies are held in
# step by scripts/onethird_mg7db4_watchlist_consistency.py, which parses both
# and fails if they disagree -- duplication that cannot silently drift.
#
# THE COST RULE.  script-controls.yml opens by saying its steps must be
# order-seconds.  On a commit that touches nothing in WATCHED this script is a
# `git diff` and a `grep`: milliseconds.  The demonstrations below are paid only
# by commits that can invalidate them -- see the DURATION TABLE for what "the
# demonstrations" costs, on which clock, and under what load.
#
# ("~17 minutes" stood here from df7db8b until mg-856d.  It was right when it
# was written -- probe + battery + demo, the three things the blocking gate ran
# that day -- and 245085e moved the battery out to Actions eight hours later
# without touching this line.  The figure did not rot; the configuration it
# described was dismantled around it, which is the harder version of the same
# defect and the reason the table below states a CONFIGURATION as well as a
# number.)
#
# ============================ THE DURATION TABLE (mg-856d) ==================
#
# WHY A TABLE.  This file stated its own runtime in NINE places.  pm-onethird
# found six and said so; the other three are the two in the WHAT RUNS HERE
# ledger near the bottom and the echo above the final exec.  None of the nine
# said which of three different clocks it was on, and while filing the ticket
# about that, pm-onethird put a clock-(c) figure into it twice.  A quantity
# stated nine times with no statement of what each instance measures is this
# repo's most-audited defect class, sitting in the comments of the gate that
# enforces it.
#
# THE THREE CLOCKS.  They are not convertible into one another and no figure
# below has been carried across them:
#   (a) GITHUB ACTIONS wall-clock, hosted runner.  Different machine, different
#       CPU, no fleet contention, pays a pip install.
#   (b) LOCAL PROCESS wall-clock on the fleet host.  What the refinery gate
#       actually spends.  Sensitive to fleet load by roughly 10x (mg-1b8c).
#   (c) END-TO-END REFINERY MR wall-clock: queue wait + (b) + the merge.  Bounded
#       below by (b) and above by nothing, because the refinery has one serial
#       slot and an MR waits behind every MR ahead of it.
#
# STATUS values: MEASURED (figure + clock + load all recorded), HISTORICAL (a
# past incident, not a specification of present behaviour), DERIVED (arithmetic
# on other rows), NOT KNOWN (conditions unrecoverable -- and the entry stays NOT
# KNOWN rather than being replaced by the nearest available measurement, which
# is pm-pogo's rule and is stricter than substituting a better-looking number).
#
#  SITE / PHRASE                     WHAT IS TIMED              CLOCK  STATUS
#  ---------------------------------------------------------------------------
#  header, THE COST RULE             probe + battery + demo,    (b)    HISTORICAL
#    (was "~17 minutes")             the blocking gate as it
#                                    stood on 2026-07-30 for
#                                    8 h, before 245085e moved
#                                    the battery to Actions.
#                                    Removed: the configuration
#                                    it described is gone.
#  READOUT, "this gate takes         this file's slow path,     (b)    DERIVED
#    ~11 min"                        uncontended.  It is the           and LOW
#                                    demo's ~11 min with the           by ~2 min
#                                    probe's ~30 s and the
#                                    readout's own gh calls
#                                    left out.
#  READOUT, "the workflow it         gate-mutation-demo.yml     (a)    MEASURED
#    reads takes ~16-21 min"         on a hosted runner.  21m          (not mine)
#                                    at 2026-08-06T11:48 on a
#                                    quiet box (load ~4),
#                                    measured by pm-onethird;
#                                    inside the stated range.
#  "the ~30-minute job"              gate-mutation-demo.yml,    (a)    DERIVED
#                                    all three demonstrations
#                                    (11 + 6 + 13); the job's
#                                    own header states the same
#                                    split and a 75-minute bound.
#  "sat in the refinery for          ONE past MR, mg-7db4's     (c)    HISTORICAL
#    22 minutes"                     own, 2026-07-30.
#  "a concurrent 25-minute           ONE past demonstration     (b)    HISTORICAL
#    demonstration"                  running beside it, same
#                                    host, same incident.
#  ledger, "mg-5ad1 blindness        that one probe.  26.5 s    (b)    MEASURED
#    probe ~30 s / ~2.5 min          uncontended is mg-75f0's;         (not mine)
#    loaded"                         2m33s loaded is mg-7db4's,
#                                    taken during a concurrent
#                                    multi-gate demonstration.
#  ledger + final echo,              that one demonstration,    (b)    MEASURED
#    "mg-60d3 mutation demo          six full --no-sweep gate          (not mine)
#    ~11 min"                        runs, uncontended.
#  ---------------------------------------------------------------------------
#  MEASURED BY mg-856d, 2026-08-06, and the first figure in this file that
#  carries its own load.  scripts/onethird_mg856d_gate_cost_measure.sh, clock
#  (b), this 10-core fleet host, /usr/bin/python3, DELIBERATELY UNDER
#  CONTENTION (the point was a second point on mg-1b8c's ~10x curve, not a
#  third quiet reading):
#
#      mg-7db4 watchlist consistency (+ self-test)     0.2 s   load 17 -> 17
#      mg-5ad1 gate blindspot probe                  105.9 s   load 17 -> 38
#      mg-60d3 gate mutation demo                   5150.4 s   load 38 -> 53
#                                                              (peak 1-min 149)
#      ------------------------------------------------------------------
#      BLOCKING SLOW PATH, end to end               5256.5 s = 1 h 27 m 36 s
#
#  Against the uncontended figures above that is 4.0x for the probe and 7.8x
#  for the demo -- consistent with mg-1b8c's ~10x and not equal to it, so the
#  10x is an order of magnitude and not a coefficient.
#
#  THE NUMBER THAT MATTERS IS NOT THE 1 h 27 m.  It is that .pogo/refinery.toml
#  sets timeout = "90m", and this run finished 2 m 23 s inside it -- 97.3% of
#  the budget, on a host that was busy but not extraordinary.  The slow path is
#  not bounded by anything except that timeout, and a load average of 149 is
#  reachable on an ordinary evening.  mg-856d's narrowing does not bound the
#  slow path; it removes ~57% of the merges that enter it.
#  ---------------------------------------------------------------------------
#  NOT IN THIS FILE, and recorded here because three agents reasoned from it:
#  1 h 17 m -- mr-d9png12tjv1h244d8420, submitted 18:51:00, merged 20:08:43 on
#  2026-08-05.  Clock (c).  It bundles queue wait, this gate and the merge, and
#  it was taken while the 1-minute load average peaked near 300.  IT IS NOT A
#  DURATION OF THIS GATE.  What this gate cost inside it is NOT KNOWN and is not
#  recoverable: the refinery records MR start and end, not gate start and end.
#  The quiet-box 21m of 2026-08-06 is NOT a substitute for it -- different clock
#  AND different load regime -- and substituting it would be the same error
#  wearing a better figure.
#
# SENSITIVITY, since a duration with no conditions is a claim that does not
# reproduce.  Every (b) figure is sensitive to FLEET LOAD and to nothing else
# that has been observed to matter.  mg-1b8c measured roughly 10x inflation for
# concurrent heavy jobs on this host, and the mg-856d measurement above was
# taken deliberately UNDER load to put a second point on that curve.
#
# AND THE DEMO IS NOT ONE PROCESS, which no figure in this file said and which
# changes what a duration here even means.  It runs its cases CONCURRENTLY --
# `--case M1 --gate repaired` and `--case M1 --gate pre-repair` start in the
# same second -- and mg-856d measured a single gate run at 829% CPU with the box
# to itself, against ~290% each when three demonstrations competed.  One "gate
# step" is therefore a 7-8-core job on a 10-core host.  The refinery's
# one-serial-slot model costs a gate as one unit of work; this one is most of
# the machine, so its duration is a function of what else the fleet is doing AND
# its cost to the fleet is not captured by the slot count.  (Observed by the
# mayor while three arms were running; measured here.)
#
# ============================================================================
#
# WHAT THIS DOES NOT ENFORCE, stated so nobody reads more into a green merge
# than is there.  The rest of `script-controls.yml` -- the mg-8489 control, the
# mg-8ff1 counterexample, the mg-2c34 gate and the mg-5ad1 blindness probe --
# runs on GitHub Actions only, so in this repo it INFORMS and does not BLOCK,
# exactly as it did before this file existed.  Mirroring the whole fast gate
# here would add minutes to every merge for every author and is a repo-wide
# policy call, not this ticket's.  It is on the record in
# docs/OneThird-mg7db4-GateDemo-Trigger.md rather than fixed silently.
#
# FAIL-CLOSED.  Every way of not knowing -- no base ref, a failed diff, no
# numpy interpreter -- runs the demo or fails the gate.  A control that
# resolves ambiguity by skipping itself is the defect this ticket is about.
#
# Run by the refinery via .pogo/refinery.toml.  Also runnable by hand:
#   ./scripts/refinery_gate.sh                 # diff against origin/main
#   GATE_DEMO_BASE=HEAD~1 ./scripts/refinery_gate.sh
#   GATE_DEMO_FORCE=1 ./scripts/refinery_gate.sh    # run the demo regardless

set -eu

cd "$(dirname "$0")/.."

# The paths that can invalidate the demonstration.  Keep in step with the
# `paths:` lists in .github/workflows/gate-mutation-demo.yml -- the consistency
# check below enforces that, and also that this list still covers every corpus
# module the gated instrument imports.
WATCHED='.github/workflows/gate-mutation-demo.yml
.github/workflows/script-controls.yml
.pogo/refinery.toml
scripts/refinery_gate.sh
scripts/onethird_mg3934_ci_history_depth_control.py
scripts/onethird_mg7db4_watchlist_consistency.py
scripts/onethird_mg856d_exemption_control.py
scripts/onethird_mg7db4_probe_mutation_battery.py
scripts/onethird_mg5ad1_gate_blindspot_probe.py
scripts/onethird_mg60d3_gate_mutation_demo.py
scripts/onethird_mg75f0_gate_class_closure_demo.py
scripts/onethird_mg2c34_n7_overlap_test.py
scripts/onethird_mg4a86_sdquant_overlap.py
scripts/onethird_mg4a86_sector_leakage_and_tempering.py
scripts/onethird_mg4a86_standard_dominance_target_audit.py
scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py
scripts/onethird_mgb0a6_spectral_killshot_probe.py
data/onethird-mg8b64-L1b-bk-transport-transfer.json'

# ---------------------------------------- the BLOCKING-only exemption --------
# mg-856d.  WATCHED answers "can this commit invalidate the demonstration?" for
# TWO consumers with very different costs: the Actions job, which runs on
# GitHub's machine and holds nothing, and this script, which holds the fleet
# refinery's ONE serial slot while it runs.  The list below is the subset for
# which the answer differs -- watched, still in both `paths:` blocks of
# gate-mutation-demo.yml, still fully demonstrated on Actions, but NOT worth the
# blocking demonstration here.
#
# THE STANDARD FOR BEING ON THIS LIST is not "cheap to skip" but MEASURED
# INSENSITIVITY: scripts/onethird_mg856d_watch_sensitivity_probe.py traces every
# file the blocking instruments open and reports which watched paths they read.
# A path they never read cannot change the answer they give, so re-running them
# on its account demonstrates nothing.  Everything else about the list --
# that it stays inside WATCHED, that it can never reach a derived-closure member
# or the gate's own decision files, and that each entry's catcher is really
# wired -- is enforced on every merge by
# scripts/onethird_mg856d_exemption_control.py, with a five-drift self-test.
# An exemption list on a gate is the easiest place in this repository to build a
# control that cannot fail, and it is not going to be left unguarded.
#
# WHAT THE ONE ENTRY BELOW STOPS PAYING FOR, said plainly rather than implied:
# 12 of the 21 merge requests that fired this gate's slow path in its first
# 7.5 days did so ONLY because they touched script-controls.yml -- 57% of the
# firings, for a demonstration that does not read the file.  Full derivation,
# and the exact list of mutations that no longer have a BLOCKING catcher (it is
# empty, and that is argued rather than assumed), in
# docs/OneThird-mg856d-GateScope-Duration.md.
#
# CATCHER .github/workflows/script-controls.yml scripts/onethird_mg3934_ci_history_depth_control.py .github/workflows/script-controls.yml
DEMO_INSENSITIVE='.github/workflows/script-controls.yml'

# ------------------------------------------------------- interpreter ---------
# bare `python3` on the fleet host has no numpy (see the mg-5ad1 audit sec 4);
# /usr/bin/python3 does.  Pick the first one that can actually import it.
PY=''
for cand in ${GATE_DEMO_PYTHON:-} /usr/bin/python3 python3 python; do
    if command -v "$cand" >/dev/null 2>&1 \
       && "$cand" -c 'import numpy' >/dev/null 2>&1; then
        PY="$cand"
        break
    fi
done
if [ -z "$PY" ]; then
    echo "refinery_gate: FAIL -- no python3 with numpy on PATH." >&2
    echo "  The gate-mutation demo cannot run, so a gate change cannot be" >&2
    echo "  verified.  Failing rather than skipping: see the header." >&2
    exit 1
fi

# ------------------------------------------- watchlist consistency -----------
# Cheap, and it guards the two lists this whole mechanism is made of.  Runs on
# every merge request, not just gate-touching ones: a commit that adds an
# import to the gated instrument does not necessarily touch anything in
# WATCHED, and that is exactly the drift this catches.
echo "=== mg-7db4 watchlist consistency"
"$PY" scripts/onethird_mg7db4_watchlist_consistency.py

# mg-856d.  Same rule, one level in: the exemption list that makes this gate
# cheaper is checked before it is used, on every merge, whether or not anything
# watched changed.  Milliseconds, standard library only, and it fails closed --
# an unsound exemption stops the merge rather than quietly skipping the demo.
echo
echo "=== mg-856d demo-exemption control"
"$PY" scripts/onethird_mg856d_exemption_control.py

# --------------------------------------------------------- what changed ------
if [ -n "${GATE_DEMO_FORCE:-}" ]; then
    echo "=== GATE_DEMO_FORCE set -- running the demo unconditionally"
    CHANGED="$WATCHED"
else
    BASE="${GATE_DEMO_BASE:-}"
    if [ -z "$BASE" ]; then
        for ref in origin/main main origin/HEAD; do
            if git rev-parse --verify --quiet "$ref" >/dev/null 2>&1; then
                BASE="$ref"
                break
            fi
        done
    fi
    if [ -z "$BASE" ]; then
        echo "refinery_gate: no base ref resolvable -- running the demo." >&2
        CHANGED="$WATCHED"
    elif ! DIFF=$(git diff --name-only "$BASE"...HEAD 2>&1); then
        echo "refinery_gate: git diff against $BASE failed:" >&2
        echo "$DIFF" >&2
        echo "refinery_gate: cannot tell what changed -- running the demo." >&2
        CHANGED="$WATCHED"
    else
        echo "=== changed vs $BASE:"
        echo "$DIFF" | sed 's/^/    /'
        CHANGED="$DIFF"
    fi
fi

# HITS is every watched path that changed -- what the Actions trigger fires on,
# and what the readout below is for.  DEMANDING is the subset that is not on the
# mg-856d exemption list: the paths that can actually change what the blocking
# demonstrations assert.  Two lists because the two questions are different, and
# collapsing them is what made 57% of this gate's slow runs demonstrate nothing.
HITS=''
DEMANDING=''
for path in $WATCHED; do
    if printf '%s\n' "$CHANGED" | grep -qxF "$path"; then
        HITS="$HITS $path"
        # Written as plain `if`s rather than `&&` chains on purpose: the
        # `set -e` exemption for a failing non-final member of an AND-OR list is
        # real but subtle, and a gate is the last place to depend on it.
        exempt=0
        for e in $DEMO_INSENSITIVE; do
            if [ "$path" = "$e" ]; then
                exempt=1
            fi
        done
        if [ "$exempt" -eq 0 ]; then
            DEMANDING="$DEMANDING $path"
        fi
    fi
done

if [ -z "$HITS" ]; then
    echo "=== no watched path changed -- gate-mutation demo not required"
    exit 0
fi

echo "=== watched paths changed:"
for h in $HITS; do
    exempt=0
    for e in $DEMO_INSENSITIVE; do
        if [ "$h" = "$e" ]; then
            exempt=1
        fi
    done
    if [ "$exempt" -eq 1 ]; then
        echo "    $h   (mg-856d: demonstrated on Actions, not blocking here)"
    else
        echo "    $h"
    fi
done

# --------------------------------------------------------------- READOUT ----
# mg-3934 -- THE CONSUMER FOR THE INFORMATIONAL CHECK, and the reason it is
# here rather than anywhere else.
#
# `.github/workflows/gate-mutation-demo.yml` says of itself that it INFORMS and
# does not BLOCK.  That was true and it was also the whole defect: that
# workflow was red on EVERY run for 24 h 08 m 55 s -- twelve consecutive
# failures, first 2026-07-30T05:36:59Z (9fa4aaa) and last 2026-07-31T05:45:54Z
# (9991380), five of them on `main` -- because its last step resolved a
# historical commit that is not in a depth-1 `actions/checkout` clone, and
# nothing consumed the result, so a demonstration that had NEVER ONCE EXECUTED
# was indistinguishable from one running and passing.  A permanently-red check
# nobody reads is worse than no check: it cannot be told apart from a working
# one and it trains every reader to skip the column.
#
# THOSE FIGURES ARE mg-3946'S, AND THEY REPLACE "21 hours, eight consecutive
# runs".  That sentence was the ticket's own undercount; the mg-3934 doc
# corrected it to twelve runs in the same commit that wrote this file and left
# the stale count standing here, which is this arc's named pattern -- the
# over-wide statement surviving in a file's own description of itself, where
# nobody is watching.  Re-derived from `gh run list --workflow='Gate mutation
# demo'`, which is the record both figures were meant to be read off.
#
# THE WINDOW IS THE MEASURED ONE, NOT A ROUNDED ONE (mg-a471).  mg-3946 wrote
# "24 h 09 m" here and in the workflow header and left "~24 hours" standing in
# the mg-3934 doc -- the same pattern one turn later, in the same finding that
# names it.  86 935 s between those two timestamps is 24 h 08 m 55 s, and that
# is now the figure at all SEVEN sites: this comment, the branch text ~90 lines
# below (the only one a reader of a merge actually sees), the workflow header,
# docs/OneThird-mg3934-CI-HistoryDepth.md secs 2 and 3.4, and -- added by
# mg-76d0 -- the mg-3934 control's step comment in gate-mutation-demo.yml and
# the static-half step comment in script-controls.yml.
#
# THIS LINE SAID *FIVE* AND THERE WERE SEVEN (mg-76d0).  The two it missed both
# wrap the phrase across a comment continuation -- `for 21` ends one line and
# `# hours` begins the next -- so `grep -rn "21 hours"` returned neither, twice
# in a row, for two different authors.  A sweep for a stale number in a corpus
# that hard-wraps its comments must flatten the continuations before matching,
# or its "no sites left" means "no sites left ON ONE LINE".
#
# Making the ~30-minute job blocking was rejected for the reason stated above
# this section -- a gate long enough to want bypassed does not survive.  So the
# result is put where somebody already looks: the refinery's Gate Output, which
# `pogo refinery show <mr>` prints to the author of the merge, on exactly the
# commits that can invalidate the demonstrations.
#
# WHAT THAT SENTENCE STILL DOES NOT ESTABLISH (mg-3946).  `pogo refinery show`
# prints it; the polecat merge protocol polls `pogo refinery show <id> --json |
# jq -r .status` and reads no other field, and pogod reaps the author seconds
# after the merge lands.  Nothing else in this repository or on the fleet reads
# a GitHub Actions result -- no workflow_run trigger, no scheduled sweep, no
# notifier.  So in the automated merge flow this readout has no reader at all,
# and its audience is exactly a human who runs `pogo refinery show` by hand.
# That is better than nothing and it is not "somebody already looks".
#
# NON-BLOCKING BY CONSTRUCTION, and deliberately NOT fail-closed -- the only
# thing in this file that is not.  The fail-closed rule in the header is about
# the DEMONSTRATION: not knowing whether the gate still works must not resolve
# to "proceed".  This is a report on a different repository's CI, over the
# network, on a host that may have no `gh` and no credential.  Failing a merge
# because a status lookup timed out would be a new way to make merges flaky,
# which is the same disease.  Every branch below therefore ends in a printed
# line and a zero exit.
echo
echo "=== gate-mutation-demo on main (informational check; not blocking)"
# mg-3946.  THE READOUT ASKS FOR THE LATEST *COMPLETED* RUN, and that is a
# correction rather than a refinement.  The first version asked for the latest
# run of any kind and guarded against an unfinished one by testing the
# conclusion field against the string `null`.  `gh --jq` interpolates a JSON
# null into a STRING as the empty string, never as "null", so the guard could
# not fire and an in-progress run was printed as red -- with the "it is red"
# paragraph under it.
#
# That was not a latent risk: it fired on this readout's FIRST live use.  MR
# mr-d9m4fr2tjv1tur4p9e40 (mg-069f, 2026-07-31 08:24) printed
#
#     ***  as of 2026-07-31T07:13:45Z ***
#
# -- an empty conclusion where the word GREEN belonged -- against run
# 30612119957, which was in progress at that moment and completed SUCCESS.
# The window is not narrow: this gate takes ~11 min and the workflow it reads
# takes ~16-21 min, on the same commit, so a gate-touching merge lands INSIDE
# the run it is reporting on more often than not.  A consumer added to stop a
# red check being ignored, whose first act is to invent a red, is the disease
# it was prescribed for.
if ! command -v gh >/dev/null 2>&1; then
    echo "    gh not on PATH -- cannot read it.  Check by hand:"
    echo "    gh run list --workflow='Gate mutation demo' --branch=main --limit=1"
else
    RUN=$(GH_PAGER=cat gh run list --workflow='Gate mutation demo' \
              --branch=main --status=completed --limit=1 \
              --json conclusion,createdAt,displayTitle,url \
              --jq '.[0] // empty | "\(.conclusion)\t\(.createdAt)\t\(.url)\t\(.displayTitle)"' \
          2>/dev/null) || RUN=''
    # Reported separately, because "the last completed run was green" and "a
    # newer run is still deciding" are different facts and the reader needs
    # both: the green may be about a commit older than the one being merged.
    PENDING=$(GH_PAGER=cat gh run list --workflow='Gate mutation demo' \
                  --branch=main --limit=1 \
                  --json status,createdAt,url \
                  --jq '.[0] // empty | select(.status != "completed")
                        | "\(.status)\t\(.createdAt)\t\(.url)"' \
              2>/dev/null) || PENDING=''
    if [ -z "$RUN" ]; then
        echo "    no completed run readable (no credential, no network, or none yet)"
    else
        CONC=$(printf '%s' "$RUN" | cut -f1)
        WHEN=$(printf '%s' "$RUN" | cut -f2)
        URL=$(printf '%s' "$RUN" | cut -f3)
        TITLE=$(printf '%s' "$RUN" | cut -f4)
        if [ "$CONC" = "success" ]; then
            echo "    GREEN as of $WHEN -- $TITLE"
            echo "    $URL"
        else
            echo "    *** $CONC as of $WHEN ***"
            echo "    $TITLE"
            echo "    $URL"
            echo "    This check does not block your merge and is not blocking"
            echo "    it now.  It is red, which means one of the demonstrations"
            echo "    that these controls can still FAIL is not currently being"
            echo "    made.  If nobody looks at it, it stays red -- that is what"
            echo "    happened for 24 h 08 m 55 s on 2026-07-30/31 -- twelve"
            echo "    consecutive red runs (mg-3934, mg-3946, mg-a471)."
        fi
    fi
    if [ -n "$PENDING" ]; then
        PSTAT=$(printf '%s' "$PENDING" | cut -f1)
        PWHEN=$(printf '%s' "$PENDING" | cut -f2)
        PURL=$(printf '%s' "$PENDING" | cut -f3)
        echo "    a newer run is $PSTAT since $PWHEN -- not a conclusion yet"
        echo "    $PURL"
        echo "    The line above is the last COMPLETED run and may be about an"
        echo "    older commit than the one you are merging."
    fi
fi

# WHAT RUNS HERE AND WHAT DOES NOT, decided by measurement rather than taste.
#
# The first version of this file also ran the mg-7db4 battery here.  Its own MR
# then sat in the refinery for 22 minutes and held the queue for every other
# author on the fleet, while a concurrent 25-minute demonstration on the same
# host stretched each gate run to roughly ten times its uncontended cost.  A
# blocking gate long enough that people want it bypassed has a shorter life
# expectancy than the defect it guards, which is the failure this whole ticket
# chain is about, arriving one layer further out.
#
# So the split, agreed with mg-75f0 and applied to my own instrument as well as
# theirs: THE BLOCKING LAYER GETS THE CHEAP TOTAL CHECK, THE INFORMATIONAL LAYER
# GETS THE EXPENSIVE COMPLETE ONE.
#
#   here (blocking)   watchlist consistency        ms, every merge
#                     mg-5ad1 blindness probe      ~30 s on CI, ~2.5 min loaded
#                     mg-60d3 mutation demo        ~11 min -- the ticket's named
#                                                  property is that a gate change
#                                                  cannot MERGE without it
#   Actions only      mg-7db4 mutation battery     the proof the probe can fire.
#                     mg-75f0 closure demo         Both are proofs ABOUT the
#                                                  checks, not checks on the
#                                                  change, and a proof that ran
#                                                  ten minutes ago on the same
#                                                  tree is not worth ten minutes
#                                                  of everyone else's queue.

# mg-856d.  The exemption is spent HERE and nowhere earlier, so everything above
# -- the consistency check, the exemption control, the changed-paths listing and
# the readout -- runs for an exempt-only merge exactly as it does for any other.
# What is skipped is precisely the two instruments that were measured not to read
# the exempt path.
if [ -z "$DEMANDING" ]; then
    echo
    echo "=== mg-856d: every watched path that changed is on DEMO_INSENSITIVE"
    echo "    The blocking demonstrations are NOT re-run.  They do not read"
    echo "    these files, so re-running them here would demonstrate nothing"
    echo "    about this change while holding the refinery's one serial slot."
    echo "    They still run in full on Actions for this same commit: the paths"
    echo "    are unchanged in gate-mutation-demo.yml.  What catches a mutation"
    echo "    of each exempt path is named in DEMO_INSENSITIVE's CATCHER lines"
    echo "    and verified as wired on every merge by the control above."
    exit 0
fi

echo
echo "=== mg-5ad1 gate blindspot probe (is the gate blind anywhere?)"
"$PY" scripts/onethird_mg5ad1_gate_blindspot_probe.py

echo
echo "=== mg-60d3 gate mutation demo (do the F3/F4 repairs still fire?)"
echo "    six full runs of the control gate.  ~11 min uncontended on the"
echo "    fleet host (clock (b), mg-7db4's figure); 1 h 25 m 50 s measured by"
echo "    mg-856d under a 1-min load average of 38-149 on the same host.  The"
echo "    refinery's own timeout is 90m.  See the DURATION TABLE in the header."
exec "$PY" scripts/onethird_mg60d3_gate_mutation_demo.py
