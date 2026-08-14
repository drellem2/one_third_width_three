#!/bin/sh
# mg-3067 -- THE LOCAL PRE-SUBMIT GATE.  Run this before `pogo refinery submit`.
#
#     ./presubmit.sh            run every control script-controls.yml runs
#     ./presubmit.sh --list     print the plan without running it
#     ./presubmit.sh --plan-check   run only the plan-coverage control
#
# ============================ WHAT IT IS FOR =================================
#
# pm-onethird's decision (mg-69b4, carried by mg-3067).  The refinery is a
# SERIAL SHARED resource with one slot; a local gate is PARALLEL and PRIVATE.
# A defect found at the refinery costs a queue round-trip, a reserved worker
# slot for the duration -- which dropped one repo's dispatch cap from 3 to 2 and
# refused a real dispatch -- and, when the fault is repo-wide, N independent
# rediscoveries by workers who did not cause it.  This file moves the cheap,
# private, own-tree class of defect off that shared resource and onto the author,
# in parallel.
#
# THE WORKED EXAMPLE (mg-457a).  `main` in this repo was red for 5 hours because
# the mg-cd04 declared-strike control is a repo-wide DOCUMENT check that only ran
# after merge.  cf63bb3c introduced the violation; it would have been red in its
# author's own worktree immediately.  Four commits landed on top of the red main,
# a queue-jumping dispatch was needed to repair it, and the mayor had to mail two
# workers pre-emptively to stop them "fixing" a control that was working
# correctly.  Against that, one local run.
#
# ============================ THE LIMIT, UP FRONT ============================
#
# THIS IS NOT A SUBSTITUTE FOR THE REFINERY GATE and nothing here should be read
# as one.  A pre-submit gate catches defects in YOUR tree.  It CANNOT catch
# interactions with what lands while you work, because that has not happened yet:
#
#   own-tree      mg-457a's declared-strike violation was introduced by one
#                 commit and was red in its own author's worktree.  CAUGHT HERE.
#   interaction   mg-5058's rebase conflict was four files rather than the one
#                 its recipe predicted, because mg-ede8 landed mid-flight and
#                 independently issued colliding control ids.  NO pre-submit run
#                 could have seen it.  NOT CAUGHT HERE, and not catchable here.
#
# The refinery gates the REBASED tree, which is the thing only it can do.  Green
# here does not predict green there.
#
# ============================ WHY NOT `build.sh` =============================
#
# mg-69b4's scope note says to mirror `onethird_program/build.sh` and states
# that this repo "has no build.sh, no refinery.toml, no Makefile today".  THE
# refinery.toml HALF OF THAT IS FALSE, checked: `.pogo/refinery.toml` exists and
# declares `commands = ["./scripts/refinery_gate.sh"]`.  That matters for the
# NAME, because the sibling's name is not decoration -- it chose `build.sh`
# precisely so that pogo's DEFAULT GATE DISCOVERY (which looks for `./build.sh`
# and `./test.sh` at the root when a repo declares no gates) would find it if
# refinery.toml were ever deleted.
#
# Here that mechanism runs backwards.  A root `build.sh` in THIS repo would mean
# that deleting `.pogo/refinery.toml` silently swaps the blocking gate from
# `scripts/refinery_gate.sh` -- the gate-mutation demonstration, the thing that
# actually blocks -- to this fast local one, and the merge would stay green while
# the demonstration quietly stopped running.  That is "a control nothing invokes"
# with a shorter fuse, which is the defect the sibling's header exists to
# prevent.  And enforcing at the refinery is the change mg-69b4 explicitly
# decided AGAINST.
#
# So the SHAPE is the sibling's -- one definition, every suite runs, the worst
# exit wins -- and the NAME is not.  `git mv presubmit.sh build.sh` reverses this
# in one command if pm-onethird disagrees; the reasoning is here so the override
# can be on the reasoning.
#
# ============================ WHAT IT RUNS ===================================
#
# THERE IS NO LIST IN THIS FILE.  The list is `.github/workflows/script-controls.yml`
# and it is read on every run by scripts/onethird_mg3067_presubmit_steps.py.  Two
# gates that can disagree are worse than one, so there is one definition and this
# file is not it.  Two declared transformations (interpreter substitution, and
# dropping the hosted runner's `pip install`) are enforced as the ONLY ones by
# `--plan-check`, which also runs in CI.
#
# It does NOT run `.github/workflows/gate-mutation-demo.yml` or
# `scripts/refinery_gate.sh`: those are the ~30-minute demonstration and the
# blocking gate, and a pre-submit gate that costs that is a pre-submit gate
# nobody runs.  If your diff can trigger the slow path, this script says so at
# the end rather than leaving you to find out in the queue.
#
# ============================ EVERY SUITE RUNS ===============================
#
# Not `&&`.  Short-circuiting means the first red control hides whether the
# others are red too, so an author fixes one thing, re-runs, and discovers the
# second only on the next round.  WITHIN a step the commands are run under
# `sh -e`, which is what GitHub's `run:` does, so a step's own short-circuit is
# preserved; ACROSS steps this continues where CI's job would stop.  That cannot
# change the verdict -- the worst exit is 0 exactly when every step is 0 -- only
# how much you learn per run.
#
# ============================ COST ===========================================
#
# `Script controls` is 3.6 min of GitHub-hosted wall time, stable across three
# green runs (4a24d9cf, 7dddbdf2, bec18a04).  pm-onethird's figure, not
# re-derived here.  That is an UPPER BOUND on what this costs locally, not an
# estimate: it includes checkout and Python provisioning, neither of which a
# worktree run pays.  For the measured local figure, its clock and the load it
# was taken under, see docs/OneThird-mg3067-PresubmitGate.md -- this comment
# deliberately does not state a second number, because a duration quoted without
# its conditions is the defect class this repo has spent days auditing (the
# DURATION TABLE at the top of scripts/refinery_gate.sh is the long version).

set -u

cd "$(dirname "$0")" || exit 2

PLAN_SCRIPT=scripts/onethird_mg3067_presubmit_steps.py
WORKFLOW=.github/workflows/script-controls.yml

# ---------------------------------------------------------- interpreter -----
# Same rule as scripts/refinery_gate.sh and for the same reason: bare `python3`
# on the fleet host has no numpy, /usr/bin/python3 does.  Pick the first
# candidate that can actually import the modules CI pip-installs.
NEEDED=$(/usr/bin/python3 "$PLAN_SCRIPT" --pip-modules 2>/dev/null \
         || python3 "$PLAN_SCRIPT" --pip-modules 2>/dev/null)

PY=''
for cand in ${PRESUBMIT_PYTHON:-} /usr/bin/python3 python3 python; do
    command -v "$cand" >/dev/null 2>&1 || continue
    missing=''
    for mod in $NEEDED; do
        "$cand" -c "import $mod" >/dev/null 2>&1 || missing="$missing $mod"
    done
    if [ -z "$missing" ]; then PY="$cand"; break; fi
done
export PY   # the emitted plan is run in a child `sh -e -c`, which needs it
if [ -z "$PY" ]; then
    echo "presubmit: FAIL -- no python3 on PATH can import:$NEEDED" >&2
    echo "presubmit: CI installs these with pip on its own runner; this gate" >&2
    echo "presubmit: will not mutate your environment to match.  Set" >&2
    echo "presubmit: PRESUBMIT_PYTHON=/path/to/python3 if you have one." >&2
    exit 2
fi

# ---------------------------------------------------------- the plan --------
# `mktemp -t PREFIX` is a BSD spelling GNU coreutils rejects; the explicit
# template works on both.
TD="${TMPDIR:-/tmp}"
PLAN=$(mktemp "$TD/presubmit-plan.XXXXXX") || exit 2
CHANGED=$(mktemp "$TD/presubmit-changed.XXXXXX") || exit 2
WATCH=$(mktemp "$TD/presubmit-watch.XXXXXX") || exit 2
DIRTY_BEFORE=$(mktemp "$TD/presubmit-before.XXXXXX") || exit 2
DIRTY_AFTER=$(mktemp "$TD/presubmit-after.XXXXXX") || exit 2
# Armed BEFORE anything is created, and the signals are named: EXIT alone does
# not fire on SIGTERM.
trap 'rm -f "$PLAN" "$CHANGED" "$WATCH" "$DIRTY_BEFORE" "$DIRTY_AFTER"' \
     EXIT INT TERM HUP

if ! "$PY" "$PLAN_SCRIPT" --emit-sh > "$PLAN"; then
    echo "presubmit: FAIL -- could not derive the plan from $WORKFLOW" >&2
    exit 2
fi
TOTAL=$(grep -c '^step ' "$PLAN")
if [ "$TOTAL" -eq 0 ]; then
    echo "presubmit: FAIL -- the plan is EMPTY.  A gate over zero controls is" >&2
    echo "presubmit: not a green gate; it is a gate that runs nothing." >&2
    exit 2
fi

case "${1:-}" in
    --list)
        exec "$PY" "$PLAN_SCRIPT" --list
        ;;
    --plan-check)
        exec "$PY" "$PLAN_SCRIPT" --check
        ;;
    '') : ;;
    *)
        echo "presubmit: unknown option $1 (try --list or --plan-check)" >&2
        exit 2
        ;;
esac

# ---------------------------------------------------------- run -------------
echo "############################################################ presubmit.sh"
echo "plan: $TOTAL steps, derived from $WORKFLOW"
echo "interpreter: $PY"
echo

# KNOWN COST 3, and it was found by running this gate rather than reasoned
# about: SOME CONTROLS WRITE TO THE TREE THEY GRADE.  The mg-5ad1 blindspot
# probe rewrites data/onethird-mg5ad1-gate-blindspot-probe.json on every run,
# and the rewrite is not empty -- floating-point noise in the last digits of
# lambda2_BK and the c_max/c_min rows moves between hosts and between runs.  CI
# never notices because it discards its checkout; an author's worktree keeps it.
# A gate that silently dirties the tree it is grading is a gate that teaches
# authors to `git add .` over a diff they did not write, so this snapshot is
# taken before the run and reported after it.  It is NOT auto-reverted: a gate
# must not mutate the author's tree, and un-mutating it is still mutating it.
git status --porcelain 2>/dev/null | sort > "$DIRTY_BEFORE" || : > "$DIRTY_BEFORE"

STATUS=0
N=0
FAILED=''

step() {
    N=$((N + 1))
    printf '############################################################ [%d/%d] %s\n' \
        "$N" "$TOTAL" "$1"
    sh -e -c "$2"
    RC=$?
    if [ "$RC" -ne 0 ]; then
        [ "$RC" -gt "$STATUS" ] && STATUS=$RC
        FAILED="$FAILED
  [$N] $1 (exit $RC)"
        echo "--- RED (exit $RC)"
    fi
    echo
}

# THE PLAN-COVERAGE CONTROL IS A PRECONDITION, NOT A STEP, and it aborts rather
# than accumulating into the worst exit.  If the plan has stopped covering the
# workflow then every green below it is over an UNKNOWN POPULATION, and a
# summary line reading "N of N passed" would be true of a population nobody
# knows the size of -- which is this repo's most-audited defect and not
# something to reproduce in the gate written to catch it.
#
# It is ALSO step 9 of the plan, because it is a step of the CI job.  It is not
# run twice: this precondition is `--check` on its own, and the plan runs the
# same command in its CI position.  Both are order-milliseconds.
printf '############################################################ precondition\n'
if ! "$PY" "$PLAN_SCRIPT" --check; then
    echo
    echo "presubmit: ABORTED before running anything.  The plan derived from"
    echo "$WORKFLOW no longer covers it, so a green"
    echo "run below would be a green over a population of unknown size."
    exit 1
fi
echo

. "$PLAN"

# ---------------------------------------------------------- readout ---------
echo "############################################################ presubmit.sh"
if [ "$STATUS" -eq 0 ]; then
    echo "GREEN -- $TOTAL of $TOTAL steps passed, plus the plan-coverage control."
else
    echo "RED -- worst exit $STATUS.  Steps that fired:$FAILED"
fi

# ---------------------------------------------------------- tree mutation ---
git status --porcelain 2>/dev/null | sort > "$DIRTY_AFTER" || : > "$DIRTY_AFTER"
NEWDIRT=$(comm -13 "$DIRTY_BEFORE" "$DIRTY_AFTER" 2>/dev/null || true)
if [ -n "$NEWDIRT" ]; then
    echo
    echo "THIS GATE WROTE TO YOUR TREE.  These paths were clean before it ran"
    echo "and are not:"
    printf '%s\n' "$NEWDIRT" | sed 's/^/  /'
    echo "That is the controls' own output, not your change.  Known instance:"
    echo "the mg-5ad1 blindspot probe rewrites its committed data file every"
    echo "run, and its last-digit floating-point values move between runs."
    echo "Nothing here reverted them -- inspect, then \`git checkout --\` the"
    echo "ones you did not mean to make."
fi

# ---------------------------------------------------------- known costs -----
# KNOWN COST 1 (mg-4c4d, sibling repo).  There, a branch that adds a new watched
# transcript is red on its first run BY CONSTRUCTION, because the gate cannot
# grade a file with no committed copy.  MEASURED HERE AND THIS REPO DOES NOT HAVE
# THAT PROPERTY -- see docs/OneThird-mg3067-PresubmitGate.md sec 4 for the
# experiment.  Said out loud rather than left as an unstated difference between
# two repos whose gates look alike.
#
# KNOWN COST 2.  The refinery runs a gate this one does not.  Advisory only: it
# never touches the exit code, and it reads scripts/refinery_gate.sh's own
# WATCHED variable rather than a second copy of the list.
BASE=$(git merge-base HEAD origin/main 2>/dev/null || echo '')
if [ -n "$BASE" ]; then
    { git diff --name-only "$BASE" HEAD 2>/dev/null
      git diff --name-only 2>/dev/null
      git ls-files --others --exclude-standard 2>/dev/null; } | sort -u > "$CHANGED"
    awk "/^WATCHED='/,/'\$/" scripts/refinery_gate.sh 2>/dev/null \
        | sed "s/^WATCHED='//; s/'\$//" | grep . > "$WATCH" 2>/dev/null || true
    HITS=$(grep -Fx -f "$WATCH" "$CHANGED" 2>/dev/null || true)
    if [ -n "$HITS" ]; then
        echo
        echo "NOTE, and it does not affect the verdict above: your diff touches"
        echo "paths on scripts/refinery_gate.sh's WATCHED list --"
        printf '%s\n' "$HITS" | sed 's/^/  /'
        echo "so the REFINERY may additionally run the gate-mutation"
        echo "demonstration, which is minutes-to-hours and holds the one serial"
        echo "slot.  Some watched paths are exempted from the blocking demo"
        echo "(mg-856d); scripts/refinery_gate.sh decides, not this notice."
        echo "Its DURATION TABLE states what that costs, on which clock, and"
        echo "under what load."
    fi
fi

echo
echo "Remember what this did NOT check: interactions with anything that lands"
echo "while you work.  The refinery gates the REBASED tree; green here does not"
echo "predict green there."
exit "$STATUS"
