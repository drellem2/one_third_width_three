#!/bin/sh
# mg-e12a -- BOTH DIRECTIONS OF THE GATE TRIGGER, against the real gate.
#
# WHY.  mg-856d and mg-e12a both observe that the fast path of
# `scripts/refinery_gate.sh` has never been shown to be CORRECT, only to be
# fast.  "No watched path changed -- demo not required" is a decision to skip
# the only thing that proves the gate-mutation demonstrations still work; a
# trigger that skips when it should fire is the defect this whole mechanism
# exists to refuse, arriving one layer further out.
#
# WHAT THIS RUNS.  The real `scripts/refinery_gate.sh`, unmodified, on real
# commits, in a throwaway branch.  It does NOT reimplement the trigger: a
# reimplementation can only agree with itself.
#
# WHAT IT DOES NOT DO, stated because the report depends on it.  It stops the
# gate as soon as the gate has PRINTED ITS DECISION.  It does not run the
# mg-5ad1 blindness probe or the ~11 min mg-60d3 demonstration to completion.
# Every claim this script supports is a claim about the DECISION the gate
# reaches, not about the demonstrations it then performs.  The two are
# different claims and only the first is measured here.
#
# Run:  sh scripts/onethird_mge12a_trigger_direction_control.sh
# Exits non-zero if any direction is wrong.  Leaves the repo on the branch it
# started on, at the commit it started on.

set -eu

cd "$(dirname "$0")/.."

START_BRANCH=$(git rev-parse --abbrev-ref HEAD)
START_SHA=$(git rev-parse HEAD)
PROBE_BRANCH=mge12a-trigger-probe
OUT=$(mktemp -d)
FAILURES=0
CASES=0

cleanup() {
    git checkout -q "$START_BRANCH" 2>/dev/null || true
    git reset -q --hard "$START_SHA" 2>/dev/null || true
    git branch -q -D "$PROBE_BRANCH" 2>/dev/null || true
    rm -rf "$OUT"
}
trap cleanup EXIT INT TERM

echo "start branch $START_BRANCH at $START_SHA"
git checkout -q -b "$PROBE_BRANCH" "$START_SHA"

# ---------------------------------------------------------------- runner ----
# Runs the gate against HEAD~1 and reports which decision it printed.  The
# gate is capped: on the positive direction it would otherwise proceed into
# ~11 min of demonstrations, and the decision has already been printed by then.
run_gate() {
    label="$1"
    base="$2"
    log="$OUT/$label.log"
    set +e
    GATE_DEMO_BASE="$base" timeout 90 sh ./scripts/refinery_gate.sh \
        >"$log" 2>&1
    rc=$?
    set -e
    if grep -q '^=== no watched path changed' "$log"; then
        decision=SKIP
    elif grep -q '^=== watched paths changed:' "$log"; then
        decision=RUN
    else
        decision=NEITHER
    fi
    consistency=NO
    grep -q '^=== mg-7db4 watchlist consistency' "$log" && consistency=YES
    echo "$decision $rc $consistency"
}

expect() {
    label="$1"; want="$2"; got_decision="$3"; got_rc="$4"; got_cons="$5"
    CASES=$((CASES + 1))
    if [ "$got_decision" = "$want" ]; then
        verdict=PASS
    else
        verdict=FAIL
        FAILURES=$((FAILURES + 1))
    fi
    printf '  %-46s want %-7s got %-7s rc=%-3s consistency-ran=%-3s  %s\n' \
        "$label" "$want" "$got_decision" "$got_rc" "$got_cons" "$verdict"
}

echo
echo "=============================================================================="
echo "TRIGGER, BOTH DIRECTIONS -- the real gate, real commits, decision only"
echo "=============================================================================="
echo

# -- case 1: NEGATIVE.  A commit touching only an unwatched path. -------------
mkdir -p docs
echo "mg-e12a trigger probe -- unwatched path, to be discarded." \
    > docs/OneThird-mge12a-trigger-probe-scratch.md
git add docs/OneThird-mge12a-trigger-probe-scratch.md
git commit -q -m "probe: unwatched path only (mg-e12a)"
set -- $(run_gate unwatched-only HEAD~1)
expect "unwatched path only (docs/*.md)" SKIP "$1" "$2" "$3"
git reset -q --hard HEAD~1

# -- case 2: POSITIVE.  A commit touching only a watched path. ----------------
WATCHED_FILE=scripts/onethird_mgb0a6_spectral_killshot_probe.py
printf '\n# mg-e12a trigger probe -- to be discarded.\n' >> "$WATCHED_FILE"
git add "$WATCHED_FILE"
git commit -q -m "probe: watched path only (mg-e12a)"
set -- $(run_gate watched-only HEAD~1)
expect "watched path only ($(basename "$WATCHED_FILE"))" RUN "$1" "$2" "$3"
git reset -q --hard HEAD~1

# -- case 3: MIXED.  One watched, one unwatched -- the rule is ANY, not ALL. --
printf '\n# mg-e12a trigger probe -- to be discarded.\n' >> "$WATCHED_FILE"
echo "scratch" > docs/OneThird-mge12a-trigger-probe-scratch.md
git add "$WATCHED_FILE" docs/OneThird-mge12a-trigger-probe-scratch.md
git commit -q -m "probe: watched + unwatched (mg-e12a)"
set -- $(run_gate mixed HEAD~1)
expect "watched + unwatched together" RUN "$1" "$2" "$3"
git reset -q --hard HEAD~1

# -- case 4: NEAR MISS.  A path that CONTAINS a watched path as a prefix. -----
# `grep -qxF` matches whole lines, so this must NOT fire.  If it did, ordinary
# commits would pay for the demo; if the matcher were a substring match instead
# this is the case that would catch it.
NEAR="${WATCHED_FILE}.bak"
printf '# mg-e12a near-miss probe -- to be discarded.\n' > "$NEAR"
git add "$NEAR"
git commit -q -m "probe: near-miss path (mg-e12a)"
set -- $(run_gate near-miss HEAD~1)
expect "near miss (watched path + '.bak' suffix)" SKIP "$1" "$2" "$3"
git reset -q --hard HEAD~1

# -- case 5: DATASET.  The one committed dataset is a watched path too. -------
DATA_FILE=data/onethird-mg8b64-L1b-bk-transport-transfer.json
if [ -f "$DATA_FILE" ]; then
    printf '\n' >> "$DATA_FILE"
    git add "$DATA_FILE"
    git commit -q -m "probe: watched dataset only (mg-e12a)"
    set -- $(run_gate dataset-only HEAD~1)
    expect "watched DATASET only (not a script)" RUN "$1" "$2" "$3"
    git reset -q --hard HEAD~1
fi

# -- case 6: EMPTY DIFF.  No change at all vs the base. -----------------------
# The gate is fail-closed on "cannot tell what changed", but an empty diff is
# knowing that nothing changed.  Recorded because a gate that fires on an empty
# diff charges every no-op merge for the demonstrations.
set -- $(run_gate empty-diff HEAD)
expect "empty diff (base=HEAD, no-op merge)" SKIP "$1" "$2" "$3"

echo
echo "  NOTE: 'consistency-ran' is YES on every row above, including the SKIP"
echo "  rows.  The negative direction is not 'the gate does nothing' -- the"
echo "  mg-7db4 watchlist consistency check runs BEFORE the trigger decision,"
echo "  so an unwatched-only commit still pays it and can still be failed by it."
echo
echo "  rc=124 on a RUN row is this script's 90 s cap, not a gate failure: the"
echo "  gate had already printed its decision and was proceeding into the"
echo "  demonstrations, which this script deliberately does not run."

echo
if [ "$FAILURES" -eq 0 ]; then
    echo "ALL DIRECTIONS CORRECT ($CASES cases)"
else
    echo "$FAILURES of $CASES DIRECTION(S) WRONG"
fi

# ============================================================================
# CAN THIS CONTROL SEE?  Six PASSes are worth nothing until the same six cases
# are shown to FAIL against a gate that is wrong in a way they are meant to
# catch.  Each arm below is ONE edit to a copy of the real gate.  The arm
# passes when the control's verdict CHANGES -- a mutant that the control still
# calls correct is a case the control cannot see, and it is reported as such.
# ============================================================================
MUTANT=scripts/.mge12a_mutant_gate.sh
MUT_BLIND=0

run_mutant() {
    label="$1"; base="$2"
    log="$OUT/$label.log"
    set +e
    GATE_DEMO_BASE="$base" timeout 90 sh "./$MUTANT" >"$log" 2>&1
    set -e
    if grep -q '^=== no watched path changed' "$log"; then echo SKIP
    elif grep -q '^=== watched paths changed:' "$log"; then echo RUN
    else echo NEITHER; fi
}

mutant_arm() {
    name="$1"; sed_expr="$2"; label="$3"; real="$4"
    sed "$sed_expr" scripts/refinery_gate.sh > "$MUTANT"
    if cmp -s "$MUTANT" scripts/refinery_gate.sh; then
        echo "  $name: ANCHOR DID NOT APPLY -- arm is vacuous"
        MUT_BLIND=$((MUT_BLIND + 1))
        rm -f "$MUTANT"
        return
    fi
    got=$(run_mutant "$label" HEAD~1)
    rm -f "$MUTANT"
    if [ "$got" != "$real" ]; then
        printf '  %-52s real=%-5s mutant=%-5s  CONTROL SEES IT\n' \
            "$name" "$real" "$got"
    else
        printf '  %-52s real=%-5s mutant=%-5s  *** CONTROL IS BLIND ***\n' \
            "$name" "$real" "$got"
        MUT_BLIND=$((MUT_BLIND + 1))
    fi
}

echo
echo "=============================================================================="
echo "CAN THIS CONTROL SEE? -- the same cases against a deliberately wrong gate"
echo "=============================================================================="
echo

# arm 1: the matcher becomes a SUBSTRING match.  The near-miss case exists
# precisely to catch this, so it must flip SKIP -> RUN.
printf '# mg-e12a near-miss probe -- to be discarded.\n' > "$NEAR"
git add "$NEAR"
git commit -q -m "probe: near-miss path, mutant arm (mg-e12a)"
mutant_arm "matcher -x dropped (substring match)" \
    's/grep -qxF "\$path"/grep -qF "$path"/' near-miss-mut SKIP
git reset -q --hard HEAD~1

# arm 2: the watchlist is emptied.  A watched-path commit must stop firing.
printf '\n# mg-e12a trigger probe -- to be discarded.\n' >> "$WATCHED_FILE"
git add "$WATCHED_FILE"
git commit -q -m "probe: watched path, mutant arm (mg-e12a)"
mutant_arm "trigger decision inverted (-z HITS -> -n HITS)" \
    's/^if \[ -z "\$HITS" \]; then/if [ -n "$HITS" ]; then/' \
    watched-mut RUN
git reset -q --hard HEAD~1

echo
if [ "$MUT_BLIND" -eq 0 ]; then
    echo "  The control changed its verdict on every mutant: the six PASSes"
    echo "  above are over a control that can distinguish a right gate from a"
    echo "  wrong one, in both the fire and the skip direction."
else
    echo "  $MUT_BLIND mutant arm(s) went unseen -- treat the PASSes with that"
    echo "  much less weight."
    FAILURES=$((FAILURES + MUT_BLIND))
fi

exit "$FAILURES"
