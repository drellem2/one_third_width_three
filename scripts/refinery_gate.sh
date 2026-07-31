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
# `git diff` and a `grep`: milliseconds.  The ~17 minutes of demonstrations are
# paid only by commits that can invalidate them.
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

HITS=''
for path in $WATCHED; do
    if printf '%s\n' "$CHANGED" | grep -qxF "$path"; then
        HITS="$HITS $path"
    fi
done

if [ -z "$HITS" ]; then
    echo "=== no watched path changed -- gate-mutation demo not required"
    exit 0
fi

echo "=== watched paths changed:"
for h in $HITS; do echo "    $h"; done

# --------------------------------------------------------------- READOUT ----
# mg-3934 -- THE CONSUMER FOR THE INFORMATIONAL CHECK, and the reason it is
# here rather than anywhere else.
#
# `.github/workflows/gate-mutation-demo.yml` says of itself that it INFORMS and
# does not BLOCK.  That was true and it was also the whole defect: from
# 2026-07-30 that workflow was red on `main` for 21 hours, on eight consecutive
# runs, because its last step resolved a historical commit that is not in a
# depth-1 `actions/checkout` clone -- and nothing consumed the result, so a
# demonstration that had NEVER ONCE EXECUTED was indistinguishable from one
# running and passing.  A permanently-red check nobody reads is worse than no
# check: it cannot be told apart from a working one and it trains every reader
# to skip the column.
#
# Making the ~30-minute job blocking was rejected for the reason stated above
# this section -- a gate long enough to want bypassed does not survive.  So the
# result is put where somebody already looks: the refinery's Gate Output, which
# `pogo refinery show <mr>` prints to the author of the merge, on exactly the
# commits that can invalidate the demonstrations.
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
if ! command -v gh >/dev/null 2>&1; then
    echo "    gh not on PATH -- cannot read it.  Check by hand:"
    echo "    gh run list --workflow='Gate mutation demo' --branch=main --limit=1"
else
    RUN=$(GH_PAGER=cat gh run list --workflow='Gate mutation demo' \
              --branch=main --limit=1 \
              --json conclusion,createdAt,displayTitle,url \
              --jq '.[0] | "\(.conclusion)\t\(.createdAt)\t\(.url)\t\(.displayTitle)"' \
          2>/dev/null) || RUN=''
    if [ -z "$RUN" ] || [ "${RUN%%	*}" = "null" ]; then
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
            echo "    happened for 21 hours on 2026-07-30 (mg-3934)."
        fi
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
echo
echo "=== mg-5ad1 gate blindspot probe (is the gate blind anywhere?)"
"$PY" scripts/onethird_mg5ad1_gate_blindspot_probe.py

echo
echo "=== mg-60d3 gate mutation demo (do the F3/F4 repairs still fire?)"
echo "    six full runs of the control gate; ~11 min idle, more under load"
exec "$PY" scripts/onethird_mg60d3_gate_mutation_demo.py
