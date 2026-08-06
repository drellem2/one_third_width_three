#!/bin/sh
# mg-856d -- measure the BLOCKING gate's cost, component by component, with the
# host load recorded around every measurement.
#
# WHY A SCRIPT AND NOT A STOPWATCH.  The ticket this belongs to exists because
# six duration figures in scripts/refinery_gate.sh do not say what they measure,
# which clock they are on, or under what load they were taken.  A replacement
# figure produced the same way would be the same defect wearing a newer number.
# So every row this emits carries: WHAT was timed, WHICH clock, and the 1-, 5-
# and 15-minute load averages immediately before and immediately after.
#
# CLOCK.  Everything here is clock (b) in the mg-856d table: wall-clock of a
# local process on the fleet host.  It is NOT the GitHub Actions workflow clock
# (a) and NOT end-to-end refinery MR wall-clock (c), which bundles queue wait.
#
# Usage:  ./scripts/onethird_mg856d_gate_cost_measure.sh [outfile.json]
# Writes JSON to outfile (default data/onethird-mg856d-gate-cost.json) and a
# human-readable table to stdout.  Runs nothing that mutates the working tree
# beyond the demo's own report files.

set -u

cd "$(dirname "$0")/.."

OUT="${1:-data/onethird-mg856d-gate-cost.json}"

PY=''
for cand in /usr/bin/python3 python3 python; do
    if command -v "$cand" >/dev/null 2>&1 \
       && "$cand" -c 'import numpy' >/dev/null 2>&1; then
        PY="$cand"
        break
    fi
done
if [ -z "$PY" ]; then
    echo "mg856d: no python3 with numpy -- cannot measure" >&2
    exit 1
fi

loadavg() {
    # macOS and Linux both print "load averages: a b c" / "load average: a, b, c"
    uptime | sed 's/.*load average[s]*: *//; s/,//g'
}

ROWS=''

measure() {
    name="$1"; shift
    before=$(loadavg)
    t0=$($PY -c 'import time; print(time.time())')
    "$@" >/dev/null 2>&1
    rc=$?
    t1=$($PY -c 'import time; print(time.time())')
    after=$(loadavg)
    secs=$($PY -c "print('%.1f' % ($t1 - $t0))")
    printf '%-46s %8ss  rc=%s  load %s -> %s\n' "$name" "$secs" "$rc" "$before" "$after"
    ROWS="$ROWS{\"what\":\"$name\",\"seconds\":$secs,\"exit\":$rc,\"load_before\":\"$before\",\"load_after\":\"$after\"},"
}

echo "mg-856d gate cost measurement -- clock (b), local process wall-clock"
echo "host: $(uname -s) $(uname -m), $(getconf _NPROCESSORS_ONLN 2>/dev/null || echo '?') cores"
echo "interpreter: $PY"
echo

measure "mg-7db4 watchlist consistency (+selftest)" \
        "$PY" scripts/onethird_mg7db4_watchlist_consistency.py
measure "mg-5ad1 gate blindspot probe" \
        "$PY" scripts/onethird_mg5ad1_gate_blindspot_probe.py
measure "mg-60d3 gate mutation demo" \
        "$PY" scripts/onethird_mg60d3_gate_mutation_demo.py

echo
NOW=$(TZ=UTC $PY -c 'import time; print(time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))')
printf '{"measured_at_utc":"%s","clock":"(b) local process wall-clock on the fleet host","host":"%s %s","cores":%s,"interpreter":"%s","rows":[%s]}\n' \
    "$NOW" "$(uname -s)" "$(uname -m)" \
    "$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 0)" "$PY" \
    "$(printf '%s' "$ROWS" | sed 's/,$//')" > "$OUT"
echo "wrote $OUT"
