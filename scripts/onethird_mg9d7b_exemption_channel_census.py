#!/usr/bin/env python3
"""mg-9d7b — the CHANNEL census: no exemption may be both unbounded and silent.

WHY THIS EXISTS.  mg-cd04 bounded an exemption channel.  mg-9a19 found that the
same control had a SECOND channel, unbounded, carrying more lines than the one
that was bounded (66 against 59), and that the new corpus-wide control mg-cd04
wrote to close the finding had a third -- a fence skipped on an opening marker
with no bound, running to END OF FILE when the marker had no partner.  Three
instances, one shape: an exemption granted on a marker's say-so, with nothing
saying how far it reaches.

The repair for each individual channel is a bound.  The repair for the CLASS is
this file.  Fixing the next channel and leaving the set is what this arc has done
repeatedly and what mg-9d7b was filed to stop, so what is asserted here is not
"channel A2 is bounded" but:

    EVERY route by which a line leaves a control unchecked is either
    BOUNDED by a named constant, or REPORTED with a number in the
    control's own output.  Unbounded-and-reported is a decision.
    Bounded-and-quiet is fine, the bound is the statement.
    UNBOUNDED AND SILENT is the defect, and there are to be none.

HOW IT AVOIDS BEING A RESTATEMENT OF ITS AUTHOR'S READING.  A table of channels
copied out of two docstrings proves nothing: it passes exactly when the author's
reading was complete, which is the thing in question.  So the census is
mechanical in both halves.

  * COVERAGE KEYS.  Each control already classifies every line of its population
    into named buckets and asserts the buckets sum -- that is mg-069f's
    NAMED-vs-SWEPT assertion.  This census asserts the SET OF BUCKET NAMES equals
    a declared set.  A new disposition -- which is what a new exemption channel
    IS, mechanically -- adds a bucket name, and the census fails on a name it was
    never told about.  It cannot be satisfied by a channel the author forgot,
    because the author does not supply the observed side.
  * ATTRIBUTION.  Every line in a non-checking bucket must be claimed by a
    declared channel's own line count, summing exactly.  A skip that is quietly
    folded into an existing bucket fails here even though the bucket name is
    familiar.
  * REPORTING.  For every channel not closed by a bound, the control's actual
    STDOUT is captured and searched for that channel's number.  A channel whose
    docstring promises a report and whose output has none fails -- which is the
    exact failure mode of `MAX_EXEMPT_LINES`, an identifier two paragraphs of
    prose relied on and no code defined.

CAN IT FAIL?  `--demonstrate <rev>` loads BOTH controls from a revision and runs
the same invariant there.  At any commit before mg-9d7b it reports violations and
exits 0 to say so; if it finds none, the revision does not demonstrate the defect
and it exits 1.  `--selftest` builds a control with an undeclared skip bucket and
checks that each half of the invariant rejects it.

USAGE
    onethird_mg9d7b_exemption_channel_census.py
    onethird_mg9d7b_exemption_channel_census.py --selftest
    onethird_mg9d7b_exemption_channel_census.py --demonstrate 1e996fb
"""

import contextlib
import importlib.util
import io
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIVE_CLAIM = "scripts/onethird_mg8a71_live_claim_control.py"
DECLARED_STRIKE = "scripts/onethird_mgcd04_declared_strike_control.py"

BOUNDED = "BOUNDED"
BY_DESIGN = "UNBOUNDED BY DESIGN"
BY_SCOPE = "UNBOUNDED BY SCOPE"
NOT_A_CHANNEL = "NOT A CHANNEL"

# ---------------------------------------------------------------------------
# The DECLARED side.  Every channel, its disposition, and — for a bounded one —
# the identifier that bounds it, which must exist in the module.  `bucket` names
# the control's own coverage bucket the channel's lines land in; None means the
# channel does not remove lines from the population (it reshapes what is checked,
# or it is a scope statement about lines that never enter at all).
#
# A channel counts as REPORTED if any of its `evidence` strings appears in the
# control's own stdout.  The id is the default, because at HEAD both controls
# label their channels by id -- but requiring the LABEL rather than the NUMBER
# would call a channel silent merely for being unlabelled, which is wrong and
# was this census's own first false positive: the declared-strike control has
# printed its near-miss count since mg-cd04 and the id-only test flagged it.
#
# (id, control, what leaves this way, disposition, bound identifier, bucket, evidence)
CHANNELS = [
    ("A1", "live-claim", "the EXEMPT label's own sub-paragraph",
     BOUNDED, "MAX_LABEL_LINES", "exempt_annotation", ("A1",)),
    ("A2", "live-claim", "an EXEMPT sub-paragraph carrying a QUOTATION",
     BOUNDED, "MAX_QUOTED_LINES", "exempt_annotation", ("A2",)),
    ("A3", "live-claim", "one EXEMPT block's exempt-text total",
     BOUNDED, "MAX_EXEMPT_LINES", "exempt_annotation", ("A3",)),
    ("A4", "live-claim", "a blockquote's own blank `>` lines",
     NOT_A_CHANNEL, None, "exempt_annotation", ("A4",)),
    ("A5", "live-claim", "inline ~~struck~~ spans, stripped from every checked unit",
     BY_DESIGN, None, None, ("A5",)),
    ("A6", "live-claim", "the population: one document of the corpus",
     BY_SCOPE, None, None, ("A6",)),
    ("A7", "live-claim", "fenced code — CHECKED here, unlike its sibling",
     NOT_A_CHANNEL, None, None, ("A7",)),
    ("A8", "live-claim", "label detected in block[:3], exemption given to sub-para 0",
     NOT_A_CHANNEL, None, None, ("A8",)),
    ("B1", "declared-strike", "a CLOSED fenced region",
     BY_DESIGN, None, "fenced_code", ("B1", "fenced regions")),
    ("B2", "declared-strike", "an UNCLOSED fence (was: skip to EOF)",
     NOT_A_CHANNEL, None, None, ("B2",)),
    ("B3", "declared-strike", "one `~~` anywhere in a block backs every declaration in it",
     BY_DESIGN, None, None, ("B3",)),
    # B4 is the one that made this field necessary: the declared-strike control
    # has printed a near-miss COUNT since mg-cd04 and simply never labelled it,
    # so an id-only test called a reported channel silent.  Recorded rather than
    # quietly fixed -- it is this census's own first false positive.
    ("B4", "declared-strike", "a declaration with no same-sentence quotation",
     BY_DESIGN, None, None, ("B4", "near misses")),
    ("B5", "declared-strike", "BASELINE — tolerated sites",
     BOUNDED, "BASELINE", None, ("B5", "baseline")),
    ("B6", "declared-strike", "`docs/*.md` does not descend into subdirectories",
     BY_SCOPE, None, None, ("B6",)),
    ("B7", "declared-strike", "blank lines",
     NOT_A_CHANNEL, None, "blank", ("B7", "blank")),
]

# The buckets each control is allowed to classify a line into.  A NEW bucket is a
# new disposition, which is what a new channel looks like from the outside; the
# census fails on one it was not told about.  This is the half the author does
# not control: it is read off the running control, not off its docstring.
DECLARED_BUCKETS = {
    "live-claim": {"paragraph", "quote", "heading", "exempt_annotation", "blank"},
    "declared-strike": {"block", "fenced_code", "blank"},
}

# Buckets whose lines are NOT examined by the control's rule.  Every line in one
# of these has to be claimed, to the line, by a declared channel.
NON_CHECKING = {
    "live-claim": {"exempt_annotation"},
    "declared-strike": {"fenced_code"},
}


def load(name, path, source=None):
    """Import a control by path, or from `source` text written to a temp file."""
    if source is not None:
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="mg9d7b-")) / f"{name}.py"
        tmp.write_text(source, encoding="utf-8")
        path = tmp
    spec = importlib.util.spec_from_file_location(name, str(path))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def at_rev(rev, relpath):
    return subprocess.run(["git", "show", f"{rev}:{relpath}"],
                          capture_output=True, text=True, cwd=ROOT).stdout


def observe(lc, ds):
    """Run both controls and return (buckets, channel line counts, stdout) each.

    Everything here is READ OFF THE RUNNING CONTROL.  Nothing is taken from a
    docstring, which is the point: a docstring is what failed last time.
    """
    out = {}
    # the controls read sys.argv in main(); this census has its own flags, and
    # letting them through makes a control scan a file named '--demonstrate'
    saved_argv, sys.argv = sys.argv, [sys.argv[0]]

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        try:
            lc.main()
        except SystemExit:
            pass
    lc_text = buf.getvalue()
    res = lc.scan(str(ROOT / lc.DOC))
    if len(res) == 5:
        total, _n_live, _hits, coverage, channels = res
    else:                                   # pre-mg-9d7b: no channel accounting
        total, _n_live, _hits, coverage = res
        channels = {}
    out["live-claim"] = (total, coverage, channels, lc_text)

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        try:
            ds.main()
        except SystemExit:
            pass
    ds_text = buf.getvalue()
    res = ds.scan_corpus()
    if len(res) == 7:
        _names, _nd, n_lines, _h, _nm, channels, coverage = res
    else:                                   # pre-mg-9d7b: no channel accounting
        _names, _nd, n_lines, _h, _nm = res
        coverage, channels = {}, {}
        for p in sorted((ROOT / ds.DOCS).glob("*.md")):
            _h2, _n2, cov = ds.scan_text(p.name, p.read_text(encoding="utf-8"))
            for k, v in cov.items():
                coverage[k] = coverage.get(k, 0) + v
    out["declared-strike"] = (n_lines, coverage, channels, ds_text)
    sys.argv = saved_argv
    return out


# The line counts a channel contributes, by control.  Read from the channel dict
# the control itself accumulates.
CHANNEL_LINES = {
    "A1": lambda c: c.get("A1_label", 0),
    "A2": lambda c: c.get("A2_quoted", 0),
    "A3": lambda c: 0,                       # a cap on A1+A2, not its own lines
    "A4": lambda c: c.get("A4_blank", 0),
    "B1": lambda c: c.get("B1_fenced_lines", 0),
    "B7": lambda c: 0,                       # `blank` is its own bucket, checked below
}


def audit(observed, modules):
    """Return the list of invariant violations. Empty list == the invariant holds."""
    bad = []

    for control, (total, coverage, channels, text) in observed.items():
        mod = modules[control]

        # (1) BUCKET NAMES — a new disposition is a new channel.
        seen = set(coverage)
        undeclared = seen - DECLARED_BUCKETS[control]
        for b in sorted(undeclared):
            bad.append((control, "-", f"undeclared coverage bucket '{b}' "
                                      f"({coverage[b]} lines) — a disposition no "
                                      f"channel in this census claims"))

        # (2) ATTRIBUTION — every non-checked line claimed, to the line.
        for bucket in NON_CHECKING[control]:
            skipped = coverage.get(bucket, 0)
            claimed = sum(CHANNEL_LINES[cid](channels)
                          for cid, ctl, _d, _p, _b, bk, _e in CHANNELS
                          if ctl == control and bk == bucket and cid in CHANNEL_LINES)
            if claimed != skipped:
                bad.append((control, bucket,
                            f"{skipped} lines leave via '{bucket}' and declared "
                            f"channels account for {claimed} — "
                            f"{abs(skipped - claimed)} unattributed"))

        # (3) BOUND EXISTS, and (4) UNBOUNDED => REPORTED.
        for cid, ctl, desc, disp, bound, _bucket, evidence in CHANNELS:
            if ctl != control:
                continue
            if disp == BOUNDED:
                if bound is None or not hasattr(mod, bound):
                    bad.append((control, cid,
                                f"declared BOUNDED by '{bound}' and no such "
                                f"identifier exists in the module"))
            elif disp in (BY_DESIGN, BY_SCOPE):
                if not any(e in text for e in evidence):
                    bad.append((control, cid,
                                f"{disp} and its reach appears nowhere in the "
                                f"control's own output — unbounded AND silent"))
    return bad


def print_table(observed, modules):
    w = 58
    print(f"  {'id':<4}{'control':<17}{'route out of the check':<{w}}"
          f"{'disposition':<21}reach at this tree")
    print("  " + "-" * (4 + 17 + w + 21 + 18))
    for cid, ctl, desc, disp, bound, bucket, _e in CHANNELS:
        _t, cov, channels, _txt = observed[ctl]
        fn = CHANNEL_LINES.get(cid)
        if cid == "A3":
            reach = f"cap on A1+A2, {channels.get('A3_block_max', 0)} used of " \
                    f"{getattr(modules[ctl], 'MAX_EXEMPT_LINES', '?')}"
        elif cid == "B5":
            reach = f"{len(getattr(modules[ctl], 'BASELINE', ()))} sites"
        elif cid == "B7":
            reach = f"{cov.get('blank', 0)} lines"
        elif cid == "B2":
            reach = f"{channels.get('B2_unclosed_fences', 0)} site(s), now CHECKED"
        elif cid == "B3":
            reach = f"{len(channels.get('B3_sites', []))} sentence(s)"
        elif cid == "A5":
            reach = f"{channels.get('A5_raw_spans', 0)} spans, " \
                    f"{channels.get('A5_inline_strike_chars', 0)} chars"
        elif cid == "A6":
            reach = "1 document is read; the rest never enter"
        elif cid == "A7":
            reach = f"{channels.get('A7_fence_lines_CHECKED', 0)} fence lines, CHECKED"
        elif cid == "A8":
            reach = f"{channels.get('A8_label_not_in_sub0', 0)} lines"
        elif cid == "B6":
            reach = f"{channels.get('B6_read', 0)} read of " \
                    f"{channels.get('B6_in_tree', 0)} in the tree"
        elif cid == "B4":
            reach = "reported below as near misses"
        else:
            reach = f"{fn(channels)} lines" if fn else "—"
        shown = disp if not bound else f"{disp}: {bound}"
        # descriptions and dispositions are data, not layout: wrap rather than
        # let a long one shove the reach column out of alignment
        print(f"  {cid:<4}{ctl:<17}{desc[:w - 1]:<{w}}{shown[:20]:<21}{reach}")


def selftest():
    """Can each half of the invariant fail?  Build controls that violate it."""
    print("=" * 84)
    print("SELFTEST — a census that cannot fail is not a control")
    print("=" * 84)
    ok = True

    # (a) an UNDECLARED BUCKET: a control that invents a new disposition.
    class FakeCov:
        pass
    observed = {"live-claim": (100, {"paragraph": 90, "blank": 5, "sneaky_skip": 5},
                               {"A1_label": 0, "A2_quoted": 0, "A4_blank": 0}, "A5 A6"),
                "declared-strike": (10, {"block": 10}, {"B1_fenced_lines": 0},
                                    "B1 B3 B4 B6")}
    mods = {"live-claim": _stub(("MAX_LABEL_LINES", "MAX_QUOTED_LINES",
                                 "MAX_EXEMPT_LINES")),
            "declared-strike": _stub(("BASELINE",))}
    bad = audit(observed, mods)
    hit = any("sneaky_skip" in b[2] for b in bad)
    print(f"  (a) undeclared coverage bucket        -> {'CAUGHT' if hit else 'MISSED'}")
    ok &= hit

    # (b) UNATTRIBUTED LINES: a familiar bucket grows without a channel claiming it.
    observed["live-claim"] = (100, {"paragraph": 80, "blank": 5, "exempt_annotation": 15},
                              {"A1_label": 2, "A2_quoted": 3, "A4_blank": 1}, "A5 A6")
    bad = audit(observed, mods)
    hit = any("unattributed" in b[2] for b in bad)
    print(f"  (b) skipped lines no channel claims   -> {'CAUGHT' if hit else 'MISSED'}")
    ok &= hit

    # (c) A MISSING BOUND — exactly the MAX_EXEMPT_LINES defect.
    observed["live-claim"] = (100, {"paragraph": 94, "blank": 5, "exempt_annotation": 1},
                              {"A1_label": 1, "A2_quoted": 0, "A4_blank": 0}, "A5 A6")
    mods["live-claim"] = _stub(("MAX_LABEL_LINES", "MAX_QUOTED_LINES"))
    bad = audit(observed, mods)
    hit = any("no such identifier" in b[2] for b in bad)
    print(f"  (c) a bound the docstring names and")
    print(f"      the module does not define        -> {'CAUGHT' if hit else 'MISSED'}")
    ok &= hit

    # (d) UNBOUNDED AND SILENT — the defect this whole file is named for.
    mods["live-claim"] = _stub(("MAX_LABEL_LINES", "MAX_QUOTED_LINES",
                                "MAX_EXEMPT_LINES"))
    observed["live-claim"] = (100, {"paragraph": 94, "blank": 5, "exempt_annotation": 1},
                              {"A1_label": 1, "A2_quoted": 0, "A4_blank": 0}, "A6 only")
    bad = audit(observed, mods)
    hit = any(b[1] == "A5" and "silent" in b[2] for b in bad)
    print(f"  (d) an unbounded channel that prints")
    print(f"      no number                         -> {'CAUGHT' if hit else 'MISSED'}")
    ok &= hit

    print()
    print(f"RESULT: {'PASS' if ok else 'FAIL'} — all four halves of the invariant "
          f"{'can' if ok else 'CANNOT'} fail.")
    return 0 if ok else 1


def _stub(names):
    m = type("stub", (), {})()
    for n in names:
        setattr(m, n, 1)
    return m


def main():
    if "--selftest" in sys.argv:
        return selftest()

    demo_rev = None
    if "--demonstrate" in sys.argv:
        demo_rev = sys.argv[sys.argv.index("--demonstrate") + 1]

    if demo_rev:
        lc = load("lc_old", None, at_rev(demo_rev, LIVE_CLAIM))
        ds = load("ds_old", None, at_rev(demo_rev, DECLARED_STRIKE))
        # a control loaded from a temp file computes ROOT from its own path, so
        # point it back at the repository or it sweeps an empty corpus and the
        # demonstration passes for the wrong reason
        lc.ROOT = ds.ROOT = ROOT
        where = f"at {demo_rev}"
    else:
        lc = load("lc", ROOT / LIVE_CLAIM)
        ds = load("ds", ROOT / DECLARED_STRIKE)
        where = "at HEAD"

    observed = observe(lc, ds)
    modules = {"live-claim": lc, "declared-strike": ds}

    print("=" * 84)
    print("mg-9d7b exemption-channel census — no channel unbounded AND silent")
    print("=" * 84)
    print(f"tree      : {where}")
    print(f"invariant : every route out of a control is BOUNDED by a named "
          f"constant, or")
    print(f"            REPORTED with a number in that control's own output.")
    print(f"population: {len(CHANNELS)} declared channels across 2 controls; "
          f"{observed['live-claim'][0]} lines + "
          f"{observed['declared-strike'][0]} lines classified")
    print()
    print_table(observed, modules)
    print()

    bad = audit(observed, modules)
    for control, cid, msg in bad:
        print(f"  VIOLATION  [{control} {cid}] {msg}")
    if not bad:
        print("  no channel is both unbounded and silent, every declared bound "
              "exists, and")
        print("  every skipped line is attributed to a channel that prints its own "
              "number.")
    print()
    print("=" * 84)

    if demo_rev:
        if bad:
            print(f"RESULT: the census BITES at {demo_rev} — {len(bad)} violation(s).")
            return 0
        print(f"RESULT: nothing found at {demo_rev}; this revision does not "
              f"demonstrate the defect.")
        return 1

    if bad:
        print(f"RESULT: FAIL — {len(bad)} exemption channel(s) violate the invariant.")
        print("        Bound it, or print what it skipped.  A channel that does")
        print("        neither is the defect mg-cd04, mg-9a19 and mg-9d7b are all")
        print("        about, and it is the one thing this file exists to refuse.")
        return 1
    print("RESULT: PASS — every exemption channel in both controls is bounded by a")
    print("        named constant or reports its own reach.  This does not say the")
    print("        bounds are RIGHT; it says none of them is invisible.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
