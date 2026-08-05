#!/usr/bin/env python3
"""mg-77e6 -- can the mg-9d7b channel census DISCOVER a channel, or only CHECK one?

WHY THIS EXISTS.  mg-9d7b's E13 was a prediction against itself: "the invariant,
asserted as code, will find at least one channel I did not think of when I wrote
this file."  Its report records the outcome as MISSED -- the census found none --
and reads that as evidence that its enumeration was a complete restatement of a
careful reading.

A NEGATIVE NEEDS AN INSTRUMENT THAT COULD HAVE SHOWN THE POSITIVE.  "The census
found no channel my reading missed" is a statement about the world only if the
census can find channels at all.  If it cannot, the same MISSED is produced by a
complete reading and by an incomplete one, and the result carries no information
about which happened.

So this probe does the one thing that settles it: it BUILDS SIXTEENTH CHANNELS --
real edits to real controls that really remove text from checking -- and runs the
census's own unmodified `observe()` and `audit()` against them.

    PART 1  five mutant controls, each a new exemption channel, three of them
            chosen to sit outside the census's mechanical reach and two chosen to
            sit inside it (positive controls: an instrument that catches nothing
            and an instrument that catches everything are equally uninformative)

    PART 2  REACH.  For the two channels claimed to be invisible, a planted live
            claim that the pristine control CATCHES and the mutated one does NOT.
            A channel that changes no verdict is a curiosity, not a channel.

    PART 3  THE DELETION SWEEP.  Simulate the author who never noticed a channel
            by deleting its row from CHANNELS and re-auditing the UNMODIFIED
            controls at HEAD.  A row the census re-discovers is one the author's
            declaration was not load-bearing for.  A row it does not is one that
            got in by reading alone -- and E13 is a question about exactly those.

    PART 4  three checks on specific claims in the deliverable: the M4 bound
            sweep (E1, expected to HOLD), whether BASELINE is a bound, and
            whether the census consults the exit code of the controls it audits.

WHAT THIS PROBE DOES NOT DO.  It does not widen the census's reach, propose a
better invariant, or touch either control on the corpus -- every mutant is a
temp file.  It does not re-do mg-9d7b.  Naming the detection class is the
finding; building a wider instrument is a different ticket.

USAGE
    onethird_mg77e6_sixteenth_channel_probe.py
    onethird_mg77e6_sixteenth_channel_probe.py --quiet
"""

import copy
import importlib.util
import pathlib
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
CENSUS = "scripts/onethird_mg9d7b_exemption_channel_census.py"
LIVE_CLAIM = "scripts/onethird_mg8a71_live_claim_control.py"
DECLARED_STRIKE = "scripts/onethird_mgcd04_declared_strike_control.py"


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, str(path))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _load_source(name, source, root):
    """Load a control from mutated SOURCE TEXT, pointed back at the repository.

    A control loaded from a temp file computes its own ROOT from `__file__`, so
    without the re-point it sweeps an empty corpus and every mutant 'passes' for
    the wrong reason -- the same trap the census's own `--demonstrate` documents.
    """
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="mg77e6-")) / f"{name}.py"
    tmp.write_text(source, encoding="utf-8")
    mod = _load(name, tmp)
    mod.ROOT = root
    return mod


CN = _load("mg9d7b_census", ROOT / CENSUS)
LC_SRC = (ROOT / LIVE_CLAIM).read_text(encoding="utf-8")
DS_SRC = (ROOT / DECLARED_STRIKE).read_text(encoding="utf-8")


def patch(source, old, new, what):
    """Textual patch that fails loudly if the anchor moved."""
    if source.count(old) != 1:
        raise SystemExit(f"anchor for {what} matched {source.count(old)} times, "
                         f"expected 1 -- the control changed under this probe")
    return source.replace(old, new)


# ---------------------------------------------------------------------------
# PART 1 -- five sixteenth channels.
#
# Each `build` returns (live_claim_source, declared_strike_source).  Each is a
# genuine new route by which text leaves a control unchecked.
# ---------------------------------------------------------------------------

# X1 -- TEXT-LEVEL REDACTION.  A5's own class: text deleted from inside a checked
# unit before the signatures see it.  The line still lands in `paragraph`; the
# unit is still yielded; only its CONTENT shrinks.  Unbounded, silent, no bucket.
# Exercised: this corpus is saturated with inline `code`, and `m_x` in backticks
# is a component of three of the four signatures.
#
# EVERY MUTANT BELOW IS EXERCISED BY THE CORPUS THE CONTROL ACTUALLY READS, and
# that is not a detail.  This probe's FIRST run used markers (`%%...%%`,
# `<!--nocheck`) that appear nowhere in `docs/OneThird-L1b-Spread-Locality.md`, so
# the new branches never ran, no bucket ever changed, and three mutants came back
# MISSED having removed exactly zero lines from the check.  A MISSED like that is
# a result about the probe, not about the census.  Each mutant now names the
# lines of the real document it moves, and Part 2 shows a real hit disappearing.
# The dormant version is kept deliberately, as X6, because it turned out to be a
# finding in its own right.
X1_OLD = '        low = INLINE_STRIKE.sub(" ", text).lower()'
X1_NEW = ('        low = re.sub(r"`[^`\\n]+`", " ",\n'
          '                     INLINE_STRIKE.sub(" ", text)).lower()')

# X2 -- FOLD INTO `blank`.  A list item is skipped and booked to a bucket that
# already exists and that no channel in the census is required to account for.
# Exercised: 17 `- ` lines in the document.
X2_OLD = ('        if line.strip() == "":\n'
          '            count("blank")\n'
          '            i += 1\n'
          '            continue\n')
X2_NEW = ('        if line.strip() == "":\n'
          '            count("blank")\n'
          '            i += 1\n'
          '            continue\n'
          '        if line.lstrip().startswith("- "):\n'
          '            count("blank")\n'
          '            i += 1\n'
          '            continue\n')
X2_OLD2 = ('        while j < n and lines[j].strip() != "" '
           'and not lines[j].startswith((">", "#")):')
X2_NEW2 = ('        while j < n and lines[j].strip() != "" '
           'and not lines[j].startswith((">", "#", "- ")):')

# X3 -- POPULATION NARROWING.  Documents are dropped after `names` is built, so
# even B6's own read/in-tree figures are untouched; the lines simply never enter
# any bucket, and a line that never enters is in no bucket to be attributed.
X3_OLD = '    for name in names:\n        if rev:'
X3_NEW = ('    for name in names:\n'
          '        if "L1b" in name:\n'
          '            continue\n'
          '        if rev:')

# X4 -- POSITIVE CONTROL: the live-claim control adopts its sibling's fence rule.
# The ONE mutant that should be caught by the bucket-name half, and a realistic
# change rather than a contrivance: the two controls disagree today about whether
# a fence is data, which is mg-9d7b's own A7.  Exercised: 34 fence-marker lines.
X4_NEW = ('        if line.strip() == "":\n'
          '            count("blank")\n'
          '            i += 1\n'
          '            continue\n'
          '        if line.lstrip().startswith("```"):\n'
          '            j = i + 1\n'
          '            while j < n and not lines[j].lstrip().startswith("```"):\n'
          '                j += 1\n'
          '            j = min(j + 1, n)\n'
          '            count("lc_fenced", j - i)\n'
          '            i = j\n'
          '            continue\n')

# X6 -- the DORMANT channel.  Identical in KIND to X4 -- a brand-new bucket name,
# the one thing the census's mechanical half exists to catch -- but keyed on a
# marker the corpus does not contain today.  Added AFTER X4's first form came
# back MISSED for exactly this reason: it is not a prediction, it is the
# accident promoted to an experiment.
X6_NEW = ('        if line.strip() == "":\n'
          '            count("blank")\n'
          '            i += 1\n'
          '            continue\n'
          '        if line.lstrip().startswith("<!--nocheck"):\n'
          '            count("nocheck")\n'
          '            i += 1\n'
          '            continue\n')

# X5 -- POSITIVE CONTROL: `exempt_annotation` grows with no channel counter.
X5_OLD = ('                for a, b_ in checkable:\n'
          '                    count("quote", b_ - a)\n')
X5_NEW = ('                for a, b_ in checkable:\n'
          '                    if b_ - a >= 3:\n'
          '                        count("exempt_annotation", b_ - a)\n'
          '                        continue\n'
          '                    count("quote", b_ - a)\n')

def _x2():
    src = patch(LC_SRC, X2_OLD, X2_NEW, "X2")
    return patch(src, X2_OLD2, X2_NEW2, "X2b"), DS_SRC


MUTANTS = [
    ("X1", "live-claim", "text-level redaction: inline `code` spans stripped from "
                         "every checked unit (A5's own class)",
     lambda: (patch(LC_SRC, X1_OLD, X1_NEW, "X1"), DS_SRC), "MISSED"),
    ("X2", "live-claim", "17 list-item lines skipped into the existing `blank` "
                         "bucket",
     _x2, "MISSED"),
    ("X3", "declared-strike", "population narrowing: whole documents never read, "
                              "B6's own figures untouched",
     lambda: (LC_SRC, patch(DS_SRC, X3_OLD, X3_NEW, "X3")), "MISSED"),
    ("X4", "live-claim", "POSITIVE CONTROL -- fenced code skipped into a NEW "
                         "bucket `lc_fenced` (34 lines)",
     lambda: (patch(LC_SRC, X2_OLD, X4_NEW, "X4"), DS_SRC), "CAUGHT"),
    ("X5", "live-claim", "POSITIVE CONTROL -- `exempt_annotation` grows with no "
                         "channel counter",
     lambda: (patch(LC_SRC, X5_OLD, X5_NEW, "X5"), DS_SRC), "CAUGHT"),
    ("X6", "live-claim", "a DORMANT new bucket: X4's kind, keyed on a marker "
                         "today's corpus does not contain",
     lambda: (patch(LC_SRC, X2_OLD, X6_NEW, "X6"), DS_SRC), "(unpredicted)"),
]


def run_census_on(lc_src, ds_src, tag):
    """Run the census's OWN observe() + audit() against these two control sources."""
    lc = _load_source(f"lc_{tag}", lc_src, ROOT)
    ds = _load_source(f"ds_{tag}", ds_src, ROOT)
    observed = CN.observe(lc, ds)
    bad = CN.audit(observed, {"live-claim": lc, "declared-strike": ds})
    return observed, bad


def _lines_moved(pristine, observed, control):
    """Lines the mutant reclassified, or removed from the population entirely.

    These are two different one-sided/two-sided arithmetics and they must not be
    told apart by a parity test -- an earlier version of this function halved the
    bucket delta whenever it happened to be even, which reports X3's 2823 removed
    lines as 1411 on any corpus where the total lands even.  The population total
    says which case it is, so it is asked rather than guessed.
    """
    a, b = pristine[control][1], observed[control][1]
    keys = set(a) | set(b)
    delta = sum(abs(a.get(k, 0) - b.get(k, 0)) for k in keys)
    lost = sum(a.values()) - sum(b.values())
    if lost > 0:                      # one-sided: lines left the population
        return lost
    return delta // 2                 # two-sided: every move is counted twice


def _x1_spans(_pristine, _observed, _control):
    """X1 is TEXT-level: by construction it moves no line between buckets.

    A line-delta is the wrong GRAIN for it, and reporting 0 here would call the
    one mutant whose class the census is most blind to `inert'.  The grain that
    fits is how many times the new branch has something to redact.
    """
    import re as _re
    lc = _load("lc_grain", ROOT / LIVE_CLAIM)
    doc = (ROOT / lc.DOC).read_text(encoding="utf-8")
    return len(_re.findall(r"`[^`\n]+`", doc))


# (measure, grain label).  Named per mutant because the probe's first run assumed
# one grain fitted all six, and three mutants keyed on markers the corpus does
# not contain ran zero new branches, moved zero lines, and came back MISSED -- a
# statement about the probe, not about the census.  A MISSED is interpretable
# only if the channel is EXERCISED, so the number is computed, and X6 is the one
# mutant allowed to be dormant because being dormant IS its experiment.
EXERCISE = {
    "X1": (_x1_spans, "inline `code` spans available to redact"),
    "X2": (_lines_moved, "lines reclassified"),
    "X3": (_lines_moved, "lines removed from the population"),
    "X4": (_lines_moved, "lines reclassified"),
    "X5": (_lines_moved, "lines reclassified"),
    "X6": (_lines_moved, "lines reclassified — 0 is the experiment"),
}


def part1(verbose=True):
    print("=" * 92)
    print("PART 1 -- SIX SIXTEENTH CHANNELS, judged by the census's own audit()")
    print("=" * 92)
    print("  `exercised` is what this mutant actually did to the REAL corpus, at "
          "the grain that fits")
    print("  its class.  A mutant that does nothing proves nothing about the "
          "census; X6 is the only")
    print("  one allowed to be dormant, because being dormant is its experiment.")
    print()
    pristine, _ = run_census_on(LC_SRC, DS_SRC, "pristine_ref")
    rows = []
    inert = []
    for mid, ctl, desc, build, expected in MUTANTS:
        lc_src, ds_src = build()
        observed, bad = run_census_on(lc_src, ds_src, mid)
        got = "CAUGHT" if bad else "MISSED"
        measure, grain = EXERCISE[mid]
        moves = measure(pristine, observed, ctl)
        if moves == 0 and mid != "X6":
            inert.append(mid)
        desc = f"{desc}\n      exercised: {moves} {grain}"
        rows.append((mid, ctl, desc, expected, got, bad, observed))
        if expected.startswith("("):
            mark = "no prediction was registered for this one"
        else:
            mark = "as predicted" if got == expected else "*** PREDICTION WRONG ***"
        print(f"  {mid}  [{ctl:<15}] {desc}")
        print(f"      census verdict: {got:<7} (predicted {expected})  {mark}")
        if verbose and bad:
            for c, cid, msg in bad:
                print(f"        VIOLATION [{c} {cid}] {msg}")
        print()
    missed = [r for r in rows if r[4] == "MISSED"]
    caught = [r for r in rows if r[4] == "CAUGHT"]
    print(f"  RESULT: {len(caught)} of {len(rows)} sixteenth channels CAUGHT, "
          f"{len(missed)} MISSED.")
    print(f"          missed: {', '.join(r[0] for r in missed) or '(none)'}")
    if inert:
        print(f"  !! INERT MUTANTS: {', '.join(inert)} moved 0 lines of the real "
              f"corpus.  Their verdicts")
        print(f"     are results about this probe, not about the census, and this "
              f"run is not interpretable.")
    print()
    return rows, inert


# ---------------------------------------------------------------------------
# PART 2 -- REACH.  A channel that changes no verdict is not a channel.
# ---------------------------------------------------------------------------

# S2-hinges-on-degree: "hinges on" AND "m_x".  A real signature of this control,
# not a sentence invented to be caught.
PLANT = "Lemma (B) hinges on capping the per-element degree m_x."
PLANT_TICKED = "Lemma (B) hinges on capping the per-element degree `m_x`."


def part2():
    print("=" * 92)
    print("PART 2 -- REACH: does the invisible channel actually let a live claim out?")
    print("=" * 92)
    print("  The planted sentence trips S2-hinges-on-degree, a signature this "
          "control really carries.")
    print()
    pristine = _load_source("lc_pristine", LC_SRC, ROOT)
    x1 = _load_source("lc_x1_reach", patch(LC_SRC, X1_OLD, X1_NEW, "X1"), ROOT)
    x2 = _load_source("lc_x2_reach", _x2()[0], ROOT)

    td = pathlib.Path(tempfile.mkdtemp(prefix="mg77e6-reach-"))
    plain = td / "plain.md"
    plain.write_text(f"# planted\n\n{PLANT}\n", encoding="utf-8")
    wrapped = td / "wrapped.md"
    wrapped.write_text(f"# planted\n\n{PLANT_TICKED}\n", encoding="utf-8")
    hidden = td / "hidden.md"
    hidden.write_text(f"# planted\n\n- {PLANT}\n", encoding="utf-8")

    def hits(mod, path):
        return len(mod.scan(str(path))[2])

    out = []
    for label, mod, path, base in (
            ("X1  the claim with `m_x` in backticks", x1, wrapped, plain),
            ("X2  the claim as a `- ` list item     ", x2, hidden, plain)):
        n_base = hits(pristine, base)
        n_pris = hits(pristine, path)
        n_mut = hits(mod, path)
        leaked = n_pris > 0 and n_mut == 0
        print(f"  {label}")
        print(f"      the same claim, unwrapped, under the PRISTINE control : "
              f"{n_base} hit(s)")
        print(f"      wrapped in the new channel, PRISTINE control          : "
              f"{n_pris} hit(s)")
        print(f"      wrapped in the new channel, MUTATED control           : "
              f"{n_mut} hit(s)")
        say = "REAL — a live claim leaves the check" if leaked else "NOT a route out"
        print(f"      -> the channel is {say}")
        print()
        out.append((label, n_base, n_pris, n_mut, leaked))
    return out


# ---------------------------------------------------------------------------
# PART 3 -- THE DELETION SWEEP.
# ---------------------------------------------------------------------------

def part3():
    print("=" * 92)
    print("PART 3 -- DELETION SWEEP: which of the census's own 15 rows could it "
          "re-discover?")
    print("=" * 92)
    print("  Delete one declared channel at a time and re-audit the UNMODIFIED "
          "controls at HEAD.")
    print("  CAUGHT = the author's declaration was not load-bearing; the census "
          "would have found it.")
    print("  MISSED = that row is in the census only because its author read it "
          "off the source.")
    print()
    lc = _load("lc_head", ROOT / LIVE_CLAIM)
    ds = _load("ds_head", ROOT / DECLARED_STRIKE)
    observed = CN.observe(lc, ds)
    modules = {"live-claim": lc, "declared-strike": ds}
    baseline = CN.audit(observed, modules)
    if baseline:
        print(f"  !! HEAD is not clean: {len(baseline)} violation(s) before any "
              f"deletion; the sweep below is not interpretable")
        return []

    full = list(CN.CHANNELS)
    results = []
    for row in full:
        cid = row[0]
        CN.CHANNELS = [r for r in full if r[0] != cid]
        bad = CN.audit(copy.deepcopy(observed), modules)
        CN.CHANNELS = full
        got = "CAUGHT" if bad else "MISSED"
        why = bad[0][2][:64] if bad else "no half of the invariant fires"
        results.append((cid, row[1], row[2], got, why))
        print(f"  {cid:<4} {row[1]:<16} {got:<7} {why}")
    caught = [r for r in results if r[3] == "CAUGHT"]
    print()
    print(f"  RESULT: the census re-discovers {len(caught)} of {len(full)} of its "
          f"own declared channels.")
    print(f"          re-discoverable: {', '.join(r[0] for r in caught)}")
    print(f"          declaration-only: "
          f"{', '.join(r[0] for r in results if r[3] == 'MISSED')}")
    print()
    return results


# ---------------------------------------------------------------------------
# PART 4 -- three specific claims in the deliverable.
# ---------------------------------------------------------------------------

def part4():
    print("=" * 92)
    print("PART 4 -- three claims in the deliverable, checked directly")
    print("=" * 92)
    out = {}

    # (a) E1/E2: the M4 bound sweep.  Reconstructed here rather than trusted.
    lc = _load("lc_sweep", ROOT / LIVE_CLAIM)
    lines = (ROOT / lc.DOC).read_text(encoding="utf-8").split("\n")
    target = None
    i = 0
    while i < len(lines):
        if lines[i].startswith(">"):
            j = i
            while j < len(lines) and lines[j].startswith(">"):
                j += 1
            blk = lines[i:j]
            head = " ".join(blk[:3]).lower()
            if any(mk.lower() in head for mk in lc.EXEMPT_MARKERS):
                subs = lc.sub_paragraphs(blk)
                if subs:
                    a, b = subs[-1]
                    txt = " ".join(x.lstrip("> ").rstrip() for x in blk[a:b])
                    if lc.QUOTATION.search(txt):
                        if target is None or (j - i) > (target[1] - target[0]):
                            target = (i, j, i + b)
            i = j
            continue
        i += 1
    # mg-9a19's OWN mutant sentence, imported rather than paraphrased: a
    # paraphrase that trips no signature scores 0 at every cap and would have
    # reported E1 as refuted for a reason having nothing to do with the bound.
    a9 = _load("mg9a19", ROOT / "scripts/onethird_mg9a19_exemption_population_audit.py")
    sentence = a9.MUTANT_SENTENCE
    td = pathlib.Path(tempfile.mkdtemp(prefix="mg77e6-m4-"))
    m4 = td / "M4.md"
    m4.write_text("\n".join(lines[:target[2]] + ["> " + sentence]
                            + lines[target[2]:]), encoding="utf-8")
    head_doc = str(ROOT / lc.DOC)
    print("  (a) E1/E2 -- MAX_QUOTED_LINES sweep against mg-9a19's M4")
    print(f"      {'cap':<6}{'HEAD hits':<12}M4 hits")
    sweep = {}
    saved = lc.MAX_QUOTED_LINES
    for cap in (10, 11, 12, 13):
        lc.MAX_QUOTED_LINES = cap
        h_head = len(lc.scan(head_doc)[2])
        h_m4 = len(lc.scan(str(m4))[2])
        sweep[cap] = (h_head, h_m4)
        note = "  <- shipped" if cap == saved else ""
        verdict = "caught" if h_m4 else "MISSED"
        print(f"      {cap:<6}{h_head:<12}{h_m4} {verdict}{note}")
    lc.MAX_QUOTED_LINES = saved
    out["sweep"] = sweep
    # GRAIN: the report's M4 column is the control's EXIT CODE (0/1); this column
    # is the HIT COUNT, which is 2 because mg-9a19's mutant sentence trips both
    # S1 and S2.  The two agree in sign at every cap, which is what E1 claims.
    e1_holds = (sweep[12][1] == 0 and sweep[13][1] == 0
                and sweep[11][1] >= 1 and sweep[10][1] >= 1
                and all(v[0] == 0 for v in sweep.values()))
    print(f"      -> E1 (a cap of 12 does NOT close M4): "
          f"{'HOLDS' if e1_holds else 'DOES NOT HOLD'}")
    out["e1"] = e1_holds
    print()

    # (b) is BASELINE a bound?
    ds = _load("ds_baseline", ROOT / DECLARED_STRIKE)
    lc2 = _load("lc_baseline", ROOT / LIVE_CLAIM)
    observed = CN.observe(lc2, ds)
    n_before = len(ds.BASELINE)
    ds.BASELINE = set(ds.BASELINE) | {("invented.md", "an invented tolerance"),
                                      ("invented2.md", "another one")}
    bad = CN.audit(observed, {"live-claim": lc2, "declared-strike": ds})
    b5_flagged = any(c[1] == "B5" for c in bad)
    print("  (b) B5 is declared BOUNDED by the identifier `BASELINE`")
    print(f"      BASELINE grown {n_before} -> {len(ds.BASELINE)} sites; census "
          f"flags B5: {b5_flagged}")
    print(f"      -> the bound-exists half is `hasattr`, which a set of ANY size "
          f"satisfies:")
    say = ("CONFIRMED — B5 names a tolerance list, not a bound on reach"
           if not b5_flagged else "the census does constrain it")
    print(f"         {say}")
    out["b5_unbounded"] = not b5_flagged
    print()

    # (c) does the census consult the control's exit code?
    broken = patch(LC_SRC, "def main():", "def main():\n    import sys as _s\n"
                                          "    print('A5 A6'); _s.exit(1)\n", "X-exit")
    _obs, bad = run_census_on(broken, DS_SRC, "exitcode")
    print("  (c) a control mutated to EXIT 1 on its own run, buckets untouched")
    print(f"      census violations: {len(bad)}")
    say = ("CONFIRMED — the census PASSES a control that is itself RED"
           if not bad else "the census notices")
    print(f"      -> {say}")
    out["exit_code_ignored"] = not bad
    print()
    return out


# What this probe MEASURED when it was written, so the characterisation cannot
# drift quietly in either direction.  A movement here is not a regression on its
# own -- widening the census's reach SHOULD move it -- but it must be deliberate,
# which is the same contract mg-9a19's RECORDED table set and mg-9d7b honoured.
RECORDED = {
    "X1": "MISSED",   # text-level redaction (A5's own class)
    "X2": "MISSED",   # skip folded into the existing `blank` bucket
    "X3": "MISSED",   # population narrowing
    "X4": "CAUGHT",   # a NEW bucket name, exercised by today's corpus
    "X5": "CAUGHT",   # unattributed lines in `exempt_annotation`
    "X6": "MISSED",   # a NEW bucket name that today's corpus never triggers
}
RECORDED_REDISCOVERABLE = ["A1", "A2", "A4", "B1"]   # of the census's own 15


def handshake(rows, sweep):
    moved = []
    for mid, _c, _d, _e, got, _b, _o in rows:
        if RECORDED.get(mid) != got:
            moved.append(f"{mid}: recorded {RECORDED.get(mid)}, got {got}")
    disc = [r[0] for r in sweep if r[3] == "CAUGHT"]
    if disc != RECORDED_REDISCOVERABLE:
        moved.append(f"re-discoverable set: recorded {RECORDED_REDISCOVERABLE}, "
                     f"got {disc}")
    return moved


def main():
    verbose = "--quiet" not in sys.argv
    print("=" * 92)
    print("mg-77e6 -- CAN THE mg-9d7b CENSUS DISCOVER A CHANNEL, OR ONLY CHECK ONE?")
    print("=" * 92)
    print("mg-9d7b E13 predicted the census would find a channel its author's "
          "reading had missed.")
    print("Its report records MISSED and reads that as a complete reading.  This "
          "probe asks the")
    print("prior question: given a channel the author did NOT declare, does the "
          "census say so?")
    print()

    rows, inert = part1(verbose)
    reach = part2()
    sweep = part3()
    claims = part4()

    print("=" * 92)
    print("VERDICT")
    print("=" * 92)
    missed = [r[0] for r in rows if r[4] == "MISSED"]
    caught = [r[0] for r in rows if r[4] == "CAUGHT"]
    real = [r[0] for r in reach if r[4]]
    disc = [r[0] for r in sweep if r[3] == "CAUGHT"]
    print(f"  sixteenth channels built            : {len(rows)}")
    print(f"  CAUGHT by the census                : {len(caught)}  "
          f"({', '.join(caught)})")
    print(f"  MISSED by the census                : {len(missed)}  "
          f"({', '.join(missed)})")
    print(f"  of the missed, demonstrably a route : {len(real)} of 2 tested "
          f"({', '.join(real)})")
    print(f"  census's own 15 rows re-discoverable: {len(disc)}  "
          f"({', '.join(disc)})")
    print(f"  A5 re-discoverable                  : "
          f"{'yes' if 'A5' in disc else 'NO'}")
    print(f"  A8 re-discoverable                  : "
          f"{'yes' if 'A8' in disc else 'NO'}")
    print()
    if missed:
        print("  E13's MISSED is not evidence that no channel was missed.  The "
              "census's mechanical")
        print("  half fires on exactly two things: a NEW BUCKET NAME, and lines "
              "in `exempt_annotation`")
        print("  or `fenced_code` that no declared channel claims.  A channel "
              "outside that class is")
        print("  invisible to it — including both channels this deliverable "
              "reports as discoveries.")
        print()
        print("  The census is a REGRESSION TEST on a declared enumeration, which "
              "is a real and")
        print("  useful thing, and it is not the DISCOVERY instrument E13 was "
              "a prediction about.")
    else:
        print("  Every sixteenth channel built here was caught.  E13's MISSED "
              "stands as evidence.")
    print()

    if inert:
        print(f"  FAIL — {', '.join(inert)} moved 0 lines.  A mutant that never "
              f"fires cannot be MISSED")
        print("  by the census; it was missed by this probe.  Fix the mutant "
              "before reading the verdict.")
        print()
        return 1

    moved = handshake(rows, sweep)
    if moved:
        print("  HANDSHAKE — a recorded outcome MOVED:")
        for m in moved:
            print(f"    {m}")
        print("  Widening the census SHOULD move these.  Re-record RECORDED in "
              "this file, in the")
        print("  commit that widens it, with the old values kept visible.")
        print()
        return 1
    print("  handshake: every recorded outcome is where mg-77e6 left it.")
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
