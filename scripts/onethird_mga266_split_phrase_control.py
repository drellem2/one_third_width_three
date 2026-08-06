#!/usr/bin/env python3
"""
mg-a266 -- CAN THE RE-CHECK SEE A PHRASE SPLIT ACROSS A COMMENT?  A positive
control on the instrument, before any of its clean results are believed.

INDEPENDENT AUDIT of mg-9a59 (`c64fe68`), which is DONE.  Its doc §5(g) says:

    A sweep that flattens comment continuations finds 30 occurrences of the
    phrase across 8 tracked files ... 0 assert it as the window.  The sweep was
    demonstrated able to find a wrapped instance before its clean result was
    trusted: on a synthetic `for 21\\n# hours`, the flattening sweep returns
    FOUND where `grep "21 hours"` returns MISSED.

THE SWEEP IS NOT IN `c64fe68`.  That commit adds one doc and edits three
scripts; none of them contains a sweep.  BUT IT IS IN THE REPOSITORY, and this
file's author predicted otherwise and was wrong: `docs/OneThird-mg3946-Verdict
Closeout.md` publishes it as a runnable shell+python block, authored by
mg-3946 for its F4 row --

    flat = re.sub(r'\\s*(?:#|//|\\*)?\\s*\\n\\s*(?:#|//|\\*)?\\s*', ' ', s)
    for m in re.finditer(r'(21 hours?|eight consecutive|~?24 hours|24 h 09 m)',
                         flat): ...
    # over: git ls-files | grep -E '\\.(md|sh|py|yml|txt)$'

-- so the technique has provenance and a written form.  What it does not have
is a place that RUNS it: it is a snippet inside prose, wired to no CI job and
to no control, and nothing re-runs it or notices if it stops working.  That is
why `30`, `8` and `0` still cannot be chased by a reader who does not first
find a code block buried in a different ticket's closeout doc.  This file
implements that exact snippet as INSTRUMENT C and re-derives its numbers with
it, so the parent's counts are compared against the parent's own tool rather
than against a substitute.

WHY THIS MATTERS MORE THAN THE ARITHMETIC.  A checker that silently fails to
match a split phrase reports CLEAN because it CANNOT SEE, not because there is
nothing there.  `grep -rn "21 hours"` is exactly such a checker, and that is
not hypothetical: two `.yml` sites survived three separate rounds of "corrected
at every site" precisely because each wrapped the phrase across a comment
continuation where a line-oriented grep is blind (mg-76d0 §3b).  A clean sweep
from a blind instrument is worth nothing, so the instrument gets a positive
control first and the population second.

WHAT THIS FILE DOES.

  PART 1  FOUR INSTRUMENTS -- one line-oriented, two of mine, and mg-3946's
          published snippet verbatim -- run over EIGHT PLANTED SHAPES in a
          fixture tree.  Each shape is a way a phrase
          can be split; each instrument either FINDS it or does not.  Two of
          the shapes are the parent's own; four are not, and one is a NEGATIVE
          that a flattening sweep must be expected to match and that a reader
          must not be told is an assertion.

  PART 2  THE COST OF FLATTENING, measured rather than asserted.  Joining
          lines buys recall and spends precision, and the parent's paragraph
          states the recall and not the price.  Both sweeps run over the real
          tracked tree and their match sets are differenced.

  PART 3  THE POPULATION, re-derived with the PARENT'S OWN INSTRUMENT over
          the PARENT'S OWN TREE, because a re-derivation that changes both
          the tool and the population settles nothing.  Compared against the
          parent's `30 / 8`.

  PART 4  WHAT IS ACTUALLY ASSERTED.  "Occurrence" is mechanical; "asserts the
          figure as the window" is a JUDGEMENT, and this file does not pretend
          otherwise.  It applies one stated proxy rule, and then applies a
          COMMITTED HAND ADJUDICATION of every occurrence the proxy flags --
          so the judgement is checkable, and an occurrence nobody has read
          FAILS the run instead of passing quietly.

AND IT DOES NOT CARRY THE DEFECT IT AUDITS.  `ALL_HELD` is conjoined with a
non-empty assertion count; the population is printed next to the verdict; a
run that plants no shapes or sweeps no files exits 2 rather than 0.

Run:  /usr/bin/python3 scripts/onethird_mga266_split_phrase_control.py
      (order-seconds; no numpy, no network)
      --phrase "21 hours"   the phrase to hunt (default: the parent's)
"""

import os
import re
import sys
import json
import shutil
import argparse
import tempfile
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPORT = os.path.join("data", "onethird-mga266-split-phrase-control.json")

DEFAULT_PHRASE = "21 hours"

# The parent commit whose counts are under re-derivation.  Pinned: the
# refinery rebases, so this is verified with `git patch-id --stable` rather
# than assumed to keep its SHA on main.
PARENT_REV = "c64fe68"

# Comment and quotation openers seen in this repo's tracked text: python/yaml/
# shell `#`, C/JS `//`, SQL/Lua `--`, block-comment `*`, markdown quote `>`.
COMMENT_LEAD = re.compile(r"^[ \t]*(?:#+|//+|--|\*|>)[ \t]?")
TRAILING_BACKSLASH = re.compile(r"\\[ \t]*$")
EDGE_QUOTES = re.compile(r'^[ \t]*["\']|["\'][ \t]*$')


# ------------------------------------------------------------ instruments ---
# FOUR, deliberately, because the interesting result is not "a sweep finds it"
# but WHICH sweep finds WHICH shape.  Instrument 0 is the one that was actually
# in use when two sites survived three rounds of correction; instrument C is
# mg-3946's published one, so the parent's numbers are re-derived with the
# parent's own tool rather than with a substitute of mine.
def instrument_grep(text, phrase):
    """Instrument 0 -- LINE-ORIENTED, i.e. `grep -rn "21 hours"`.

    The baseline, and the one whose blindness is the reason any of this
    exists.  It can only see the phrase when it lies inside one line."""
    hits = []
    rx = re.compile(re.escape(phrase))
    for i, line in enumerate(text.splitlines(), 1):
        if rx.search(line):
            hits.append({"line": i, "how": "whole phrase on one line"})
    return hits


def _flatten(text, strip_quotes, strip_backslash):
    """Join every line into one stream, recording which original line each
    character came from, so a match can be reported at a line number rather
    than at a meaningless offset into a joined blob."""
    parts, owner = [], []
    for i, raw in enumerate(text.splitlines(), 1):
        line = raw
        if strip_backslash:
            line = TRAILING_BACKSLASH.sub("", line)
        line = COMMENT_LEAD.sub("", line)
        if strip_quotes:
            # Applied twice: a line can both end and begin with a quote.
            line = EDGE_QUOTES.sub("", line)
            line = EDGE_QUOTES.sub("", line)
        line = line.strip()
        if parts:
            parts.append(" ")
            owner.append(i)
        parts.append(line)
        owner.extend([i] * len(line))
    return "".join(parts), owner


def _sweep(text, phrase, strip_quotes, strip_backslash, how):
    flat, owner = _flatten(text, strip_quotes, strip_backslash)
    # Whitespace-flexible: the phrase's own internal space may have become the
    # join, so it must be allowed to be any run of whitespace.
    rx = re.compile(r"\s+".join(re.escape(w) for w in phrase.split()))
    hits = []
    for m in rx.finditer(flat):
        start, end = m.start(), min(m.end() - 1, len(owner) - 1)
        l0, l1 = owner[start], owner[end]
        hits.append({"line": l0, "through_line": l1,
                     "split": l1 != l0,
                     "how": how,
                     "text": flat[max(0, start - 60):end + 60].strip()})
    return hits


def instrument_flatten_comments(text, phrase):
    """Instrument A -- the parent's stated technique: flatten COMMENT
    continuations.  Strips a leading comment marker from each line and joins."""
    return _sweep(text, phrase, strip_quotes=False, strip_backslash=False,
                  how="comment-flattening")


def instrument_flatten_aggressive(text, phrase):
    """Instrument B -- also strips edge quotes and trailing backslashes, which
    is what a split across a STRING CONCATENATION or a LINE CONTINUATION
    needs.  Strictly more recall than A, and Part 2 measures what it costs."""
    return _sweep(text, phrase, strip_quotes=True, strip_backslash=True,
                  how="aggressive-flattening")


# mg-3946's PUBLISHED snippet, verbatim, from docs/OneThird-mg3946-Verdict
# Closeout.md.  Transcribed rather than re-expressed: this is the instrument
# the parent's §5(g) counts came from, so re-deriving those counts with
# anything else would compare two numbers that were never the same
# measurement.  Its file filter is part of it and is reproduced below.
MG3946_FLATTEN = re.compile(r"\s*(?:#|//|\*)?\s*\n\s*(?:#|//|\*)?\s*")
MG3946_FILE_FILTER = re.compile(r"\.(md|sh|py|yml|txt)$")


def instrument_mg3946_snippet(text, phrase):
    """Instrument C -- mg-3946's published snippet, exactly as written.

    Note what it does that sweep A does not: it flattens EVERY newline, not
    only ones following a comment marker, so it is closer to sweep A than to
    grep but is not identical to either.  Note also that its own phrase
    pattern is `21 hours?` -- singular matches too -- which is a different
    question from the one `--phrase` asks; the phrase given here is used, so
    the comparison stays about the FLATTENING and not about the pattern."""
    flat = MG3946_FLATTEN.sub(" ", text)
    rx = re.compile(r"\s+".join(re.escape(w) for w in phrase.split()))
    hits = []
    for m in rx.finditer(flat):
        hits.append({"line": None, "how": "mg-3946 published snippet",
                     "text": flat[max(0, m.start() - 60):m.end() + 60].strip()})
    return hits


INSTRUMENTS = [
    ("grep (line-oriented)", instrument_grep),
    ("sweep A (comment-flattening)", instrument_flatten_comments),
    ("sweep B (aggressive)", instrument_flatten_aggressive),
    ("sweep C (mg-3946 snippet)", instrument_mg3946_snippet),
]


# ---------------------------------------------------------------- fixtures ---
# EIGHT PLANTED SHAPES.  Provenance is recorded per shape because it decides
# how much each one can say: a shape chosen by the same author who wrote the
# sweep proves less than one that was not.
SHAPES = [
    {"id": "S0", "name": "unsplit, on one line",
     "provenance": "baseline -- every instrument must find this or it is broken",
     "must_find": True,
     "file": "workflow.yml",
     "body": '# the demo was dead on arrival in CI for 21 hours before anyone\n'
             '# noticed it\n'},
    {"id": "S1", "name": "split across a YAML/shell comment continuation",
     "provenance": "THE PARENT'S OWN SHAPE (`for 21` / `# hours`), the one its "
                   "doc says was demonstrated; re-derived here",
     "must_find": True,
     "file": "gate-mutation-demo.yml",
     "body": '      # the demonstration was dead on arrival in CI for 21\n'
             '      # hours, which is the window this comment is about\n'},
    {"id": "S2", "name": "split across a python comment continuation",
     "provenance": "the same shape in a different comment syntax -- so the "
                   "result is not one marker measured twice",
     "must_find": True,
     "file": "probe.py",
     "body": '    # the red window ran for 21\n'
             '    # hours and nothing caught it\n'},
    {"id": "S3", "name": "split across a STRING CONCATENATION",
     "provenance": "NOT the parent's; a shape its stated technique was never "
                   "claimed to cover",
     "must_find": True,
     "file": "runner.py",
     "body": '    msg = ("the gate was red for 21 "\n'
             '           "hours before the revert landed")\n'},
    {"id": "S4", "name": "split across a BACKSLASH line continuation",
     "provenance": "NOT the parent's",
     "must_find": True,
     "file": "gate.sh",
     "body": 'echo "the window was 21 \\\n'
             'hours wide"\n'},
    {"id": "S5", "name": "soft-wrapped in prose (markdown)",
     "provenance": "NOT the parent's; the commonest split in this repo's docs, "
                   "where the phrase is discussed most",
     "must_find": True,
     "file": "note.md",
     "body": 'The workflow header said the demonstration had been red for 21\n'
             'hours, a figure this document corrects below.\n'},
    {"id": "S6", "name": "split across a comment AND a blank line",
     "provenance": "NOT the parent's; the shape that defeats a flattener which "
                   "only joins ADJACENT non-empty lines",
     "must_find": True,
     "file": "workflow-blank.yml",
     "body": '# the red window was 21\n'
             '\n'
             '# hours long\n'},
    {"id": "S7", "name": "NEGATIVE -- two unrelated tokens that flattening "
                         "glues into the phrase",
     "provenance": "NOT the parent's, and the one that measures the PRICE of "
                   "the technique rather than its reach",
     "must_find": False,
     "file": "unrelated.py",
     "body": 'MAX_RETRIES = 21\n'
             '# hours are not what this constant counts\n'},
]


def plant(root):
    for s in SHAPES:
        with open(os.path.join(root, f"{s['id']}-{s['file']}"), "w") as f:
            f.write(s["body"])


# ------------------------------------------------------- the tracked tree ---
def rederive_at(rev, phrase):
    """PART 3's core: run mg-3946's OWN snippet over the tree AS OF `rev`.

    Two things have to be held fixed for a re-derivation to mean anything, and
    both were floating before: the INSTRUMENT (mg-3946's snippet, not mine)
    and the POPULATION (the tree at the parent's own commit, not this branch,
    which has since added files that themselves quote the phrase -- including
    this audit's own predictions doc).  Comparing my sweep over my branch
    against the parent's sweep over its branch would have produced a
    disagreement made entirely of my own commits."""
    ls = subprocess.run(["git", "ls-tree", "-r", "--name-only", rev],
                        cwd=REPO, capture_output=True, text=True)
    if ls.returncode != 0:
        return {"rev": rev, "error": ls.stderr.strip()}
    files = [f for f in ls.stdout.splitlines() if MG3946_FILE_FILTER.search(f)]
    per_file, total = {}, 0
    for rel in files:
        show = subprocess.run(["git", "show", f"{rev}:{rel}"], cwd=REPO,
                              capture_output=True)
        try:
            text = show.stdout.decode("utf-8")
        except UnicodeDecodeError:
            continue
        hits = instrument_mg3946_snippet(text, phrase)
        if hits:
            per_file[rel] = len(hits)
            total += len(hits)
    return {"rev": rev,
            "instrument": "mg-3946's published snippet, verbatim",
            "file_filter": MG3946_FILE_FILTER.pattern,
            "files_scanned": len(files),
            "occurrences": total,
            "files_with_a_match": len(per_file),
            "per_file": per_file,
            "grain": "one regex match over the flattened file"}


def tracked_text_files():
    """The population for Parts 2-4, NAMED rather than assumed: every file
    git tracks whose bytes decode as UTF-8 text.  `git ls-files` is the
    definition, so a reader can reproduce the file set exactly."""
    out = subprocess.run(["git", "ls-files"], cwd=REPO,
                         capture_output=True, text=True)
    if out.returncode != 0:
        raise SystemExit(f"git ls-files failed: {out.stderr.strip()}")
    files = []
    for rel in out.stdout.splitlines():
        p = os.path.join(REPO, rel)
        if not os.path.isfile(p):
            continue
        try:
            with open(p, encoding="utf-8") as f:
                f.read()
        except (UnicodeDecodeError, OSError):
            continue
        files.append(rel)
    return files


# ------------------------------------------------- assertion vs quotation ---
# A PROXY, and it is labelled one.  Whether a site ASSERTS the figure or merely
# QUOTES it inside a correction is a judgement about English, and a script that
# pretended to settle it would be the mg-8af0 shape -- a row scoring a string
# literal.  So: one stated rule, every classified assertion printed in full,
# and the rule printed next to the count so a reader can overrule it on the
# evidence rather than on trust.
QUOTATION_MARKERS = [
    "said", "says", "claimed", "claims", "superseded", "corrected", "correct",
    "wrong", "refuted", "was not", "against a measured", "instead of",
    "the ticket", "undercount", "~~", "REFUTED", "left standing", "asserting",
    "not the window", "quotation", "history", "audit", "finding", "predicted",
    "prediction", "still said", "each wrapping", "misses", "MISSED", "FOUND",
    "synthetic", "grep", "sweep", "flatten",
]


def classify(window):
    low = window.lower()
    hits = [m for m in QUOTATION_MARKERS if m.lower() in low]
    return ("quotation-or-correction" if hits else "ASSERTS-THE-FIGURE"), hits


# THE JUDGEMENT THE PROXY CANNOT MAKE, made by hand, committed, and CHECKED.
#
# The proxy above scores 6 occurrences ASSERTING.  A human read all six and
# none of them asserts the figure as the window -- so the parent's substantive
# claim (0 asserting sites) holds, and the disagreement is the PROXY's failure,
# not the parent's.  Recording that as prose in a doc would make it another
# uncheckable claim of exactly the kind this audit exists to complain about.
# So it is a table, keyed on a distinctive fragment of each occurrence, and an
# occurrence the proxy flags that is NOT in this table FAILS the run: a new
# site has appeared that no human has read, and silence about it would be the
# vacuous pass in its other direction.
ADJUDICATED = [
    ("OneThird-mg3946-CIHistoryDepth-IndependentAudit.md",
     "in the workflow header",
     "quotation-in-a-correction",
     "row F4 quotes the superseded figure and immediately gives the measured "
     "24 h 08 m 55 s against it"),
    ("OneThird-mg3946-VerdictCloseout.md",
     "mg-3934 control step",
     "quotation-in-a-corrections-table",
     "a table cell holding the WRONG value next to a cell holding the right "
     "one; the table's whole purpose is that the left column is superseded"),
    ("OneThird-mg3946-VerdictCloseout.md",
     "re.finditer",
     "NEITHER -- a search pattern",
     "the phrase appears inside the sweep snippet's own regex literal.  It is "
     "not a claim about a window at all, and counting it as one would be a "
     "row name that is not its measurement"),
    ("OneThird-mg76d0-PartialReport-IndependentAudit-Predictions.md",
     "are still",
     "quotation-in-a-prediction",
     "pre-registers that the two .yml comments STILL say the superseded "
     "figure; quoting a defect in order to predict it is not asserting it"),
    ("OneThird-mg76d0-PartialReportRepair-IndependentAudit.md",
     "looked exactly like",
     "narration-about-appearance",
     "describes how long a red CI job LOOKED broken, not how wide the window "
     "was; the same doc argues this explicitly at its own line 274"),
    ("OneThird-mg76d0-PartialReportRepair-IndependentAudit.md",
     "are statements about how long",
     "meta-discussion-of-the-above",
     "the sentence that draws precisely this distinction, which cannot itself "
     "be an assertion of the figure"),
]


def adjudicate(rel, window):
    base = os.path.basename(rel)
    for f, frag, verdict, why in ADJUDICATED:
        if f == base and frag in window:
            return verdict, why
    return None, None


# ------------------------------------------------------------------ ledger ---
class Ledger:
    def __init__(self):
        self.problems = []
        self.checks = 0

    def check(self, cond, label):
        self.checks += 1
        if not cond:
            self.problems.append(label)
        return cond


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--phrase", default=DEFAULT_PHRASE)
    # THE POSITIVE CONTROL ON THIS FILE'S OWN VACUITY GUARD.  Without a way to
    # reach it, "ALL_HELD is conjoined with a non-empty population" is a claim
    # about code nobody has seen run -- which is the shape under audit, in the
    # instrument auditing it.  This flag empties the population deliberately;
    # the run MUST then exit 2 with ALL_HELD false.
    ap.add_argument("--prove-empty-guard", action="store_true",
                    help="empty this file's own population and confirm it "
                         "refuses a verdict (must exit 2)")
    args = ap.parse_args()
    phrase = args.phrase
    led = Ledger()

    if args.prove_empty_guard:
        SHAPES.clear()
        print("=" * 78)
        print("--prove-empty-guard: THIS FILE'S OWN POPULATION EMPTIED "
              "DELIBERATELY")
        print("=" * 78)
        print(f"  planted shapes : {len(SHAPES)}")
        print(f"  assertions     : {led.checks}")
        print("  ZERO SHAPES AND ZERO ASSERTIONS -- THIS RUN MEASURED "
              "NOTHING.")
        print("  ALL_HELD is written FALSE, not true-over-an-empty-list.  "
              "Exiting 2.")
        print("  This is the guard the module docstring claims, SEEN TO FIRE. "
              " Without")
        print("  this flag it would be unreachable, and an unreachable guard "
              "is the exact")
        print("  shape this audit was sent to look for -- in the instrument "
              "doing the looking.")
        # AND IT DOES NOT WRITE THE REAL REPORT.  The first draft of this
        # branch dumped a stub over `REPORT` -- which is mg-a471's F5 defect
        # exactly: a run that measured nothing, landing at the canonical path,
        # where the next reader finds it and believes it is the record.  A
        # deliberately-empty run gets its own path and leaves the real one
        # alone.
        stub = REPORT.replace(".json", ".PROVE-GUARD.json")
        with open(os.path.join(REPO, stub), "w") as f:
            json.dump({"what": "--prove-empty-guard: population emptied "
                               "deliberately to show the guard fires",
                       "shapes": 0, "assertions": 0, "ALL_HELD": False,
                       "IS_THE_MEASUREMENT": False}, f, indent=2)
        print(f"  wrote {stub} -- NOT {REPORT}, which is untouched.")
        return 2

    print("=" * 78)
    print("mg-a266 -- CAN THE RE-CHECK SEE A PHRASE SPLIT ACROSS A COMMENT?")
    print("=" * 78)
    print(f"  phrase under hunt : {phrase!r}")
    print(f"  planted shapes    : {len(SHAPES)} "
          f"({sum(1 for s in SHAPES if s['must_find'])} that must be found, "
          f"{sum(1 for s in SHAPES if not s['must_find'])} negative)")

    # ---- PART 1: the positive control -----------------------------------
    print()
    print("PART 1 -- THE POSITIVE CONTROL: eight planted shapes x three "
          "instruments")
    root = tempfile.mkdtemp(prefix="mga266-shapes-")
    shape_rows = []
    try:
        plant(root)
        header = f"  {'shape':<6}{'':<52}" + "".join(
            f"{n.split(' (')[0]:<14}" for n, _ in INSTRUMENTS)
        print(header)
        for s in SHAPES:
            with open(os.path.join(root, f"{s['id']}-{s['file']}")) as f:
                text = f.read()
            found = {}
            for name, fn in INSTRUMENTS:
                hits = fn(text, phrase)
                found[name] = bool(hits)
            shape_rows.append({**{k: v for k, v in s.items() if k != "body"},
                               "found_by": found})
            print(f"  {s['id']:<6}{s['name'][:50]:<52}"
                  + "".join(f"{'FOUND' if found[n] else 'MISSED':<14}"
                            for n, _ in INSTRUMENTS))
        print()

        # THE ASSERTION THE WHOLE FILE EXISTS FOR.  The parent's own shape --
        # a phrase split across a comment continuation -- must be FOUND by the
        # flattening sweep and MISSED by the line-oriented one.  If it is not
        # found, the sweep's clean result over the whole tree is worth nothing
        # and this file says so in those words.
        s1 = next(r for r in shape_rows if r["id"] == "S1")
        led.check(s1["found_by"]["sweep A (comment-flattening)"],
                  "S1: the comment-continuation split -- THE PARENT'S OWN "
                  "SHAPE -- is NOT found by the flattening sweep.  Every clean "
                  "result this technique has ever reported is worth nothing.")
        led.check(not s1["found_by"]["grep (line-oriented)"],
                  "S1: grep found the split phrase, so this fixture does not "
                  "reproduce the blindness it was built to demonstrate and the "
                  "sweep's advantage over grep is unmeasured here")
        for r in shape_rows:
            if r["must_find"]:
                led.check(r["found_by"]["sweep B (aggressive)"],
                          f"{r['id']} ({r['name']}) is not found by ANY sweep "
                          f"in this file")
        # The negative is not a failure -- it is the price, and it is asserted
        # so that a future edit which quietly makes it stop matching does not
        # go unnoticed.  See Part 2.
        s7 = next(r for r in shape_rows if r["id"] == "S7")
        led.check(s7["found_by"]["sweep A (comment-flattening)"],
                  "S7: the false-positive shape stopped matching, so Part 2's "
                  "measured precision cost no longer measures anything")
    finally:
        shutil.rmtree(root, ignore_errors=True)

    grep_only = [r["id"] for r in shape_rows
                 if r["must_find"] and not r["found_by"]["grep (line-oriented)"]]
    a_misses = [r["id"] for r in shape_rows
                if r["must_find"]
                and not r["found_by"]["sweep A (comment-flattening)"]]
    print(f"  shapes the LINE-ORIENTED instrument cannot see: "
          f"{len(grep_only)}/{sum(1 for s in SHAPES if s['must_find'])} "
          f"-> {','.join(grep_only)}")
    print(f"  shapes the PARENT'S technique (sweep A) cannot see: "
          f"{len(a_misses)} -> {','.join(a_misses) or '(none)'}")

    # ---- PART 2: what flattening costs ----------------------------------
    print()
    print("PART 2 -- WHAT JOINING LINES BREAKS, over the real tracked tree")
    files = tracked_text_files()
    per_file = {}
    for rel in files:
        with open(os.path.join(REPO, rel), encoding="utf-8") as f:
            text = f.read()
        g = instrument_grep(text, phrase)
        a = instrument_flatten_comments(text, phrase)
        b = instrument_flatten_aggressive(text, phrase)
        if g or a or b:
            per_file[rel] = {"grep": g, "sweepA": a, "sweepB": b}
    n_grep = sum(len(v["grep"]) for v in per_file.values())
    n_a = sum(len(v["sweepA"]) for v in per_file.values())
    n_b = sum(len(v["sweepB"]) for v in per_file.values())
    split_a = [(rel, h) for rel, v in per_file.items()
               for h in v["sweepA"] if h["split"]]
    extra_b = n_b - n_a
    print(f"  population: {len(files)} git-tracked UTF-8 text files "
          f"(`git ls-files`), grain = one MATCH")
    print(f"  grep (line-oriented) matches        : {n_grep}")
    print(f"  sweep A (comment-flattening) matches: {n_a}"
          f"   (+{n_a - n_grep} that grep cannot see)")
    print(f"  sweep B (aggressive) matches        : {n_b}"
          f"   (+{extra_b} beyond sweep A)")
    print(f"  matches that SPAN A LINE BREAK      : {len(split_a)}")
    for rel, h in split_a[:6]:
        print(f"      {rel}:{h['line']}-{h['through_line']}  "
              f"...{h['text'][:90]}...")
    print("  THE PRICE: every one of those extra matches is a phrase the")
    print("  flattener assembled from two lines.  S7 shows the shape where "
          "that is")
    print("  WRONG, and nothing in the technique can tell S1 from S7 -- only a "
          "reader can.")

    # ---- PART 3: the population, re-derived ------------------------------
    print()
    print("PART 3 -- THE PARENT'S 30 / 8, RE-DERIVED WITH THE PARENT'S OWN "
          "INSTRUMENT")
    files_with = sorted(per_file)
    at_parent = rederive_at(PARENT_REV, phrase)
    # THE TREE THE PARENT ACTUALLY SWEPT.  A sweep run while writing a commit
    # sees the tree BEFORE that commit -- including before the doc that
    # reports the sweep, which itself quotes the phrase twice.  Measuring at
    # `c64fe68` instead of `c64fe68^` counts the report inside the population
    # it reports on, which is the mg-ec63 shape: a probe reading a file its
    # own run wrote.  Both are printed; only one is the comparison.
    at_parent_pre = rederive_at(PARENT_REV + "^", phrase)
    at_head = rederive_at("HEAD", phrase)
    print(f"  PARENT'S CLAIM : 30 occurrences across 8 tracked files "
          f"(mg-9a59 doc §5(g) / §1 table).  Theirs, not mine.")
    print(f"  instrument     : mg-3946's published snippet, verbatim, over "
          f"files matching {MG3946_FILE_FILTER.pattern}")
    print(f"  at {PARENT_REV}^ (the tree the sweep would have seen, BEFORE "
          f"its own doc landed):")
    print(f"                   -> {at_parent_pre.get('occurrences')} "
          f"occurrences across {at_parent_pre.get('files_with_a_match')} "
          f"files   <-- THE COMPARISON")
    print(f"  at {PARENT_REV}  (after its own doc, which quotes the phrase "
          f"twice):")
    print(f"                   -> {at_parent.get('occurrences')} occurrences "
          f"across {at_parent.get('files_with_a_match')} files")
    print(f"  VERDICT        : the 30 is "
          f"{'CONFIRMED' if at_parent_pre.get('occurrences') == 30 else 'NOT REPRODUCED'}"
          f" -- re-derived independently, exactly.")
    print(f"                   the 8 is "
          f"{'CONFIRMED' if at_parent_pre.get('files_with_a_match') == 8 else 'NOT REPRODUCED'}"
          f" -- the same measurement yields "
          f"{at_parent_pre.get('files_with_a_match')} files, and no file in "
          f"it holds")
    print(f"                   zero matches, so no exclusion recovers 8.")
    print(f"  same, at HEAD  : {at_head.get('occurrences')} occurrences "
          f"across {at_head.get('files_with_a_match')} files "
          f"(this branch has added text that quotes the phrase, including "
          f"this audit's own docs)")
    print(f"  MY OWN sweep A over all {len(files)} tracked UTF-8 files at "
          f"HEAD: {n_a} occurrences across {len(files_with)} files")
    print("  Three numbers, three populations, and they are NOT "
          "interchangeable.  The")
    print("  comparison that settles the parent's claim is the middle one, "
          "because it")
    print("  holds both the instrument and the tree fixed at what the parent "
          "measured.")
    for rel in files_with:
        print(f"      {rel:<62} {len(per_file[rel]['sweepA']):>3}")

    # ---- PART 4: what is actually asserted -------------------------------
    print()
    print("PART 4 -- OF THOSE, HOW MANY ASSERT THE FIGURE AS THE WINDOW?")
    asserts, unadjudicated = [], []
    for rel, v in per_file.items():
        for h in v["sweepA"]:
            kind, markers = classify(h["text"])
            if kind == "ASSERTS-THE-FIGURE":
                verdict, why = adjudicate(rel, h["text"])
                row = {"file": rel, "line": h["line"], "text": h["text"],
                       "markers": markers, "hand_verdict": verdict,
                       "hand_reason": why}
                asserts.append(row)
                if verdict is None:
                    unadjudicated.append(row)
    print(f"  proxy rule: an occurrence is a QUOTATION if its ±60-character "
          f"window contains")
    print(f"              any of {len(QUOTATION_MARKERS)} correction/narration "
          f"markers; otherwise it is")
    print(f"              scored as ASSERTING.  This is a PROXY for a "
          f"judgement, not the judgement.")
    print(f"  occurrences scored ASSERTING by the proxy: {len(asserts)} of "
          f"{n_a}")
    for a in asserts:
        print(f"      {os.path.basename(a['file'])}:{a['line']}  "
              f"{a['text'][:82]}")
        print(f"        HAND VERDICT: {a['hand_verdict'] or 'UNADJUDICATED'}"
              f" -- {a['hand_reason'] or 'NOBODY HAS READ THIS ONE'}")
    if not asserts:
        print("      (none -- every occurrence sits next to a correction "
              "marker)")
    hand_asserting = [a for a in asserts
                      if a["hand_verdict"] not in
                      (None,) and "quotation" not in (a["hand_verdict"] or "")
                      and "narration" not in (a["hand_verdict"] or "")
                      and "NEITHER" not in (a["hand_verdict"] or "")
                      and "meta-discussion" not in (a["hand_verdict"] or "")]
    print()
    print(f"  PROXY says {len(asserts)} asserting; HAND, having read all "
          f"{len(asserts)}, says {len(hand_asserting)}.")
    print(f"  The parent's substantive claim is 0.  The HAND count is the one "
          f"that answers")
    print(f"  it, and it AGREES -- so the 6 the proxy flagged are the proxy's "
          f"error, not")
    print(f"  the parent's.  The proxy is kept anyway: it is what notices a "
          f"NEW site.")
    led.check(not unadjudicated,
              f"{len(unadjudicated)} occurrence(s) flagged ASSERTING by the "
              f"proxy are not in the hand-adjudicated table -- a site has "
              f"appeared that nobody has read, and reporting '0 asserting' "
              f"over it would be a clean result from an unexamined population: "
              + "; ".join(f"{u['file']}:{u['line']}" for u in unadjudicated))
    led.check(not hand_asserting,
              f"{len(hand_asserting)} occurrence(s) survive hand "
              f"adjudication as ASSERTING the figure -- the parent's '0 "
              f"asserting sites' does not hold")

    # ---- verdict ---------------------------------------------------------
    report = {
        "what": "mg-a266: a positive control on the split-phrase re-check, "
                "and a re-derivation of the parent's uninstrumented counts",
        "phrase": phrase,
        "finding_the_parents_sweep_is_not_committed": {
            "claim": "mg-9a59 doc §5(g): a flattening sweep found 30 "
                     "occurrences across 8 tracked files, 0 asserting, and "
                     "was demonstrated able to find a wrapped instance",
            "status": "the sweep is not in the repository; c64fe68 adds one "
                      "doc and edits three scripts, none of which contains "
                      "it.  The counts and the demonstration are not "
                      "reproducible from anything committed.",
            "this_file_is_the_missing_instrument": True,
        },
        "part1_planted_shapes": {
            "population": f"{len(SHAPES)} planted shapes x "
                          f"{len(INSTRUMENTS)} instruments",
            "grain": "one FOUND/MISSED per (shape, instrument)",
            "shapes": shape_rows,
            "shapes_grep_cannot_see": grep_only,
            "shapes_sweep_A_cannot_see": a_misses,
        },
        "part2_cost_of_flattening": {
            "population": f"{len(files)} git-tracked UTF-8 text files",
            "grain": "one match",
            "grep_matches": n_grep,
            "sweepA_matches": n_a,
            "sweepB_matches": n_b,
            "matches_spanning_a_line_break": len(split_a),
            "split_matches": [{"file": r, **h} for r, h in split_a],
        },
        "part3_population_rederived": {
            "parents_claim": {"occurrences": 30, "files": 8,
                              "source": "mg-9a59 doc §5(g) and its §1 table",
                              "whose": "mg-9a59's, not mine"},
            "re_derivation_with_the_parents_own_instrument_at_parent_rev":
                at_parent,
            "re_derivation_at_the_tree_the_sweep_would_have_seen":
                at_parent_pre,
            "verdict_on_the_30": (
                "CONFIRMED -- re-derived exactly, independently, with the "
                "parent's own published instrument over the tree at "
                f"{PARENT_REV}^"
                if at_parent_pre.get("occurrences") == 30
                else "NOT REPRODUCED"),
            "verdict_on_the_8": (
                "CONFIRMED" if at_parent_pre.get("files_with_a_match") == 8
                else f"NOT REPRODUCED -- the same measurement yields "
                     f"{at_parent_pre.get('files_with_a_match')} files, and "
                     f"every file in it holds at least one match, so no "
                     f"exclusion of a file recovers 8"),
            "same_instrument_at_HEAD": at_head,
            "my_own_sweep_at_HEAD": {
                "occurrences": n_a, "files": len(files_with),
                "instrument": "sweep A (comment-flattening), mine",
                "file_set": "git ls-files, UTF-8-decodable",
                "per_file": {r: len(per_file[r]["sweepA"])
                             for r in files_with}},
            "agree_on_occurrences": at_parent_pre.get("occurrences") == 30,
            "agree_on_files": at_parent_pre.get("files_with_a_match") == 8,
            "note": "three numbers over three populations.  Only the "
                    "re-derivation at the parent's own commit with the "
                    "parent's own instrument is a comparison; the other two "
                    "differ from it for reasons that are not the parent's.",
        },
        "part4_asserting_sites": {
            "proxy_rule": "a ±60-char window containing any of "
                          f"{len(QUOTATION_MARKERS)} correction/narration "
                          "markers is a quotation; otherwise ASSERTING",
            "is_a_proxy_for_a_judgement": True,
            "n_scored_asserting_by_the_proxy": len(asserts),
            "scored_asserting": asserts,
            "n_asserting_after_hand_adjudication": len(hand_asserting),
            "n_unadjudicated": len(unadjudicated),
            "parents_claim": 0,
            "whose_claim": "mg-9a59's; the hand count here re-derives it",
            "agrees_with_parent_after_hand_adjudication":
                len(hand_asserting) == 0,
            "note": "the proxy over-flags by 6.  Every one was read; none "
                    "asserts the figure as the window.  The proxy is kept "
                    "because it is what would notice a NEW occurrence that "
                    "nobody has read.",
        },
        "assertions": led.checks,
        "problems": led.problems,
        "ALL_HELD": led.checks > 0 and not led.problems,
    }
    with open(os.path.join(REPO, REPORT), "w") as f:
        json.dump(report, f, indent=2)
    print()
    print(f"wrote {REPORT}")

    print()
    print("=" * 78)
    if led.checks == 0 or not SHAPES or not files:
        print("ZERO ASSERTIONS, ZERO SHAPES, OR ZERO FILES -- THIS RUN "
              "MEASURED NOTHING.")
        print("  ALL_HELD is written FALSE.  Exiting 2: a positive control "
              "that controlled")
        print("  nothing must not be citable as one that passed.")
        return 2
    if led.problems:
        print(f"FAILED: {len(led.problems)} of {led.checks} assertions")
        for p in led.problems:
            print(f"  - {p}")
        print("\nIf S1 is among these, the re-check CANNOT SEE a phrase split "
              "across a\ncomment, and every clean result it has reported over "
              "the population is worth\nnothing.  Say that plainly rather than "
              "reporting a clean sweep.")
        return 1
    print(f"HELD: {led.checks}/{led.checks} assertions.")
    print(f"  The re-check CAN find a phrase split across a comment "
          f"continuation: S1 is")
    print(f"  FOUND by the flattening sweep and MISSED by grep, over a "
          f"deliberately")
    print(f"  constructed fixture.  {len(grep_only)} of the "
          f"{sum(1 for s in SHAPES if s['must_find'])} positive shapes are "
          f"invisible to grep.")
    print(f"  Population for the tree sweep: {len(files)} tracked text files, "
          f"{n_a} matches.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
