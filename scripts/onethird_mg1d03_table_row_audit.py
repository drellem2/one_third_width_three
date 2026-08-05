#!/usr/bin/env python3
"""mg-1d03 — mg-0242 G3: every ROW of the two mis-stated tables, COUNTED.

WHY THIS EXISTS.  mg-0242 finding G3 is two named-vs-counted gaps that the
mg-069f repair INTRODUCED:

  * the closeout's §6.1 table -- the table whose entire purpose is to report
    population NAMED vs population SWEPT -- said the live-claim control sweeps
    "537/537 lines".  It sweeps 539.
  * the direction check's docstring labels the 404 -> 4 469 POSET row
    "6.9x larger".  4 469/404 = 11.06x.  6.9x is the PAIR ratio (6.87x) and the
    TRIPLE ratio (6.90x) -- a real number from an adjacent GRAIN, which is why
    it read as plausible.

mg-0242's instruction was not "fix those two figures".  It was: *a table that got
its own row wrong has not earned trust on its neighbours -- check the other rows
by CALLING the helper rather than reading the figure.*  That is this script.  It
parses the rows OUT OF THE FILES, obtains every figure by calling the generator
or running the scanner, and compares.  No figure in this script is a literal
copied from the table it audits.

THREE PARTS.

  (A) CLOSEOUT §6.1, ROW BY ROW.  Population: the three rows of §6.1 of
      docs/OneThird-mg8a71-VerdictRepairs-Closeout.md.  Grain: one integer per
      (row x column x quantity) -- posets, (poset, reference-order) pairs and
      element triples for rows 1-2; lines for row 3.  Every integer >= 100 in
      the row is extracted and matched against a COUNTED value; an integer in
      the row that no counted value explains is a FAILURE, not a curiosity.

  (B) THE DOCSTRING TABLE, ROW BY ROW.  Population: the 4 rows (n = 3, 4, 5,
      total) x 2 columns of the table in `posets_with_identity_extension`'s
      docstring in scripts/onethird_mgfccb_direction_check.py.  Grain: one
      integer per (n x family).  Plus the ratio label on the totals row, which
      is recomputed rather than read.

  (C) THE RATIO, AT EVERY SITE AND AT ITS GRAIN.  G3's second half is not a
      typo, it is a GRAIN error: 6.9x is true of pairs and triples and false of
      posets, so the figure is only meaningful once the grain is named.  This
      sweeps docs/, scripts/ and .github/ for every family-ratio literal and
      requires each ASSERTION to name its grain and to be right at that grain.
      Two structural classes are counted and listed rather than failed on:

        QUOTATION      the literal sits in backticks or inside a quoted span --
                       quoting a wrong figure is not asserting it;
        NAMED-vs-COUNTED  the line carries BOTH the wrong figure and the counted
                       one -- that is a report OF the defect, and the arc's whole
                       method is writing those down.

      Both classes are enumerated line by line, because "exempt and silent" is
      the failure mode this corpus keeps finding in itself.

Exits non-zero if any row disagrees with the count, or if any ratio assertion
omits its grain or is wrong at the grain it names.

Run:  python3 scripts/onethird_mg1d03_table_row_audit.py
"""

import importlib.util
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
NS = (3, 4, 5)

CLOSEOUT = "docs/OneThird-mg8a71-VerdictRepairs-Closeout.md"
DIRECTION_CHECK = "scripts/onethird_mgfccb_direction_check.py"
LIVE_CLAIM = "scripts/onethird_mg8a71_live_claim_control.py"

FAILURES = []

# Any integer of 3+ digits, allowing the corpus's space-grouped thousands
# ("6 385"), and refusing anything glued to a letter or a decimal point so that
# `A001035` and the `11.06` of a ratio are not read as populations.
INT_RE = re.compile(r"(?<![\w.])(\d{1,3}(?: \d{3})+|\d{3,})(?![\w.])")

# A family-ratio literal: `6.9x`, `11.06×`, `6.87x`, ...
RATIO_RE = re.compile(r"(?<![\w.])(\d{1,2}\.\d{1,2})\s*[x×]")


def load(name, relpath):
    spec = importlib.util.spec_from_file_location(name, ROOT / relpath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def ints_in(text):
    """Every population-sized integer in `text`, in order, ungrouped."""
    return [int(m.group(1).replace(" ", "")) for m in INT_RE.finditer(text)]


# ------------------------------------------------------------------ counting --


def count_family(gen, n_range=NS):
    """posets / (poset, reference-order) pairs / (poset, order, element) triples."""
    posets = pairs = triples = 0
    per_n = {}
    for n in n_range:
        c = 0
        for p in gen(n):
            c += 1
            les = len(list(p.linear_extensions()))
            pairs += les
            triples += les * n
        per_n[n] = c
        posets += c
    return per_n, posets, pairs, triples


def counted_populations(dc):
    ident = count_family(dc.posets_with_identity_extension)
    lab = count_family(dc.all_labelled_posets)
    return ident, lab


# ------------------------------------------------------------------ part A ---


def section_61_rows(text):
    """The data rows of §6.1, keyed by the script each row is about."""
    rows, in_61 = {}, False
    for lineno, line in enumerate(text.split("\n"), 1):
        if line.startswith("### 6.1"):
            in_61 = True
            continue
        if in_61 and line.startswith("#"):
            break
        if in_61 and line.startswith("|"):
            m = re.search(r"`(onethird_\w+\.py)`", line)
            if m:
                rows[m.group(1)] = (lineno, line)
    return rows


def part_a(ident, lab, swept_lines, buckets):
    print("=" * 96)
    print("(A) CLOSEOUT §6.1, ROW BY ROW — every figure COUNTED, none read")
    print("=" * 96)
    text = (ROOT / CLOSEOUT).read_text(encoding="utf-8")
    rows = section_61_rows(text)
    _, i_posets, i_pairs, i_triples = ident
    _, l_posets, l_pairs, l_triples = lab

    expected = {
        "onethird_mgfccb_direction_check.py": (
            "identity-extension family",
            "posets / (poset, order) pairs / element triples, each NAMED once and "
            "SWEPT once",
            {i_posets: 2, i_pairs: 2, i_triples: 2}),
        "onethird_mg8a71_audit_instrument.py": (
            "all-labelled family (A001035)",
            "posets / (poset, order) pairs / element triples, each NAMED once and "
            "SWEPT once",
            {l_posets: 2, l_pairs: 2, l_triples: 2}),
        "onethird_mg8a71_live_claim_control.py": (
            "the live-claim control's own file",
            "lines, NAMED once and SWEPT once (the `n/n lines` cell)",
            {swept_lines: 2}),
    }

    print(f"  population: {len(rows)} data rows of §6.1 of {CLOSEOUT}")
    print(f"  grain     : one integer per (row x column x quantity)")
    print()
    if set(rows) != set(expected):
        FAILURES.append(
            f"§6.1 rows changed: parsed {sorted(rows)}, expected {sorted(expected)}")
        print(f"  [GAP ] §6.1 no longer holds exactly the three rows this audit knows")
        return
    for script, (lineno, line) in sorted(rows.items()):
        pop, grain, want = expected[script]
        got = ints_in(line)
        tally = {v: got.count(v) for v in set(got)}
        ok = tally == want
        print(f"  row: {script}   (line {lineno})")
        print(f"      POPULATION : {pop}")
        print(f"      GRAIN      : {grain}")
        print(f"      COUNTED    : {', '.join(f'{k} x{v}' for k, v in sorted(want.items()))}")
        print(f"      IN THE ROW : {', '.join(f'{k} x{v}' for k, v in sorted(tally.items())) or '—'}")
        print(f"      [{'OK  ' if ok else 'GAP '}]"
              f"{'' if ok else '  <-- the row disagrees with the count'}")
        if not ok:
            missing = {k: v for k, v in want.items() if tally.get(k) != v}
            extra = {k: v for k, v in tally.items() if want.get(k) != v}
            FAILURES.append(
                f"§6.1 row {script}: counted {missing} but the row has {extra}")
        print()

    # the third row also NAMES the bucket set; the scanner's keys are the count
    named_buckets = set(re.findall(
        r"\{([^}]*)\}", rows["onethird_mg8a71_live_claim_control.py"][1]))
    if named_buckets:
        named = {b.strip().replace("-", "_")
                 for b in list(named_buckets)[0].split(",")}
        counted = set(buckets)
        ok = named == counted
        print(f"  row 3 also NAMES a bucket set — checked against the scanner's keys")
        print(f"      POPULATION : the coverage buckets of the live-claim scanner")
        print(f"      GRAIN      : one bucket name")
        print(f"      NAMED      : {sorted(named)}")
        print(f"      COUNTED    : {sorted(counted)}")
        print(f"      [{'OK  ' if ok else 'GAP '}]")
        if not ok:
            FAILURES.append(f"§6.1 row 3 bucket names {sorted(named)} != scanner "
                            f"keys {sorted(counted)}")
    print()


# ------------------------------------------------------------------ part B ---


def docstring_table_rows(doc):
    """(label, col1, col2, trailing-text) for each data row of the docstring table."""
    out = []
    for line in doc.split("\n"):
        m = re.match(r"\s*(\d+|tot)\s*\|\s*(\d+)\s*\|\s*(\d+)(.*)$", line)
        if m:
            out.append((m.group(1), int(m.group(2)), int(m.group(3)),
                        m.group(4).strip()))
    return out


def part_b(dc, ident, lab):
    print("=" * 96)
    print("(B) THE DOCSTRING TABLE, ROW BY ROW — the helper called for every cell")
    print("=" * 96)
    doc = dc.posets_with_identity_extension.__doc__ or ""
    rows = docstring_table_rows(doc)
    i_per_n, i_posets, _, _ = ident
    l_per_n, l_posets, _, _ = lab
    want = {str(n): (i_per_n[n], l_per_n[n]) for n in NS}
    want["tot"] = (i_posets, l_posets)

    print(f"  population: {len(rows)} data rows x 2 columns of the table in "
          f"`posets_with_identity_extension`'s docstring")
    print(f"  grain     : one poset count per (n x family)")
    print()
    if {r[0] for r in rows} != set(want):
        FAILURES.append(f"docstring table rows changed: {[r[0] for r in rows]}")
        print(f"  [GAP ] the table no longer holds rows {sorted(want)}")
        return
    for label, c1, c2, tail in rows:
        w1, w2 = want[label]
        ok = (c1, c2) == (w1, w2)
        pop = ("n = " + label if label != "tot" else "n = 3,4,5 together")
        print(f"  row {label:<4} POPULATION : {pop}")
        print(f"           GRAIN      : posets in the identity-extension family | "
              f"posets in the labelled family")
        print(f"           IN THE ROW : {c1} | {c2}")
        print(f"           COUNTED    : {w1} | {w2}")
        print(f"           [{'OK  ' if ok else 'GAP '}]")
        if not ok:
            FAILURES.append(
                f"docstring row {label}: row says {c1}|{c2}, counted {w1}|{w2}")
        if label == "tot":
            m = RATIO_RE.search(tail)
            ratio = l_posets / i_posets
            print()
            print(f"  the totals row also carries a RATIO label — recomputed, not read")
            print(f"      POPULATION : the two families at n = 3,4,5")
            print(f"      GRAIN      : POSETS ({l_posets} / {i_posets}) — the grain of "
                  f"the row it is attached to")
            print(f"      COMPUTED   : {ratio:.4f}x")
            print(f"      LABELLED   : {tail or '(no label)'}")
            if not m:
                FAILURES.append("the docstring totals row carries no ratio label")
                print(f"      [GAP ]  no ratio label on the row")
            else:
                named = float(m.group(1))
                grain_named = bool(re.search(r"poset", tail, re.I))
                good = abs(named - ratio) < 0.05 and grain_named
                print(f"      [{'OK  ' if good else 'GAP '}]"
                      f"{'' if good else '  <-- wrong figure, or grain not named'}")
                if not good:
                    FAILURES.append(
                        f"docstring totals-row ratio: labelled {named}x"
                        f"{' (grain not named)' if not grain_named else ''}, "
                        f"computed {ratio:.4f}x at POSET grain")
    print()


# ------------------------------------------------------------------ part C ---

SWEEP_DIRS = ("docs", "scripts", ".github")
SWEEP_SUFFIXES = (".md", ".py", ".yml")

# Whole words only.  A first draft matched the bare substrings and bound the
# ratio in "...larger than the repair's" to the PAIR grain, where 6.9x is right,
# so the site passed silently.  The word "repair" containing the word "pair" is
# not a curiosity in a corpus about repairs -- it is most of the sentences.
GRAIN_WORDS = {r"\bposets?\b": "posets",
               r"\bpairs?\b": "pairs",
               r"\btriples?\b": "triples"}


def binding_grain(window, match):
    """The grain a ratio literal is about: the grain word NEAREST to it.

    A deterministic rule, and the reason G3's second half existed at all: `6.9x`
    is true of pairs and of triples and false of posets, so a ratio with no grain
    beside it is not a claim a reader can check.  Nearest-word binding is what
    lets a sentence contrast two grains ("the ratio of PAIRS (6.87x) ... not of
    posets") without either figure being read against the wrong one.

    `window` is the literal's own line plus the line after it, because prose in
    this corpus is hard-wrapped: "under-swept 11.06x in / posets" is one
    sentence and the grain IS named in it.  A line-scoped rule failed four such
    sites, all correctly written -- a control that fires on line breaks trains
    its readers to reflow rather than to name the grain.
    """
    best, best_d = None, None
    for word, grain in GRAIN_WORDS.items():
        for wm in re.finditer(word, window, re.I):
            d = (wm.start() - match.end() if wm.start() >= match.end()
                 else match.start() - wm.end())
            if best_d is None or d < best_d:
                best, best_d = grain, d
    return best


def quoted_spans(line):
    """Index ranges covered by backticks or by a quoted span."""
    spans = []
    for m in re.finditer(r"`[^`]*`|\"[^\"]*\"|“[^”]*”|'[^']{4,}'", line):
        spans.append((m.start(), m.end()))
    return spans


def part_c(ratios):
    print("=" * 96)
    print("(C) THE RATIO AT EVERY SITE — an assertion must name its GRAIN")
    print("=" * 96)
    print(f"  the three true ratios, computed:  "
          + ",  ".join(f"{g} {v:.4f}x" for g, v in ratios.items()))
    print(f"  population: every *{', *'.join(SWEEP_SUFFIXES)} under "
          f"{', '.join(d + '/' for d in SWEEP_DIRS)}")
    print(f"  grain     : one site = one ratio literal on one line")
    print()
    known = sorted(ratios.values())
    assertions = quotations = reports = 0
    bad = []
    quoted_sites, report_sites = [], []
    files = sorted(p for d in SWEEP_DIRS for p in (ROOT / d).rglob("*")
                   if p.suffix in SWEEP_SUFFIXES and p.is_file())
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        fenced = False
        all_lines = path.read_text(encoding="utf-8").split("\n")
        for lineno, line in enumerate(all_lines, 1):
            if line.lstrip().startswith("```"):
                fenced = not fenced
                continue
            if fenced:
                continue
            hits = [m for m in RATIO_RE.finditer(line)
                    if any(abs(float(m.group(1)) - k) < 0.05 for k in known)]
            if not hits:
                continue
            values = {round(float(m.group(1)), 2) for m in hits}
            # a line carrying BOTH the wrong figure and the counted one is a
            # report OF the defect, not an instance of it
            is_report = (any(abs(v - ratios["posets"]) < 0.05 for v in values)
                         and any(abs(v - ratios["triples"]) < 0.06 for v in values))
            spans = quoted_spans(line)
            for m in hits:
                inside = any(s <= m.start() < e for s, e in spans)
                if is_report:
                    reports += 1
                    report_sites.append((rel, lineno, m.group(0), line.strip()))
                    continue
                if inside:
                    quotations += 1
                    quoted_sites.append((rel, lineno, m.group(0), line.strip()))
                    continue
                assertions += 1
                named = float(m.group(1))
                window = line + " " + (all_lines[lineno] if lineno < len(all_lines)
                                       else "")
                grain = binding_grain(window, m)
                if grain is None:
                    bad.append((rel, lineno, m.group(0), "no GRAIN named on the line",
                                line.strip()))
                    continue
                if abs(named - ratios[grain]) >= 0.05:
                    bad.append((rel, lineno, m.group(0),
                                f"wrong at its binding grain: {grain} = "
                                f"{ratios[grain]:.2f}x", line.strip()))
    print(f"  ASSERTIONS       : {assertions}   (must name the grain and be right at it)")
    print(f"  QUOTATIONS       : {quotations}   (in backticks or a quoted span — listed, never failed on)")
    for rel, lineno, lit, snip in quoted_sites:
        print(f"      {rel}:{lineno}  {lit}")
        print(f"          > {snip[:100]}")
    print(f"  NAMED-vs-COUNTED : {reports}   (the line carries BOTH figures — a report of G3)")
    for rel, lineno, lit, snip in report_sites:
        print(f"      {rel}:{lineno}  {lit}")
    print()
    if bad:
        print(f"  {len(bad)} ratio assertion(s) without a grain, or wrong at the grain named:")
        for rel, lineno, lit, why, snip in bad:
            print(f"      [GAP ] {rel}:{lineno}  {lit} — {why}")
            print(f"             > {snip[:110]}")
            FAILURES.append(f"ratio site {rel}:{lineno} ({lit}): {why}")
    else:
        print("  every ratio assertion in the corpus names its grain and is right at it")
    print()


# --------------------------------------------------------------------- main --


def demonstrate(rev):
    """Run this control against a tree where G3 is still present.

    A control that has only ever been run where it passes is not a control.  The
    tree is materialised with `git archive` and THIS script is copied into it, so
    what runs is today's rule against yesterday's text -- exactly the comparison
    a reader wants, and not "the old tree's own checker agreed with the old
    tree".
    """
    print("=" * 96)
    print(f"DEMONSTRATION — the same rules against {rev}, where G3 is present")
    print("=" * 96)
    with tempfile.TemporaryDirectory() as td:
        tmp = pathlib.Path(td)
        tar = subprocess.run(["git", "archive", rev], capture_output=True,
                             cwd=ROOT, check=True).stdout
        subprocess.run(["tar", "-x", "-C", str(tmp)], input=tar, check=True)
        me = pathlib.Path(__file__)
        shutil.copy(me, tmp / "scripts" / me.name)
        r = subprocess.run([sys.executable, str(tmp / "scripts" / me.name)],
                           capture_output=True, text=True)
        gaps = [l for l in r.stdout.split("\n") if l.strip().startswith("- ")]
        print(f"  exit code there : {r.returncode}")
        print(f"  gaps found there: {len(gaps)}")
        for g in gaps:
            print(f"    {g.strip()}")
        print()
        if r.returncode == 0:
            print(f"RESULT: this control does NOT bite at {rev}; that revision does "
                  f"not demonstrate the defect.")
            return 1
        print(f"RESULT: the control BITES at {rev} — {len(gaps)} gap(s), so its "
              f"green at HEAD is a measurement.")
        return 0


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--demonstrate":
        return demonstrate(sys.argv[2])

    dc = load("dc", DIRECTION_CHECK)
    lc = load("lc", LIVE_CLAIM)

    print("=" * 96)
    print("mg-1d03 — mg-0242 G3: the two mis-stated tables, checked ROW BY ROW")
    print("=" * 96)
    print()

    ident, lab = counted_populations(dc)
    swept_lines, _, _, buckets, _ = lc.scan(lc.DOC)

    part_a(ident, lab, swept_lines, buckets)
    part_b(dc, ident, lab)
    part_c({
        "posets": lab[1] / ident[1],
        "pairs": lab[2] / ident[2],
        "triples": lab[3] / ident[3],
    })

    print("=" * 96)
    if FAILURES:
        print(f"RESULT: FAIL — {len(FAILURES)} row(s) or ratio site(s) disagree with "
              f"the count:")
        for f in FAILURES:
            print(f"  - {f}")
        return 1
    print("RESULT: PASS — every row of both tables equals the value obtained by")
    print("        CALLING the helper, and every ratio assertion in the corpus names")
    print("        the GRAIN it is true at.  mg-0242 G3 is closed at both sites and")
    print("        at the neighbours the finding said to check.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
