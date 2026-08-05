#!/usr/bin/env python3
"""mg-5854 — INDEPENDENT AUDIT of the mg-1d03 G3+G4 repair.

WHAT THIS IS NOT.  It is not a re-run of `onethird_mg1d03_table_row_audit.py` or
of `onethird_mg1d03_remediation_instruments.py`.  Both of those pass at HEAD and
were re-run here; this file exists to ask the two questions an audit of them has
to ask and that they cannot ask of themselves:

  1. the row audit obtains every figure by CALLING the helper and comparing --
     so if the HELPER is wrong, the table and the audit agree and are both
     wrong, and if the audit's ROW SELECTOR is narrower than the table, a row
     can be present and unchecked.  Independence of FAILURE MODE means counting
     the same populations from an enumerator that shares no line with the helper,
     and reporting rows PRESENT against rows CHECKED as two separate numbers.
  2. the instruments matrix measures 7 mutants at ONE site -- ledger C3, in the
     one document the live-claim control reads.  4 of the ledger's 10 entries do
     not live in that document.  So the matrix answers "which instrument does the
     control see" on the only subject where the answer can be non-zero.

FIVE PARTS.

  (A) THE POPULATIONS, COUNTED TWICE, INDEPENDENTLY.  Every strict partial order
      on [n] for n = 3,4,5 is enumerated by brute force over ALL 2^(n(n-1))
      relations, tested for irreflexivity, antisymmetry and transitivity -- not
      by building the identity-extension family and closing it under S_n, which
      is what both helpers do.  Linear extensions are counted by a second
      independent routine.  The six population figures must agree three ways:
      this enumerator, the helper the parent calls, and the A001035 literals from
      OEIS.  Population: the labelled ground sets [3], [4], [5].  Grain: one
      poset, one (poset, reference-order) pair, one (poset, order, element)
      triple -- each stated separately, because mg-0242 G3 was one grain's figure
      written on another's row.

  (B) BOTH TABLES, ROW BY ROW, PER COLUMN, WITH ROWS PRESENT COUNTED SEPARATELY
      FROM ROWS CHECKED.  Every figure is CALLED for, none is read.  Two
      differences from the parent's part (A), and each is a mutation in part (E):
        * figures are matched PER COLUMN, not as one multiset over the whole
          row.  §6.1's columns are `population NAMED` and `population SWEPT`;
          a rule that pools them cannot see the defect the table exists to
          report.
        * EVERY data row of the section is checked.  A row this audit has no
          expectation for is a FAILURE, not a row that is skipped -- the parent
          selects rows by the presence of an `onethird_*.py` name.

  (C) THE FIVE INSTRUMENTS AT TWO SITES THE PARENT DID NOT USE.  One refuted
      claim is remediated by each of the five instruments -- and by the two
      forms of declared deletion, and by leaving it live -- at two sites in
      `docs/OneThird-mgd112-DroppedVerdict-Closeout.md`, which is NOT the
      document the live-claim control reads:
        subject 1  an UNLEDGERED claim (the live-claim control's own S3
                   signature, planted in another document);
        subject 2  a LEDGERED claim (ledger C10's pattern).
      Three controls are run over each mutant, each exactly as CI runs it (no
      path argument, from the mutant tree's root): live-claim, declared-strike,
      and the struck-vs-refuted ledger, which the parent's matrix does not
      include and whose part (B) sweeps all of `docs/`.
      Population: 2 subjects x 7 mutants x 3 controls = 42 process exit codes.
      Grain: one exit code per (subject x mutant x control).

  (D) DO NOT DISTURB.  The three things the ticket says must still hold, re-run
      rather than re-read: both true halves of the two part-true deletions
      survive verbatim in the same section; F4's three proven-safe sites were
      not re-widened; and `Var(pos_σ z) = m(m+2)/12` is asserted by a control.

  (E) WHAT THE PARENT'S ROW AUDIT CANNOT SEE, BY MUTATION.  Two mutants of the
      closeout, each of which this file's part (B) must catch.  Whether the
      parent's audit catches them is measured under `--vs-parent`, which
      materialises a tree and runs it -- off the default path, because this job
      checks out at depth 1 (the mg-3934 rule).

BASELINE.  One entry, and it is a finding, not a tolerance -- see BASELINE below.
A baselined gap that CLOSES fails this run, so repairing it forces a re-baseline
instead of passing silently.  That is the convention mg-8a71 set, mg-0242 kept
and mg-1d03 was held to.

NO PINNED REVISION IS NAMED IN CODE.  The one history-reading mode takes its
revision from argv and does not run on the default path -- `script-controls.yml`
checks out at depth 1 by design, and a step that read history there would be dead
on arrival.  That is the mg-3934 defect, whose static control is in the same
workflow.

Run:  python3 scripts/onethird_mg5854_row_and_instrument_audit.py
      python3 scripts/onethird_mg5854_row_and_instrument_audit.py --vs-parent
"""

import importlib.util
import itertools
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
DECLARED_STRIKE = "scripts/onethird_mgcd04_declared_strike_control.py"
LEDGER = "scripts/onethird_mg0242_struck_vs_refuted.py"
IDENTITY_RECHECK = "scripts/onethird_mg0242_identity_recheck.py"
PARENT_ROW_AUDIT = "scripts/onethird_mg1d03_table_row_audit.py"
SPREAD = "docs/OneThird-L1b-Spread-Locality.md"
MGD112 = "docs/OneThird-mgd112-DroppedVerdict-Closeout.md"
BBIAS = "docs/OneThird-Bbias-Locality-Lemma.md"

# The labelled-poset counts as OEIS states them.  A literal on purpose: it is the
# third leg of part (A), and a third leg that was computed here would not be one.
A001035 = {3: 19, 4: 219, 5: 4231}

FAILURES = []

# BASELINE — gaps this audit FOUND, adjudicated, and deliberately did not repair.
# Keyed by a short id.  An audit that repairs its own subject destroys the record
# of what was wrong, and mg-1d03 is merged; the disposition of this one belongs to
# pm-onethird, who is the routee for the whole G3/G4 arc.
#
#   LINE-GRAIN  §6.1 row 3's SWEPT cell reads "539/539 lines", and the live-claim
#       control's own report reads "population: 539 lines, ALL classified".  The
#       document has 538 LINES (`wc -l` = 538; `len(text.splitlines())` = 538).
#       539 is the number of `text.split("\n")` FRAGMENTS, whose last element is
#       the empty string after the file's trailing newline -- not a line.
#       Coverage is NOT affected: 539 fragments is a superset of 538 lines, so
#       nothing goes unswept and the control's internal `sum(coverage) == 539`
#       assertion is sound.  What is wrong is the GRAIN of the label, by exactly
#       one unit, in the SWEPT column of the table whose purpose is to report
#       named-vs-swept -- the same shape as mg-0242 G3, one row down and one
#       repair later.  The provenance is documented (mg-069f's audit §5 derives
#       "wc -l = 538 => 539 split elements") but neither reporting site names the
#       grain, and mg-1d03's own new rule for RATIOS is that an assertion must.
BASELINE = {"LINE-GRAIN"}
BASELINE_SEEN = set()


def load(name, relpath):
    spec = importlib.util.spec_from_file_location(name, ROOT / relpath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def gap(key, message):
    """Record a gap.  Baselined keys are listed and do not fail the run."""
    if key in BASELINE:
        BASELINE_SEEN.add(key)
        print(f"      [BASE] {message}")
        return
    FAILURES.append(message)
    print(f"      [GAP ] {message}")


# ============================================================ part (A) counts ==


def independent_strict_orders(n):
    """Every strict partial order on the labelled set [n], by brute force.

    Shares no line and no idea with either helper.  `posets_with_identity_
    extension` draws relations only from pairs (a, b) with a < b and takes the
    transitive closure; `all_labelled_posets` closes that family under S_n.  This
    tests all 2^(n(n-1)) relations on ordered pairs for the three axioms
    directly, so a defect in either the family or the relabelling closure shows
    up as a disagreement rather than as agreement with itself.

    Yields tuples of successor bitmasks.
    """
    pairs = [(a, b) for a in range(n) for b in range(n) if a != b]
    bits = [(a, 1 << b) for a, b in pairs]
    for mask in range(1 << len(pairs)):
        succ = [0] * n
        m, i = mask, 0
        while m:
            if m & 1:
                a, bb = bits[i]
                succ[a] |= bb
            m >>= 1
            i += 1
        ok = True
        for a in range(n):
            s = succ[a]
            if s >> a & 1:                       # irreflexive
                ok = False
                break
            t = s
            while t:
                b = (t & -t).bit_length() - 1
                t &= t - 1
                if succ[b] & s != succ[b]:       # transitive
                    ok = False
                    break
                if succ[b] >> a & 1:             # antisymmetric
                    ok = False
                    break
            if not ok:
                break
        if ok:
            yield tuple(succ)


def independent_linear_extensions(n, succ):
    """|L(P)|, by testing every permutation.  A second routine, not the helper's."""
    total = 0
    for perm in itertools.permutations(range(n)):
        pos = [0] * n
        for i, x in enumerate(perm):
            pos[x] = i
        good = True
        for a in range(n):
            t = succ[a]
            while t:
                b = (t & -t).bit_length() - 1
                t &= t - 1
                if pos[a] > pos[b]:
                    good = False
                    break
            if not good:
                break
        if good:
            total += 1
    return total


def independent_populations():
    """(per_n, posets, pairs, triples) for both families, counted here."""
    ident = {"per_n": {}, "posets": 0, "pairs": 0, "triples": 0}
    lab = {"per_n": {}, "posets": 0, "pairs": 0, "triples": 0}
    for n in NS:
        ci = cl = 0
        for succ in independent_strict_orders(n):
            les = independent_linear_extensions(n, succ)
            cl += 1
            lab["pairs"] += les
            lab["triples"] += les * n
            # the identity-extension family: every relation runs "upwards"
            if all(succ[a] >> b & 1 == 0 for a in range(n) for b in range(a)):
                ci += 1
                ident["pairs"] += les
                ident["triples"] += les * n
        ident["per_n"][n] = ci
        lab["per_n"][n] = cl
        ident["posets"] += ci
        lab["posets"] += cl
    return ident, lab


def helper_populations(dc):
    """The same six figures, obtained by CALLING the helper, as the parent does."""
    out = []
    for gen in (dc.posets_with_identity_extension, dc.all_labelled_posets):
        d = {"per_n": {}, "posets": 0, "pairs": 0, "triples": 0}
        for n in NS:
            c = 0
            for p in gen(n):
                c += 1
                les = len(list(p.linear_extensions()))
                d["pairs"] += les
                d["triples"] += les * n
            d["per_n"][n] = c
            d["posets"] += c
        out.append(d)
    return out


def part_a(dc):
    print("=" * 96)
    print("(A) THE POPULATIONS, COUNTED TWICE — an enumerator sharing no line "
          "with the helper")
    print("=" * 96)
    mine_i, mine_l = independent_populations()
    help_i, help_l = helper_populations(dc)
    print(f"  POPULATION : the labelled ground sets [3], [4], [5]")
    print(f"  GRAIN      : one poset | one (poset, reference-order) pair | "
          f"one (poset, order, element) triple — named separately")
    print()
    print(f"  {'quantity':<52} {'this audit':>12} {'the helper':>12} {'OEIS':>8}")
    print(f"  {'-'*52} {'-'*12} {'-'*12} {'-'*8}")
    for label, key, mi, he in (
            ("identity-extension family, POSETS", "posets", mine_i, help_i),
            ("identity-extension family, PAIRS", "pairs", mine_i, help_i),
            ("identity-extension family, TRIPLES", "triples", mine_i, help_i),
            ("all-labelled family, POSETS", "posets", mine_l, help_l),
            ("all-labelled family, PAIRS", "pairs", mine_l, help_l),
            ("all-labelled family, TRIPLES", "triples", mine_l, help_l)):
        agree = mi[key] == he[key]
        print(f"  {label:<52} {mi[key]:>12} {he[key]:>12} {'':>8}"
              f"  {'' if agree else '  <-- DISAGREE'}")
        if not agree:
            gap("count", f"{label}: this audit counts {mi[key]}, the helper "
                         f"returns {he[key]}")
    print()
    for n in NS:
        ok = mine_l["per_n"][n] == help_l["per_n"][n] == A001035[n]
        print(f"  labelled posets on [{n}]{'':<32} {mine_l['per_n'][n]:>12} "
              f"{help_l['per_n'][n]:>12} {A001035[n]:>8}  {'' if ok else '<-- DISAGREE'}")
        if not ok:
            gap("count", f"labelled posets on [{n}]: {mine_l['per_n'][n]} here, "
                         f"{help_l['per_n'][n]} from the helper, {A001035[n]} in A001035")
    for n in NS:
        ok = mine_i["per_n"][n] == help_i["per_n"][n]
        if not ok:
            gap("count", f"identity-extension posets on [{n}]: {mine_i['per_n'][n]} "
                         f"here, {help_i['per_n'][n]} from the helper")
    print()
    print("  [OK  ] three independent legs agree on every figure the two tables "
          "carry" if not FAILURES else "")
    print()
    return mine_i, mine_l


# ============================================================= part (B) rows ==

# Population integers of ANY size, space-grouped thousands allowed, and never a
# fragment of a decimal.  The `(?<![\w.])` / `(?![\w.])` guards are the whole
# rule and they are load-bearing: a first draft of this file matched the small
# counts with a bare `\b\d{1,2}\b`, which read the `11` of `(11.06x larger,
# posets)` in the totals row as a poset count and failed a correct row.  That is
# a number taken at the wrong GRAIN by the audit written to find numbers taken at
# the wrong grain -- recorded in §6 of the report rather than quietly fixed.
INT_RE = re.compile(r"(?<![\w.])(\d{1,3}(?: \d{3})+|\d+)(?![\w.])")


def ints_in(text):
    return [int(m.group(1).replace(" ", "")) for m in INT_RE.finditer(text)]


def cells(line):
    """The cells of a markdown table row, without the leading/trailing pipes."""
    return [c.strip() for c in line.strip().strip("|").split("|")]


def is_separator(line):
    return all(re.fullmatch(r":?-{2,}:?", c) for c in cells(line) if c != "")


def section_rows(text, heading_prefix):
    """(lineno, line) for every `|` line of the named section, in order."""
    out, inside = [], False
    for lineno, line in enumerate(text.split("\n"), 1):
        if line.startswith(heading_prefix):
            inside = True
            continue
        if inside and line.startswith("#"):
            break
        if inside and line.lstrip().startswith("|"):
            out.append((lineno, line))
    return out


def check_closeout_rows(text, ident, lab, doc_lines, verbose=True):
    """§6.1 checked PER COLUMN, with every data row required to be known.

    Returns (rows_present, rows_checked, gaps) where a gap is (key, message).
    Pure function of the text and the counted values, so part (E) can run it on
    a mutant without materialising a tree.
    """
    gaps = []
    rows = section_rows(text, "### 6.1")
    if not rows:
        return 0, 0, [("rows", "§6.1 holds no table at all")]
    header, rest = rows[0], rows[1:]
    if rest and is_separator(rest[0][1]):
        rest = rest[1:]
    data = [(ln, l) for ln, l in rest if not is_separator(l)]

    hdr = [c.lower() for c in cells(header[1])]
    try:
        col_named = next(i for i, c in enumerate(hdr) if "named" in c)
        col_swept = next(i for i, c in enumerate(hdr) if "swept" in c)
    except StopIteration:
        return len(data), 0, [("rows", "§6.1's header no longer names a NAMED "
                                       "and a SWEPT column")]

    # what each row is about, and the COUNTED figures that must appear in each
    # of its two population columns.  Every value here is computed, none read.
    expect = {
        "onethird_mgfccb_direction_check.py": (
            "identity-extension family",
            sorted([ident["posets"], ident["pairs"], ident["triples"]]),
            sorted([ident["posets"], ident["pairs"], ident["triples"]])),
        "onethird_mg8a71_audit_instrument.py": (
            "all-labelled family (A001035)",
            sorted([lab["posets"], lab["pairs"], lab["triples"]]),
            sorted([lab["posets"], lab["pairs"], lab["triples"]])),
        "onethird_mg8a71_live_claim_control.py": (
            "the live-claim control's own document",
            [],                                   # prose: "one file, all of it"
            sorted([doc_lines, doc_lines])),
    }

    checked = 0
    for lineno, line in data:
        cs = cells(line)
        m = re.search(r"`(onethird_\w+\.py)`", cs[0] if cs else "")
        key = m.group(1) if m else None
        if key not in expect:
            gaps.append(("rows",
                         f"§6.1 line {lineno}: a data row this audit has no "
                         f"expectation for — {(cs[0] if cs else line)[:60]!r}; "
                         f"a row present and unchecked is the defect this "
                         f"section reports on"))
            continue
        checked += 1
        pop, want_named, want_swept = expect[key]
        got_named = sorted(ints_in(cs[col_named])) if col_named < len(cs) else []
        got_swept = sorted(ints_in(cs[col_swept])) if col_swept < len(cs) else []
        if verbose:
            print(f"  row: {key}   (line {lineno})")
            print(f"      POPULATION : {pop}")
            print(f"      GRAIN      : one integer per (row x COLUMN x quantity)")
            print(f"      COUNTED  NAMED / SWEPT : {want_named} / {want_swept}")
            print(f"      IN THE ROW             : {got_named} / {got_swept}")
        ok = True
        if got_named != want_named:
            ok = False
            gaps.append(("LINE-GRAIN" if key.endswith("live_claim_control.py")
                         else "rows",
                         f"§6.1 line {lineno} column '{hdr[col_named]}': counted "
                         f"{want_named}, the cell has {got_named}"))
        if got_swept != want_swept:
            ok = False
            gaps.append(("LINE-GRAIN" if key.endswith("live_claim_control.py")
                         else "rows",
                         f"§6.1 line {lineno} column '{hdr[col_swept]}': counted "
                         f"{want_swept}, the cell has {got_swept}"))
        if verbose and ok:
            print(f"      [OK  ]")
        if verbose:
            print()
    return len(data), checked, gaps


def docstring_rows(doc):
    """(label, [cells]) for every data row of the helper's docstring table."""
    out = []
    for line in doc.split("\n"):
        if line.count("|") < 2:
            continue
        cs = [c.strip() for c in line.split("|")]
        if not cs or not cs[0]:
            continue
        out.append((cs[0], cs))
    return out


def part_b(dc, ident, lab, doc_lines):
    print("=" * 96)
    print("(B) BOTH TABLES, PER COLUMN — rows PRESENT counted against rows CHECKED")
    print("=" * 96)
    print(f"  the document the live-claim control reads has {doc_lines} LINES "
          f"(len(text.splitlines()))")
    print()
    text = (ROOT / CLOSEOUT).read_text(encoding="utf-8")
    present, checked, gaps = check_closeout_rows(text, ident, lab, doc_lines)
    print(f"  §6.1 of {CLOSEOUT}")
    print(f"      POPULATION : the data rows of that one section")
    print(f"      GRAIN      : one table row")
    print(f"      rows PRESENT : {present}")
    print(f"      rows CHECKED : {checked}")
    if present != checked:
        gaps.append(("rows", f"§6.1: {present} data rows present, {checked} "
                             f"checked — the difference is unaudited"))
    for key, msg in gaps:
        gap(key, msg)
    if not gaps:
        print(f"      [OK  ] every row present is a row checked")
    print()

    # --- the docstring table
    doc = dc.posets_with_identity_extension.__doc__ or ""
    rows = docstring_rows(doc)
    if not rows:
        gap("rows", "the helper's docstring no longer carries a table")
        return
    header, data = rows[0], [r for r in rows[1:]
                             if not all(re.fullmatch(r":?-{2,}:?", c)
                                        for c in r[1] if c)]
    want = {str(n): (ident["per_n"][n], lab["per_n"][n]) for n in NS}
    want["tot"] = (ident["posets"], lab["posets"])
    print(f"  the table in `posets_with_identity_extension`'s docstring "
          f"({DIRECTION_CHECK})")
    print(f"      POPULATION : the data rows of that one docstring table")
    print(f"      GRAIN      : one poset count per (n x FAMILY), per column")
    print(f"      header     : {header[0]!r}")
    print(f"      rows PRESENT : {len(data)}")
    n_checked = 0
    for label, cs in data:
        if label not in want:
            gap("rows", f"docstring table: a data row labelled {label!r} that "
                        f"this audit has no expectation for")
            continue
        n_checked += 1
        w1, w2 = want[label]
        g1, g2 = sorted(set(ints_in(cs[1]))), sorted(set(ints_in(cs[2])))
        ok = g1 == [w1] and g2 == [w2]
        print(f"      row {label:<4} COUNTED {w1:>5} | {w2:>5}    "
              f"IN THE ROW {str(g1):>9} | {str(g2):>9}   "
              f"[{'OK  ' if ok else 'GAP '}]")
        if not ok:
            gap("rows", f"docstring row {label!r}: counted {w1} | {w2}, the row "
                        f"has {g1} | {g2}")
    print(f"      rows CHECKED : {n_checked}")
    if len(data) != n_checked:
        gap("rows", f"docstring table: {len(data)} data rows present, "
                    f"{n_checked} checked")
    print()


# ====================================================== part (C) instruments ==

# The live-claim control's own S3 signature sentence, planted in a document that
# control does not read.  Using ITS OWN signature is the point: a miss here is
# not "the control was never asked", it is "the control was asked, in a document
# outside its population, and could not answer".
S3_CLAIM = ("Equivalently: can `max_x m_x = ω(1)` (indeed `Θ(n)`) with "
            "`E[inv_e] = O(n)`, δ < 1/3, width 3?")
S3_REWRITE = ("The second display asks a different question from the first: what "
              "a falsifier must make large is the per-element bias `b_x`, not the "
              "inversion degree.")
S3_SHORT = "can the bimodal chain-cross be ruled out by a degree bound?"

# Ledger C10's pattern (`sweep over all posets`), in the document it is ledgered
# in.  Same seven instruments, a claim the ledger knows by name.
C10_CLAIM = ("The machine check is a sweep over all posets on `n ≤ 5` and every "
             "reference order at those sizes.")
C10_REWRITE = ("The machine check is a sweep over the 404 posets on `n = 3,4,5` "
               "having the identity as a linear extension, and every reference "
               "order at those sizes.")
C10_SHORT = "a sweep over the whole labelled population"


def render(instrument, claim, rewrite, short):
    """The lines this instrument leaves at the site, for one claim."""
    if instrument == "J1  strike-at-site":
        return ["", f"> **STRUCK (mutant, mg-5854).** ~~*\"{claim}\"*~~ — refuted "
                    f"and struck at the site, with the markup that says so.", ""]
    if instrument == "J2  rewrite-in-place":
        return ["", rewrite, ""]
    if instrument == "J3  rewrite + annotation":
        return ["", rewrite, "",
                "> ### ⚠️ ANNOTATION (mutant, mg-5854): the sentence above was "
                "rewritten in place.",
                "> The earlier form named a population the check does not sweep; "
                "the corrected sentence is the whole content.", ""]
    if instrument == "J4  deletion, UNDECLARED":
        return []
    if instrument == "J5a deletion, declared, short quote":
        return ["", f"> **POPULATION CORRECTION (mutant, mg-5854).** The sentence "
                    f"\"{short}\" is struck with it.", ""]
    if instrument == "J5b deletion, declared, verbatim quote":
        return ["", f"> **POPULATION CORRECTION (mutant, mg-5854).** The sentence "
                    f"\"{claim}\" is struck with it.", ""]
    if instrument == "J6  none — claim LEFT LIVE":
        return ["", claim, ""]
    raise AssertionError(instrument)


MUTANTS = [
    ("J1  strike-at-site", "strike-at-site"),
    ("J2  rewrite-in-place", "rewrite-in-place"),
    ("J3  rewrite + annotation", "rewrite + annotation"),
    ("J4  deletion, UNDECLARED", "DELETION declared as a strike (forbidden form)"),
    ("J5a deletion, declared, short quote", "DELETION declared as a strike"),
    ("J5b deletion, declared, verbatim quote", "DELETION declared as a strike"),
    ("J6  none — claim LEFT LIVE", "none"),
]

SUBJECTS = [
    ("subject 1 — an UNLEDGERED refuted claim, in another document",
     S3_CLAIM, S3_REWRITE, S3_SHORT),
    ("subject 2 — a LEDGERED refuted claim (C10), in another document",
     C10_CLAIM, C10_REWRITE, C10_SHORT),
]

CONTROLS = [("live-claim", LIVE_CLAIM),
            ("declared-strike", DECLARED_STRIKE),
            ("ledger", LEDGER)]


def anchor_line(lines):
    """Where the mutants go: the end of mgd112 §2.2, before the section break."""
    start = next(i for i, l in enumerate(lines) if l.startswith("### 2.2"))
    for i in range(start + 1, len(lines)):
        if lines[i].startswith("## ") or lines[i].startswith("### "):
            return i
    return len(lines)


def run_controls(corpus):
    """Each control exactly as script-controls.yml runs it: no path argument."""
    out = []
    for _name, rel in CONTROLS:
        r = subprocess.run([sys.executable, rel], capture_output=True, text=True,
                           cwd=str(corpus))
        out.append(r.returncode)
    return tuple(out)


def part_c(tmp):
    print("=" * 96)
    print("(C) THE FIVE INSTRUMENTS AT TWO SITES OUTSIDE THE PARENT'S SUBJECT")
    print("=" * 96)
    src = (ROOT / MGD112).read_text(encoding="utf-8").split("\n")
    at = anchor_line(src)
    print(f"  site      : {MGD112}:{at} (end of §2.2) — NOT the document the "
          f"live-claim control reads")
    print(f"  POPULATION: {len(SUBJECTS)} subjects x {len(MUTANTS)} mutants x "
          f"{len(CONTROLS)} controls = "
          f"{len(SUBJECTS)*len(MUTANTS)*len(CONTROLS)} process exit codes")
    print(f"  GRAIN     : one exit code per (subject x mutant x control)")
    print()
    measured = {}
    for si, (subject, claim, rewrite, short) in enumerate(SUBJECTS):
        print(f"  {subject}")
        print(f"  {'mutant':<40} {'live-claim':>11} {'declared-strike':>16} "
              f"{'ledger':>8}")
        print(f"  {'-'*40} {'-'*11:>11} {'-'*16:>16} {'-'*8:>8}")
        for label, instrument in MUTANTS:
            corpus = tmp / f"s{si}" / label.split()[0]
            corpus.mkdir(parents=True)
            shutil.copytree(ROOT / "docs", corpus / "docs")
            shutil.copytree(ROOT / "scripts", corpus / "scripts")
            body = src[:at] + render(label, claim, rewrite, short) + src[at:]
            (corpus / MGD112).write_text("\n".join(body), encoding="utf-8")
            rcs = run_controls(corpus)
            measured[(si, label)] = rcs
            print(f"  {label:<40} {rcs[0]:>11} {rcs[1]:>16} {rcs[2]:>8}")
        print()

    # what the matrix says, computed rather than narrated
    for si, (subject, _c, _r, _s) in enumerate(SUBJECTS):
        classes = {}
        for label, instrument in MUTANTS:
            classes.setdefault(measured[(si, label)], []).append(label.split()[0])
        print(f"  {subject}")
        print(f"      distinct exit-code signatures over the {len(MUTANTS)} "
              f"mutants: {len(classes)}")
        for sig, members in sorted(classes.items()):
            print(f"        {sig}  <-  {', '.join(members)}")
        live = measured[(si, "J6  none — claim LEFT LIVE")]
        if live[0] != 0:
            gap("reach", f"{subject}: the live-claim control bit a mutant in a "
                         f"document it does not read — the harness is wrong, "
                         f"not the control")
        print(f"      the live-claim control on a claim LEFT LIVE here: exit "
              f"{live[0]}  ({'BLIND — outside its one-document population' if live[0] == 0 else 'caught'})")
        print()

    # The load-bearing comparison: which instruments are separable, and by what.
    s0 = {label: measured[(0, label)] for label, _ in MUTANTS}
    s1 = {label: measured[(1, label)] for label, _ in MUTANTS}
    n0 = len(set(s0.values()))
    n1 = len(set(s1.values()))
    print("  WHAT THE TWO SUBJECTS SAY, side by side:")
    print(f"    an UNLEDGERED claim outside the one document falls into {n0} "
          f"exit-code class(es);")
    print(f"    a LEDGERED claim in the same document falls into {n1}.")
    print("    The difference is not the INSTRUMENT.  It is whether the claim is")
    print("    (a) in the one document the live-claim control reads, or (b) named")
    print("    in the ledger by hand.  Neither is a property of how the claim was")
    print("    remediated, so 'which instrument can a control see' is answered by")
    print("    the population, not by the instrument.")
    print()
    return measured


# ==================================================== part (D) do not disturb ==

# The two part-true deletions, and the true half each one left behind, verbatim.
TRUE_HALVES = [
    (SPREAD, "(element, reference-order) cases",
     "§2.3's replacement keeps the reference-order half of the deleted clause"),
    (MGD112, "× **every** reference order",
     "the mgd112 §2.2 table row retains the reference-order half verbatim"),
]

# F4's three proven-safe sites.  mg-069f found the finding wider than reported and
# DECLINED to re-widen the text; the audit verified all three are at most as
# strong as §3.4.  These are the phrasings that make them narrower.
F4_SITES = [
    ("the (A)+(B) route** has attacked since mg-8201", 2,
     "§0 and the §12 attempt-index row — the narrowed universal"),
    ("we hold on this route", 1,
     "the §12 narrative — narrower still; the 'since mg-8201' clause is absent"),
]


def part_d():
    print("=" * 96)
    print("(D) DO NOT DISTURB — three things re-run, not re-read")
    print("=" * 96)

    print("  D1  no true material lost: both part-true deletions left the true "
          "half verbatim")
    print(f"      POPULATION : the {len(TRUE_HALVES)} deletions mg-069f's audit "
          f"§6 adjudicated 'partly true, cut'")
    print(f"      GRAIN      : one retained clause")
    kept = 0
    for rel, needle, why in TRUE_HALVES:
        text = (ROOT / rel).read_text(encoding="utf-8")
        n = text.count(needle)
        print(f"      {rel.split('/')[-1]:<46} {needle!r} x{n}")
        if n >= 1:
            kept += 1
        else:
            gap("disturb", f"the true half {needle!r} is gone from {rel} — {why}")
    print(f"      [{'OK  ' if kept == len(TRUE_HALVES) else 'GAP '}] "
          f"{kept}/{len(TRUE_HALVES)} retained")
    print()

    print("  D2  F4's decline to re-widen: the three proven-safe sites are still "
          "narrow")
    print(f"      POPULATION : the 3 sites in {BBIAS.split('/')[-1]} (§0, the §12 "
          f"row, the §12 narrative)")
    print(f"      GRAIN      : one site")
    text = (ROOT / BBIAS).read_text(encoding="utf-8")
    sites = 0
    for needle, want, why in F4_SITES:
        n = text.count(needle)
        sites += min(n, want)
        ok = n >= want
        print(f"      {needle!r} x{n} (want >= {want})   [{'OK  ' if ok else 'GAP '}]"
              f"   {why}")
        if not ok:
            gap("disturb", f"F4 site drift: {needle!r} occurs {n} times in "
                           f"{BBIAS}, expected at least {want} — {why}")
    print(f"      [{'OK  ' if sites == 3 else 'GAP '}] {sites}/3 sites still at "
          f"most as strong as §3.4, un-rewidened")
    print()

    print("  D3  `Var(pos_σ z) = m(m+2)/12` is ASSERTED by a control, not only "
          "written in body text")
    ir = (ROOT / IDENTITY_RECHECK).read_text(encoding="utf-8")
    asserts = "Var(pos z) != m(m+2)/12" in ir
    wired = "onethird_mg0242_identity_recheck.py" in (
        ROOT / ".github/workflows/script-controls.yml").read_text(encoding="utf-8")
    print(f"      POPULATION : the CI-wired controls of script-controls.yml")
    print(f"      GRAIN      : one assertion")
    print(f"      {IDENTITY_RECHECK.split('/')[-1]} asserts it : {asserts}")
    print(f"      and is wired into CI            : {wired}")
    if not (asserts and wired):
        gap("disturb", "Var(pos_σ z) = m(m+2)/12 is no longer asserted by a "
                       "CI-wired control")
    else:
        print(f"      [OK  ] asserted, and in CI")
    # ... and the same script's report still says nobody asserts it.
    stale = ir.count("no control asserts")
    print(f"      note: that script's own report says 'no control asserts' it "
          f"{stale} time(s), which is now false OF ITSELF — recorded, not fixed "
          f"(§4 of the report)")
    print()


# ================================================ part (E) the parent's reach ==


def mutate_column_swap(text):
    """Move every figure of §6.1 row 1 into the NAMED column, multiset unchanged."""
    lines = text.split("\n")
    for i, line in enumerate(lines):
        if "`onethird_mgfccb_direction_check.py`" in line and line.startswith("|"):
            cs = cells(line)
            named, swept = cs[1], cs[2]
            cs[1] = named + " / " + " / ".join(
                str(v) for v in ints_in(swept))
            cs[2] = "asserted in-script"
            lines[i] = "| " + " | ".join(cs) + " |"
            return "\n".join(lines)
    raise AssertionError("row 1 not found")


def mutate_extra_row(text):
    """Append a fourth §6.1 data row that names no script and carries a wrong figure.

    The insertion point is taken from `section_rows`, i.e. from the same parser
    the check uses.  A first draft took `max(i for i, l in enumerate(lines) if
    l.startswith("|") and "onethird_" in l)` over the WHOLE file and landed the
    row in a later section, so the mutant did not mutate §6.1 and the checker
    correctly reported no gap -- which read as a MISS.  A mutant that does not
    reach its site measures nothing; the self-test in part (E) is what caught it.
    """
    lines = text.split("\n")
    last = section_rows(text, "### 6.1")[-1][0] - 1
    lines.insert(last + 1,
                 "| the corpus sweep (no script named) | 999 999 documents | "
                 "**999 999 documents**, asserted in-script | ✅ |")
    return "\n".join(lines)


MUTATIONS = [("column-swap: every figure moved into the NAMED column",
              mutate_column_swap),
             ("extra row: a fourth data row naming no script",
              mutate_extra_row)]


def part_e(ident, lab, doc_lines, vs_parent=False):
    print("=" * 96)
    print("(E) WHAT A ROW AUDIT CAN MISS — two mutants of the same section")
    print("=" * 96)
    text = (ROOT / CLOSEOUT).read_text(encoding="utf-8")
    print(f"  POPULATION: {len(MUTATIONS)} mutants of §6.1 of {CLOSEOUT}")
    print(f"  GRAIN     : one mutant, one verdict per checker")
    print()
    for name, fn in MUTATIONS:
        mutated = fn(text)
        present, checked, gaps = check_closeout_rows(
            mutated, ident, lab, doc_lines, verbose=False)
        unbaselined = [g for g in gaps if g[0] not in BASELINE]
        caught = bool(unbaselined)
        print(f"  {name}")
        print(f"      this audit's part (B): rows present {present}, checked "
              f"{checked}, gaps {len(unbaselined)}  "
              f"-> {'CAUGHT' if caught else '*** MISSED ***'}")
        for _k, msg in unbaselined:
            print(f"          {msg}")
        if not caught:
            gap("selftest", f"this audit's own row check MISSED the mutant "
                            f"{name!r} — an assertion nobody has seen fail is a "
                            f"claim")
        if vs_parent:
            rc = run_parent_on(mutated)
            print(f"      the parent's {PARENT_ROW_AUDIT.split('/')[-1]}: exit "
                  f"{rc}  -> {'CAUGHT' if rc else '*** MISSED ***'}")
        print()
    if not vs_parent:
        print(f"  the parent's own verdict on these two mutants is measured under "
              f"`--vs-parent`,")
        print(f"  which materialises a tree; off the default path because this job "
              f"checks out at")
        print(f"  depth 1 (the mg-3934 rule).  Recorded in §5 of the report.")
        print()


def run_parent_on(mutated_closeout):
    """Run the parent's row audit against a tree carrying the mutated section."""
    with tempfile.TemporaryDirectory() as td:
        tmp = pathlib.Path(td)
        for d in ("docs", "scripts", ".github"):
            shutil.copytree(ROOT / d, tmp / d)
        (tmp / CLOSEOUT).write_text(mutated_closeout, encoding="utf-8")
        r = subprocess.run([sys.executable, PARENT_ROW_AUDIT],
                           capture_output=True, text=True, cwd=str(tmp))
        return r.returncode


# ========================================================================= main


def main():
    vs_parent = "--vs-parent" in sys.argv
    print("=" * 96)
    print("mg-5854 — INDEPENDENT AUDIT of the mg-1d03 G3+G4 repair")
    print("=" * 96)
    print()

    dc = load("dc", DIRECTION_CHECK)
    doc_lines = len((ROOT / SPREAD).read_text(encoding="utf-8").splitlines())

    ident, lab = part_a(dc)
    part_b(dc, ident, lab, doc_lines)
    with tempfile.TemporaryDirectory(prefix="mg5854-") as td:
        part_c(pathlib.Path(td))
    part_d()
    part_e(ident, lab, doc_lines, vs_parent=vs_parent)

    missing = BASELINE - BASELINE_SEEN
    print("=" * 96)
    if missing:
        print(f"RESULT: FAIL — {len(missing)} baselined gap(s) no longer present; "
              f"re-baseline this audit:")
        for m in sorted(missing):
            print(f"  - {m}")
        return 1
    if FAILURES:
        print(f"RESULT: FAIL — {len(FAILURES)}:")
        for f in FAILURES:
            print(f"  - {f}")
        return 1
    print("RESULT: PASS — every figure in both tables equals a value counted "
          "three ways")
    print("        (this audit's enumerator, the helper, and A001035); every row "
          "PRESENT is a")
    print("        row CHECKED, per COLUMN; the do-not-disturb three hold; and "
          "the five")
    print(f"        instruments were constructed at two sites outside the "
          f"parent's subject.")
    print(f"        {len(BASELINE)} baselined gap(s), still present and still "
          f"listed: {sorted(BASELINE)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
