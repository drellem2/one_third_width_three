#!/usr/bin/env python3
"""mg-8a71 — a *doc-level* control for the mg-fccb §2.3 direction repair.

WHY THIS EXISTS, AND WHY THE NUMERIC CONTROL IS NOT ENOUGH.
`scripts/onethird_mgfccb_direction_check.py` proves `b_x <= m_x` on a corpus of
posets.  It cannot see the defect it was written for.  The defect was never a
false *number*: it was a false *sentence sitting in live body text*, and mg-fccb's
own stated reason for striking it rather than annotating it was that mg-1fdb's
annotation "left the wrong claim in the body".  That is a property of the
document, so it needs a document-level check.

WHAT IT CHECKS.  In `docs/OneThird-L1b-Spread-Locality.md`, the refuted inference

    a large per-element inversion DEGREE  max_x m_x  falsifies lemma (B)
    (equivalently: (B) "hinges on" capping m_x; equivalently: the bimodal
     chain-cross question and the max_x m_x question are the same question)

must not be asserted in **live body text**.  Text inside a *marked* blockquote --
one whose opening lines carry `~~` (struck), `ANNOTATION`, `STRUCK`, or
`RE-DERIVATION` -- is not live: that is the corpus's convention for retaining a
refuted claim as a record.  An unmarked blockquote (a display) IS live.  So is a
plain paragraph -- except for any `~~inline strikethrough~~` span inside it,
which is the same convention applied at sentence granularity and is stripped
before the signatures are applied (added mg-069f, when the §5 fix below needed to
strike one sentence of a numbered-list item without striking the item).

BASELINE: EMPTY, as of 2026-07-31 (mg-069f).  This control was written with two
known-live sites as an explicit baseline -- §3.2's "Equivalently" and §5
recommendation 2's converse, the two sites mg-8a71 finding F1 recorded as still
asserting a refuted claim in body text.  The baseline was F1 made executable, not
a tolerance: it was built to fail when a site DISAPPEARED, forcing a re-baseline
to zero once F1 was fixed.  mg-069f struck both at the site, the control failed
with "baseline site disappeared" exactly as designed, and the baseline is now
empty.  From here the control is a plain assertion: the refuted inference is
asserted in live body text NOWHERE in this document, and any reappearance --
including §2.3's struck sentence returning to live text -- fails.

POPULATION.  One file, all of it, and the script now PROVES that rather than
asserting it: every line of `docs/OneThird-L1b-Spread-Locality.md` is classified
into exactly one of {paragraph, quote, heading, exempt-annotation, blank}, the
buckets are printed, and the run asserts they sum to the file's line count.  Not
a sample.  Headings were silently dropped before mg-069f -- used as section
labels and never scanned -- while this paragraph claimed "all of it"; that is the
same NAMED-vs-SWEPT defect this control's own subject matter is about, so it is
recorded rather than quietly fixed.

USAGE
    onethird_mg8a71_live_claim_control.py [path]        # default: the doc in-repo
Demonstration against a commit where the defect IS present:
    git show 1b00147^:docs/OneThird-L1b-Spread-Locality.md > /tmp/pre.md
    onethird_mg8a71_live_claim_control.py /tmp/pre.md   # -> exit 1, §2.3 flagged
"""

import re
import sys

DOC = "docs/OneThird-L1b-Spread-Locality.md"

# Two kinds of marked blockquote, and they are NOT treated the same (mg-069f).
#
# EXEMPT: commentary ABOUT the refuted claim — an annotation has to quote and
# discuss the inference to diagnose it, so signatures fired there would be pure
# false positives.  Skipped entirely.
#
# STRIKE: a block retaining a refuted claim as a record.  These are NOT skipped.
# They are checked after inline ~~struck~~ spans are removed, so a block that
# merely *declares* STRUCK while leaving the sentence unstruck still fails.
# Before mg-069f a strike block was skipped on the strength of its label alone,
# and a mutant that deleted the ~~ markup and kept the label passed.
EXEMPT_MARKERS = ("ANNOTATION", "RE-DERIVATION")
STRIKE_MARKERS = ("~~", "STRUCK")

# Signatures of the refuted inference.  Each is (id, description, predicate).
SIGNATURES = [
    ("S1-jensen-falsifier",
     "Jensen step used to turn a large m_x into a (B) failure",
     lambda t: "jensen" in t and "m_x" in t
               and ("(b) fails" in t or "Θ(n²)" in t or "theta(n^2)" in t)),
    ("S2-hinges-on-degree",
     "lemma (B) said to 'hinge on' capping the per-element degree m_x",
     lambda t: "hinges on" in t and "m_x" in t),
    ("S3-equivalently-degree",
     "chain-cross question equated with the max_x m_x question",
     lambda t: "equivalently" in t and "max_x m_x" in t),
    ("S4-nonexistence-converse",
     "non-existence of the chain-cross asserted to BE (B) (converse over-read)",
     lambda t: re.search(r"non-existence\s+\*?is\*?\s+\(b\)", t) is not None),
]

# (signature id, section) pairs tolerated as live.  EMPTY since mg-069f struck
# the two mg-8a71 F1 sites at the site; see the module docstring.  Adding to this
# set is how a future reader would tolerate a live refuted claim — so don't,
# without a finding that says why.
BASELINE = set()

# An inline ~~struck~~ span is marked text, not live text.
INLINE_STRIKE = re.compile(r"~~.+?~~", re.DOTALL)


def live_paragraphs(lines, coverage=None):
    """Yield (start_line_no, section_heading, paragraph_text) for checkable text.

    EXEMPT blockquotes (ANNOTATION / RE-DERIVATION) are dropped here; everything
    else — plain paragraphs, headings, unmarked display quotes, and STRIKE
    blockquotes — is yielded, and `scan` strips inline ~~struck~~ spans before
    applying the signatures.

    `coverage`, if given, is a dict that accumulates a line count for every
    disposition, so the caller can assert that the population NAMED is the
    population SWEPT.  Every line of the file lands in exactly one bucket.
    """
    if coverage is None:
        coverage = {}

    def count(bucket, k=1):
        coverage[bucket] = coverage.get(bucket, 0) + k

    section = "(preamble)"
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if line.startswith("#"):
            section = line.strip()
            # headings are CHECKED too, not just used as labels: a section title
            # is body text a reader reads (mg-069f — before this, headings were
            # silently dropped while the docstring claimed "one file, all of it")
            count("heading")
            yield i + 1, section, line.strip()
            i += 1
            continue
        if line.startswith(">"):
            # consume the whole blockquote block, decide live/marked once
            j = i
            block = []
            # maximal run of '>' lines; a blank line ENDS the block, so a display
            # quote is never merged with the annotation quote that follows it
            while j < n and lines[j].startswith(">"):
                block.append(lines[j])
                j += 1
            head = " ".join(block[:3]).lower()
            exempt = any(mk.lower() in head for mk in EXEMPT_MARKERS)
            if exempt:
                count("exempt_annotation", j - i)
            else:
                count("quote", j - i)
                text = " ".join(b.lstrip("> ").rstrip() for b in block)
                if text.strip():
                    yield i + 1, section, text
            i = j
            continue
        if line.strip() == "":
            count("blank")
            i += 1
            continue
        # a plain paragraph
        j = i
        para = []
        while j < n and lines[j].strip() != "" and not lines[j].startswith((">", "#")):
            para.append(lines[j])
            j += 1
        count("paragraph", j - i)
        yield i + 1, section, " ".join(p.rstrip() for p in para)
        i = j


def scan(path):
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    hits = []
    n_live = 0
    coverage = {}
    for lineno, section, text in live_paragraphs(lines, coverage):
        n_live += 1
        # inline ~~strikethrough~~ is the retain-as-record convention at sentence
        # granularity; drop those spans before testing what the text asserts
        low = INLINE_STRIKE.sub(" ", text).lower()
        for sig_id, desc, pred in SIGNATURES:
            if pred(low):
                hits.append((sig_id, section, lineno, desc, text[:150]))
    # the population NAMED must be the population SWEPT: every line accounted for
    assert sum(coverage.values()) == len(lines), (
        f"coverage gap: {sum(coverage.values())} lines classified of {len(lines)}"
    )
    return len(lines), n_live, hits, coverage


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DOC
    total, n_live, hits, coverage = scan(path)
    print("=" * 78)
    print("mg-8a71 live-claim control — the refuted m_x-falsifier inference")
    print("=" * 78)
    print(f"file      : {path}")
    checked = total - coverage.get("blank", 0) - coverage.get("exempt_annotation", 0)
    print(f"population: {total} lines, ALL classified — "
          f"{coverage.get('paragraph', 0)} paragraph + {coverage.get('quote', 0)} quote + "
          f"{coverage.get('heading', 0)} heading = {checked} CHECKED, "
          f"{coverage.get('exempt_annotation', 0)} exempt (ANNOTATION / RE-DERIVATION), "
          f"{coverage.get('blank', 0)} blank")
    print(f"            -> {n_live} checkable units; inline ~~struck~~ spans dropped "
          f"before matching")
    print(f"signatures: {len(SIGNATURES)}; baseline: {len(BASELINE)} tolerated live sites")
    print()
    found = set()
    for sig_id, section, lineno, desc, snippet in hits:
        state = "BASELINE" if (sig_id, section) in BASELINE else "*** NEW ***"
        found.add((sig_id, section))
        print(f"  [{state}] {sig_id} @ line {lineno}  ({section})")
        print(f"            {desc}")
        print(f"            > {snippet.strip()}")
    if not hits:
        print("  no live assertion of the refuted inference found — the whole file")
    print()
    new = found - BASELINE
    gone = BASELINE - found
    for sig_id, section in sorted(new):
        print(f"  FAIL: NEW live site  {sig_id} in {section}")
    for sig_id, section in sorted(gone):
        print(f"  FAIL: baseline site disappeared (re-baseline this control): "
              f"{sig_id} in {section}")
    print("=" * 78)
    if new or gone:
        print("RESULT: FAIL — the live-claim set differs from the recorded baseline.")
        return 1
    print("RESULT: PASS — the refuted inference is asserted in live body text at NO")
    print("        site in this document.  The two sites mg-8a71 finding F1 recorded")
    print("        as outstanding (§3.2's 'Equivalently', §5 rec 2's converse) were")
    print("        struck at the site by mg-069f; §2.3's struck sentence has not")
    print("        returned to live body text.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
