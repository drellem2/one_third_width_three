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

HOW FAR A MARKER REACHES (mg-cd04, closing mg-0242 finding G2).  mg-069f stopped
a STRIKE block exempting itself by its label alone -- such a block is now checked
with inline `~~` spans removed, so declaring STRUCK without the markup fails.
That tightening was applied to ONE of the two marker classes.  EXEMPT blocks
(`ANNOTATION` / `RE-DERIVATION`) were still skipped ENTIRELY on a label read from
`block[:3]`, with NO bound on how long the block ran; mg-0242 demonstrated the
gap by mutation (refuted sentence in an ANNOTATION tail -> exit 0, MISSED; the
same sentence as a paragraph -> exit 1, caught) and showed it was not
hypothetical -- the longest ANNOTATION block in this file runs 53 lines and
swallows load-bearing prose that mg-069f itself wrote.

An EXEMPT marker now reaches only as far as the thing it is a marker FOR:

  * the block is split into sub-paragraphs at its own blank (`>`-only) lines;
  * the sub-paragraph carrying the label is exempt;
  * each following sub-paragraph is exempt only while it carries a QUOTATION --
    a `~~struck~~` span or a quoted sentence.  Commentary about a refuted claim
    has to quote the claim, and that quotation is the whole reason the exemption
    exists; a sub-paragraph that quotes nothing is not commentary, it is body
    text, and the exempt run ENDS there;
  * and in no case does a label exempt more than MAX_EXEMPT_LINES lines.

Everything past the exempt prefix is checked as an ordinary quote unit.  This is
the same rule as the strike tightening -- BACK THE LABEL WITH MARKUP -- applied
to the class it was missing, plus the length bound the strike form gets for free
by being per-sentence.

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

ONE FILE IS STILL THE POPULATION, AND THAT IS ITS OWN LIMIT.  mg-0242 finding G1
was a block in `docs/OneThird-mgd112-DroppedVerdict-Closeout.md` that declared a
sentence struck and did not strike it -- the exact defect the paragraph above
closed, one document over from where this control looks, so this control could
not see it.  The population is deliberately not widened here: mg-0242 measured a
corpus-wide run of THESE signatures at ~94% false positive, because audit
documents discuss refuted claims in tables and prose the convention has no way to
mark.  What generalises is not the signature but the STRUCTURE -- "a sentence
that declares a strike must carry the markup" is content-free -- and that check
is now corpus-wide in `scripts/onethird_mgcd04_declared_strike_control.py` (2
baselined hits over 242 documents, and it bites at bb1cb9b where G1 is live).
Read the two together: this one asks whether a named claim is
live in one document; that one asks whether any document in the corpus declares a
strike it did not make.

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
# false positives.  Skipped — but only as far as the quotation runs, and never
# past MAX_EXEMPT_LINES (mg-cd04, mg-0242 G2; before that, skipped ENTIRELY on
# the strength of the label, for a block of any length).
#
# STRIKE: a block retaining a refuted claim as a record.  These are NOT skipped.
# They are checked after inline ~~struck~~ spans are removed, so a block that
# merely *declares* STRUCK while leaving the sentence unstruck still fails.
# Before mg-069f a strike block was skipped on the strength of its label alone,
# and a mutant that deleted the ~~ markup and kept the label passed.
EXEMPT_MARKERS = ("ANNOTATION", "RE-DERIVATION")
STRIKE_MARKERS = ("~~", "STRUCK")

# The bound on the ONE exemption still granted on a label's word alone: the
# label's own sub-paragraph (mg-cd04).  A label is a line or two; 6 is generous
# against every marker in this corpus and far short of the 53-line block mg-0242
# found a three-line label covering.  Every exempt line beyond it has to be
# backed by markup in its own sub-paragraph, so no further global cap is needed —
# the same shape as the strike rule, where each struck sentence carries its ~~.
MAX_LABEL_LINES = 6

# What makes a sub-paragraph of an EXEMPT block commentary rather than body text:
# it QUOTES the thing it is commenting on.  A struck span, or a quoted sentence
# long enough not to be a stray pair of quote marks.  Deliberately NOT inline
# code — `m_x` appears in nearly every line of this corpus, so accepting it would
# hand the exemption straight back.
QUOTATION = re.compile(r'~~.+?~~|"[^"\n]{8,}"|“[^”\n]{8,}”', re.DOTALL)

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


def sub_paragraphs(block):
    """Half-open (start, end) index pairs of a blockquote's own sub-paragraphs.

    A blockquote's internal blank lines are `>` or `>` + whitespace; markdown
    keeps them inside the block, which is exactly how a 53-line block ends up
    with one label at the top and six paragraphs of body text under it.
    """
    subs = []
    i = 0
    n = len(block)
    while i < n:
        if not block[i].lstrip(">").strip():
            i += 1
            continue
        j = i
        while j < n and block[j].lstrip(">").strip():
            j += 1
        subs.append((i, j))
        i = j
    return subs


def exempt_partition(block):
    """Split an EXEMPT blockquote into (exempt lines, checkable sub-paragraphs).

    mg-cd04 (mg-0242 finding G2).  The label used to exempt `len(block)`, whatever
    that was.  Two rules replace that, and between them every exempt line is now
    either close to the label or backed by its own markup:

      * the LABEL's own sub-paragraph is exempt on the label's word alone — that
        is what a label is — but only for MAX_LABEL_LINES lines.  This is the one
        unbacked exemption left, and it is the one that is bounded;
      * every OTHER sub-paragraph is exempt only if it carries a QUOTATION.  An
        annotation earns its exemption by quoting the claim it diagnoses; a
        sub-paragraph that quotes nothing is body text wearing a label three
        lines up, which is precisely the mg-0242 G2 blind spot.

    Judged per sub-paragraph rather than as a prefix run, deliberately: a genuine
    annotation interleaves quoting paragraphs with non-quoting ones (§2.3's
    mg-1fdb block does), and cutting the run at the first non-quoting paragraph
    would merge every quotation after it into one checked unit and fire on the
    quotations themselves.  Per sub-paragraph, each is judged on its own markup —
    and the appended-tail mutant is still caught, because the mutant quotes
    nothing.

    Returns (n_exempt_lines, [(start, end), ...]) over indices into `block`.
    """
    subs = sub_paragraphs(block)
    if not subs:
        return len(block), []          # nothing but blank quote lines
    n_exempt = 0
    checkable = []
    for idx, (start, end) in enumerate(subs):
        if idx == 0:
            cut = min(end, start + MAX_LABEL_LINES)
            n_exempt += cut - start
            if cut < end:
                checkable.append((cut, end))
            continue
        text = " ".join(b.lstrip("> ").rstrip() for b in block[start:end])
        if QUOTATION.search(text):
            n_exempt += end - start
        else:
            checkable.append((start, end))
    # the block's own blank lines are exempt bookkeeping, not text
    n_exempt += sum(1 for b in block if not b.lstrip(">").strip())
    return n_exempt, checkable


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
            # mg-cd04: the label no longer exempts the block.  It exempts a
            # bounded label sub-paragraph plus whichever sub-paragraphs back
            # themselves with a quotation; the rest are ordinary quote units.
            if exempt:
                n_exempt, checkable = exempt_partition(block)
                count("exempt_annotation", n_exempt)
                for a, b_ in checkable:
                    count("quote", b_ - a)
                    text = " ".join(x.lstrip("> ").rstrip() for x in block[a:b_])
                    if text.strip():
                        yield i + 1 + a, section, text
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
    print()
    print("WHAT THIS GREEN DOES NOT SAY (mg-0242 finding G4, closed by mg-1d03).")
    print("        Five remediation instruments are in use in this arc —")
    print("        strike-at-site (the standard), rewrite + annotation,")
    print("        rewrite-in-place, deletion, and none-with-a-routing.  THIS")
    print("        CONTROL CANNOT TELL THE FIRST THREE APART: it asks only whether")
    print("        a refuted claim is asserted in live text, and strike, rewrite")
    print("        and rewrite-with-annotation all end with it not asserted.")
    print("        So PASS means NO UN-REMEDIATED CLAIM.  It does not mean 'every")
    print("        remediation used the standard', and it does not mean 'the")
    print("        corpus kept a record of what was there' — rewrite-in-place")
    print("        keeps none, and is invisible here.")
    print("        The standard is named in full in")
    print("        scripts/onethird_mg0242_struck_vs_refuted.py INSTRUMENTS;")
    print("        its part (E) measures this blind spot rather than asserting it.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
