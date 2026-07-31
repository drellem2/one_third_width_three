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
refuted claim as a record.  An unmarked blockquote (a display) IS live.

BASELINE.  Two sites are known to still assert it in live body text at the time
this control was written (mg-8a71 audit finding F1): §3.2's "Equivalently" and
§5 recommendation 2's converse.  Both carry an annotation *below* them but the
claim itself is unstruck.  They are recorded as an explicit, named baseline so
the control passes today; the control fails if a site LEAVES the baseline set,
if a NEW site appears, or if the struck §2.3 sentence returns to live text.

POPULATION.  One file, all of it: every line of
`docs/OneThird-L1b-Spread-Locality.md`, classified live/marked, grouped into
paragraphs, four signatures applied to each live paragraph.  Not a sample.

USAGE
    onethird_mg8a71_live_claim_control.py [path]        # default: the doc in-repo
Demonstration against a commit where the defect IS present:
    git show 1b00147^:docs/OneThird-L1b-Spread-Locality.md > /tmp/pre.md
    onethird_mg8a71_live_claim_control.py /tmp/pre.md   # -> exit 1, §2.3 flagged
"""

import re
import sys

DOC = "docs/OneThird-L1b-Spread-Locality.md"

# A blockquote block is NOT live if its opening lines carry one of these markers.
MARKERS = ("~~", "ANNOTATION", "STRUCK", "RE-DERIVATION")

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

# (signature id, section) pairs known to be live at HEAD — mg-8a71 finding F1.
BASELINE = {
    ("S3-equivalently-degree", "### 3.2 The open question (the wall)"),
    ("S4-nonexistence-converse", "## 5. Status and what remains"),
}


def live_paragraphs(lines):
    """Yield (start_line_no, section_heading, paragraph_text) for LIVE text only."""
    section = "(preamble)"
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if line.startswith("#"):
            section = line.strip()
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
            head = " ".join(block[:3])
            marked = any(mk.lower() in head.lower() for mk in MARKERS)
            if not marked:
                text = " ".join(b.lstrip("> ").rstrip() for b in block)
                if text.strip():
                    yield i + 1, section, text
            i = j
            continue
        if line.strip() == "":
            i += 1
            continue
        # a plain paragraph
        j = i
        para = []
        while j < n and lines[j].strip() != "" and not lines[j].startswith((">", "#")):
            para.append(lines[j])
            j += 1
        yield i + 1, section, " ".join(p.rstrip() for p in para)
        i = j


def scan(path):
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    hits = []
    n_live = 0
    for lineno, section, text in live_paragraphs(lines):
        n_live += 1
        low = text.lower()
        for sig_id, desc, pred in SIGNATURES:
            if pred(low):
                hits.append((sig_id, section, lineno, desc, text[:150]))
    return len(lines), n_live, hits


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DOC
    total, n_live, hits = scan(path)
    print("=" * 78)
    print("mg-8a71 live-claim control — the refuted m_x-falsifier inference")
    print("=" * 78)
    print(f"file      : {path}")
    print(f"population: {total} lines, {n_live} LIVE paragraphs "
          f"(marked blockquotes — struck / ANNOTATION / RE-DERIVATION — excluded)")
    print(f"signatures: {len(SIGNATURES)}; baseline: {len(BASELINE)} known-live sites")
    print()
    found = set()
    for sig_id, section, lineno, desc, snippet in hits:
        state = "BASELINE" if (sig_id, section) in BASELINE else "*** NEW ***"
        found.add((sig_id, section))
        print(f"  [{state}] {sig_id} @ line {lineno}  ({section})")
        print(f"            {desc}")
        print(f"            > {snippet.strip()}")
    if not hits:
        print("  no live assertion of the refuted inference found")
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
    print("RESULT: PASS — the refuted inference is asserted live only at the two")
    print("        sites recorded as outstanding by the mg-8a71 audit (finding F1);")
    print("        §2.3's struck sentence has not returned to live body text.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
