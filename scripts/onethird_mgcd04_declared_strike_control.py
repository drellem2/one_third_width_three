#!/usr/bin/env python3
"""mg-cd04 — a CORPUS-WIDE control: a block that DECLARES a strike must make it.

WHY THIS EXISTS.  mg-0242 finding G1.  mg-069f closed, in
`onethird_mg8a71_live_claim_control.py`, the hole where a blockquote could exempt
itself by DECLARING `STRUCK` without carrying the `~~` markup -- found by
mutation, fixed in the same commit.  In that same commit mg-069f wrote, into
`docs/OneThird-mgd112-DroppedVerdict-Closeout.md` §2.2, a POPULATION CORRECTION
block that said a sentence *"is struck with it"* and did not strike it.  The
defect it had just closed in the instrument, reproduced in its own new text, ONE
DOCUMENT OVER from where the instrument looks.

So the finding is not really about that block.  It is about the population.  The
live-claim control reads one file, deliberately and at length; a defect authored
into any of the other 240 is invisible to it, and the class this one belongs to
is not file-specific at all.  **A control whose population stops at one document
is the same defect one level up** -- which is what mg-0242 said and could not
act on, because it was an audit.

WHY THE POPULATION CAN BE THE WHOLE CORPUS HERE, AND IS NOT THERE.  mg-0242 §8
measured the obvious generalisation and rejected it: running the live-claim
control's four SIGNATURES corpus-wide is ~94% false positive, because audit and
closeout documents legitimately discuss refuted claims in tables and prose that
the convention has no way to mark.  That is a property of the signatures -- they
are about one specific refuted inference, and quoting it is not asserting it.

This control checks the STRUCTURE instead, and structure generalises where
content does not:

    a block that says text inside it is struck must contain ~~ markup.

No claim, no subject matter, no adjudication -- the check is entirely
content-free, so an audit document quoting a refuted sentence does not trip it,
and a block that promises a strike it did not make does.  Measured over all of
`docs/`: 2 hits at HEAD, both the mg-0242 report quoting the very defect it found
(baselined below by name) and 1 reported near miss; at `bb1cb9b`, where the
defect is live, exactly 1 unbaselined hit -- the defect -- and nothing else in
the 239 documents that tree holds.

WHAT COUNTS AS A DECLARATION.  A self-referential strike verb -- "is struck",
"are struck", "struck with it", "now struck", "struck here" -- in a block that
also carries a QUOTED SENTENCE.  Both halves are required, and the quotation is
what makes the declaration self-referential: a block that says a claim "is
struck" without quoting anything is reporting on an edit made elsewhere, which is
what most of this corpus's prose about strikes is.

POPULATION: every `*.md` in `docs/`, every block, and the run PROVES it rather
than asserting it -- every line lands in exactly one of {block, blank} and the
buckets are asserted to sum to each file's line count.  That assertion is here
because a NAMED-vs-SWEPT gap is the recurring defect of this whole arc, and a
control introduced to answer a population finding is the last place to leave one.

USAGE
    onethird_mgcd04_declared_strike_control.py            # the corpus
    onethird_mgcd04_declared_strike_control.py --demonstrate <rev>
        # re-run against a revision where the defect IS present; exits 0 only if
        # the unbaselined G1 site is found there, so the control is shown to bite
"""

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = "docs"

# A self-referential strike declaration.  Kept tight on purpose: "struck at the
# site by mg-069f" and "the struck sentence" are reports and descriptions, not
# declarations, and matching them would drown the signal.
DECLARATION = re.compile(
    r"\b(?:is|are)\s+(?:now\s+|hereby\s+)?struck\b"
    r"|\bstruck\s+with\s+it\b"
    r"|\bstruck\s+here\b"
    r"|\b(?:strike|striking)\s+it\s+here\b",
    re.IGNORECASE)

# A quoted sentence -- what makes the declaration point at text in this block.
# Not inline code: `m_x` is on nearly every line of this corpus.
QUOTATION = re.compile(r'"[^"\n]{8,}"|“[^”\n]{8,}”|\*"[^"\n]+"\*')

# The strike markup the declaration must be backed by.
STRIKE_MARKUP = "~~"

# BASELINE — blocks that declare a strike, quote a sentence, and carry no markup,
# and are RIGHT to.  Keyed by (file, first quoted span), which survives reflow in
# a way line numbers do not.
#
# Both entries are `docs/OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md`
# QUOTING the G1 defect in order to report it.  An audit that could not quote the
# text it found would not be an audit; mg-0242 §8 makes the same point about the
# signature sweep, and measured it at 16 of 17 hits.  The audit's finding text is
# a record and is not rewritten by the repair that closes it.
#
# Adding to this set is how a future reader would tolerate an unmade strike, so
# don't, without a finding that says why.  A baseline entry that STOPS matching
# also fails the run, so repairing one forces a re-baseline rather than passing
# silently -- the convention mg-8a71 set and mg-0242 kept.
BASELINE = {
    ("OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md",
     "is struck with it"),
    ("OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md",
     "over every poset and every reference order at those sizes"),
}


FENCE = re.compile(r"^\s*(```|~~~)")


def blocks(lines, coverage=None):
    """Yield (start_line_no, block_lines) for every maximal non-blank run.

    Blocks, not paragraphs: a declaration and the markup that should back it are
    in the same visual unit, and a blockquote's internal `>` lines are non-blank,
    so a whole blockquote is one block.  `coverage` accumulates a line count per
    disposition so the caller can assert NAMED == SWEPT.

    FENCED CODE IS SKIPPED, and that is a rule, not a convenience.  Inside a
    fence the corpus is showing text as literal data, not asserting it -- a `~~`
    in there would not strike anything either -- so a fence is the marked way for
    a document to reproduce a defective block verbatim without promising a strike
    of its own.  Found the way findings in this family usually are: the first
    draft of THIS repair's own report quoted the G1 block as a blockquote and
    tripped this control.  The alternative was a baseline entry per document that
    ever discusses the defect, which is a control that grows a tolerance every
    time it is right.
    """
    if coverage is None:
        coverage = {}

    def count(bucket, k=1):
        coverage[bucket] = coverage.get(bucket, 0) + k

    i = 0
    n = len(lines)
    while i < n:
        if FENCE.match(lines[i]):
            j = i + 1
            while j < n and not FENCE.match(lines[j]):
                j += 1
            j = min(j + 1, n)             # consume the closing fence
            count("fenced_code", j - i)
            i = j
            continue
        if lines[i].strip() == "":
            count("blank")
            i += 1
            continue
        j = i
        while j < n and lines[j].strip() != "" and not FENCE.match(lines[j]):
            j += 1
        count("block", j - i)
        yield i + 1, lines[i:j]
        i = j


SENTENCE_SPLIT = re.compile(r"(?<=[.!?])\s+")


def scan_text(name, text):
    """Return (hits, near_misses, coverage) for one document.

    A hit is a SENTENCE that declares a strike, quotes the sentence it is
    declaring struck, and carries no `~~`.  Sentence scope, not block scope, is
    what separates a declaration from a report: `OneThird-mg8a71-VerdictRepairs-
    Closeout.md` §0 quotes a remediation standard in one sentence and says two
    claims elsewhere "are now struck" in the next, which is a true report about
    another document and not a promise about its own text.  Block scope calls
    that a defect; sentence scope does not, and sentence scope is right.

    Sentences that declare a strike in a block that quotes something, but not in
    the same sentence, are returned as NEAR MISSES -- reported, never failed on,
    so the narrowing is visible rather than silent.
    """
    lines = text.split("\n")
    coverage = {}
    hits = []
    near = []
    for lineno, blk in blocks(lines, coverage):
        # Flatten before matching.  Prose here is hard-wrapped at ~100 columns
        # and a quoted sentence routinely straddles the wrap -- the G1 site
        # itself does.  A line-oriented match would have missed the one defect
        # this control was built for.
        flat = " ".join(l.lstrip("> ").rstrip() for l in blk)
        if STRIKE_MARKUP in flat:
            continue                      # the declaration is backed; done
        if not DECLARATION.search(flat):
            continue
        matched = False
        for sentence in SENTENCE_SPLIT.split(flat):
            if not DECLARATION.search(sentence):
                continue
            q = QUOTATION.search(sentence)
            if not q:
                continue
            quote = q.group(0).strip('*"“”').lower()
            hits.append((name, lineno, quote, flat[:160]))
            matched = True
        if not matched and QUOTATION.search(flat):
            near.append((name, lineno, flat[:120]))
    assert sum(coverage.values()) == len(lines), (
        f"{name}: coverage gap: {sum(coverage.values())} of {len(lines)} lines")
    return hits, near, coverage


def scan_corpus(rev=None):
    hits = []
    near = []
    n_docs = n_lines = 0
    if rev:
        listing = subprocess.run(
            ["git", "ls-tree", "--name-only", f"{rev}:{DOCS}"],
            capture_output=True, text=True, cwd=ROOT).stdout.split()
        names = sorted(f for f in listing if f.endswith(".md"))
    else:
        names = sorted(p.name for p in (ROOT / DOCS).glob("*.md"))
    for name in names:
        if rev:
            text = subprocess.run(["git", "show", f"{rev}:{DOCS}/{name}"],
                                  capture_output=True, text=True, cwd=ROOT).stdout
        else:
            text = (ROOT / DOCS / name).read_text(encoding="utf-8")
        h, nm, cov = scan_text(name, text)
        hits.extend(h)
        near.extend(nm)
        n_docs += 1
        n_lines += sum(cov.values())
    return names, n_docs, n_lines, hits, near


def report(rev=None):
    names, n_docs, n_lines, hits, near = scan_corpus(rev)
    where = f"at {rev}" if rev else "at HEAD"
    print("=" * 84)
    print("mg-cd04 declared-strike control — a block that declares a strike must "
          "make it")
    print("=" * 84)
    print(f"tree      : {where}")
    print(f"population: {n_docs} documents in {DOCS}/, {n_lines} lines, ALL "
          f"classified (block | fenced code | blank)")
    print(f"            the mg-8a71 live-claim control reads 1 of these {n_docs}; "
          f"that is mg-0242 G1.")
    print(f"rule      : DECLARATION + QUOTATION in the SAME SENTENCE, and no "
          f"'{STRIKE_MARKUP}' in the block")
    print(f"baseline  : {len(BASELINE)} tolerated site(s)")
    print()
    found = set()
    for name, lineno, quote, snippet in hits:
        key = (name, quote)
        found.add(key)
        state = "BASELINE" if key in BASELINE else "*** NEW ***"
        print(f"  [{state}] {name}:{lineno}")
        print(f"            declares struck: \"{quote[:70]}\"")
        print(f"            > {snippet}")
        print()
    if not hits:
        print("  no sentence in the corpus declares a strike it did not make")
        print()
    print(f"  near misses (a strike declared in a quoting BLOCK but not in the")
    print(f"  quoting SENTENCE — reported, never failed on): {len(near)}")
    for name, lineno, snippet in near:
        print(f"      {name}:{lineno}")
        print(f"          > {snippet}")
    print()
    return found


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--demonstrate":
        rev = sys.argv[2]
        print("DEMONSTRATION — the same control against a tree where G1 is present")
        print()
        found = report(rev)
        new = found - BASELINE
        print("=" * 84)
        for key in sorted(new):
            print(f"  FOUND (as intended): {key[0]} — \"{key[1][:60]}\"")
        if new:
            print(f"RESULT: the control BITES at {rev} — "
                  f"{len(new)} unmade declared strike(s).")
            return 0
        print(f"RESULT: nothing found at {rev}; this revision does not demonstrate "
              f"the defect.")
        return 1

    found = report()
    new = found - BASELINE
    gone = BASELINE - found
    for name, quote in sorted(new):
        print(f"  FAIL: a block declares a strike and does not make it: "
              f"{name} — \"{quote[:60]}\"")
    for name, quote in sorted(gone):
        print(f"  FAIL: baseline site no longer matches (re-baseline this control): "
              f"{name} — \"{quote[:60]}\"")
    print("=" * 84)
    if new or gone:
        print("RESULT: FAIL — the declared-strike set differs from the recorded")
        print("        baseline.  Either add the ~~ markup at the site, or record")
        print("        why the block is right to declare without it.")
        return 1
    print("RESULT: PASS — across the whole of docs/, every block that declares a")
    print("        sentence struck backs the declaration with ~~ markup, except the")
    print("        baselined quotations inside the audit that found the defect.")
    print("        mg-0242 finding G1 is closed at the site AND at the population.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
