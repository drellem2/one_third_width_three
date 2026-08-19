#!/usr/bin/env python3
"""mg-0242 — STRUCK vs REFUTED: does the repair apply its own standard everywhere?

WHY THIS EXISTS.  mg-fccb struck one sentence on a stated ground -- an annotation
"leaves the wrong claim in the body" -- and left the same standard unapplied at
two sites it had itself proved false.  mg-8a71 found that (F1); mg-069f fixed the
two sites.  This instrument asks the next question, which nobody has asked
mechanically: over the WHOLE arc, how many claims were proved false, and how many
of those are actually gone from live body text?  The two numbers are the finding.

FOUR PARTS.

  (A) THE LEDGER.  Every claim the mg-fccb -> mg-8a71 -> mg-069f arc proves,
      asserts or inherits as FALSE, with the site it lives at and a textual
      signature.  For each, the live/marked classifier decides whether the claim
      is still asserted in live body text.  Struck is counted against refuted.
      The classifier is deliberately the REPAIR'S OWN (imported from
      onethird_mg8a71_live_claim_control.py), so the standard being applied is
      the standard the repair set, not one this audit invented.

  (B) THE CORPUS SWEEP.  The repair's live-claim control is one file by design
      and says so.  This applies the same four signatures -- plus a fifth for the
      "single pin" sentence the repair flagged and did not act on -- to EVERY
      markdown file in docs/.  A refuted inference struck in its home document
      and left live in a consumer is the exact defect mg-fccb was written to fix,
      one document over.

  (C) MUTANT: THE EXEMPT-BLOCK TAIL.  mg-069f closed the hole where a blockquote
      could exempt itself by DECLARING "STRUCK" without the markup.  That
      tightening was applied to STRIKE blocks only; EXEMPT blocks (ANNOTATION /
      RE-DERIVATION) were still skipped ENTIRELY on the strength of a label read
      from the first three lines, with no bound on how long the block ran.  This
      constructs the mutant and reports whether the control sees it.  A control
      mutant is worthless unless it is also shown to CATCH the same sentence when
      it is genuinely live, so the paired mutant is run too.

      CLOSED by mg-cd04, and this part is now an ASSERTION rather than a report.
      All three mutants must exit 1.  When mg-0242 filed the finding M1 exited 0;
      the exemption is now per-sub-paragraph and quotation-backed, with the
      label's own reach bounded, so a sentence appended to an ANNOTATION tail is
      checked like any other.  M1 returning to exit 0 means the blind spot is
      back, and this script fails.

  (D) DELETION REVIEW.  Over-correction is the risk this audit family exists to
      name -- mg-8a71's F5 was exactly "the strike removed a true clause".  This
      lists every line the repair DELETED from a document (as opposed to added),
      so each can be adjudicated true/false at the site.

Exits non-zero if any claim in the ledger that the arc proved false is still
asserted in live body text and is not recorded here as a known, flagged
exception.

Run:  python3 scripts/onethird_mg0242_struck_vs_refuted.py
"""

import importlib.util
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
# No pinned revision is named in code.  The two history-reading modes take their
# revision from argv (`--tree <rev>`, `--deletions <rev>`) and neither runs on the
# default path, because script-controls.yml checks out at depth 1 by design and a
# step that read history there would be dead on arrival -- the mg-3934 defect,
# whose static control caught an earlier draft of this script doing exactly that.
# For the record, the revisions this audit used by hand:
#   the repair under audit         bb1cb9b   (mg-069f)
#   mg-fccb HEAD, F1's two sites   1b00147
#   the arc's base                 1b00147^

SPREAD = "docs/OneThird-L1b-Spread-Locality.md"
SELF_DOC = "OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md"

# Assertion failures collected outside the ledger's own live/baseline logic --
# the instrument standard (part A's tally, part E's detectability matrix).  Any
# entry here fails the run; see main().
FAILURES = []


def load_control():
    spec = importlib.util.spec_from_file_location(
        "lc", ROOT / "scripts/onethird_mg8a71_live_claim_control.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


LC = load_control()


# ------------------------------------------------------------------ part A ---
# Every claim the arc proves, asserts or inherits as FALSE.  `pattern` is matched
# against the live-text units of `file`; `expect` is what the repair's own record
# says the disposition is.  `instrument` records HOW the claim was removed from
# live text, because "struck" and "rewritten" are different instruments and the
# repair used both without saying so.
SIG = {sid: pred for sid, _desc, pred in LC.SIGNATURES}

LEDGER = [
    # id, file, pattern, refuted-by, expected disposition, instrument
    # C1/C2 use the CONTROL'S OWN predicates, not a pattern of this audit's
    # invention -- the point is to apply the repair's standard, not a stricter
    # one.  (A first pass used a bare /jensen/ here and flagged §2.3's CORRECTED
    # sentence, which uses Jensen legitimately; that miss is recorded in §8 of
    # the report rather than quietly fixed.)
    ("C1  §2.3 Jensen ⇒ (B) fails by Θ(n²)", SPREAD,
     SIG["S1-jensen-falsifier"], "mg-1fdb / mg-fccb", "gone",
     "strike-at-site (mg-fccb)"),
    ("C2  §2.3 (B) 'hinges on' capping m_x", SPREAD,
     SIG["S2-hinges-on-degree"], "mg-1fdb / mg-fccb", "gone",
     "strike-at-site (mg-fccb)"),
    ("C3  §3.2 'Equivalently' = the max_x m_x question", SPREAD,
     r"equivalently.*max_x m_x", "mg-fccb's own §2.3 derivation", "gone",
     "strike-at-site (mg-069f, F1)"),
    ("C4  §5 rec 2 'that non-existence IS (B)'", SPREAD,
     r"non-existence\s+\*?is\*?\s+\(b\)", "mg-fccb's own annotation", "gone",
     "strike-at-site (mg-069f, F1)"),
    ("C5  §5 rec 1 'This is the single pin'", SPREAD,
     r"this is the single pin", "mg-fccb's annotation: 'rec 1 is not a pin'",
     "LIVE — flagged, not acted on", "none (routed to pm-onethird)"),
    ("C6  §13 row 2 'restored … to the body's Finding 3.4 form'",
     "docs/OneThird-Bbias-Locality-Lemma.md",
     r"restored at all three sites", "mg-8a71 F4 (widened by mg-069f)", "gone",
     "rewrite-in-place (mg-069f, F4)"),
    ("C7  §2.3 machine-check 'over all posets on n = 3,4,5'", SPREAD,
     r"over all posets on", "mg-8a71 F2", "gone",
     "rewrite + annotation (mg-069f, F2)"),
    ("C8  mgd112 §2.2 row 'over **all** posets on n ≤ 5'",
     "docs/OneThird-mgd112-DroppedVerdict-Closeout.md",
     r"over \*\*all\*\* posets", "mg-8a71 F2", "gone",
     "rewrite + annotation (mg-069f, F2)"),
    ("C9  mgd112 §2.2 'over every poset and every reference order'",
     "docs/OneThird-mgd112-DroppedVerdict-Closeout.md",
     r"over every poset and every reference order", "mg-8a71 F2", "gone",
     "DELETION declared as a strike (mg-069f, F2); markup added mg-cd04 (G1)"),
    ("C10 mgd112 §6 'sweep over all posets n ≤ 5'",
     "docs/OneThird-mgd112-DroppedVerdict-Closeout.md",
     r"sweep over all posets", "mg-8a71 F2", "gone",
     "rewrite-in-place (mg-069f, F2)"),
]

# ------------------------------------------------- THE FIVE INSTRUMENTS (G4) ---
# mg-0242 finding G4, ticketed and closed as mg-1d03.
#
# THE FINDING.  Claims proved false in this arc were remediated FIVE different
# ways, and only the first was ever named as the standard.  The standard as
# stated -- "strike at the site; an annotation leaves the wrong claim in the
# body" -- does not distinguish the other four, so a worker who rewrote in place
# or annotated was not violating a rule: THE RULE DID NOT COVER WHAT THEY DID.
# That is why C9 could be written in good faith by an author applying the rule.
#
# G4 IS A FINDING ABOUT A MISSING STANDARD, NOT ABOUT FIVE MISTAKES.  Four of the
# five uses were sound; they were simply unnamed.  The remedy is to name all five
# and say when each is acceptable -- NOT to mandate strike-at-site everywhere.
#
# `detects` names the control that can tell this instrument apart FROM THE
# OTHERS, and it is the uncomfortable half: only two of the five are separable by
# any control in CI.  See part (E), which measures this rather than asserting it.
INSTRUMENTS = {
    "strike-at-site": dict(
        rank="PREFERRED",
        record="the wrong text stays in place, visibly wrong, inside ~~ markup",
        acceptable=(
            "always, and it is the default.  Use it whenever the false text is a "
            "SENTENCE or CLAUSE a reader could otherwise still act on: the reader "
            "sees what was believed and that it is no longer believed, at the one "
            "place they would look."),
        detects="live-claim control — only as ABSENCE FROM LIVE TEXT, which the "
                "next three produce too",
        observed="not live, and the text survives inside a ~~struck~~ span"),
    "rewrite + annotation": dict(
        rank="acceptable",
        record="the text is replaced; an ANNOTATION block quotes what was there",
        acceptable=(
            "when the false text cannot simply be struck because correct text "
            "must stand in the same position -- a table cell, a population "
            "clause, a figure inside a sentence that is otherwise true.  Striking "
            "a table cell and writing the replacement beside it makes the table "
            "unreadable; the annotation carries the record instead.  This is what "
            "mg-1d03 itself used on both G3 figures."),
        detects="NOTHING — indistinguishable from strike-at-site to every control "
                "in CI",
        observed="not live; the text survives inside an ANNOTATION/RE-DERIVATION "
                 "block or a ~~ span"),
    "rewrite-in-place": dict(
        rank="acceptable ONLY under the condition below",
        record="NONE — the corpus keeps no trace of what the text said",
        acceptable=(
            "only when the false text is not itself a finding: a DESCRIPTION that "
            "was wrong, where an audit or closeout elsewhere already carries the "
            "record.  It is NOT acceptable for a claim this arc proved false, "
            "because then the corpus's only record of the refutation is the "
            "refutation, and the thing refuted is gone.  When in doubt, this is "
            "the instrument to escalate to 'rewrite + annotation'."),
        detects="NOTHING — indistinguishable from strike-at-site to every control "
                "in CI",
        observed="not live, and the text is absent from the file entirely"),
    "DELETION declared as a strike": dict(
        rank="NOT ACCEPTABLE — this is the defect, not an instrument",
        record="claims to keep one and does not",
        acceptable=(
            "never.  A block that says text 'is struck' and carries no ~~ markup "
            "asserts a record it did not make.  This is mg-0242 finding G1 (C9), "
            "closed by mg-cd04 at the site."),
        detects="mg-cd04 declared-strike control — CORPUS-WIDE, and this is the "
                "ONE instrument any control can name",
        observed="declaration present, markup absent"),
    "none": dict(
        rank="acceptable ONLY when routed",
        record="the claim stays live and is flagged",
        acceptable=(
            "when the disposition is not the worker's to make -- an adjudication "
            "between two prior findings, as with C5.  Acceptable only if it is "
            "FLAGGED and ROUTED to a named owner and recorded in a control "
            "baseline, so 'not acted on' cannot decay into 'forgotten'."),
        detects="live-claim control, but ONLY if a signature exists for the claim "
                "-- C5 has none there and is reached only by this ledger's "
                "EXTRA_SIGNATURES",
        observed="live"),
}

# BASELINE — the ledger entries that ARE live in body text at bb1cb9b, recorded
# explicitly in the style mg-8a71 used for its own control.  A THIRD live entry
# fails the run, and a baseline entry becoming struck ALSO fails it, so repairing
# one forces a re-baseline instead of passing silently.
#
#   C5  the repair flagged this one itself and routed it to pm-onethird rather
#       than reversing mg-8a71's adjudication.  Flagged, not hidden.
#
# RE-BASELINED 2026-07-31 by mg-cd04.  C9 was the second entry: mg-069f's own
# POPULATION CORRECTION block in mgd112 §2.2 said the sentence "is struck with it"
# and did not strike it, so by the very rule mg-069f added to the control ("a
# block may not exempt itself by its label") the sentence read as live.  mg-cd04
# added the ~~ markup at the site, the baseline-disappeared gate fired exactly as
# it was built to, and C9 is removed from this set rather than left to pass
# silently.  LIVE is now 1, and it is C5 — flagged, routed, and not this
# instrument's to disposition.
KNOWN_LIVE = {
    "C5  §5 rec 1 'This is the single pin'",
}


def read(path, tree=None):
    if tree:
        return subprocess.run(["git", "show", f"{tree}:{path}"],
                              capture_output=True, text=True, cwd=ROOT).stdout
    return pathlib.Path(ROOT / path).read_text(encoding="utf-8")


def live_units_text(text):
    """(lineno, section, text) for live body text, by the repair's own rules."""
    out = []
    for lineno, section, t in LC.live_paragraphs(text.split("\n"), {}):
        out.append((lineno, section, LC.INLINE_STRIKE.sub(" ", t).lower()))
    return out


def live_units(path, tree=None):
    return live_units_text(read(path, tree))


def part_a(tree=None):
    print("=" * 96)
    print("(A) THE LEDGER — every claim the arc proved false, and whether it is gone")
    print("=" * 96)
    units = {}
    struck = live = 0
    unexpected = []
    live_ids = []
    for cid, f, pat, by, expect, instrument in LEDGER:
        if f not in units:
            units[f] = live_units(f, tree)
        test = pat if callable(pat) else (
            lambda t, rx=re.compile(pat, re.IGNORECASE): rx.search(t) is not None)
        hits = [(ln, sec) for ln, sec, t in units[f] if test(t)]
        is_live = bool(hits)
        if is_live:
            live += 1
            live_ids.append(cid)
        else:
            struck += 1
        state = "LIVE" if is_live else "gone"
        agree = "" if state in expect else "   <-- DISAGREES WITH THE RECORD"
        print(f"  {cid}")
        print(f"      file      : {f}")
        print(f"      refuted by: {by}")
        print(f"      instrument: {instrument}")
        print(f"      live now  : {state}"
              f"{'  @ lines ' + ', '.join(str(h[0]) for h in hits) if hits else ''}"
              f"{agree}")
        if is_live and cid not in KNOWN_LIVE:
            unexpected.append(cid)
        print()
    total = len(LEDGER)
    print(f"  REFUTED (claims the arc proved/inherited false) : {total}")
    print(f"  REMOVED from live body text                     : {struck}")
    print(f"  STILL LIVE                                      : {live}"
          f"   ({', '.join(c.split()[0] for c in live_ids) or '—'})")
    print()
    kinds = {}
    for cid, f, pat, by, expect, instrument in LEDGER:
        kinds[instrument.split(" (")[0]] = kinds.get(instrument.split(" (")[0], 0) + 1
    # This line read "the repair used three, and named only one" until mg-1d03,
    # over a tally that has always printed FIVE keys -- a named-vs-counted error
    # inside the line whose job is to report the count.  It is COMPUTED now.
    print(f"  BY INSTRUMENT — the arc used {len(kinds)}, and named 1 as the"
          f" standard (mg-0242 finding G4, closed by mg-1d03):")
    for k, v in sorted(kinds.items(), key=lambda kv: -kv[1]):
        spec = INSTRUMENTS.get(k)
        print(f"      {v:>2}  {k:<30} {spec['rank'] if spec else '?? NOT IN THE NAMED STANDARD'}")
    # P12 / the partition.  A sixth instrument appearing, or the counts ceasing
    # to sum to the ledger, fails the run rather than being narrated.
    unnamed = sorted(set(kinds) - set(INSTRUMENTS))
    if unnamed:
        FAILURES.append(
            f"ledger uses instrument(s) the standard does not name: {unnamed}. "
            f"Add them to INSTRUMENTS with a rank and an acceptability rule, or "
            f"use one that is named — an unnamed instrument is finding G4 again.")
    if sum(kinds.values()) != total:
        FAILURES.append(
            f"instrument tally {sum(kinds.values())} != {total} ledger entries")
    print(f"      {'':>2}  {'':<30} population: the {total} ledger entries;"
          f" grain: one instrument per entry; sum {sum(kinds.values())}")
    gone_from_baseline = KNOWN_LIVE - set(live_ids)
    return total, struck, live, unexpected, gone_from_baseline, live_ids


# ------------------------------------------------------------------ part B ---

EXTRA_SIGNATURES = LC.SIGNATURES + [
    ("S5-single-pin",
     "'the single pin' — false by mg-fccb's own annotation ('rec 1 is not a pin')",
     lambda t: "single pin" in t and "max_x m_x" in t),
]


def part_b():
    print("=" * 96)
    print("(B) CORPUS SWEEP — the same signatures over EVERY document, not one")
    print("=" * 96)
    docs = sorted((ROOT / "docs").glob("*.md"))
    total_live_units = 0
    hits = []
    for path in docs:
        for lineno, section, text in live_units(path):
            total_live_units += 1
            for sig_id, desc, pred in EXTRA_SIGNATURES:
                if pred(text):
                    hits.append((path.name, sig_id, lineno, section))
    print(f"  population: {len(docs)} documents in docs/, "
          f"{total_live_units} live text units, {len(EXTRA_SIGNATURES)} signatures")
    print(f"  (the repair's own control sweeps 1 document of these {len(docs)})")
    print()
    by_file = {}
    for fname, sig_id, lineno, section in hits:
        by_file.setdefault(fname, []).append((sig_id, lineno, section))
    for fname in sorted(by_file):
        print(f"  {fname}")
        for sig_id, lineno, section in by_file[fname]:
            print(f"      {sig_id:<26} line {lineno:>4}  {section[:60]}")
    if not hits:
        print("  no live assertion of any signature anywhere in docs/")
    print()
    own = [h for h in hits if h[0] == SELF_DOC]
    print(f"  live hits corpus-wide: {len(hits)} in {len(by_file)} document(s)")
    print(f"    of which in THIS audit's own report ({SELF_DOC}): {len(own)}")
    print(f"    in the pre-existing corpus                        : {len(hits) - len(own)}")
    print("  Every hit outside docs/OneThird-L1b-Spread-Locality.md was read at the")
    print("  site: all are QUOTATIONS inside audit and closeout documents diagnosing")
    print("  the refuted claim -- propagation tables, consumer ledgers, quoted")
    print("  sentences -- not assertions.  The one substantive hit is S5 in")
    print("  Spread-Locality (ledger entry C5).  See the report's section 8.")
    return len(docs), total_live_units, hits


# ------------------------------------------------------------------ part C ---

MUTANT_SENTENCE = (
    "Lemma (B) therefore hinges on whether the frozen structure caps the "
    "per-element inversion degree `m_x`, and by Jensen a large `m_x` makes (B) "
    "fails by Θ(n²)."
)


def run_control(path):
    r = subprocess.run(
        [sys.executable, str(ROOT / "scripts/onethird_mg8a71_live_claim_control.py"),
         str(path)],
        capture_output=True, text=True)
    return r.returncode


def part_c(tmpdir):
    print("=" * 96)
    print("(C) MUTANTS — is the exemption bounded by anything?")
    print("=" * 96)
    src = (ROOT / SPREAD).read_text(encoding="utf-8")
    lines = src.split("\n")

    # locate the LAST line of the longest ANNOTATION blockquote
    best = None
    i = 0
    while i < len(lines):
        if lines[i].startswith(">"):
            j = i
            while j < len(lines) and lines[j].startswith(">"):
                j += 1
            head = " ".join(lines[i:i + 3]).lower()
            if any(mk.lower() in head for mk in LC.EXEMPT_MARKERS):
                if best is None or (j - i) > (best[1] - best[0]):
                    best = (i, j)
            i = j
            continue
        i += 1
    assert best, "no ANNOTATION blockquote found"
    start, end = best
    print(f"  longest ANNOTATION blockquote: lines {start+1}-{end} "
          f"({end - start} lines), label read from lines {start+1}-{start+3}")

    # M1: the refuted sentence appended to the TAIL of that exempt block
    m1 = lines[:end] + ["> ", "> " + MUTANT_SENTENCE] + lines[end:]
    p1 = tmpdir / "mutant_exempt_tail.md"
    p1.write_text("\n".join(m1), encoding="utf-8")
    rc1 = run_control(p1)

    # M2: the SAME sentence as an ordinary paragraph — the control must catch it,
    # otherwise M1 proves nothing about the exemption
    m2 = lines[:end] + ["", MUTANT_SENTENCE] + lines[end:]
    p2 = tmpdir / "mutant_plain_paragraph.md"
    p2.write_text("\n".join(m2), encoding="utf-8")
    rc2 = run_control(p2)

    # M3: the same sentence appended to the tail of a STRIKE block — mg-069f
    # closed this one, so it must be caught; the contrast is the whole point
    sbest = None
    i = 0
    while i < len(lines):
        if lines[i].startswith(">"):
            j = i
            while j < len(lines) and lines[j].startswith(">"):
                j += 1
            head = " ".join(lines[i:i + 3]).lower()
            if (any(mk.lower() in head for mk in LC.STRIKE_MARKERS)
                    and not any(mk.lower() in head for mk in LC.EXEMPT_MARKERS)):
                sbest = (i, j)
                break
            i = j
            continue
        i += 1
    rc3 = None
    if sbest:
        m3 = lines[:sbest[1]] + ["> ", "> " + MUTANT_SENTENCE] + lines[sbest[1]:]
        p3 = tmpdir / "mutant_strike_tail.md"
        p3.write_text("\n".join(m3), encoding="utf-8")
        rc3 = run_control(p3)

    print()
    print(f"  M1  refuted sentence in the TAIL of an ANNOTATION block -> exit {rc1}"
          f"   {'MISSED' if rc1 == 0 else 'caught'}")
    print(f"  M2  same sentence as a plain paragraph                  -> exit {rc2}"
          f"   {'MISSED' if rc2 == 0 else 'caught'}")
    if rc3 is not None:
        print(f"  M3  same sentence in the TAIL of a STRIKE block         -> exit {rc3}"
              f"   {'MISSED' if rc3 == 0 else 'caught'}")
    return rc1, rc2, rc3, (start + 1, end)


# ------------------------------------------------------------------ part E ---
# mg-0242 finding G4, closed by mg-1d03.  The five instruments are NAMED in
# INSTRUMENTS above; this part MEASURES which of them any control can tell apart.
#
# The measurement is the point.  "Only strike-at-site is named as the standard"
# is a statement about the rule; "four of the five are unpoliced by construction"
# is a statement about the instruments, and it is the one that decides how a
# green run should be read.  It is measured here rather than narrated, by
# remediating ONE refuted sentence five different ways in a copy of the
# controlled document and running both corpus controls over each.


def load_declared_strike_control():
    spec = importlib.util.spec_from_file_location(
        "dsc", ROOT / "scripts/onethird_mgcd04_declared_strike_control.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def instrument_forms():
    """The same refuted sentence, remediated one way per instrument.

    Population: the five instruments of INSTRUMENTS.  Grain: one mutant document
    per instrument, each differing from the controlled document in exactly the
    lines listed here.
    """
    q = f'"{MUTANT_SENTENCE}"'
    return [
        ("strike-at-site", ["", f"~~{MUTANT_SENTENCE}~~"]),
        ("rewrite + annotation",
         ["", "> **ANNOTATION (mutant).** The claim below was refuted and the",
          "> sentence rewritten; the original read:",
          ">", f"> {q}"]),
        # the true replacement text leaves NO trace of the claim: the mutant is
        # the unmodified document, and that is exactly what makes it invisible.
        ("rewrite-in-place", []),
        ("DELETION declared as a strike",
         ["", "> **POPULATION CORRECTION (mutant).** The sentence that followed —",
          f"> {q} — is struck with it."]),
        ("none", ["", MUTANT_SENTENCE]),
    ]


def part_e(tmpdir):
    print("=" * 96)
    print("(E) INSTRUMENT DETECTABILITY — which of the five can any control see?")
    print("=" * 96)
    dsc = load_declared_strike_control()
    base = (ROOT / SPREAD).read_text(encoding="utf-8").split("\n")
    print(f"  method: one refuted sentence, remediated five ways in a copy of")
    print(f"          {SPREAD},")
    print("          then both corpus controls run over each copy.")
    print("          population: the 5 named instruments; grain: one mutant per")
    print("          instrument, 2 control verdicts per mutant.")
    print()
    # MEASURE FIRST, JUDGE AFTER.  A first draft of this table decided each row's
    # verdict against the rows already seen, so whichever instrument of an
    # indistinguishable set ran first was labelled SEPARATED -- an order-dependent
    # readout, in a part whose subject is readouts that mislead.  The grouping is
    # computed from the complete matrix now, and the column is read off it.
    seen = {}
    for name, extra in instrument_forms():
        text = "\n".join(base + extra)
        p = tmpdir / f"instr_{name.replace(' ', '_').replace('+', 'and')}.md"
        p.write_text(text, encoding="utf-8")
        lc_rc = run_control(p)
        ds_hits, _near, _cov = dsc.scan_text(p.name, text)
        seen[name] = (lc_rc, len(ds_hits))

    # Group the instruments by the verdict PAIR they produce.  Any group of size
    # > 1 is a set of instruments no control in CI can tell apart -- so a green
    # run cannot mean "the standard was followed".
    groups = {}
    for name, sig in seen.items():
        groups.setdefault(sig, []).append(name)

    print(f"  {'instrument':<30} {'live-claim':<12} {'declared-strike':<16} verdict")
    print(f"  {'-'*30} {'-'*12} {'-'*16} {'-'*30}")
    for name, _extra in instrument_forms():
        lc_rc, n_hits = seen[name]
        peers = [g for g in groups[(lc_rc, n_hits)] if g != name]
        verdict = ("separable" if not peers
                   else "INDISTINGUISHABLE from " + ", ".join(peers))
        print(f"  {name:<30} exit {lc_rc:<7} {n_hits:<16} {verdict}")
    print()
    blind = [g for g in groups.values() if len(g) > 1]
    for sig, names in sorted(groups.items()):
        tag = "INDISTINGUISHABLE" if len(names) > 1 else "separable"
        print(f"  (live-claim exit {sig[0]}, declared-strike hits {sig[1]}):"
              f" {tag} — {', '.join(names)}")
    print()
    print("  WHAT THIS MEANS FOR A GREEN RUN.  The controls answer 'is this claim")
    print("  asserted in live body text' and 'does a block promise a strike it did")
    print("  not make'.  Neither asks WHICH instrument was used, so instruments")
    print("  that all end with the claim out of live text are one thing to them.")
    print("  Green therefore means NO UN-REMEDIATED CLAIM, never NO UNRECORDED")
    print("  REMEDIATION.  The instrument column of part (A) is the only record")
    print("  that distinguishes them, and it is maintained by hand.")
    if not blind:
        FAILURES.append(
            "part (E) found every instrument separable — that contradicts G4 as "
            "filed.  Either a control gained discrimination (good: update "
            "INSTRUMENTS[...]['detects'] and this check) or the mutants stopped "
            "exercising the instruments they name.")
    return seen, groups


# ------------------------------------------------------------------ part D ---


def part_d(rev):
    """The deletion review.  Runs ONLY when a revision is passed explicitly.

    NOT on the default path, and that is deliberate.  script-controls.yml checks
    out at actions/checkout's default depth 1, on purpose and at length; a step
    that read a pinned revision there would be dead on arrival in CI however
    correct it is locally.  That is precisely the mg-3934 defect, and mg-3934's
    static control caught this script doing it -- so the history read is now
    behind `--deletions <rev>`, run by hand, with the adjudication written up in
    the report rather than recomputed on every push.
    """
    print()
    print("=" * 96)
    print("(D) DELETION REVIEW — every line the repair removed, for adjudication")
    print("=" * 96)
    if not rev:
        print("  skipped on the default path (this job checks out at depth 1).")
        print("  Run it explicitly against the repair commit:")
        print("      python3 scripts/onethird_mg0242_struck_vs_refuted.py"
              " --deletions bb1cb9b")
        print("  Adjudication of all 38 deleted lines: §6 of")
        print("  docs/OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md")
        return []
    out = subprocess.run(
        ["git", "show", rev, "--", "docs/", ".github/"],
        capture_output=True, text=True, cwd=ROOT).stdout
    dels = [l[1:] for l in out.split("\n")
            if l.startswith("-") and not l.startswith("---")]
    dels = [d for d in dels if d.strip()]
    print(f"  document/CI lines DELETED by {rev}: {len(dels)}")
    for d in dels:
        print(f"      - {d.strip()[:110]}")
    return dels


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--deletions":
        part_d(sys.argv[2])
        return 0
    if len(sys.argv) > 2 and sys.argv[1] == "--tree":
        rev = sys.argv[2]
        print("=" * 96)
        print(f"DEMONSTRATION — the ledger at {rev}, where the F1 defect is present")
        print("=" * 96)
        total, struck, live, unexpected, gone, there = part_a(tree=rev)
        here = part_a()[5]
        print(f"  at {rev}: REFUTED {total}, REMOVED {struck}, LIVE {live}")
        print()
        # mg-cd04: the drift used to be narrated ("the two sites mg-069f struck
        # are the difference").  It is now COMPUTED, because the narration was
        # short: five claims left live text between these two trees, not two.
        # Same ledger, same classifier, different commit — so the difference has
        # to be named claim by claim or the number means nothing.
        moved = [c for c in there if c not in here]
        arrived = [c for c in here if c not in there]
        print(f"  LIVE at {rev} : {', '.join(c.split()[0] for c in there) or '—'}")
        print(f"  LIVE at HEAD    : {', '.join(c.split()[0] for c in here) or '—'}")
        print(f"  LEFT live text  : {', '.join(c.split()[0] for c in moved) or '—'}"
              f"   ({len(moved)} claims — this is the drift, itemised)")
        print(f"  ENTERED live text: {', '.join(c.split()[0] for c in arrived) or '—'}")
        print()
        print("  The reading holds: every claim in LEFT was removed by a disposition")
        print("  in the arc, and nothing ENTERED.  The drift is the repair working.")
        for cid in moved:
            inst = next(l[5] for l in LEDGER if l[0] == cid)
            print(f"      {cid.split()[0]:<4} {inst}")
        return 0 if live > len(here) else 1

    total, struck, live, unexpected, gone, live_ids = part_a()
    print()
    ndocs, nunits, hits = part_b()
    print()
    with tempfile.TemporaryDirectory(prefix="mg0242-mutants-") as td:
        rc1, rc2, rc3, span = part_c(pathlib.Path(td))
        print()
        seen, groups = part_e(pathlib.Path(td))
    part_d(None)

    print()
    print("=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  count REFUTED : {total}")
    print(f"  count STRUCK  : {struck}   (removed from live body text)")
    print(f"  count LIVE    : {live}   "
          f"({'all in the baseline' if not unexpected else 'UNBASELINED: ' + ', '.join(unexpected)})")
    print(f"  corpus-wide live hits of the refuted inference: {len(hits)}")
    print(f"  exempt-block tail mutant: exit {rc1} "
          f"({'the exemption is UNBOUNDED' if rc1 == 0 else 'bounded'});"
          f" paired live-paragraph mutant: exit {rc2};"
          f" strike-block tail mutant: exit {rc3}")
    blind = max((len(g) for g in groups.values()), default=0)
    print(f"  remediation instruments in use: {len(INSTRUMENTS)}; named as the"
          f" standard: 1 (strike-at-site).")
    print(f"  largest set of instruments NO control in CI can tell apart: {blind}."
          f"  A green run below means NO UN-REMEDIATED CLAIM.  It does not, and")
    print("  cannot, mean every remediation used the preferred instrument.")
    rc = 0
    if FAILURES:
        print("\nRESULT: FAIL — the remediation standard is violated:")
        for f in FAILURES:
            print(f"          {f}")
        rc = 1
    if unexpected:
        print("\nRESULT: FAIL — a refuted claim is live in body text and is not in")
        print("        the baseline.  Either strike it or record why it stands.")
        rc = 1
    if gone:
        print("\nRESULT: FAIL — baseline entr(y|ies) no longer live; re-baseline:")
        for g in sorted(gone):
            print(f"          {g}")
        rc = 1
    # mg-cd04: G2 is closed, so the mutants are now a REGRESSION TEST, not a
    # report.  All three must be caught.  M1 was the finding (exit 0 at mg-0242);
    # M2 and M3 were already caught and are kept because a mutant that is missed
    # proves nothing unless the same sentence is demonstrably catchable.
    missed = [name for name, code in
              (("M1 exempt-block tail", rc1),
               ("M2 plain paragraph", rc2),
               ("M3 strike-block tail", rc3)) if code == 0]
    if missed:
        print("\nRESULT: FAIL — the control missed a mutant it must catch: "
              + ", ".join(missed) + ".")
        if rc1 == 0:
            print("        M1 missed means mg-0242 finding G2 has REGRESSED: an")
            print("        ANNOTATION label is exempting a block on its own word")
            print("        again.  See onethird_mg8a71_live_claim_control.exempt_partition.")
        rc = 1
    if rc == 0:
        print("\nRESULT: PASS — the ledger matches its recorded baseline, and all")
        print("        three mutants are caught (mg-0242 G2 closed by mg-cd04).")
    return rc


if __name__ == "__main__":
    sys.exit(main())
