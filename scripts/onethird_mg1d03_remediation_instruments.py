#!/usr/bin/env python3
"""mg-1d03 — mg-0242 G4: FIVE remediation instruments are in use, ONE is named.

WHY THIS EXISTS.  The mg-fccb -> mg-8a71 -> mg-069f arc proved ten claims false
and removed them from live body text five different ways:

    strike-at-site x4,  rewrite-in-place x2,  rewrite + annotation x2,
    deletion declared as a strike x1,  none (flagged and routed) x1.

Only STRIKE-AT-SITE was ever named as the standard.  mg-0242 G4:

    "The control enforces one remedy while the practice uses five, so four of
     them are unpoliced by construction.  That is why C9 could be written in
     good faith: a worker who rewrote in place, or annotated, was not violating
     a rule -- the rule did not cover what they did."

G4 is a finding about a MISSING STANDARD, not about five mistakes, and mg-0242
says so explicitly: do not resolve it by mandating strike-at-site everywhere
without checking the four other uses were wrong.  They were not.  Each of the
four is right in a case the standard has to describe, and this script is where
the standard lives in executable form.

THREE PARTS.

  (A) THE STANDARD.  All five instruments, what each does, WHEN each is
      acceptable, and which control can SEE it.  The set is asserted against the
      instrument column of the mg-0242 ledger -- so "five" is a COUNT of the
      ledger, not a number in a sentence.  Population: the 10 ledger entries of
      onethird_mg0242_struck_vs_refuted.py part (A).  Grain: one instrument key
      per entry.

  (B) THE DETECTION MATRIX, BY MUTATION.  The "which control can see it" column
      is the load-bearing one and is the one a document cannot be trusted on, so
      it is not asserted -- it is MEASURED.  One refuted claim (ledger C3, §3.2's
      "Equivalently") is remediated by each instrument in turn, in a scratch copy
      of the corpus, and both controls are run over each mutant.  Population: 7
      mutants x 2 controls = 14 process exit codes.  Grain: one exit code.

      A mutant matrix is worthless without a positive control, so the claim is
      also RESTORED LIVE and unstruck (I6): a run where the live-claim control
      does not exit 1 proves the other six rows measured nothing.

  (C) THE REACH STATEMENT.  mg-0242: "If the control can only see strike-at-site,
      say so at the point it reports -- otherwise a green control means 'no
      un-struck claims' and is read as 'no unremediated claims'."  This asserts
      the live-claim control's own report block says which of the five it can
      distinguish, by running it and reading its output.  Before mg-1d03 that
      output contained the word "instrument" 0 times.

Exits non-zero if the ledger uses an instrument the standard does not name, if
the measured detection matrix differs from the standard's claim, or if the
live-claim control's report no longer states its reach.

Run:  python3 scripts/onethird_mg1d03_remediation_instruments.py
"""

import contextlib
import importlib.util
import io
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
SPREAD = "docs/OneThird-L1b-Spread-Locality.md"
LIVE_CLAIM = "scripts/onethird_mg8a71_live_claim_control.py"
DECLARED_STRIKE = "scripts/onethird_mgcd04_declared_strike_control.py"
LEDGER = "scripts/onethird_mg0242_struck_vs_refuted.py"

FAILURES = []

# ---------------------------------------------------------------------------
# (A) THE STANDARD.  `key` is the instrument key as the ledger writes it.
# `detectable` is a CLAIM, and part (B) measures it.
#
# THE STANDARD IS strike-at-site.  Not because the other four are wrong, but
# because it is the only one that leaves the refuted claim WHERE IT WAS SAID,
# marked as false: a reader who arrives carrying the old claim finds it and sees
# it refuted, a consumer citing it can still locate it, and -- the reason it is
# the standard rather than merely the nicest -- it is the only instrument that
# leaves a mechanical trace, so it is the only one a control can confirm was
# used.  The other four are acceptable in the cases named below; what is never
# acceptable is a refuted claim leaving live text with no trace at all, which is
# the one case the whole family of controls is blind to (row I4 of part B).
STANDARD = "strike-at-site"

INSTRUMENTS = [
    dict(key="strike-at-site",
         does="`~~...~~` at the site, plus a block saying who struck it and why",
         when="THE STANDARD.  Use for any claim that was ASSERTED and is now "
              "known false, whenever the sentence can stay on the page.",
         detectable="live-claim: the claim is no longer live AND the markup is "
                    "at the site; declared-strike: a declaration is backed"),
    dict(key="rewrite-in-place",
         does="the false sentence is replaced by a true one; no trace remains",
         when="Acceptable when the defect is a MISSTATEMENT of a fact that is "
              "otherwise sound -- a wrong population name, a wrong figure, a "
              "wrong grain -- so there is no refuted inference to preserve and "
              "the corrected sentence is the whole content.  NOT acceptable for "
              "a refuted inference: the reader who remembers it finds nothing.",
         detectable="neither control can tell this from strike-at-site"),
    dict(key="rewrite + annotation",
         does="rewrite-in-place plus a dated block naming what changed and why",
         when="Preferred over a bare rewrite whenever the claim was CONSUMED "
              "elsewhere or cited as evidence: the annotation is what lets a "
              "consumer notice.  Required when the rewrite changes a number "
              "another document quotes.",
         detectable="neither control can tell this from strike-at-site"),
    dict(key="DELETION declared as a strike",
         does="the sentence is removed; a block declares it struck",
         when="Acceptable only when the sentence has NO true residue and the "
              "deletion is declared at the site.  An UNDECLARED deletion is "
              "invisible to every control in CI (part B, row I4) and is the one "
              "instrument this standard forbids outright.",
         detectable="declared-strike: DETECTED when the declaration carries no "
                    "`~~` markup -- this is mg-0242 G1, and it is the only "
                    "instrument distinction any control in CI can make"),
    dict(key="none",
         does="the claim is left live, flagged, and routed to an owner",
         when="Acceptable only when the disposition is CONTESTED or belongs to "
              "another owner (ledger C5: mg-069f declined to reverse mg-8a71's "
              "adjudication and routed it to pm-onethird).  Requires an entry "
              "in the ledger's KNOWN_LIVE with the routee named -- an unflagged "
              "'none' is just an unremediated claim.",
         detectable="live-claim: DETECTED, the claim is still live -- but only "
                    "in the one document that control reads"),
]


def load(name, relpath, root=None):
    spec = importlib.util.spec_from_file_location(name, ROOT / relpath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    if root is not None:
        mod.ROOT = root
    return mod


def part_a():
    print("=" * 96)
    print("(A) THE STANDARD — all five instruments, and the ledger they are "
          "counted from")
    print("=" * 96)
    led = load("led", LEDGER)
    used = {}
    for entry in led.LEDGER:
        key = entry[5].split(" (")[0]
        used[key] = used.get(key, 0) + 1
    print(f"  POPULATION : the {len(led.LEDGER)} ledger entries of "
          f"{LEDGER} part (A)")
    print(f"  GRAIN      : one instrument key per entry")
    print(f"  COUNTED    : {len(used)} distinct instruments over "
          f"{sum(used.values())} entries")
    print()
    named = {i["key"] for i in INSTRUMENTS}
    for inst in INSTRUMENTS:
        n = used.get(inst["key"], 0)
        star = "  <== THE STANDARD" if inst["key"] == STANDARD else ""
        print(f"  [{n} use(s)]  {inst['key']}{star}")
        print(f"      does      : {inst['does']}")
        print(f"      when      : {inst['when']}")
        print(f"      detectable: {inst['detectable']}")
        print()
    unnamed = set(used) - named
    unused = named - set(used)
    if unnamed:
        FAILURES.append(f"the ledger uses instrument(s) this standard does not "
                        f"name: {sorted(unnamed)}")
        print(f"  [GAP ] the ledger uses {sorted(unnamed)}, which this standard "
              f"does not name")
    if unused:
        print(f"  note: {sorted(unused)} named here with 0 ledger uses "
              f"(the standard describes the case, the arc did not hit it)")
    if not unnamed:
        print(f"  [OK  ] every instrument the ledger uses is named here, and the "
              f"standard is {STANDARD!r}")
    print()
    return used


# ---------------------------------------------------------------------------
# (B) THE DETECTION MATRIX
#
# The claim under remediation is ledger C3 -- §3.2's "Equivalently: can max_x m_x
# ..." -- which mg-069f struck at the site.  It is the right subject because it
# IS one of the arc's refuted claims and the live-claim control has a signature
# for it (S3), so a control that misses it is missing something it was built to
# catch.

STRUCK_LINE = ("> ~~Equivalently: can `max_x m_x = ω(1)` (indeed `Θ(n)`) with "
               "`E[inv_e] = O(n)`, δ < 1/3, width 3?~~")
LIVE_LINE = ("> Equivalently: can `max_x m_x = ω(1)` (indeed `Θ(n)`) with "
             "`E[inv_e] = O(n)`, δ < 1/3, width 3?")
REWRITE_LINE = ("> The second display asks a DIFFERENT question from the first: "
                "the quantity a falsifier must make large is the per-element "
                "bias `b_x`, not the inversion degree.")
ANNOTATION = [
    "",
    "> ### ⚠️ ANNOTATION (mutant, mg-1d03): the display above was rewritten in "
    "place, not struck.",
    "> The earlier form equated the chain-cross question with a degree question; "
    "this document had already proved they are different.",
    "",
]
DECLARATION_SHORT = [
    "",
    "> **POPULATION CORRECTION (mutant, mg-1d03).** The display "
    "\"Equivalently: can the bimodal chain-cross be ruled out by a degree "
    "bound?\" is struck with it.",
    "",
]
DECLARATION_VERBATIM = [
    "",
    "> **POPULATION CORRECTION (mutant, mg-1d03).** The display "
    "\"Equivalently: can `max_x m_x = ω(1)` (indeed `Θ(n)`) with "
    "`E[inv_e] = O(n)`, δ < 1/3, width 3?\" is struck with it.",
    "",
]

MUTANTS = [
    ("I1  strike-at-site (HEAD, unmutated)", "strike-at-site",
     lambda ls, i: ls),
    ("I2  rewrite-in-place", "rewrite-in-place",
     lambda ls, i: ls[:i] + [REWRITE_LINE] + ls[i + 1:]),
    ("I3  rewrite + annotation", "rewrite + annotation",
     lambda ls, i: ls[:i] + [REWRITE_LINE] + ANNOTATION + ls[i + 1:]),
    ("I4  deletion, UNDECLARED", "DELETION declared as a strike",
     lambda ls, i: ls[:i] + ls[i + 1:]),
    ("I5a deletion, declared (quotes a short form)",
     "DELETION declared as a strike",
     lambda ls, i: ls[:i] + DECLARATION_SHORT + ls[i + 1:]),
    ("I5b deletion, declared (quotes the sentence verbatim)",
     "DELETION declared as a strike",
     lambda ls, i: ls[:i] + DECLARATION_VERBATIM + ls[i + 1:]),
    ("I6  none — the claim RESTORED LIVE (positive control)", "none",
     lambda ls, i: ls[:i] + [LIVE_LINE] + ls[i + 1:]),
]

# What part (A)'s `detectable` column amounts to, as exit codes.  Recorded here
# so a change in either control's reach fails this script instead of quietly
# widening or narrowing what a green run means.
#
# mg-1d03 predictions P7-P9 were written against these rows before any mutant
# was built.  P7 and P9 were confirmed; P8 was confirmed on I5a and REFUTED on
# I5b, and the refutation is a finding: a declaration that quotes the refuted
# sentence verbatim reads to the live-claim control as an assertion of it.  The
# outcomes are in docs/OneThird-mg1d03-G3G4-Repair.md §0; the table below is the
# measurement, not the prediction.
EXPECTED = {
    "I1  strike-at-site (HEAD, unmutated)": (0, 0),
    "I2  rewrite-in-place": (0, 0),
    "I3  rewrite + annotation": (0, 0),
    "I4  deletion, UNDECLARED": (0, 0),
    "I5a deletion, declared (quotes a short form)": (0, 1),
    "I5b deletion, declared (quotes the sentence verbatim)": (1, 1),
    "I6  none — the claim RESTORED LIVE (positive control)": (1, 0),
}


def run_live_claim(path):
    r = subprocess.run([sys.executable, str(ROOT / LIVE_CLAIM), str(path)],
                       capture_output=True, text=True)
    return r.returncode


def run_declared_strike(corpus_root):
    """The declared-strike control over a scratch corpus, as `main()` scores it."""
    mod = load("ds_mutant", DECLARED_STRIKE, root=corpus_root)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        found = mod.report()
    new = found - mod.BASELINE
    gone = mod.BASELINE - found
    return 1 if (new or gone) else 0


def part_b(tmp):
    print("=" * 96)
    print("(B) THE DETECTION MATRIX — measured by mutation, not asserted")
    print("=" * 96)
    src = (ROOT / SPREAD).read_text(encoding="utf-8")
    lines = src.split("\n")
    idx = [i for i, l in enumerate(lines) if l.strip() == STRUCK_LINE.strip()]
    if len(idx) != 1:
        FAILURES.append(f"the C3 site is not where this script expects it: "
                        f"{len(idx)} matches of the struck line in {SPREAD}")
        print(f"  [GAP ] expected exactly 1 occurrence of the C3 struck line, "
              f"found {len(idx)}")
        return {}
    i = idx[0]
    print(f"  subject   : ledger C3, {SPREAD}:{i+1} — §3.2's \"Equivalently\", "
          f"struck at the site by mg-069f")
    print(f"  POPULATION: {len(MUTANTS)} mutants x 2 controls = "
          f"{2*len(MUTANTS)} process exit codes")
    print(f"  GRAIN     : one exit code per (mutant x control)")
    print()
    print(f"  {'mutant':<54} {'live-claim':>11} {'declared-strike':>16}")
    print(f"  {'-'*54} {'-'*11:>11} {'-'*16:>16}")
    measured = {}
    for label, instrument, mutate in MUTANTS:
        corpus = tmp / label.split()[0]
        shutil.copytree(ROOT / "docs", corpus / "docs")
        target = corpus / SPREAD
        target.write_text("\n".join(mutate(lines, i)), encoding="utf-8")
        rc_lc = run_live_claim(target)
        rc_ds = run_declared_strike(corpus)
        measured[label] = (rc_lc, rc_ds)
        want = EXPECTED.get(label)
        agree = "" if want == (rc_lc, rc_ds) else \
            f"   <-- expected {want}, measured {(rc_lc, rc_ds)}"
        print(f"  {label:<54} {rc_lc:>11} {rc_ds:>16}{agree}")
        if want != (rc_lc, rc_ds):
            FAILURES.append(f"{label}: expected exit codes {want}, measured "
                            f"{(rc_lc, rc_ds)}")
    print()
    pos = measured.get("I6  none — the claim RESTORED LIVE (positive control)")
    if pos and pos[0] != 1:
        FAILURES.append("the positive control did not bite: the live-claim "
                        "control exited 0 on a mutant that asserts the refuted "
                        "claim in plain body text, so no row above measures "
                        "anything")
        print("  [GAP ] positive control I6 did not bite — the matrix is void")
    else:
        print("  positive control I6 bites: the live-claim control DOES catch this")
        print("  claim when it is live, so the zeros above are reach, not blindness.")
    print()
    print("  WHAT THE MATRIX SAYS, in one line: of the five instruments, the")
    print("  controls in CI distinguish exactly ONE boundary -- a strike DECLARED")
    print("  but not MADE.  Strike-at-site, rewrite-in-place, rewrite+annotation")
    print("  and an UNDECLARED DELETION are pairwise indistinguishable to both.")
    print("  A green live-claim run means 'no refuted claim is live in this one")
    print("  document'.  It does NOT mean 'every refutation was remediated', and")
    print("  it cannot mean 'remediated to the standard'.")
    print()
    return measured


# ---------------------------------------------------------------------------
# (C) THE REACH STATEMENT


def part_c():
    print("=" * 96)
    print("(C) THE REACH STATEMENT — does the control say what its green means?")
    print("=" * 96)
    r = subprocess.run([sys.executable, str(ROOT / LIVE_CLAIM)],
                       capture_output=True, text=True)
    out = r.stdout
    n_instrument = out.lower().count("instrument")
    # the count must be the COUNT, not a word: the reach line is regenerated
    # against len(INSTRUMENTS), so adding a sixth instrument here without saying
    # so there fails this check rather than silently widening what green means
    names_five = f"{len(INSTRUMENTS)} remediation instruments" in out
    print(f"  POPULATION: the stdout of {LIVE_CLAIM} at HEAD "
          f"({len(out.splitlines())} lines, exit {r.returncode})")
    print(f"  GRAIN     : word occurrences")
    print(f"  'instrument' occurs      : {n_instrument}   "
          f"(0 before mg-1d03 — the report said nothing about which "
          f"remediations it can see)")
    print(f"  names how many there are : {names_five}")
    ok = n_instrument > 0 and names_five
    print(f"  [{'OK  ' if ok else 'GAP '}] the report "
          f"{'states' if ok else 'does NOT state'} its reach at the point it "
          f"reports")
    if not ok:
        FAILURES.append("the live-claim control's report does not state which of "
                        "the five remediation instruments it can see; a green run "
                        "then reads as 'no unremediated claims'")
    print()


def main():
    print("=" * 96)
    print("mg-1d03 — mg-0242 G4: five remediation instruments, one standard")
    print("=" * 96)
    print()
    part_a()
    with tempfile.TemporaryDirectory() as td:
        part_b(pathlib.Path(td))
    part_c()
    print("=" * 96)
    if FAILURES:
        print(f"RESULT: FAIL — {len(FAILURES)}:")
        for f in FAILURES:
            print(f"  - {f}")
        return 1
    print("RESULT: PASS — every instrument the ledger uses is named in the")
    print("        standard, the standard's detection claims match what mutation")
    print("        measures, and the live-claim control states its reach where it")
    print("        reports.  mg-0242 G4 is answered: the standard is")
    print(f"        {STANDARD!r}, the other four are acceptable in the cases")
    print("        named above, and exactly one boundary is machine-detectable.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
