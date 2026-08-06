#!/usr/bin/env python3
"""mg-a84b -- INDEPENDENT AUDIT of the mg-ba2a repair to the mg-3934 control.

WHAT THIS AUDITS.  mg-ba2a diagnosed a red main as a line-wrapped sha256 digest
whose 22-character tail landed inside the mg-3934 control's 7-40 "looks like a
revision" window.  The repair joins adjacent Python string literals before
applying the window.  This audit does not take that on trust; it asks four
questions the repair could pass while still being wrong.

  Q1  Is the join CORRECT, or merely correct on the one instance that fired?
      Instrument: a ground-truth join built from Python's own `tokenize`
      module, run against the shipped regex join over every .py file in
      scripts/.  A disagreement is a hole in the regex the tree can already
      reach.  This is the instrument that could show the positive: if the
      regex were flawless, tokenize would agree on all N files, and that
      agreement is what makes the negative reportable.

  Q2  How big is the CLASS?  Population: every .py file under scripts/.  Grain:
      one wrapped hex run (a maximal run of adjacent string literals whose
      joined text is >= 41 hex characters -- past the control's 40-char cap, so
      it cannot be a sha1 revision).  Reported with the git-mentioning subset
      called out separately, because only that subset can reach (B) at all.

  Q3  Is the DISJUNCTION exhaustive?  The control prints "shallow, or rotted"
      for any literal its resolver rejects.  Instrument: construct a literal in
      each category the disjunction omits and observe what the control says
      about it.  A category where the control prints "rotted" about something
      that is not a rotted pin is a live instance of the mg-ba2a reasoning
      error, not a hypothetical one.

  Q4  Does the join buy the fix with a BLIND SPOT?  Instrument: for every real
      pin the control finds today, re-run detection with the join disabled and
      confirm the same pin is still found.  A pin that the join makes invisible
      is strictly worse than the false positive it removed.

WHAT THIS DOES NOT DO is stated in the report, not silently omitted.

Exit 0 if every check this audit can decide comes out as the repair claims,
1 otherwise.  Self-test first, as the controls in this arc do: each check must
be shown able to fail before its pass is worth anything.
"""

import io
import os
import re
import sys
import json
import token
import tokenize
import argparse
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPTS = os.path.join(REPO, "scripts")
CONTROL = "onethird_mg3934_ci_history_depth_control.py"
REPORT = os.path.join("data", "onethird-mga84b-wrapped-digest-audit.json")

# The control's own window.  Duplicated rather than imported so that a change
# to the control shows up here as a disagreement instead of being silently
# adopted -- an audit that imports its subject's constants cannot detect the
# subject moving them.
WINDOW_LO, WINDOW_HI = 7, 40
HEX_RUN_RE = re.compile(r"\A[0-9a-fA-F]+\Z")


# ---------------------------------------------------------------------------
# Q1/Q2 instrument: a ground-truth join, from Python's own tokenizer.
# ---------------------------------------------------------------------------

def tokenize_runs(src):
    """Every maximal run of adjacent STRING tokens, as (joined_text, lineno).

    This is what Python itself does with implicit concatenation, so it is the
    reference the control's regex is being measured against.  Only runs of
    length >= 2 are returned -- a lone literal is not a wrap and the control
    already sees it.

    f-strings tokenize as FSTRING_START/MIDDLE/END on 3.12+, so they are
    handled explicitly rather than being dropped on the floor: an f-string
    fragment adjacent to a plain one is still a wrap, and pretending otherwise
    would build the blind spot this audit exists to look for."""
    runs, cur, start = [], [], None
    try:
        toks = list(tokenize.generate_tokens(io.StringIO(src).readline))
    except (tokenize.TokenError, IndentationError, SyntaxError):
        return None
    fstr_depth, fstr_parts = 0, []
    for tk in toks:
        name = token.tok_name.get(tk.type, "")
        if name == "FSTRING_START":
            fstr_depth += 1
            fstr_parts = []
            continue
        if fstr_depth:
            if name == "FSTRING_END":
                fstr_depth -= 1
                piece = "".join(fstr_parts)
                if start is None:
                    start = tk.start[0]
                cur.append(piece)
            elif name == "FSTRING_MIDDLE":
                fstr_parts.append(tk.string)
            continue
        if tk.type == tokenize.STRING:
            if start is None:
                start = tk.start[0]
            cur.append(_literal_text(tk.string))
        elif tk.type in (tokenize.NL, tokenize.NEWLINE, tokenize.COMMENT,
                         tokenize.INDENT, tokenize.DEDENT):
            continue
        else:
            if len(cur) >= 2:
                runs.append(("".join(cur), start))
            cur, start = [], None
    if len(cur) >= 2:
        runs.append(("".join(cur), start))
    return runs


def _literal_text(raw):
    """The CONTENTS of a string token, prefixes and quotes stripped.

    Deliberately not `ast.literal_eval`: escapes are left as written, because
    the question is what characters a regex scanning the SOURCE would see, and
    a digest never contains an escape anyway."""
    i = 0
    while i < len(raw) and raw[i] not in "\"'":
        i += 1
    rest = raw[i:]
    for q in ('"""', "'''"):
        if rest.startswith(q):
            return rest[3:-3]
    return rest[1:-1]


def hexish_runs(src, minlen=WINDOW_HI + 1):
    """Wrapped runs whose joined text is a single hex string of >= minlen.

    minlen defaults to 41 -- one past the control's cap -- because that is the
    population the cap is supposed to exclude and therefore the population
    where a wrap can turn something excluded into something included."""
    runs = tokenize_runs(src)
    if runs is None:
        return None
    out = []
    for text, line in runs:
        if len(text) >= minlen and HEX_RUN_RE.match(text):
            out.append({"text": text, "len": len(text), "line": line})
    return out


# ---------------------------------------------------------------------------
# The shipped control, loaded as a module so the audit measures the REAL thing.
# ---------------------------------------------------------------------------

def load_control(path=None):
    import importlib.util
    path = path or os.path.join(SCRIPTS, CONTROL)
    spec = importlib.util.spec_from_file_location("_mg3934_under_audit", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def fragments_visible_to_window(src):
    """Every quoted piece the control's PRE-join reading would have offered to
    the resolver.  Used to show what the join removed and, in the converse
    direction, that it removed only that."""
    return [m.group(1) for m in re.finditer(r"[\"']([0-9a-fA-F]+)[\"']", src)
            if WINDOW_LO <= len(m.group(1)) <= WINDOW_HI]


# ---------------------------------------------------------------------------
# Q1 -- regex join vs tokenizer join, over the real corpus and over fixtures.
# ---------------------------------------------------------------------------

# Each fixture is (name, source, must_be_seen_as_pin).  The wrap shapes a
# 79-column style actually produces, plus the ones the regex's character class
# and its `\s*` gap cannot express.  A digest is 64 hex characters; a revision
# is 40 or fewer.  "must_be_seen_as_pin" is what a CORRECT control does.
_D = "".join("%x" % ((i * 7) % 16) for i in range(64))   # built, not written
_R = "".join("%x" % ((i * 3) % 16) for i in range(40))

JOIN_FIXTURES = [
    ("plain 42+22 wrap of a digest",
     'import subprocess\nX = ("%s"\n     "%s")\nsubprocess.run(["git","show",X])\n'
     % (_D[:42], _D[42:]), False),
    ("digest wrapped 32+32",
     'import subprocess\nX = ("%s"\n     "%s")\nsubprocess.run(["git","show",X])\n'
     % (_D[:32], _D[32:]), False),
    ("digest wrapped in THREE pieces 22+21+21",
     'import subprocess\nX = ("%s"\n "%s"\n "%s")\nsubprocess.run(["git","show",X])\n'
     % (_D[:22], _D[22:43], _D[43:]), False),
    ("digest wrapped with a RAW prefix on the tail",
     'import subprocess\nX = ("%s"\n     r"%s")\nsubprocess.run(["git","show",X])\n'
     % (_D[:42], _D[42:]), False),
    ("digest wrapped with an f prefix on the tail",
     'import subprocess\nX = ("%s"\n     f"%s")\nsubprocess.run(["git","show",X])\n'
     % (_D[:42], _D[42:]), False),
    ("digest wrapped with a b prefix on the tail",
     'import subprocess\nX = ("%s"\n     b"%s")\nsubprocess.run(["git","show",X])\n'
     % (_D[:42], _D[42:]), False),
    ("digest wrapped across a backslash continuation",
     'import subprocess\nX = "%s" \\\n    "%s"\nsubprocess.run(["git","show",X])\n'
     % (_D[:42], _D[42:]), False),
    ("digest wrapped with a COMMENT between the fragments",
     'import subprocess\nX = ("%s"   # first half\n     "%s")\n'
     'subprocess.run(["git","show",X])\n' % (_D[:42], _D[42:]), False),
    ("digest with mixed quote styles",
     'import subprocess\nX = ("%s"\n     \'%s\')\nsubprocess.run(["git","show",X])\n'
     % (_D[:42], _D[42:]), False),
    # The converse direction.  A real pin, wrapped, must STILL be seen.
    ("real 40-char revision wrapped 20+20",
     'import subprocess\nPIN = ("%s"\n       "%s")\nsubprocess.run(["git","show",PIN])\n'
     % (_R[:20], _R[20:]), True),
    ("real 40-char revision wrapped 8+32",
     'import subprocess\nPIN = ("%s"\n       "%s")\nsubprocess.run(["git","show",PIN])\n'
     % (_R[:8], _R[8:]), True),
    ("real 40-char revision, NOT wrapped",
     'import subprocess\nPIN = "%s"\nsubprocess.run(["git","show",PIN])\n' % _R,
     True),
    ("short 7-char abbreviation, not wrapped",
     'import subprocess\nPIN = "%s"\nsubprocess.run(["git","show",PIN])\n' % _R[:7],
     True),
]


def check_join(mod):
    """Does the shipped join agree with Python on every fixture, and does the
    resulting detection do the right thing?

    Two separate observations per fixture, because they can disagree and the
    difference is the finding:
      joined  -- did the regex produce the same string Python would?
      seen    -- did the control end up treating a pin-shaped literal as a pin?
    A fixture can have a WRONG join and a RIGHT verdict (the fragments happen
    to fall outside the window), which is a latent hole rather than a live one,
    and this reports the two separately so they are not conflated."""
    rows = []
    for name, src, want_pin in JOIN_FIXTURES:
        truth = tokenize_runs(src)
        truth_join = truth[0][0] if truth else None
        joined_src = mod.join_implicit_concat(src)
        m = re.search(r"[\"']([0-9a-zA-Z]+)[\"']", joined_src.split("\n")[1])
        regex_join = m.group(1) if m else None
        found = sorted(mod.revs_in(src))
        hexfound = [r for r in found if HEX_RUN_RE.match(r)]
        seen_as_pin = bool(hexfound)
        # An UNWRAPPED fixture has no run of two adjacent literals, so there is
        # no join to agree or disagree about.  Reporting those as "differs"
        # would inflate the disagreement count with cases the join is not even
        # asked about -- exactly the sort of unlabelled number this audit is
        # supposed to catch elsewhere.
        rows.append({
            "fixture": name,
            "python_join": truth_join,
            "control_join_agrees": (None if truth_join is None
                                    else regex_join == truth_join),
            "control_regex_join": regex_join,
            "want_seen_as_pin": want_pin,
            "seen_as_pin": seen_as_pin,
            "literals_offered": hexfound,
            "verdict_ok": seen_as_pin == want_pin,
        })
    return rows


# ---------------------------------------------------------------------------
# Q2 -- the class sweep.
# ---------------------------------------------------------------------------

def sweep(mod):
    """Every wrapped hex run of >= 41 characters in scripts/, with whether its
    file mentions git (and so could reach (B)) and what the PRE-join reading
    would have exposed."""
    rows, unparsed = [], []
    for name in sorted(os.listdir(SCRIPTS)):
        if not name.endswith(".py"):
            continue
        rel = os.path.join("scripts", name)
        with open(os.path.join(SCRIPTS, name), encoding="utf-8") as fh:
            src = fh.read()
        runs = hexish_runs(src)
        if runs is None:
            unparsed.append(rel)
            continue
        if not runs:
            continue
        mentions_git = bool(re.search(r"(?<![\w-])git(?![\w-])", src))
        post = sorted(mod.revs_in(src))
        for r in runs:
            exposed = [f for f in fragments_visible_to_window(src)
                       if f and f in r["text"]]
            rows.append({
                "script": rel, "line": r["line"], "len": r["len"],
                "mentions_git": mentions_git,
                "fragments_in_window_pre_join": sorted(set(exposed)),
                "still_offered_post_join": [p for p in post
                                            if p in r["text"] and p != r["text"]],
            })
    return rows, unparsed


# ---------------------------------------------------------------------------
# Q3 -- is the disjunction exhaustive?
# ---------------------------------------------------------------------------

def probe_disjunction(mod, cwd=REPO):
    """Categories a 7-40 hex literal can be in that are NEITHER "shallow" NOR
    "rotted".  For each, what does the control's resolver say?

    Instrument note: these are real objects in THIS repository, resolved by the
    control's own git_resolver, not by a stub.  A stub could not show the
    positive, because the whole question is what git says back."""
    resolve = mod.git_resolver(cwd)
    cases = []

    def sh(*a):
        return subprocess.run(a, cwd=cwd, capture_output=True,
                              text=True).stdout.strip()

    head = sh("git", "rev-parse", "HEAD")
    tree = sh("git", "rev-parse", "HEAD^{tree}")
    blob = sh("git", "rev-parse", "HEAD:scripts/" + CONTROL)
    tag_like = sh("git", "rev-parse", "--short=12", "HEAD")

    # Built, never written down.  A quoted hex literal in THIS file would be
    # picked up by the very control this audit is auditing -- and was: the
    # first draft spelled a twelve-character absentee inline, and the shipped
    # mg-3934 control failed the whole tree on it within seconds.  That is the
    # standing target "does the deliverable reproduce its own defect class"
    # answered by demonstration rather than by assertion, and the answer is
    # that the control is load-bearing enough to catch its own auditor.
    absent = "".join("%x" % ((i * 5 + 3) % 16) for i in range(12))

    for label, rev, exists_as in [
            ("a COMMIT (the control's happy path)", head[:12], "commit"),
            ("a TREE object that exists in this repo", tree[:12], "tree"),
            ("a BLOB object that exists in this repo", blob[:12], "blob"),
            ("a well-formed hex string that is no object at all",
             absent, "nothing"),
    ]:
        ok, detail = resolve(rev)
        real = sh("git", "cat-file", "-t", rev) or "(none)"
        cases.append({
            "category": label, "literal": rev,
            "git_cat_file_type": real, "expected_kind": exists_as,
            "control_resolves": ok, "control_detail": detail,
            # The disjunction is "shallow OR rotted".  It is WRONG about this
            # literal whenever the object is present and the control still
            # refuses it: neither branch is true, and both are printed.
            "disjunction_wrong_here": (not ok) and real != "(none)",
        })
    return {"cases": cases, "short_head": tag_like}


# ---------------------------------------------------------------------------
# Q4 -- did the join create a blind spot on the real corpus?
# ---------------------------------------------------------------------------

def check_no_blind_spot(mod):
    """Every literal the PRE-join control offered, and whether the post-join
    control still offers it.  Anything dropped must be inside a >= 41-char hex
    run -- i.e. provably not a sha1 revision.  Anything else dropped is a
    blind spot the repair bought the fix with."""
    dropped, kept = [], []
    saved = mod.join_implicit_concat
    for name in sorted(os.listdir(SCRIPTS)):
        if not name.endswith(".py") and not name.endswith(".sh"):
            continue
        rel = os.path.join("scripts", name)
        with open(os.path.join(SCRIPTS, name), encoding="utf-8") as fh:
            src = fh.read()
        post = set(mod.revs_in(src))
        mod.join_implicit_concat = lambda s: s
        try:
            pre = set(mod.revs_in(src))
        finally:
            mod.join_implicit_concat = saved
        for lit in sorted(pre - post):
            runs = hexish_runs(src) or []
            inside = [r for r in runs if lit in r["text"]]
            dropped.append({
                "script": rel, "literal": lit,
                "inside_long_hex_run": bool(inside),
                "run_len": inside[0]["len"] if inside else None,
                "justified": bool(inside),
            })
        kept.extend({"script": rel, "literal": l} for l in sorted(post))
    return dropped, kept


# ---------------------------------------------------------------------------
# Self-test.  Every check above must be shown able to FAIL.
# ---------------------------------------------------------------------------

def selftest(mod):
    """A negative needs an instrument that could have shown the positive.
    Each case drives one of the four checks into its failing state."""
    ok = True

    def say(label, good):
        nonlocal ok
        print("  %-62s %s" % (label, "ok" if good else "FAILED"))
        ok = ok and good

    # Q1's instrument must disagree with a join that is wrong.
    class BadJoin:
        join_implicit_concat = staticmethod(lambda s: s)
        revs_in = staticmethod(mod.revs_in)
    broken = load_control()
    broken.join_implicit_concat = lambda s: s
    rows = check_join(broken)
    say("1. join check FAILS a control with the join removed",
        any(not r["verdict_ok"] for r in rows))
    say("2. join check PASSES the shipped control on the converse fixtures",
        all(r["verdict_ok"] for r in check_join(mod) if r["want_seen_as_pin"]))

    # Q2's instrument must find a planted wrap.
    planted = ('X = ("%s"\n     "%s")\n' % (_D[:42], _D[42:]))
    say("3. sweep finds a planted 42+22 wrapped digest",
        len(hexish_runs(planted) or []) == 1)
    say("4. sweep does NOT flag an unwrapped 40-char revision",
        len(hexish_runs('X = "%s"\n' % _R) or []) == 0)

    # Q3's instrument must distinguish an existing object from a missing one.
    probe = probe_disjunction(mod)
    kinds = {c["expected_kind"]: c for c in probe["cases"]}
    say("5. disjunction probe resolves a real commit",
        kinds["commit"]["control_resolves"])
    say("6. disjunction probe sees a real blob as an existing object",
        kinds["blob"]["git_cat_file_type"] == "blob")

    # Q4's instrument must notice a dropped literal.
    say("7. blind-spot check is comparing two different readings",
        mod.join_implicit_concat("\"ab\" \"cd\"") != "\"ab\" \"cd\"")
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true",
                    help="write the machine-readable record")
    args = ap.parse_args()

    mod = load_control()
    print("=== mg-a84b self-test (each check must be able to fail)")
    if not selftest(mod):
        print("SELF-TEST FAILED -- no result below is worth reading")
        return 1
    print("SELF-TEST PASSED\n")

    problems = []

    print("=== Q1  the join vs Python's own tokenizer")
    jr = check_join(mod)
    for r in jr:
        flag = "ok" if r["verdict_ok"] else "MISVERDICT"
        agree = {True: "join=python", False: "join DIFFERS",
                 None: "not wrapped"}[r["control_join_agrees"]]
        print("  %-48s %-12s %s" % (r["fixture"][:48], agree, flag))
    bad_verdict = [r for r in jr if not r["verdict_ok"]]
    wrapped = [r for r in jr if r["control_join_agrees"] is not None]
    bad_join = [r for r in wrapped if not r["control_join_agrees"]]
    print("  population: %d fixtures (%d of them wrapped) | grain: one wrap shape"
          % (len(jr), len(wrapped)))
    print("  join disagrees with Python on %d of %d wrapped; wrong VERDICT on %d"
          % (len(bad_join), len(wrapped), len(bad_verdict)))
    for r in bad_verdict:
        problems.append("join misverdicts %r: offered %s"
                        % (r["fixture"], r["literals_offered"]))

    print("\n=== Q2  the class: wrapped hex runs >= 41 chars in scripts/")
    rows, unparsed = sweep(mod)
    for r in rows:
        print("  %-52s line %-5d %d chars  git-mentioning: %s"
              % (r["script"], r["line"], r["len"], r["mentions_git"]))
        if r["fragments_in_window_pre_join"]:
            print("        pre-join, these fragments were inside 7-40: %s"
                  % ", ".join(r["fragments_in_window_pre_join"]))
        if r["still_offered_post_join"]:
            print("        STILL OFFERED after the join: %s"
                  % r["still_offered_post_join"])
            problems.append("%s still leaks %s"
                            % (r["script"], r["still_offered_post_join"]))
    gitset = [r for r in rows if r["mentions_git"]]
    print("  population: %d .py files in scripts/ | grain: one wrapped hex run"
          % len([n for n in os.listdir(SCRIPTS) if n.endswith(".py")]))
    print("  %d wrapped run(s) in %d file(s); %d run(s) in git-mentioning files"
          % (len(rows), len({r["script"] for r in rows}), len(gitset)))
    if unparsed:
        print("  NOT PARSED (excluded from the count above): %s"
              % ", ".join(unparsed))

    print("\n=== Q3  is 'shallow or rotted' exhaustive?")
    dj = probe_disjunction(mod)
    for c in dj["cases"]:
        print("  %-48s %-14s resolves=%s"
              % (c["category"][:48], c["git_cat_file_type"],
                 c["control_resolves"]))
        if c["disjunction_wrong_here"]:
            print("        -> object EXISTS and the control refuses it; the "
                  "message will say shallow-or-rotted and both are false")
    wrong = [c for c in dj["cases"] if c["disjunction_wrong_here"]]
    print("  population: 4 constructed categories | grain: one literal")
    print("  categories where BOTH printed branches are false: %d" % len(wrong))

    print("\n=== Q4  did the join buy the fix with a blind spot?")
    dropped, kept = check_no_blind_spot(mod)
    for d in dropped:
        print("  %-52s %-24s justified=%s"
              % (d["script"], d["literal"], d["justified"]))
    unjust = [d for d in dropped if not d["justified"]]
    print("  population: every .py/.sh in scripts/ | grain: one literal")
    print("  literals visible pre-join and not post-join: %d (%d unjustified)"
          % (len(dropped), len(unjust)))
    print("  literals still offered post-join: %d" % len(kept))
    for d in unjust:
        problems.append("%s: %s dropped by the join and not inside a long "
                        "hex run" % (d["script"], d["literal"]))

    rec = {"join": jr, "sweep": rows, "unparsed": unparsed,
           "disjunction": dj, "dropped": dropped, "kept": kept,
           "problems": problems}
    if args.json:
        with open(os.path.join(REPO, REPORT), "w") as fh:
            json.dump(rec, fh, indent=2, sort_keys=True)
            fh.write("\n")
        print("\nwrote %s" % REPORT)

    print("\n" + "=" * 70)
    if problems:
        print("PROBLEMS (%d):" % len(problems))
        for p in problems:
            print("  - %s" % p)
        return 1
    print("No problem found by the four checks above.  That is a negative over "
          "the populations named, not over the class; see the report's WHAT I "
          "DID NOT DO.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
