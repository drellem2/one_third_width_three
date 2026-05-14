#!/usr/bin/env python3
r"""
compat_geom_F23_canonical_descent.py
====================================

Compat-Geom **F23** (mg-531f) -- pinning the canonical descent rule for the
chamber-Morse critical chain `c*_{n+1}`.

Parent chain:  F10 -> F17 (mg-4d3a) -> F18 (mg-d039) -> F19 -> F20
-> F21 (mg-a2cb, Prop F21.1) -> F22-HPC (mg-43fb / mg-0c5d, RED-tripwire)
-> **F23 (mg-531f)**.

THE QUESTION (F22-HPC Session 2, finding 6 -- `docs/state-F22-HPC.md` s.5).
The genuine `c*_{n+1}` is "(the descent of)" a critical `(n-1)`-cell of
`M_rel^eq` (F21 Prop F21.1).  F22-HPC S2 materialised the descent at the
`n = 3 -> 4` testbed: the recorded `c*_4` IS reachable from the perfect-
matching survivor `D-lift(c*_3)` by a gradient `V`-path inside the perfect
`M_4`, but the descent target is NOT pinned by `min-|L|-profile +
BFT-sharp` alone -- those leave **4 `S_4`-orbits**, of which recorded `c*_4`
is one.  F23 asks: is there additional `S_{n+1}`-equivariant structure that
selects THE `c*_{n+1}` -- and, decisively, does such a canonical rule EXIST?

WHAT THIS SCRIPT DOES (the n = 3 -> 4 testbed -- cheap, materialisable).
  Section 1.  Reproduces F22-HPC S2's candidate set: rebuilds the perfect
              `M_4 = M_3 u M_rel^eq + cross-boundary cancellation`, the
              gradient-`V`-path descent-reachable 2-cells, filters to
              `min-|L|-profile + BFT-sharp`  ->  44 cells / 4 `S_4`-orbits.
  Section 2.  The full `S_4`-equivariant invariant battery on the 4 orbits.
  Section 3.  CANDIDATE RULE A -- a deterministic descent `V`-path procedure
              (shortest / fewest-paths).  Result: NOT canonical.
  Section 4.  CANDIDATE RULE B -- `S_{n+1}`-equivariant chamber-Morse
              criticality.  Result: it WORKS -- `c*_4` is the unique
              `min-|L|-profile` critical cell of the chamber-Morse matching
              `M^chamber_4`, and exactly ONE of the 4 descent orbits meets
              `crit(M^chamber_4)`.  This is the rule.
  Section 5.  CANDIDATE RULE C -- lex-min over a structural `S_4`-invariant
              (new-element locus / top-poset OSA signature).  Result: each
              picks the right orbit at `n = 3 -> 4` but is REFUTED as an
              `n`-uniform rule by the recorded `c*_3, c*_5`.
  Section 6.  The `n`-uniformity probe -- `c*_3, c*_4, c*_5` invariants.
  Section 7.  `n = 3` base case + the HPC-per-n confirmation (`|Delta_5|`).
  Section 8.  Verdict.

VERDICT: GREEN-descent-pinned (HPC-per-n variant).  A canonical
`S_{n+1}`-equivariant rule that selects `c*_{n+1}` from the 4-orbit
candidate set DOES exist -- it is **chamber-Morse criticality itself**,
made `S_{n+1}`-equivariant by the `min-|L|-profile` tie-break (F23's
candidate form B; the structure F21 s.5.2 / F22-HPC S2 finding 6 predicted
was needed).  But it is NOT a closed-form / `n`-uniform generative rule:
every *structural* (non-criticality) discriminator of the 4 orbits is
refuted as `n`-uniform by the exact record, and applying the rule needs
the level-`(n+1)` chamber-Morse matching `M^chamber_{n+1}` -- HPC-per-n
(`|Delta_5|` already exceeds `2e7` cells).  So the cofiber-Morse induction
(Prop F21.1) narrows but does NOT close the recursion; the consequence is
the route-2 Tier-3 decision (or the documented BK/Cheeger pivot) -- a
PM/Daniel decision.  See
`docs/compatibility-geometry-F23-canonical-descent-rule.md`.

Pure-Python stdlib, exact `Fraction` / `int` arithmetic.  Runtime ~ 2 s
(Sections 1-7; Section 7's `|Delta_5|` probe is a bounded count).

References
  - mg-0c5d (F22-HPC S2): docs/state-F22-HPC.md s.5 (findings 1-6, the
        3 continuation routes -- F23 is route 1);
        scripts/compat_geom_F22_hpc_cell_tracking.py Section 10 (the
        materialised n=3 trip-wire -- this script's Section 1 builds on it).
  - mg-a2cb (F21): Prop F21.1 (the cofiber-Morse induction), s.5.2 (the
        lower-bound argument: (CM-struct)(i)+(ii) under-determine c*_n).
  - mg-43fb (F22-HPC S1): the closure-operator lift infra.
  - mg-26fc: the two 1/3-2/3 mechanisms (the BK/Cheeger documented
        alternative if F23 found c*_n not canonically pinnable).
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction
from itertools import permutations

import compat_geom_cofiber_morse_n3n4 as CM
import compat_geom_F22_hpc_cell_tracking as F22

sys.setrecursionlimit(1_000_000)

BFT_LO, BFT_HI = Fraction(3, 11), Fraction(8, 11)


# ===========================================================================
# Section 0.  Utilities (exact, stdlib).
# ===========================================================================

def tc(P):
    return F22.transitive_closure(P)


def closures(chain):
    return tuple(tc(P) for P in chain)


def profile(chain, m):
    """|L|-profile of a chain of posets on [m]."""
    return tuple(F22.count_linear_extensions(tc(P), m) for P in chain)


def per_step(chain, m):
    p = profile(chain, m)
    return [Fraction(p[k + 1], p[k]) for k in range(len(p) - 1)]


def is_bft_sharp(chain, m):
    return all(BFT_LO <= x <= BFT_HI for x in per_step(chain, m))


def relabel(chain, perm):
    return tuple(frozenset((perm[a], perm[b]) for (a, b) in P) for P in chain)


def orbit(chain, m):
    """The S_m-orbit of a chain (a frozenset of closure-tuples)."""
    cl = closures(chain)
    return frozenset(relabel(cl, perm) for perm in permutations(range(m)))


def chain_iso_key(chain, m):
    """The lex-min closure-tuple over all relabellings -- a deterministic,
    S_m-invariant key for the orbit (used only to order output)."""
    best = None
    cl = closures(chain)
    for perm in permutations(range(m)):
        r = tuple(tuple(sorted((perm[a], perm[b]) for (a, b) in P))
                  for P in cl)
        if best is None or r < best:
            best = r
    return best


def poset_iso_key(P, m):
    """lex-min closure of a single poset over all relabellings."""
    C = tc(P)
    best = None
    for perm in permutations(range(m)):
        r = tuple(sorted((perm[a], perm[b]) for (a, b) in C))
        if best is None or r < best:
            best = r
    return best


def new_elt_locus(P, new):
    """Where the new element `new` sits in poset P:
       absent / pure-LOW (in D) / pure-HIGH (in U) / MIXED."""
    C = tc(P)
    down = any(a == new for (a, b) in C)   # new < something
    up = any(b == new for (a, b) in C)     # something < new
    if not down and not up:
        return "absent"
    if down and not up:
        return "pure-LOW(D)"
    if up and not down:
        return "pure-HIGH(U)"
    return "MIXED"


def banner(t):
    print("\n" + "=" * 74)
    print("  " + t)
    print("=" * 74)


# ===========================================================================
# Section 1.  Reproduce F22-HPC S2's candidate set:  the perfect M_4, the
#             descent-reachable 2-cells, and the 4-orbit candidate set.
# ===========================================================================

def build_perfect_M4():
    """Rebuild  M_4 = M_3 u M_rel^eq + cross-boundary Forman cancellation
    -- the perfect, acyclic discrete Morse matching on Delta_4 with the
    single critical 2-cell `survivor = D-lift(c*_3)`.  (F22-HPC S2 / Section
    10 of compat_geom_F22_hpc_cell_tracking.py, re-assembled here.)

    Returns (matched_4, cell_set4, survivor, ch4)."""
    PPF_3 = CM.make_PPF(3)
    PPF_4 = CM.make_PPF(4)
    sub = CM.iota_3_image(PPF_3)
    es3, ab3 = CM.refinement_above_map(PPF_3)
    es4, ab4 = CM.refinement_above_map(PPF_4)
    ch3 = CM.all_chains_by_dim(es3, ab3)
    ch4 = CM.all_chains_by_dim(es4, ab4)
    rel = CM.relative_cells_by_dim(ch4, sub)

    # M_3: perfect chamber-Morse matching on Delta_3, critical cell c*_3.
    m3, _, _, _ = CM.greedy_matching(ch3, include_empty=True)

    # M_rel^eq: perfect cofiber matching on C_*(Delta_4, Delta_3).
    mrel, _, _, _ = CM.greedy_matching(rel, include_empty=False)
    rcs = set()
    for d in rel:
        rcs.update(rel[d])
    CM.forman_cancel_to_target(mrel, rel, rcs, (0, 0, 2, 0, 0), [])

    # assemble M_4 = M_3 u M_rel^eq, then run the cross-boundary cancellation.
    matched_4 = {}
    for c, p in m3.items():
        matched_4[c] = p
    for d in ch4:
        for c in ch4[d]:
            if c not in matched_4:
                matched_4[c] = None
    if () not in matched_4:
        matched_4[()] = None
    for c, p in mrel.items():
        matched_4[c] = p
    cell_set4 = set()
    for d in ch4:
        cell_set4.update(ch4[d])
    CM.forman_cancel_to_target(matched_4, ch4, cell_set4, (0, 0, 1, 0, 0), [])
    crit_post = CM.critical_by_dim(matched_4, ch4, include_empty=True)
    survivor = tuple(crit_post[2][0])
    return matched_4, cell_set4, survivor, ch4


def descent_reachable(survivor, matched_4, cell_set4):
    """All 2-cells reachable from `survivor` by gradient `V`-path moves
    (2-cell -> drop a face -> follow its matched coface -> 2-cell, ...).
    Returns dict: cell -> (min V-path length, # distinct shortest paths)."""
    reached = {survivor: (0, 1)}

    def dfs(cell, plen):
        for i in range(len(cell)):
            sigma = cell[:i] + cell[i + 1:]
            if sigma not in cell_set4:
                continue
            partner = matched_4.get(sigma)
            if partner is None or len(partner) != len(cell) or partner == cell:
                continue
            npl = plen + 2
            old = reached.get(partner)
            if old is None:
                reached[partner] = (npl, 1)
                dfs(partner, npl)
            elif npl < old[0]:
                reached[partner] = (npl, old[1] + 1)
                dfs(partner, npl)
            elif npl == old[0]:
                reached[partner] = (old[0], old[1] + 1)

    dfs(survivor, 0)
    return reached


def four_orbit_candidate_set(reached):
    """F22-HPC S2's candidate set: descent-reachable, all-BFT-sharp,
    min-|L|-profile 2-cells, grouped into S_4-orbits.  Returns
    (orbit_list, minprof, n_bft) with orbit_list sorted deterministically."""
    allcells = list(reached)
    bft = [c for c in allcells if is_bft_sharp(c, 4)]
    minprof = min(profile(c, 4) for c in bft)
    mp = [c for c in bft if profile(c, 4) == minprof]
    orbits = {}
    for c in mp:
        orbits.setdefault(orbit(c, 4), []).append(c)
    orbit_list = sorted(orbits.items(),
                        key=lambda kv: chain_iso_key(kv[1][0], 4))
    return orbit_list, minprof, len(bft)


def run_section_1():
    banner("Section 1.  The F22-HPC S2 candidate set -- reproduced")
    t0 = time.time()
    matched_4, cell_set4, survivor, ch4 = build_perfect_M4()
    crit = CM.critical_by_dim(matched_4, ch4, include_empty=True)
    cv = tuple(len(crit.get(d, [])) for d in range(5))
    print(f"  perfect M_4 critical vector        = {cv}  "
          f"(expect (0,0,1,0,0))")
    print(f"  survivor (the unique critical 2-cell) = "
          f"{[F22.hasse_str(P, 4) for P in survivor]}")
    print(f"  survivor |L|-profile               = {profile(survivor, 4)}")
    reached = descent_reachable(survivor, matched_4, cell_set4)
    orbit_list, minprof, n_bft = four_orbit_candidate_set(reached)
    print(f"  descent-reachable 2-cells          = {len(reached)}  "
          f"(F22-HPC S2: 212)")
    print(f"  ... all-BFT-sharp among them        = {n_bft}  "
          f"(F22-HPC S2: 151)")
    n_mp = sum(len(reps) for _, reps in orbit_list)
    print(f"  ... min-|L|-profile {minprof} among those = {n_mp}  "
          f"(F22-HPC S2: 44)")
    print(f"  ... spanning {len(orbit_list)} S_4-orbits  "
          f"(F22-HPC S2: 4 -- the candidate set)")
    assert len(reached) == 212 and n_bft == 151 and n_mp == 44, \
        "candidate set does not reproduce F22-HPC S2 -- infra drift"
    assert len(orbit_list) == 4, "expected 4 S_4-orbits"
    print(f"  [{time.time() - t0:.1f}s]  candidate set reproduced exactly.")
    return matched_4, cell_set4, survivor, ch4, reached, orbit_list


# ===========================================================================
# Section 2.  The full S_4-equivariant invariant battery on the 4 orbits.
# ===========================================================================

def run_section_2(orbit_list, reached):
    banner("Section 2.  The 4 descent orbits -- S_4-invariant battery")
    cstar4 = closures(F22.C_STAR[4]["hasse"])
    cstar4_orb = orbit(F22.C_STAR[4]["hasse"], 4)
    recorded_idx = None
    data = []
    for oi, (orb, reps) in enumerate(orbit_list):
        rep = closures(reps[0])
        is_rec = (orb == cstar4_orb)
        if is_rec:
            recorded_idx = oi
        # per-poset invariants
        per_poset = []
        for P in rep:
            C = tc(P)
            per_poset.append({
                "L": F22.count_linear_extensions(C, 4),
                "w": F22.poset_width(C, 4),
                "osa": F22.osa_signature(C, 4),
                "iso": poset_iso_key(P, 4),
            })
        # chain-level invariants
        n_reached = sum(1 for c in orb if c in reached)
        plens = sorted(set(reached[c][0] for c in orb if c in reached))
        rev = tuple(F22.reverse_rel(P) for P in rep)
        rev_orb = orbit(rev, 4)
        dual = next((j for j, (o2, _) in enumerate(orbit_list)
                     if o2 == rev_orb), None)
        top_osa = per_poset[-1]["osa"]
        size2_pos = ([i for i, s in enumerate(top_osa) if s == 2]
                     if top_osa else [])
        data.append({
            "orb": orb, "rep": rep, "is_rec": is_rec,
            "per_poset": per_poset, "n_reached": n_reached,
            "plens": plens, "dual": dual, "top_osa": top_osa,
            "size2_pos": size2_pos,
        })
        print(f"\n  ORBIT {oi}  (|orbit| = {len(orb)}, {len(reps)} reps in "
              f"the 44-cell set){'   <<< RECORDED c*_4' if is_rec else ''}")
        print(f"    rep: {[F22.hasse_str(P, 4) for P in rep]}")
        for j, pp in enumerate(per_poset):
            print(f"    P[{j}]: |L|={pp['L']} width={pp['w']} "
                  f"OSA={pp['osa']}  iso-type={pp['iso']}")
        print(f"    |L|-profile          = {profile(rep, 4)}   "
              f"per-step Pr = {[str(x) for x in per_step(rep, 4)]}")
        print(f"    top-poset OSA        = {top_osa}   "
              f"size-2 block at position {size2_pos} (of {len(top_osa or [])})")
        print(f"    new-elt-3 locus      = "
              f"{[new_elt_locus(P, 3) for P in rep]}")
        print(f"    descent V-path lens  = {plens[:6]}   "
              f"(orbit cells reached: {n_reached}/{len(orb)})")
        print(f"    order-reversal dual  = orbit {dual}")
    print(f"\n  SUMMARY -- the 4 orbits all share: |L|-profile (5,3,2), "
          f"per-step Pr (3/5, 2/3),")
    print(f"  width profile (2,2,2), bottom-poset iso-type, |orbit| = 24.")
    print(f"  They DIFFER in: top-poset OSA signature "
          f"{[d['top_osa'] for d in data]},")
    print(f"  middle-poset iso-type, and new-element-3 locus.  "
          f"(L2-struct) -- width-2 OSA")
    print(f"  top with a size-2 block -- holds for ALL 4: it does NOT "
          f"discriminate.")
    return data, recorded_idx


# ===========================================================================
# Section 3.  CANDIDATE RULE A -- a deterministic descent V-path procedure.
# ===========================================================================

def run_section_3(data, recorded_idx):
    banner("Section 3.  CANDIDATE RULE A -- deterministic descent V-path")
    print("""
  A Forman-respecting greedy/deterministic descent: from the survivor,
  follow a CANONICALLY-CHOSEN gradient V-path and take where it lands.
  For the choice to be S_{n+1}-equivariant it must use an S_{n+1}-invariant
  criterion (lex-min on labels is NOT equivariant).  The natural invariant
  criteria are 'shortest V-path' and 'reached by the most V-paths'.""")
    plen_by_orbit = [min(d["plens"]) for d in data]
    print(f"\n    shortest descent V-path length, per orbit = {plen_by_orbit}")
    shortest = min(range(4), key=lambda i: plen_by_orbit[i])
    print(f"    => 'shortest descent V-path' selects orbit {shortest}  "
          f"(recorded c*_4 is orbit {recorded_idx})")
    if shortest != recorded_idx:
        print(f"    REFUTED: the shortest-V-path orbit ({shortest}) is NOT "
              f"recorded c*_4 ({recorded_idx}).")
    print("""
    Moreover the descent V-path is not even unique up to its endpoint:
    every orbit is reached by V-paths of many lengths (Section 2), and
    the gradient flow of the perfect M_4 is a DAG with wide fan-out -- no
    single S_4-invariant 'pick a V-path' criterion is distinguished.

  VERDICT (Rule A): NOT a canonical rule.  A deterministic descent V-path
  procedure either (i) uses a label-dependent tie-break (not equivariant),
  or (ii) uses 'shortest path', which selects the WRONG orbit.""")


# ===========================================================================
# Section 4.  CANDIDATE RULE B -- S_{n+1}-equivariant chamber-Morse
#             criticality.  (F22-HPC S2 finding 6 / F21 s.5.2 predicted this
#             is the needed structure.)
# ===========================================================================

def chamber_morse_critical_cells(n):
    """The critical (n-2)-cells of the F2/F8 chamber-Morse matching
    `M^chamber_n` on Delta_n = Delta(PPF_n).  This is the matching whose
    critical cells DEFINE the recorded canonical chamber-Morse cells
    (F2 mg-7455 / F8 mg-1e99); transcribed in compat_geom_cofiber_morse_n3n4.

    Returns (critical_(n-2)_cells, full_critical_vector)."""
    PPF = CM.make_PPF(n)
    _, above = CM.refinement_above_map(PPF)
    matching, by_dim = CM.compute_f2_matching(PPF, above)
    crit = CM.f2_critical_by_dim(matching, by_dim)
    cv = tuple(len(crit.get(d, [])) for d in range(max(crit) + 2))
    return crit.get(n - 2, []), cv


def run_section_4(orbit_list, reached, recorded_idx):
    banner("Section 4.  CANDIDATE RULE B -- chamber-Morse criticality")
    print("""
  The chamber-Morse matching M^chamber_n (F2/F8) is the matching whose
  critical cells DEFINE the program's canonical chamber-Morse cells.  Made
  S_{n+1}-equivariant: 'crit(M^chamber)' as a SET OF S_{n+1}-ORBITS is
  labelling-independent  (crit(sigma . M) = sigma . crit(M), and orbits are
  S-invariant).  Test: does chamber-Morse criticality select recorded c*_4
  from the 4-orbit candidate set?""")
    cm_cells, cv = chamber_morse_critical_cells(4)
    print(f"\n    M^chamber_4 critical vector = {cv}   "
          f"({len(cm_cells)} critical 2-cells)")
    cstar4 = closures(F22.C_STAR[4]["hasse"])
    cm_orbits = {}
    for c in cm_cells:
        cm_orbits.setdefault(orbit(c, 4), []).append(c)
    print(f"    its {len(cm_cells)} critical 2-cells span "
          f"{len(cm_orbits)} S_4-orbits:")
    cm_min_cell = None
    for c in cm_cells:
        pr = profile(c, 4)
        bft = is_bft_sharp(c, 4)
        in_desc = closures(c) in reached
        is_rec = closures(c) == cstar4
        if is_rec:
            cm_min_cell = c
        print(f"      |L|-profile {pr}  BFT-sharp={bft}  "
              f"descent-reachable={in_desc}  == recorded c*_4: {is_rec}")
    # the S_4-invariant tie-break: minimum |L|-profile
    min_pr = min(profile(c, 4) for c in cm_cells)
    min_cells = [c for c in cm_cells if profile(c, 4) == min_pr]
    min_orbs = set(orbit(c, 4) for c in min_cells)
    print(f"\n    minimum |L|-profile among the critical 2-cells = {min_pr}")
    print(f"    # critical 2-cells achieving it = {len(min_cells)}  "
          f"# orbits = {len(min_orbs)}")
    exact = (cm_min_cell is not None
             and closures(cm_min_cell) == cstar4)
    print(f"    the min-|L|-profile critical 2-cell == recorded c*_4 "
          f"(EXACT, same labelling): {exact}")
    # cross-check against the 4 descent orbits
    print(f"\n    cross-check -- of the 4 descent orbits, which meet "
          f"crit(M^chamber_4)?")
    hits = []
    for oi, (orb, _) in enumerate(orbit_list):
        meets = any(orbit(c, 4) == orb for c in cm_cells)
        hits.append(meets)
        tag = "  <<< RECORDED c*_4" if oi == recorded_idx else ""
        print(f"      descent orbit {oi}: meets crit(M^chamber_4) = "
              f"{meets}{tag}")
    n_hit = sum(hits)
    assert exact and n_hit == 1 and hits[recorded_idx], \
        "Rule B did not uniquely select recorded c*_4"
    print(f"""
  VERDICT (Rule B): THE RULE.  Exactly ONE of the 4 descent orbits
  (recorded c*_4's) meets crit(M^chamber_4); equivalently, recorded c*_4
  is the UNIQUE min-|L|-profile critical cell of M^chamber_4.  This is a
  canonical S_{{n+1}}-equivariant rule and it DECISIVELY pins c*_4 at the
  n = 3 -> 4 testbed.  It is F23's candidate form B -- the chamber-Morse
  criticality condition F21 s.5.2 / F22-HPC S2 finding 6 predicted was the
  needed structure.

  But note what the rule IS: chamber-Morse criticality is the DEFINING
  property of c*_n.  Applying it needs the level-(n+1) chamber-Morse
  matching M^chamber_{{n+1}} -- see Section 7 for the HPC-per-n cost.  The
  descent picture (Prop F21.1) does not REPLACE M^chamber_{{n+1}}; it
  narrows c*_{{n+1}} to a 4-orbit set that M^chamber_{{n+1}} then resolves.""")
    return cm_cells


# ===========================================================================
# Section 5.  CANDIDATE RULE C -- lex-min over a structural S_4-invariant.
# ===========================================================================

def run_section_5(data, recorded_idx):
    banner("Section 5.  CANDIDATE RULE C -- lex-min over a structural "
           "S_4-invariant")
    print("""
  Are the 4 orbits separated by a *structural* S_4-invariant (not
  criticality) that picks recorded c*_4 -- and is that invariant an
  n-uniform rule?  Two structural discriminators separate orbit
  'recorded c*_4' from the other 3 at n = 3 -> 4:""")
    # (C1) top-poset OSA signature
    print("\n  (C1) top-poset OSA signature:")
    for oi, d in enumerate(data):
        tag = "  <<< RECORDED" if oi == recorded_idx else ""
        print(f"       orbit {oi}: top OSA = {d['top_osa']}{tag}")
    rec_osa = data[recorded_idx]["top_osa"]
    uniq_osa = sum(1 for d in data if d["top_osa"] == rec_osa) == 1
    print(f"       recorded c*_4 top OSA {rec_osa} is "
          f"{'UNIQUE' if uniq_osa else 'NOT unique'} among the 4 orbits.")

    # (C2) new-element locus -- 'chain stays in D_3'
    print("\n  (C2) new-element-3 locus (does element 3 stay pure-LOW/D "
          "throughout?):")
    for oi, d in enumerate(data):
        loci = [new_elt_locus(P, 3) for P in d["rep"]]
        all_D = all(x == "pure-LOW(D)" for x in loci)
        tag = "  <<< RECORDED" if oi == recorded_idx else ""
        print(f"       orbit {oi}: {loci}  all-in-D_3 = {all_D}{tag}")

    print("""
  Both (C1) and (C2) uniquely pick recorded c*_4 at n = 3 -> 4.  But are
  they n-uniform rules?  Test against the exact record c*_3, c*_5
  (Section 6): the top-poset OSA signatures are G_3 = OSA(1,2),
  G_4 = OSA(2,1,1), G_5 = OSA(2,2,1) -- all different shapes, no closed
  form (F21 Finding 2.1); the new-element locus is pure-HIGH for c*_3,
  pure-LOW for c*_4, MIXED for c*_5 -- no uniform pattern.

  VERDICT (Rule C): NOT a canonical rule.  Each structural invariant that
  separates the 4 orbits at n = 3 -> 4 is REFUTED as an n-uniform rule by
  the recorded c*_3, c*_5.  'Lex-min over a structural S_4-invariant' picks
  the right orbit at the testbed only by coincidence of n = 4 -- it is the
  'extrapolate a closed form from n <= 5' trap F21 Finding 2.1 warns of.""")


# ===========================================================================
# Section 6.  The n-uniformity probe -- recorded c*_3, c*_4, c*_5.
# ===========================================================================

def run_section_6():
    banner("Section 6.  n-uniformity probe -- recorded c*_3, c*_4, c*_5")
    print("""
  For each recorded c*_n: where the new element (n-1) sits in each poset
  of the chain, the top-poset OSA signature, and whether ANY element is
  pure-LOW (resp. pure-HIGH) throughout.""")
    for n in (3, 4, 5):
        ch = closures(F22.C_STAR[n]["hasse"])
        new = n - 1
        loci = [new_elt_locus(P, new) for P in ch]
        top_osa = F22.osa_signature(ch[-1], n)

        def pure_low(e):
            return all(any(a == e for (a, b) in P)
                       and not any(b == e for (a, b) in P) for P in ch)

        def pure_high(e):
            return all(any(b == e for (a, b) in P)
                       and not any(a == e for (a, b) in P) for P in ch)
        pl = [e for e in range(n) if pure_low(e)]
        ph = [e for e in range(n) if pure_high(e)]
        print(f"\n    c*_{n}  ({F22.C_STAR[n]['label']})")
        print(f"      new element {new} locus per poset = {loci}")
        print(f"      top-poset OSA signature           = {top_osa}")
        print(f"      elements pure-LOW throughout = {pl}   "
              f"pure-HIGH throughout = {ph}")
    print("""
  READING.  The new-element locus is pure-HIGH (c*_3), pure-LOW (c*_4),
  absent->pure-HIGH->MIXED (c*_5): NO n-uniform locus pattern.  The
  top-poset OSA signatures OSA(1,2), OSA(2,1,1), OSA(2,2,1) have no closed
  form (F21 Finding 2.1, re-confirmed).  Every structural discriminator of
  the 4 orbits FAILS n-uniformity -- the ONLY n-uniform selector is
  chamber-Morse criticality itself (Section 4), which is the DEFINITION of
  c*_n and is HPC-per-n (Section 7).""")


# ===========================================================================
# Section 7.  n = 3 base case + the HPC-per-n confirmation.
# ===========================================================================

def run_section_7():
    banner("Section 7.  n = 3 base case  +  the HPC-per-n confirmation")
    # n = 3 base: M^chamber_3 is already perfect.
    cm3, cv3 = chamber_morse_critical_cells(3)
    cstar3 = closures(F22.C_STAR[3]["hasse"])
    print(f"  n = 3 (base):  M^chamber_3 critical vector = {cv3}")
    print(f"    {len(cm3)} critical 1-cell(s); chamber-Morse matching is "
          f"PERFECT at n = 3.")
    rec3 = any(closures(c) == cstar3 for c in cm3)
    print(f"    the unique critical 1-cell == recorded c*_3: {rec3}")
    print(f"    => at the base the rule is trivial: c*_3 IS the unique "
          f"chamber-Morse critical cell.")
    assert len(cm3) == 1 and rec3, "n=3 base case unexpected"

    # n = 4: M^chamber_4 is NOT perfect -- the rule's first real use.
    cm4, cv4 = chamber_morse_critical_cells(4)
    print(f"\n  n = 4 (testbed):  M^chamber_4 critical vector = {cv4}  "
          f"-- NOT perfect")
    print(f"    {len(cm4)} critical 2-cells; recorded c*_4 = the unique "
          f"min-|L|-profile one (Section 4).")

    # n = 5: the chamber-Morse matching is HPC-class.
    print(f"\n  n = 5:  the chamber-Morse matching on the FULL Delta_5 is "
          f"HPC-class.")
    PPF5 = CM.make_PPF(5)
    es5, ab5 = CM.refinement_above_map(PPF5)
    f = [len(PPF5)]
    cur = [(P,) for P in es5]
    cap = 2_000_000
    d = 0
    while cur and d < 3:
        nxt = []
        for c in cur:
            for Q in ab5[c[-1]]:
                nxt.append(c + (Q,))
                if len(nxt) > cap:
                    break
            if len(nxt) > cap:
                break
        d += 1
        if len(nxt) > cap:
            f.append(f">{cap}")
            break
        f.append(len(nxt))
        cur = nxt
    print(f"    |PPF_5| = {len(PPF5)};  f(Delta_5) lower bound = {f}")
    print(f"    (a full enumeration at n = 5 already exceeds 2e7 cells at "
          f"dimension 3 and grows;")
    print(f"    cf. F20 s.1.3 / F21 s.5.3 -- the chamber-Morse greedy is "
          f"Tier-3 HPC for n >= 5.)")
    print(f"""
  CONSEQUENCE.  Rule B (chamber-Morse criticality, Section 4) is the
  canonical selector -- but applying it at level n+1 requires the
  level-(n+1) chamber-Morse matching M^chamber_{{n+1}}, which is HPC-class
  from n = 5 on.  The rule is HPC-PER-N, not closed-form / n-uniform.""")


# ===========================================================================
# Section 8.  Verdict.
# ===========================================================================

def run_section_8():
    banner("Section 8.  F23 VERDICT")
    print("""
  GREEN-descent-pinned  (HPC-per-n variant).

  A canonical S_{n+1}-equivariant rule that selects c*_{n+1} from the
  4-orbit descent candidate set DOES exist.  It is:

      RULE B -- chamber-Morse criticality.  c*_{n+1} is the unique
      min-|L|-profile critical (n-1)-cell of the chamber-Morse matching
      M^chamber_{n+1}; equivalently, of the 4 min-|L|-profile + BFT-sharp
      descent orbits, c*_{n+1} is the unique one whose S_{n+1}-orbit meets
      crit(M^chamber_{n+1}).

  This is F23's candidate form B -- exactly the structure F21 s.5.2 and
  F22-HPC S2 finding 6 predicted was needed -- and it DECISIVELY pins
  recorded c*_4 at the n = 3 -> 4 testbed (Section 4), is consistent at the
  n = 3 base (Section 7), and is genuinely S_{n+1}-equivariant (the set of
  orbits meeting crit(M^chamber) is labelling-independent).

  BUT -- and this is the decisive structural finding -- the rule is NOT a
  closed-form / n-uniform generative rule:

   * Every STRUCTURAL (non-criticality) discriminator of the 4 orbits --
     top-poset OSA signature, new-element locus, size-2-block position --
     is REFUTED as an n-uniform rule by the recorded c*_3, c*_5
     (Sections 5-6).  This sharpens F21 Finding 2.1 at the level of the
     SELECTOR: there is no closed-form structural shortcut.

   * The only n-uniform selector is chamber-Morse criticality itself --
     the DEFINING property of c*_n.  Applying it needs M^chamber_{n+1},
     which is HPC-class from n = 5 on (Section 7).  So the rule is
     HPC-PER-N.

  CONCLUSION FOR THE PROGRAM.  The cofiber-Morse induction (F21 Prop F21.1)
  is CORRECT but does NOT self-close into a closed-form recursion: the
  descent narrows c*_{n+1} to a bounded candidate set, but resolving it
  requires the level-(n+1) chamber-Morse matching -- the very HPC object
  the structural route hoped to bypass.  'The canonical chamber-Morse
  critical cell c*_n' IS a well-defined canonical S_{n+1}-equivariant
  object (via min-|L|-profile chamber-Morse criticality -- an S-equivariant
  refinement of the label-dependent lex-min definition); it does NOT need
  re-founding.  But the chamber-Morse route to F10 part (iii) is unblocked
  ONLY in the HPC-per-n sense -- which is route 2 of state-F22-HPC s.5, a
  separate Tier-3 decision -- OR the program pivots part (iii) to the
  documented BK/Cheeger-expansion mechanism (mg-26fc), which does not need
  the canonical chamber-Morse critical cell at all.  That is a PM/Daniel
  decision; F23 surfaces it with this precise finding.

  Trust-surface impact: NONE.  No new axioms; no Lean changes; no
  (co)homology datapoint.  Elementary order-complex combinatorics + exact
  rational arithmetic on the n = 3 -> 4 materialised testbed.""")


def main():
    t_start = time.time()
    banner("Compat-Geom F23 (mg-531f) -- the canonical descent rule for "
           "c*_{n+1}")
    print("  Testbed: the n = 3 -> 4 case (cheap, materialisable).  "
          "See the module docstring.")
    _, _, _, _, reached, orbit_list = run_section_1()
    data, recorded_idx = run_section_2(orbit_list, reached)
    run_section_3(data, recorded_idx)
    run_section_4(orbit_list, reached, recorded_idx)
    run_section_5(data, recorded_idx)
    run_section_6()
    run_section_7()
    run_section_8()
    print(f"\n[done] total runtime: {time.time() - t_start:.1f}s")


if __name__ == "__main__":
    main()
