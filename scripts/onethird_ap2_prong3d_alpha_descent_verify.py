#!/usr/bin/env python3
r"""
onethird_ap2_prong3d_alpha_descent_verify.py
============================================

OneThird Algebraic-Program **AP-2 Prong 3D-alpha** (mg-5ff1) -- the constructive
descent ray.  Follow-up to mg-8bd6 (Prong 3C), which REFUTED the 14/39 floor by
exhibiting a width-3 poset at n=10 with Q = 6/17 < 14/39, narrowing the
counterexample-hunt corridor to (1/3, 6/17], and discovered the DESCENT LADDER

        Q = 1/3 + 1/(3k) = (k+1)/(3k),   binding-pair Pr = (2k-1)/(3k) -> 2/3,

with three integral rungs k = 11 (n=5, Q=4/11), 13 (n=7, Q=14/39), 17 (n=10,
Q=6/17).  Prong 3D-alpha attempts the CONSTRUCTIVE descent ray: name a jump
operator P_k -> P_{k'} that steps the ladder, and extend it (PRIMARY >=3 rungs;
STRONGER cofinal K; WEAKER finite-stall; REFUTATION off-ladder smaller Q).

VERDICT (this prong): **Outcome-4 clean diagnosis + WEAKER finite-stall.**
  No jump operator extending the ladder beyond k=17 is found.  Concretely:

  (A) NEW STRUCTURAL FINDING -- all three ladder witnesses are SELF-DUAL width-3
      posets (they admit an order-reversing automorphism sigma), and the near-
      twin binding pair is the sigma-orbit pair:
          seed   (k=11): sigma = (a0 c0)(b1 b2)(b0)        [b0 sigma-fixed]
          14/39  (k=13): sigma = (0 6)(1 5)(2 4)(3)        [reversal, 3 fixed]
          6/17   (k=17): sigma : i <-> i+5 (mod 10)        [fixed-point-free]
      Self-duality is the hidden symmetry of the descent ladder; it is verified
      here by an explicit order-reversing-involution finder.

  (B) THE NAIVE JUMP-OPERATOR CANDIDATES OVERSHOOT.  Every one-parameter stretch
      of a witness (lengthen the central chain up / down; lengthen the heavy
      twin's chain) leaves the ladder immediately: Q rises toward 1/2, not down
      toward 1/3.  The closed-form reason is the gadget identity for a point x
      parallel to a t-chain y_1<...<y_t:
          Pr[x < y_i] = i/(t+1).
      The textbook gadget t=2 is the UNIQUE chain length whose incomparable
      pairs sit at exactly {1/3, 2/3} with NO middle pair; for t>=3 a middle
      pair lands near 1/2 and Q jumps up.  So "lengthen a chain" cannot descend
      the ladder -- it manufactures a balanced side pair.

  (C) 6/17 IS A STRICT SELF-DUAL LOCAL FLOOR.  Exhaustively over every width-3
      self-dual extension of the 6/17 witness by one sigma-symmetric move:
          +1 (a sigma-fixed central element): all 10 width-3 cases -> min Q=4/11;
          +2 (a sigma-symmetric pair):        all 163 width-3 cases -> min Q=6/17,
      with equality ONLY for the trivial global-top/global-bottom adjunction
      (D=empty, U=full), which is Q-preserving (the order-polytope analogue of
      Prong-3A Lemma B, "series = max").  Every NON-trivial self-dual local move
      raises Q.  Together with Prong 3C's beam+anneal stall to n<=14, the
      constructive descent ray does NOT extend below 6/17.

  So the descent ladder is -- as far as construction and exhaustive local /
  self-dual search reach -- a THREE-RUNG phenomenon (k = 11, 13, 17).  The
  corridor is UNCHANGED at (1/3, 6/17]; 6/17 is the stall rung / corridor
  ceiling.  This neither proves inf Q = 1/3 (PRIMARY/STRONGER not reached) nor
  proves a floor Q >= 6/17 (that is the Prong-3E target); it is a clean negative
  diagnosis of the constructive route, with the self-duality + overshoot
  mechanism as the structural content.

GUARD (roadmap 8.2 anti-Cheeger, INHERITED STRICT).  Every Q encountered is
> 1/3 (lowest anywhere is 6/17).  The guard does NOT fire; M1..M4 + MC suffice;
no SIXTH codebase is triggered (that trigger is reserved for a Q <= 1/3 claim,
which does not arise here).

Reuses the mg-8bd6 / mg-3b16 five-engine harness (M1 order-ideal DP, M2 AP-0
kernel, M3 minimal-element-removal recursion, M4 brute permutations, MC Ehrhart
order-polynomial) VERBATIM, and adds: the self-duality finder, the jump-operator
attempt constructors (overshooting families + the i/(t+1) gadget identity), the
exhaustive self-dual local-floor scan, and the ladder-rung Q checker.  Pure
standard library; default run a few seconds.
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction

# Five-engine harness + the three ladder witnesses, verbatim from the Prong-3C
# kernel (which itself re-exports the mg-3b16 / mg-2715 engines).
from onethird_ap2_prong3c_width3_floor_verify import (
    verify_C, k_of, witness_14_39_n7, witness_6_17_n10,
    FOUR_11, FOURTEEN_39, SIX_17,
)
from onethird_ap2_prong3b_gamma_familyC_probe import seed_4_11
from onethird_ap2_prong3b_beta_familyD_probe import (
    transitive_pred, incomparable_pairs, width_of, Q_primary, augment, count_le_dp,
    guard_check, GuardHalt, THIRD,
)

# --------------------------------------------------------------------------- #
# Order-reversing-involution finder (the self-duality witness).               #
# --------------------------------------------------------------------------- #
def find_involution(elems, below):
    """Return an order-reversing involution sigma (as a list over the index of
    `elems`) if the poset is self-dual, else None.  Backtracking with a
    down/up-degree-signature prune; fast at the witness sizes (n<=10)."""
    elems = list(elems)
    n = len(elems)
    idx = {e: i for i, e in enumerate(elems)}
    rel = [[False] * n for _ in range(n)]          # rel[i][j] = (elem i < elem j)
    for e in elems:
        for p in below[e]:
            rel[idx[p]][idx[e]] = True
    dn = [len(below[e]) for e in elems]
    up = [sum(1 for d in elems if e in below[d]) for e in elems]
    sig = [(dn[i], up[i]) for i in range(n)]
    rev = [(up[i], dn[i]) for i in range(n)]
    sigma = [-1] * n
    used = [False] * n

    def consistent(i, j):
        for a in range(n):
            if sigma[a] == -1:
                continue
            b = sigma[a]
            if rel[a][i] != rel[j][b] or rel[i][a] != rel[b][j]:
                return False
        return True

    def bt(i):
        if i == n:
            return all(sigma[sigma[a]] == a for a in range(n))
        if sigma[i] != -1:
            return bt(i + 1)
        for j in range(n):
            if used[j] or sig[i] != rev[j] or not consistent(i, j):
                continue
            sigma[i] = j; sigma[j] = i; used[i] = used[j] = True
            if bt(i + 1):
                return True
            sigma[i] = sigma[j] = -1; used[i] = used[j] = False
        return False

    return sigma if bt(0) else None


def assert_self_dual(name, elems, pairs):
    below = transitive_pred(list(elems), pairs)
    sigma = find_involution(list(elems), below)
    assert sigma is not None, f"{name}: expected self-dual, none found"
    # decode sigma into element labels for display
    el = list(elems)
    cycles = []
    seen = set()
    for i in range(len(el)):
        if i in seen:
            continue
        j = sigma[i]
        if j == i:
            cycles.append(f"({el[i]})"); seen.add(i)
        else:
            cycles.append(f"({el[i]} {el[j]})"); seen.add(i); seen.add(j)
    print(f"    {name:28s} self-dual: sigma = {''.join(cycles)}")
    return sigma


# --------------------------------------------------------------------------- #
# Closed-form gadget identity: point x || (t-chain y_1<...<y_t), Pr[x<y_i]=i/(t+1)
# --------------------------------------------------------------------------- #
def gadget_point_chain(t):
    elems = ["x"] + [f"y{i}" for i in range(1, t + 1)]
    pairs = [(f"y{i}", f"y{i + 1}") for i in range(1, t)]
    return elems, pairs


# --------------------------------------------------------------------------- #
# Jump-operator ATTEMPT families (all OVERSHOOT for t>=2 -- leave the ladder). #
# --------------------------------------------------------------------------- #
def famA_seed_top(t):
    """Seed (k=11) with its central chain's TOP stretched to a chain c0<...<c_{t-1}."""
    elems = ["a0", "b0", "b1", "b2"] + [f"c{i}" for i in range(t)]
    pairs = [("a0", "b0"), ("a0", "b1"), ("b0", "c0"), ("b2", "c0")]
    pairs += [(f"c{i}", f"c{i + 1}") for i in range(t - 1)]
    return elems, pairs


def famB_seed_bottom(t):
    """Seed (k=11) with its central chain's BOTTOM stretched to a chain."""
    elems = [f"a{i}" for i in range(t)] + ["b0", "b1", "b2", "c0"]
    pairs = [("a0", "b0"), ("a0", "b1"), ("b0", "c0"), ("b2", "c0")]
    pairs += [(f"a{i + 1}", f"a{i}") for i in range(t - 1)]
    return elems, pairs


def famC_14_heavy(t):
    """14/39 (k=13) with the heavy twin's down-chain stretched to length t."""
    elems = [1, 2, 3, 4, 5, 6] + [f"z{i}" for i in range(t)]
    pairs = [(1, 4), (1, 5), (2, 4), (2, 5), (3, 6), (4, 6)]
    if t > 0:
        pairs += [(f"z{t - 1}", 2), ("z0", 3)]
        pairs += [(f"z{i}", f"z{i + 1}") for i in range(t - 1)]
    return elems, pairs


# --------------------------------------------------------------------------- #
# Self-dual local-extension floor scan on the 6/17 witness.                    #
# --------------------------------------------------------------------------- #
def _close(n, pairs):
    below = {i: set() for i in range(n)}
    for a, b in pairs:
        below[b].add(a)
    ch = True
    while ch:
        ch = False
        for c in range(n):
            new = set(below[c])
            for p in list(below[c]):
                new |= below[p]
            if new != below[c]:
                below[c] = new; ch = True
    for c in range(n):
        if c in below[c]:
            return None
    return {i: frozenset(below[i]) for i in range(n)}


def _ideals(base, below0):
    return [frozenset(c for c in base if (m >> c) & 1)
            for m in range(1 << len(base))
            if all(set(below0[e]) <= frozenset(c for c in base if (m >> c) & 1) for e in
                   (c for c in base if (m >> c) & 1))]


def _filters(base, below0):
    out = []
    for m in range(1 << len(base)):
        S = frozenset(c for c in base if (m >> c) & 1)
        if all((y in S) for x in S for y in base if x in below0[y]):
            out.append(S)
    return out


def selfdual_extend_fixed(base_n, base_pairs, sigma):
    """All width-3 self-dual extensions adding ONE sigma-fixed central element f
    (down-set D an ideal, up-set = sigma(D) a filter).  Yields (Q, e, D)."""
    below0 = _close(base_n, base_pairs)
    base = list(range(base_n))
    f = base_n
    for D in _ideals(base, below0):
        Uf = frozenset(sigma[x] for x in D)
        if D & Uf:
            continue
        pairs = list(base_pairs) + [(d, f) for d in D] + [(f, w) for w in Uf]
        nb = _close(base_n + 1, pairs)
        if nb is None or width_of(list(range(base_n + 1)), nb) != 3:
            continue
        e, Q, arg = Q_primary(list(range(base_n + 1)), nb)
        if Q is not None:
            yield Q, e, tuple(sorted(D)), (pairs, base_n + 1)


def selfdual_extend_pair(base_n, base_pairs, sigma):
    """All width-3 self-dual extensions adding a sigma-symmetric PAIR (u,v=sigma u)
    with u having down-ideal D and up-filter U; v gets the dual relations.
    Yields (Q, e, D, U, is_trivial)."""
    below0 = _close(base_n, base_pairs)
    base = list(range(base_n))
    ids = _ideals(base, below0)
    fils = _filters(base, below0)
    u, v = base_n, base_n + 1
    for D in ids:
        for U in fils:
            if D & U:
                continue
            Dv = frozenset(sigma[x] for x in U)
            Uv = frozenset(sigma[x] for x in D)
            pairs = list(base_pairs)
            pairs += [(d, u) for d in D] + [(u, w) for w in U]
            pairs += [(d, v) for d in Dv] + [(v, w) for w in Uv]
            nb = _close(base_n + 2, pairs)
            if nb is None or width_of(list(range(base_n + 2)), nb) != 3:
                continue
            e, Q, arg = Q_primary(list(range(base_n + 2)), nb)
            if Q is None:
                continue
            trivial = (len(D) == 0 and len(U) == base_n)   # u = global top, v = global bottom
            yield Q, e, tuple(sorted(D)), tuple(sorted(U)), trivial, (pairs, base_n + 2)


def main():
    ap = argparse.ArgumentParser(description="OneThird AP-2 Prong 3D-alpha descent-ray verify")
    ap.add_argument("--tmax", type=int, default=6, help="overshoot-family stretch range (default 6)")
    args = ap.parse_args()

    print("#" * 74)
    print("# OneThird AP-2 Prong 3D-alpha  --  constructive descent ray (k-jump)")
    print("# mg-5ff1   VERDICT: Outcome-4 clean diagnosis + WEAKER finite-stall at 6/17")
    print("#" * 74)

    try:
        # ---- 1. THE THREE LADDER RUNGS (five-engine + ladder identity) ----
        print("\n### 1. THE THREE KNOWN RUNGS -- five-engine + ladder identity ###\n")
        rungs = [("4/11 seed (k=11)", seed_4_11(), FOUR_11, 11),
                 ("14/39 witness (k=13)", witness_14_39_n7(), FOURTEEN_39, 13),
                 ("6/17 witness (k=17)", witness_6_17_n10(), SIX_17, 17)]
        for nm, (el, pr), Qexp, kexp in rungs:
            r = verify_C(nm, el, pr)
            assert r.Q == Qexp and r.width == 3, f"{nm}: Q/width mismatch"
            assert k_of(r.Q) == kexp, f"{nm}: k mismatch"
            assert 3 * r.Q - 1 == Fraction(1, kexp)
            assert r.Q == Fraction(kexp + 1, 3 * kexp)
            print(f"    {nm:24s} e={r.e:>4} Q={r.Q} = (k+1)/(3k), k={kexp}  [M1=M2=M3=M4=MC]")

        # ---- 2. SELF-DUALITY (the hidden symmetry of the ladder) ----
        print("\n### 2. SELF-DUALITY -- all three witnesses admit sigma (order-reversing) ###\n")
        assert_self_dual("4/11 seed", *seed_4_11())
        assert_self_dual("14/39 witness", *witness_14_39_n7())
        sigma6 = assert_self_dual("6/17 witness", *witness_6_17_n10())
        print("    => the near-twin binding pair is the sigma-orbit pair; the descent")
        print("       ladder lives in the SELF-DUAL width-3 subspace.")

        # ---- 3. JUMP-OPERATOR ATTEMPT (a): closed-form gadget identity ----
        print("\n### 3a. WHY NAIVE STRETCHES OVERSHOOT -- gadget Pr[x<y_i] = i/(t+1) ###\n")
        print("     point x || (t-chain y_1<...<y_t):  t=2 is the UNIQUE length with")
        print("     pairs at exactly {1/3,2/3} and no middle pair (=> Q=1/3).")
        for t in range(1, 6):
            el, pr = gadget_point_chain(t)
            below = transitive_pred(el, pr)
            e = count_le_dp(el, below)
            prs = [Fraction(count_le_dp(el, augment(below, "x", f"y{i}")), e)
                   for i in range(1, t + 1)]
            for i in range(1, t + 1):
                assert prs[i - 1] == Fraction(i, t + 1), "gadget i/(t+1) identity failed"
            _, Q, _ = Q_primary(el, below)
            tag = "  <- gadget: Q=1/3 (no middle pair)" if t == 2 else \
                  ("  <- middle pair -> 1/2, Q jumps up" if t >= 3 else "")
            print(f"     t={t}: e={e}  Pr[x<y_i]={[str(p) for p in prs]}  Q={Q}{tag}")

        # ---- 3. JUMP-OPERATOR ATTEMPT (b): one-parameter stretches LEAVE the ladder
        print("\n### 3b. JUMP-OPERATOR CANDIDATES -- one-parameter stretches OVERSHOOT ###\n")
        print("     (t=1 reproduces a rung; t>=2 leaves the ladder: 3Q-1 != 1/integer,")
        print("      Q rises toward 1/2 because a side pair becomes balanced.)\n")
        for fam_name, fam in [("famA seed-top  ", famA_seed_top),
                              ("famB seed-bot  ", famB_seed_bottom),
                              ("famC 14-heavy  ", famC_14_heavy)]:
            row = []
            for t in range(1, args.tmax + 1):
                el, pr = fam(t)
                below = transitive_pred(list(el), pr)
                _, Q, _ = Q_primary(list(el), below)
                guard_check(f"{fam_name} t={t}", Q)
                k = k_of(Q)
                onladder = (k is not None and k == int(k)
                            and Q == Fraction(int(k) + 1, 3 * int(k)))
                row.append(f"t={t}:{float(Q):.4f}{'(L)' if onladder else ''}")
            print(f"     {fam_name}: " + "  ".join(row))
        print("\n     '(L)' = on the ladder.  Only t=1 is on it; every stretch overshoots.")

        # ---- 4. SELF-DUAL LOCAL FLOOR at 6/17 (exhaustive +1 and +2) ----
        print("\n### 4. 6/17 IS A STRICT SELF-DUAL LOCAL FLOOR (exhaustive +1, +2) ###\n")
        bn, bp = 10, witness_6_17_n10()[1]
        # normalise the 6/17 pair-list to the {0..9} integer labels used by sigma6
        # (witness_6_17_n10 already returns integer-labelled pairs).
        sig = sigma6

        # +1: sigma-fixed central element
        min1 = None; cnt1 = 0; best1 = None
        for Q, e, D, _poset in selfdual_extend_fixed(bn, bp, sig):
            guard_check(f"6/17 +fixed D={D}", Q)
            cnt1 += 1
            if min1 is None or Q < min1:
                min1 = Q; best1 = (e, D)
        print(f"    +1 (sigma-fixed central element): {cnt1} width-3 self-dual extensions,")
        print(f"        min Q = {min1} = {float(min1):.6f}  (>= 6/17={float(SIX_17):.6f})  e,D={best1}")
        assert min1 >= SIX_17, "a +1 self-dual extension dipped below 6/17?!"

        # +2: sigma-symmetric pair.  A self-dual pair adjunction is e-PRESERVING
        # (Q-preserving, the Lemma-B analogue) exactly when it adjoins a global
        # top together with a global bottom -- detected here by e == base e.
        base_e = 187
        min2 = None; cnt2 = 0; epreserve_Q = set(); eincrease_min = None
        for Q, e, D, U, _flag, _poset in selfdual_extend_pair(bn, bp, sig):
            guard_check(f"6/17 +pair D={D} U={U}", Q)
            cnt2 += 1
            if min2 is None or Q < min2:
                min2 = Q
            if e == base_e:
                epreserve_Q.add(Q)
            else:
                if eincrease_min is None or Q < eincrease_min:
                    eincrease_min = Q
        print(f"    +2 (sigma-symmetric pair):        {cnt2} width-3 self-dual extensions,")
        print(f"        min Q = {min2} = {float(min2):.6f}")
        print(f"        e-preserving (global top+bottom) adjunctions hold Q in {sorted(map(str,epreserve_Q))}")
        print(f"        min over e-INCREASING extensions = {eincrease_min} = "
              f"{float(eincrease_min):.6f} > 6/17")
        assert min2 == SIX_17, "expected +2 self-dual floor = 6/17 (none below)"
        assert epreserve_Q == {SIX_17}, "e-preserving adjunctions must hold 6/17"
        assert eincrease_min > SIX_17, "an e-INCREASING +2 extension matched/beat 6/17?!"
        print("\n    => NO self-dual +2 extension beats 6/17; 6/17 is held ONLY by the")
        print("       Q-preserving global-top/bottom adjunction (Lemma-B analogue), and every")
        print("       e-INCREASING self-dual move RAISES Q.  With Prong 3C's beam+anneal stall")
        print("       to n<=14, the constructive descent ray does NOT extend below 6/17.")

        # ---- 5. VERDICT ----
        print("\n" + "#" * 74)
        print("# §8.2 GUARD + VERDICT")
        print("#" * 74)
        print(f"\n  ladder rungs (exact, five-engine): 4/11 (k=11), 14/39 (k=13), 6/17 (k=17)")
        print(f"  lowest Q anywhere in this prong .. 6/17 = {float(SIX_17):.6f} > 1/3")
        print(f"\n  §8.2 anti-Cheeger guard: lowest Q = 6/17 > 1/3 ==> guard does NOT fire")
        print(f"    (no Q<=1/3 candidate; M1..M4,MC suffice; no sixth codebase triggered).")
        print(f"\n  VERDICT: Outcome-4 clean diagnosis + WEAKER finite-stall.")
        print(f"    * NEW: the ladder witnesses are SELF-DUAL width-3 posets; the near-twin")
        print(f"      binding pair is the sigma-orbit pair.")
        print(f"    * Naive one-parameter jump-operator candidates OVERSHOOT (gadget identity")
        print(f"      Pr[x<y_i]=i/(t+1): only the t=2 length gives 1/3 with no middle pair).")
        print(f"    * 6/17 is a STRICT self-dual local floor: every non-trivial self-dual")
        print(f"      extension (+1, +2) raises Q; only the Q-preserving trivial adjunction")
        print(f"      holds 6/17.  No jump operator P_k -> P_{{k'>17}} found.")
        print(f"    * Corridor UNCHANGED at (1/3, 6/17]; 6/17 = stall rung / corridor ceiling.")
        print(f"      PRIMARY/STRONGER (inf Q=1/3) NOT reached; a Q>=6/17 floor is the Prong-3E")
        print(f"      target (not claimed here).")
        print("\n  CLEAN EXIT: five engines agree on every rung; ladder identities hold;")
        print("  self-duality verified; overshoot + self-dual local-floor confirmed; guard cleared.")

    except GuardHalt as gh:
        print("\n" + "!" * 74)
        print("# §8.2 GUARD FIRED -- HALT (INHERITED STRICT)")
        print("!" * 74)
        print(f"\n  {gh}")
        print("\n  Q <= 1/3 candidate: M1..M4 + MC all used; a fresh SIXTH codebase plus")
        print("  brute-force re-enumeration are mandatory before any claim.")
        sys.exit(2)


if __name__ == "__main__":
    main()
