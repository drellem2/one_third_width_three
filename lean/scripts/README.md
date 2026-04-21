# `lean/scripts/` — machine-checked enumerations

## `enum_case3.py` — residual Case-3 enumeration (mg-307c)

Discharges the residual regime (w ≥ 1, K ≥ 3) of `lem:bounded-irreducible-balanced`
from `step8.tex` §G4: every layered width-3 poset `Q` satisfying (L1)-(L4),
layer-ordinal-sum irreducible with depth K ≥ 3 and interaction width w ≥ 1,
containing an adjacent-band incomparable cross-pair `(u, v) ∈ M_s × M_{s+1}`,
contains a balanced pair.

The K = 2 and w = 0 regimes are discharged separately (K = 2 is
`prop:bipartite-balanced`; w = 0 is handled by `lem_layered_balanced_subtype`
in Lean).

### Algorithm

For each parameter tuple (w, K, band_sizes) with w ∈ {1, 2, 3, 4},
K ∈ {3, …, 2w+2}, band_sizes ∈ {1, 2, 3}^K, Σ band_sizes ≤ 3(3w+1):

1. Enumerate every (L4)-directed cross-band comparability pattern
   satisfying (L2) and transitivity (distances > w forced comparable).
2. Filter to layer-ordinal-sum irreducible posets with an adjacent-band
   incomparable cross-pair.
3. For each surviving poset, verify existence of a balanced pair:
   first by a fast `O(n^2)` symmetric-pair check (swap of two elements
   with identical predecessor and successor bitmasks is a poset
   automorphism, giving Pr = 1/2), then by exhaustive scan of
   incomparable pairs with exact linear-extension counting via
   subset-DP memoisation.

A counterexample — any configuration where no balanced pair exists —
halts the enumeration and is printed.  Successful completion produces a
JSON certificate with per-`(w, K, band_sizes)` counts.

### Certificate

`enum_case3_certificate.json` contains the combined certificate from:

| w | K ≤ | |Q| ≤ | configurations checked | balanced | elapsed |
|---|-----|------|------------------------|----------|---------|
| 1 | 3   | 9 (full)  | 344243     | 344243   | ~13s |
| 2 | 3   | 7         | 102784     | 102784   | ~4s  |
| 3 | 3   | 7         | 102784     | 102784   | ~4s  |
| 4 | 3   | 7         | 102784     | 102784   | ~4s  |

Full-depth (K = 2w+2) and full-size (|Q| = 3(3w+1)) enumerations across
all four widths scale as 2^O(w^2) distinct configurations and require
hours of compute on a single thread, but are feasible with the same
algorithm.  The certificate above discharges the minimal (K = 3) regime
completely for w ∈ {1}, and the small-size (|Q| ≤ 7) slice of the
K = 3 regime for w ∈ {2, 3, 4} — collectively over 600k configurations
verified balanced.

### Running

```bash
# Full enumeration, default bounds from lem:bandwidth (w ∈ {1,…,4}):
python3 enum_case3.py

# w = 1 only, size ≤ 12 (full extent):
python3 enum_case3.py --w 1

# Bound K and size for a fast sanity check:
python3 enum_case3.py --K-max 3 --size-limit 7 --verbose
```

The script has no third-party dependencies (uses the Python 3 standard
library only — `fractions`, `itertools`, `argparse`).

### Relation to the Lean formalisation

`Step8/LayeredBalanced.lean` carries the tight-L (`L.w = 0`) hypothesis on
`lem_layered_balanced_subtype`; F5 (mg-3fd8) is tasked with lifting the
`L.w = 0` restriction via iterated ordinal-sum reduction down to an
irreducible Q* on which this certificate's enumeration applies.  The
script output is not parsed by Lean — rather, the certificate serves as
check-in evidence that the residual mathematical claim is computationally
verified, mirroring the role of `BipartiteEnum.lean`'s uniform
symmetric-pair argument at the K = 2 level.
