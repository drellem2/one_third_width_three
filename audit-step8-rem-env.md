# Audit: `rem:*` environments in `step8.tex` (mg-232e)

Date: 2026-04-21

Performed under mg-232e (Q2). Read every `rem:*` environment in
`step8.tex` and flagged any that assert mathematical claims without
proof. Output: one new gap (A7 = mg-0015); other under-spelled
remarks are either decorative, already captured by an existing A-item,
or carry inline justification.

## Remarks catalogued

| Line | Label | Verdict |
|------|-------|---------|
| 273 | `rem:decomp-reduction` | proved inline (cross-pair + ordinal-sum reduction) |
| 290 | `rem:n-dependence-g1` | **flagged: arithmetic-condition fallback** (→ A7) |
| 371 | *(unlabeled)* "Why a single-cut argument suffices" | decorative/motivational |
| 778 | `rem:small-n` | decorative — content delegated to `lem:small-n` |
| 825 | `rem:one-invocation` | decorative/bookkeeping |
| 1068 | `rem:G2-sharp` | corollary of preceding `prop:G2` proof |
| 1080 | `rem:G2-order` | **flagged: same arithmetic-condition fallback** (→ A7) |
| 1119 | *(unlabeled)* "Notation clashes" | decorative/bookkeeping |
| 1208 | `rem:final-constants-audit` | **flagged: same arithmetic-condition fallback** (→ A7) |
| 1349 | `rem:layered-from-step7` | **flagged** — already captured by A5 (mg-a356) |
| 1514 | `rem:shallow-layering` | decorative — content in `lem:layered-balanced` |
| 1526 | *(unlabeled)* "Disjoint-union analogue is absorbed" | argued correctly inline (uses (L2)+(L3) of `def:layered`) |
| 1745 | *(unlabeled)* "Finite enumeration" (bipartite) | confirmation of `prop:bipartite-balanced` |
| 1798 | `rem:g3-g4-interface` | decorative summary of G3/G4 interplay |

## New gap surfaced: A7 (mg-0015)

Three `rem:*` environments assert that when the quantitative
arithmetic condition $\gamma^2 c_5(T) c_6 \delta_0 \ge 8$ fails, the
small-$n$ base case (`rem:small-n`) handles the 1/3--2/3 property
"directly" or "without invoking the cascade":

- `rem:n-dependence-g1` (step8.tex:306-310)
- `rem:G2-order` (step8.tex:1098-1102)
- `rem:final-constants-audit` "Satisfiability" ¶ (step8.tex:1299-1304)

The same claim appears in the main-theorem proof's "Realizability of
the cascade" paragraph (step8.tex:554-557).

**Why this is under-spelled.** `rem:small-n` + `lem:small-n`
only cover $n \le n_0(\gamma, T)$, where
$n_0(\gamma, T) = \Theta(C_{\mathrm{exc}}(T)/\gamma)$ is set by the
perturbation threshold `eq:n0-main` — independently of the arithmetic
condition. The Kahn--Linial fallback inside `rem:small-n` discharges
all $n$ only when $\gamma \ge 1/3 - \delta_{\mathrm{KL}} \approx
0.0573$. For $\gamma < 1/3 - \delta_{\mathrm{KL}}$ *and* arithmetic
condition failing *and* $n > n_0(\gamma, T)$, the paper has no
coverage.

Concretely, $\eta(\gamma,n)(n-1) = 2(n-1)/(\gamma n)$ increases in
$n$, so if the arithmetic condition fails at $n \to \infty$
($\gamma^2 c_5 c_6 \delta_0 < 8$), the cascade breaks for all
sufficiently large $n$, and `rem:small-n` has no mechanism to
intercept those $n$.

See mg-0015 for the full work item and suggested resolutions.

## Relationship to existing A-items

- **A1** (mg-17e1) — `lem:window-localization` expansion.
- **A2** (mg-164c) — irreducible ⇒ adjacent incomparable cross-pair.
- **A3** (mg-ec58) — Gap M-b: inner windowLocalization isolation.
- **A4** (mg-c774) — chained balanced-pair lift.
- **A5** (mg-a356) — `rem:layered-from-step7` ground-set lift (covers
  the gap flagged in the `rem:*` at line 1349).
- **A6** (mg-d0e4) — `eq:exc-perturb` perturbation bound.
- **A7** (mg-0015) — *new* — arithmetic-condition fallback in
  `rem:n-dependence-g1`/`rem:G2-order`/`rem:final-constants-audit`.

The rest of the `rem:*` environments are either purely decorative
(bookkeeping, summaries, motivational) or carry sufficient inline
justification for their claims.
