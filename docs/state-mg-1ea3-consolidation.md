# State — mg-1ea3: compat-geom F-series consolidation onto main

**Ticket:** mg-1ea3 — Consolidate scattered compat-geom F-series branches onto main.
**Status:** DONE (single session). Integration branch built; submitted to refinery targeting `main`.
**Date:** 2026-05-14.

## What was done

All **39** `compat-geom-*` branches on `origin` were consolidated onto one
integration branch off current `main` (`16ae18f`), in **chronological order** (by
tip commit date). The history is a **linear sequence of 39 squash-merge commits**
(one per branch, `compat-geom consolidation: <branch>`) so it rebases cleanly in
the refinery and the per-branch narrative stays auditable. The resulting tree is
identical to a straight `git merge --no-ff` of all 39 branches.

### Branches consolidated (chronological)

scoping, hecke-scoping, hecke-brightwell, cell-poset, pathP3, heap-windowC,
cuts-by-pairs, eigensheaves, poset-cohomology, posn-sphere, site-refinement,
F1-refined, F2-discrete-morse, F3-omega-spectrum, F4-inductive-survey,
F5-chamber-morse-n5, F6-forman-cancellation, F7-equivariant-morse,
F7prime-equivariant-matching, F8-inductive-general-n, F8pp-quillen-fiber,
F8prime-n6-icop, F8ppp-betti-cofiber, F8p5-lit-integration, F8p4-spectral-E2,
F8p-hpc-n6, out-s6-audit-n6, F9-constructive-lift, PCR-Lit-3-fi-module,
PCR-Lit-2-hersh-welker, F9-S2-n7-pattern, F10-general-n-proof,
F12-methodology-paper, F11-fg-cofiber-attack, F13-E1-functoriality,
F14-B4-cofiber-cohomology, F15-E2-partial-d3-iso, mg26fc-bruhat-expansion-lens,
F16-route-ii-weaker-central-stability.

### Result

- **85 files changed** vs `main` (75 added, 10 modified): 38 `compatibility-geometry-*`
  docs + manifesto, 9 `state-F*.md` ledgers, methodology-paper draft/status,
  general-n-proof-synthesis, 24 `scripts/*.py`, 1 new Lean file
  (`Step8/Case3Enum/K4W1.lean`), and the pathP3 Lean delta (9 modified Lean files +
  `lean/README.md`).
- `docs/roadmap.md` and `docs/path-c-cleanup-roadmap.md`: **unchanged** — no
  compat-geom branch ever touched a roadmap file (the worry in the brief did not
  materialise; each branch was a pure deliverable-doc/script addition).
- Deliverable integrity verified: all 146 (file, blob, branch) entries across the
  39 branches are present in the final tree — 138 byte-identical, 8 union-reconciled
  (the 3 files below).

## Conflict resolution

The consolidation was almost entirely conflict-free: every shared file across
branches carried byte-identical content **except** three, all resolved by union
with **nothing dropped**:

1. **`.gitignore`** — 4 branch variants, each additive over `main`. Resolved to the
   union of all entries: `scripts/_n6_cache/`, `scripts/_*.log`,
   `scripts/__pycache__/`, `__pycache__/`, `*.pyc`, `.pogo/`, `.claude/`.
2. **`docs/state-F8prime-HPC.md`** — `out-s6-audit-n6`'s version (93 lines) is a
   strict superset of the `F8p-hpc-n6` / F9 version (79 lines): it inserts one
   `mg-3219 follow-up` block. Kept the superset.
3. **`docs/state-F9.md`** — `F9-S2-n7-pattern` is the Session-2 evolution of
   `F9-constructive-lift`'s Session-1 ledger (same lineage; F9-S2's commit is a true
   git descendant of F9-constructive's). Took the 187-line Session-2 version: it
   fills in the Session-1 PENDING entries with results — no Session-1 fact lost.

No **genuine semantic conflict** (two tickets disagreeing on a fact) was found, so
no STOP/escalation to pm-onethird was required.

## Lean build note

Only `compat-geom-pathP3` carries Lean changes (its delivered content for mg-9a4a:
narrowing the `InCase3Scope` gate; +1 new file, +88/-3 in `AXIOMS.md`, all
additive — **no new project axiom**, signature unchanged). `main`'s `lean/` tree is
**byte-identical** to pathP3's merge-base (`cd8c4a5`) — `main` has had only
roadmap-regeneration commits since. Therefore the integration branch's `lean/` tree
equals pathP3's tip `lean/` tree exactly; if pathP3 built clean as a delivered
ticket, so does this branch. No Lean toolchain is available in the polecat
environment for a local `lake build`; CI (`.github/workflows/lean.yml`) verifies on
merge to `main`.

## Out of scope / follow-ups

- **Arc branches** `a8-s2-cont-execution-arc`, `a8-s2-cont-scoping-arc`: checked per
  the brief — they contain **zero compat-geom content** (EX-series / path-alpha
  work, merge-base `e1caaae` from 2026-05-06, predating compat-geom). Correctly
  excluded.
- **`cat-mg-4d3a` (F17)** and **`cat-mg-a814` (UC2)**: in flight during this
  consolidation — to be folded in via a later follow-up, not blocked on here.
- The ~240 `polecat-*` branches: separate leftover-work cruft, out of scope.
