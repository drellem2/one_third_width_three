# EVALUATION — a lightweight unixy CLI to track proof/formalization progress

**Work item:** `mg-9f98` (Daniel request, 2026-07-13). **Type:** evaluation, not a build.
**Question:** should we build a small unix-style CLI to track proof + formalization
progress in a big math project — to stop *losing the thread* — or does the existing
stack (git + Lean + markdown + `mg`) already carry that load?

**Bottom line up front (BLUF).**
**Do not build a stateful proof-tracker CLI or daemon.** It would become a *third*
source of truth next to Lean and the docs, and — like every hand-maintained status
artifact in this repo already does — it would drift. **Recommended: a minimal middle
path** — one flat, git-tracked status file (a convention, ~1 line per proof node) plus
a **~150-line, stateless, read-only** `proof-status` script that *derives* the picture
from ground truth (Lean `sorry`/axiom counts, git freshness, the flat file) and, most
importantly, **flags drift**. Build it *only if* the staleness pain is actually biting —
and the evidence in this repo says it is. Everything else the tool might do, markdown +
git + `mg` already do as well or better.

---

## §1. The real problem: what "losing the thread" looks like here

This repo (`one_third_width_three`, the width-3 1/3–2/3 program) is the concrete case.
Measured today:

| Artifact | Count | What it is |
|---|---:|---|
| Commits on `main` | 228 | throughput is high; many are one-polecat-session |
| `docs/*.md` | 206 | proof docs, scoping, audits, probe reports, **state ledgers** |
| `docs/state-*.md` | ~80 | per-ticket cumulative "ledger" docs (F10, F19, S7-*, Case3Witness, …) |
| `docs/*status*.md` | ~19 | per-sub-lemma rollups (a5-*, a8-*, path-c, …) |
| Lean files | 147 | the formalization |
| `sorry` in Lean | 32 | open formalization obligations |
| named `axiom`s | 15 | paper-transcribed gaps (canonicalized in `lean/AXIOMS.md`) |
| `mg` work items (all) | 1690 | dispatch/task tracker across the fleet |

The "thread" is not one thread. There are **three overlapping layers**, and they are
tracked in three different ways with no unified view:

1. **The formalized slice** — Lean. Ground truth is machine-checked: `lake build`
   passes or not, `sorry` count, `#print axioms`. Objective, but only covers what has
   reached Lean.
2. **The paper proof tree** — LaTeX (`step1..8.tex`, `main.tex`) plus `AXIOMS.md` and
   the `\GAP{}` macro that now marks known math gaps inline. Status here is prose.
3. **The exploratory research frontier** — the `docs/` probe/scoping layer: the
   `F`-series (compatibility-geometry F1–F31), `Prong 3A–3I`, `L1b`, the algebraic
   program, the cap-enumerations. This is where most *walls* live and where "losing the
   thread" actually happens. Almost none of it is in Lean; it is a forest of markdown
   verdicts.

**The verdict vocabulary already exists** but is trapped in prose. Grepping doc bodies:
`GREEN` in 166 docs, `AMBER` in 121, `RED` in 104, `WALL` in 11, "conjectur…" in 89.
So the project already speaks a five-state status language (proven / green / amber /
red / walled) — it just isn't *queryable*, *aggregated*, or *freshness-checked*.

**Concrete symptoms of losing the thread (all observed in this repo):**

- **No frontier view.** To answer "what is currently open, walled, or at the frontier?"
  you must read across ~200 docs. There is no `one screen` answer.
- **Staleness is admitted, not prevented.** `PROOF-STRUCTURE-ONBOARDING.md` opens with a
  maintenance contract and the line *"If a section conflicts with current source, source
  wins and this file is wrong — fix it."* Its own §1–§3 are flagged as predating a later
  refactor (`mg-9add`) and describing a now-deleted code path. The status layer drifts
  from ground truth and the docs *know* it.
- **Unit mismatch between the tracker and the proof.** `mg` tracks *dispatches*. A `done`
  `mg` ticket means *a polecat finished a session*, not *a lemma is proven*. Several
  landed tickets in the log are audits that ended `RED` ("the math is NOT finished").
  So the one tool that *is* a CLI tracker answers "what work happened," not "what is the
  status of claim X."
- **Ground truth and prose are disconnected.** Nothing checks that a doc saying "S7-E is
  formalized" still corresponds to a live, `sorry`-free Lean anchor. The `sorry`/axiom
  counts drift silently against the narrative.

That is the honest problem statement. Note what it is **not**: it is *not* a capture
problem. This project captures state obsessively (80 state ledgers!). It is an
**aggregation + query + freshness** problem.

---

## §2. Option A — a lightweight unixy CLI proof-progress tracker

The idea: a CLI that tracks lemma/sub-lemma states (proven / walled / conjectured /
formalized-in-lean) and sits alongside git + Lean.

**What it would track.** A node per proof obligation: an id (`S7-E`, `L1b`, `F31`,
`cap-5`), a status from the five-state vocabulary, a Lean anchor (file:line or theorem
name), a paper anchor (`step8.tex:2714`), the owning doc, and the `mg` ticket(s).
Edges for dependencies (this is the proof *tree*).

**The trap — and it is the decisive one.** The obvious CLI design is *stateful*: a
command like `proof set S7-E formalized` that writes to a local DB or JSON store. **That
store is a fourth source of truth** (after Lean, LaTeX, and the docs), and it is the
*most* prone to drift because updating it is a separate manual act that nothing forces.
This repo has already run the experiment: the `state-*.md` ledgers and `AXIOMS.md` *are*
a hand-maintained status store, and the onboarding doc documents its own staleness. A
stateful CLI reproduces exactly that failure mode with worse ergonomics (you lose
markdown's prose, diffs, and grep-ability) and no compensating benefit.

**What "unixy" actually should mean here.** The unix lesson is not "write a CLI." It is
**compose small tools over plain text, and derive state instead of storing it.** A tool
that *reads* Lean + git + one flat file and *computes* the rollup — holding **no mutable
state of its own** — is unixy. A tool with its own database is not; it is a
mini-application wearing a CLI. The distinction is the whole evaluation.

**What a stateless-derive tool buys over a plain `STATUS.md`** (the honest short list):

- **Query/rollup:** "count by status," "list all `WALL`s," "show frontier (open nodes
  whose deps are all proven)." Markdown can't compute this; you read it.
- **Freshness/drift check (the load-bearing feature):** cross-check the flat file's
  claims against ground truth — *node marked `formalized` but its Lean anchor still has a
  `sorry`* → flag; *anchor theorem no longer exists* → flag; *owning doc untouched for N
  commits while the node is "in progress"* → flag. This is precisely the thing humans and
  markdown are bad at and the thing this repo demonstrably suffers.
- **Ground-truth pull:** auto-report `sorry`/axiom counts from Lean so the formalized
  slice's numbers are never hand-typed.

Everything *else* a tracker CLI might offer — capturing narrative, recording why a wall
is a wall, onboarding a new contributor — **markdown + git already do strictly better.**

---

## §3. Option B — just use Lean end-to-end; is a separate tracker redundant?

Daniel's alternative: use Lean from beginning to end, and let Lean's own tooling
(`sorry`-tracking, `#check`, `#print axioms`, build state) be the progress signal.

**Where Option B is genuinely sufficient — the formalized slice.** For anything that has
reached Lean, Lean *is* the tracker and no external tool can beat it, because its signal
is machine-checked, not asserted:

- `lake build` — binary "does the whole thing still compile."
- `grep -rn sorry` — 32 open obligations, exactly located.
- `#print axioms OneThird.width3_one_third_two_thirds` — the exact axiom surface the
  headline still leans on. `AXIOMS.md` already curates this.
- `#check` / the type of a theorem — the precise contract of a lemma.

For a proof that is *born formalized* (Lean-first, every lemma stubbed with `sorry` then
discharged), Option B would make a separate tracker almost entirely redundant. This is a
real and attractive workflow, and for a *future* project it may be the right default.

**Where Option B is insufficient for *this* project — everything before Lean.** Look at
where the thread is actually lost: the `F`-series, `Prong 3A–3I`, `L1b`, the algebraic
program, the near-ordinal-sum probes. This is **pre-formalization research**: deciding
*whether a route works at all*, hitting *walls* (F31 chain-locality; Prong 3E self-dual
floor), running empirical n=11–13 sweeps. Lean has nothing to say here because there is
nothing to formalize yet — the math is being *discovered or ruled out*. A `sorry` can
only stand for a statement you can already write down; it cannot represent "we tried the
correlation-inequality route and it's provably insufficient (`mg-f9f4`)." The majority of
the "losing the thread" surface in this repo is exactly this un-Lean-able exploratory
layer.

So: **Lean is a necessary ground-truth input, not a sufficient tracker.** Option B solves
the formalized slice and says nothing about the paper-math slice or the research frontier
— which is where the pain is.

---

## §4. Honest recommendation

**Ranked, with the skeptical bar applied ("prove the tool earns its complexity").**

### Don't: build a stateful proof-tracker CLI or daemon (heavy Option A). ❌
It duplicates `mg` (dispatch tracking), Lean (formalized ground truth), and the docs
(narrative), and adds a fourth store that will drift — the exact failure this repo
already exhibits with its hand-maintained ledgers. It loses markdown's prose and diffs.
No.

### Don't: rely on Lean end-to-end for *this* project (pure Option B). ❌ (for now)
Lean is the right tracker for the formalized slice and should keep being ground truth,
but ~most of the thread here lives in pre-formalization research that Lean structurally
cannot represent. Adopt Lean-first *going forward* if desired, but it does not solve
today's problem.

### Do: the minimal middle path — one flat file + a stateless read-only script. ✅ (conditionally)
Build this **only if** the staleness/frontier pain is actually costing time — and the
evidence (a self-admittedly-stale onboarding doc, 200 docs with no frontier view, a
tracker whose unit is dispatches) says it is. Keep it ruthlessly small.

**The convention (this is 90% of the value and is nearly free):**
One git-tracked flat file, e.g. `proof-tree.toml` (or `STATUS.md` with a table). One
row per proof node:

```toml
[[node]]
id        = "S7-E"                      # stable handle
status    = "formalized"                # proven | formalized | amber | red | walled | open
paper     = "step7.tex:prop:72"         # anchor into LaTeX
lean       = "OneThird.Step7.prop_72"    # theorem name OR file:line, or "" if not in Lean
doc       = "docs/state-S7-E-*.md"      # where the narrative lives
mg        = ["mg-516f"]                 # dispatch(es)
deps      = ["S7-C", "S7-D"]            # proof-tree edges
note      = "grounded assembly; bandwidth ≤ 4"
```

This alone gives a single, diffable, grep-able index of the proof tree — something the
206 scattered docs do not currently provide. It is just markdown+git; it needs no tool.

**The tool (the other 10% — the part markdown can't do):**
A single stateless script, `scripts/proof-status` (bash or ~150 lines of Python),
**read-only, no state of its own.** Subcommands:

- `proof-status frontier` — list nodes that are `open` but whose `deps` are all
  `proven`/`formalized` (the actionable frontier); print counts by status.
- `proof-status walls` — list every `walled`/`red` node with its `note` (the "what have
  we ruled out" view — currently unanswerable without reading everything).
- `proof-status check` — **the load-bearing command.** For every node, cross-check the
  claim against ground truth and print drift:
  - `status=formalized` but the `lean` anchor is missing or its file still contains a
    `sorry` in scope → **DRIFT**.
  - `lean` anchor names a theorem not found by `grep`/`lake env lean` → **STALE ANCHOR**.
  - node `open`/`amber` but `doc` untouched for > N commits (`git log`) → **possibly
    abandoned**.
  - report `sorry`/axiom totals pulled live from Lean, so no count is ever hand-typed.
- `proof-status show <id>` — one node's full record + its live Lean status.

**Why this earns its complexity (the test the task demanded):**
Against plain markdown+git, the only thing it adds is *computation over the flat file +
ground truth* — the rollup, the frontier, and above all the **drift check.** Drift is the
one failure this repo provably has and that no amount of disciplined markdown prevents,
because it requires *cross-referencing prose against machine state on every change.* A
~150-line stateless script does that; a human doesn't. That is a real, narrow,
defensible win. Everything outside that narrow win, we deliberately *don't* build.

**Why it stays unixy and won't drift like the ledgers did:** it stores nothing. The flat
file is the only human-edited artifact (and it's plain text under git). The tool's output
is always recomputed from Lean + git + that file, so it *cannot* silently disagree with
ground truth — the worst case is it *tells you* the file disagrees, which is the point.

**Explicit non-goals (kill these if they creep in):**
no database, no daemon, no long-running process, no `set`/mutate commands, no
re-implementing `mg` (link to `mg` ids, don't track dispatches), no parsing of Lean
proofs (grep the `sorry`s; let `lake` be the checker), no web UI.

**Smallest useful v1 (a half-day, not a project):**
1. Write `proof-tree.toml` for the *current headline path only* (~15–25 nodes: the
   `MainAssembly` proof-by-contradiction spine + its 5 axioms + the live `sorry`). Not
   all 200 docs — just the load-bearing tree.
2. Write `proof-status check` and `proof-status frontier`. Nothing else.
3. Run `check`; if it surfaces even one real drift on day one (a doc claiming something
   Lean no longer supports), the tool has already paid for itself. If it surfaces none,
   the flat file alone was the win and you can stop there — that is a *successful*
   outcome, not a failure.

### Cheapest alternative if even v1 is too much: ⚙️
Skip the custom script entirely and lean harder on what exists: keep a single
`STATUS.md` frontier table by hand, and add a **CI check** (the repo already has a Lean
GitHub Action) that fails if the `sorry`/axiom count changes without a corresponding
`STATUS.md`/`AXIOMS.md` edit. That gets ~60% of the drift protection for near-zero new
code and no new tool. Consider this the true minimum; escalate to the `proof-status`
script only if the frontier/query need is felt in practice.

---

## §5. Summary table

| Approach | Formalized slice | Paper-math slice | Research frontier | Drift protection | New complexity | Verdict |
|---|---|---|---|---|---|---|
| Stateful tracker CLI/daemon (heavy A) | dup of Lean | its own store | its own store | **worse** (4th store) | high | ❌ don't |
| Pure Lean end-to-end (B) | ✅ excellent | ✗ n/a | ✗ can't represent | ✅ for Lean only | low | ✅ keep as ground truth, insufficient alone |
| markdown `STATUS.md` + git only | manual | ✅ prose | ✅ prose | ✗ none | ~zero | good, but no frontier/drift |
| **Flat file + stateless read-only script (middle path)** | pulls Lean truth | ✅ prose + index | ✅ prose + index | ✅ **the point** | ~150 LOC | ✅ **recommended, if pain is real** |
| `STATUS.md` + CI count-guard (cheapest) | CI-guarded | ✅ prose | ✅ prose | ~partial | ~zero | ✅ true minimum |

**One-line answer to Daniel:** don't build a proof-tracker *application*; the unix move
is a flat status file plus a tiny **stateless** script whose only real job is to shout
when the prose and the Lean/git ground truth disagree — build that, and only that, and
only once the drift is actually costing you.

---

*Author: polecat `mg-9f98`, 2026-07-14. Evaluation only; no proof/Lean/data files
touched (per constraint — `dbd1` is proving L1b concurrently). Grounded on the live state
of `one_third_width_three`: 228 commits, 206 docs, 147 Lean files, 32 `sorry`s, 15
axioms, `mg` = 1690 items.*
