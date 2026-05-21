# State — S7-F-B — Session 1: wire the synchronization maps from the `ChainLiftData`; handle orphan inclusion

**Ticket:** mg-120d (OneThird-S7-F-B — S7-F bridge sub-arc B: wire the
synchronization maps `f_AB/f_AC/f_BC` from the `ChainLiftData`, prove
monotonicity, extend the domain, make orphan inclusion decidable).
**Type:** Lean deliverable.
**Parent:** FULL REFACTOR Phase 2, Piece 3 (the S7-F bridge),
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 sub-arc
`mg-S7-F-B`.
**Depends:** mg-3119 (S7F-R2, reconciled contract), mg-974c (S7F-R1,
concrete `ChainLiftData`). Parallelizable with mg-S7-F-A.
**Predecessors read:** `docs/PROOF-STRUCTURE-ONBOARDING.md`;
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3;
`docs/state-S7F-R1-Session1.md` (the concrete `ChainLiftData`);
`docs/state-S7F-Checkpoint3-Session1.md`; `step8.tex:2009-2167`.

---

## §0. Verdict — **GREEN — sync maps wired; orphan inclusion decidable**

The S7-F bridge sub-arc B is delivered. `lean/OneThird/Step8/SyncMaps.lean`
(NEW, sorry-free, no new axioms, builds clean, imported into
`OneThird.lean`) **wires** the synchronization maps `f_AB/f_AC/f_BC`
carried by a `ChainLiftData α` into the band-assembly-ready form the
S7-F-C band assembly (`step8.tex:2108-2167`) consumes:

* **Orphan inclusion is decidable.** `SyncMap.IsOrphan` is the
  decidable "`f_••` undefined at a chain tail" predicate
  (`SyncMap.decidableIsOrphan`); `SyncMap.orphans : Finset (Fin nA)`
  is the orphan index set; `ChainLiftData.refOrphans` collects the
  band-anchor orphans of `f_AB`/`f_AC`. Every chain index is
  classified — `orphans_eq_compl_domain` /
  `card_domain_add_card_orphans` prove domain and orphan set
  partition `Fin nA`.
* **The domain is extended.** `SyncMap.onDomain` is the partial map
  restricted to its domain as a genuine *total* function
  `f.domain → Fin nB`; `SyncMap.extend` is the total extension to all
  of `Fin nA` with a fallback; `ChainLiftData.fABwired`/`fACwired`
  are the band-assembly-ready total maps on `X \ X^exc_sync`.
* **Monotonicity is proved.** `SyncMap.onDomain_monotone` lifts the
  `SyncMap.weakly_monotone` field to a genuine `Monotone`;
  `ChainLiftData.fABwired_monotone`/`fACwired_monotone` propagate it
  across chains into the poset order — the (L4) input.

The genuine-content bar is cleared: every piece of the API is
exercised on the F7a concrete witness `gridChainLiftData` (mg-974c)
in §6, including its **real chain-tail orphan** — the orphan
handling is non-vacuous.

**One ill-posed obligation block-and-reported (§3).** The paper's
per-chain bound `|X^exc_sync| ≤ K_bw` (`step8.tex:2053`) is **not
provable from the bare `ChainLiftData`** — the structure carries no
field tying the orphan count to `K_bw`. Per the Piece-3 design note
(default Resolution A) it is **not** fabricated; it is **made
explicit** as the named, decidable predicate
`ChainLiftData.BoundedSyncOrphans`, a downstream hypothesis. The
structural half that *is* derivable from bare data
(`orphan_count_le_of_bounded`, `refOrphans_card_le`) is proved.

---

## §1. What S7-F-B is

The S7-F bridge `lem:layered-from-step7` (`step8.tex:2009-2089`)
consumes a `ChainLiftData α` (`ChainPotentials.lean:328` — Dilworth
triple + chain potential + sync maps `f_AB/f_AC/f_BC` + `K_bw`) and
must build a ground-set `LayeredDecomposition` on `X \ X^exc`. The
band assembly (`step8.tex:2108-2111`) is

```
  L_k := { a_k, b_{f_AB(k)}, c_{f_AC(k)} } ∩ (X \ X^exc).
```

Piece 3 is decomposed (scoping §2.3) into sub-arcs A (exceptional
set), **B (synchronization maps — this ticket)**, C (band assembly),
D (chain-removal subtype lift), Z (integration). The original
pre-re-scope plan had sub-arc B *construct* the maps; the
Checkpoint-3 re-scope (mg-ca83/mg-3119/mg-974c) pinned the maps as
**input** carried by the `ChainLiftData`. So S7-F-B is now a
**wiring** task — take the input maps and expose them in the shape
the band assembly needs, with three explicit obligations from the
ticket: (1) prove monotonicity, (2) extend the domain, (3) make the
orphan-inclusion decision decidable.

---

## §2. The deliverable — `lean/OneThird/Step8/SyncMaps.lean`

Namespace `OneThird.Step8`. Six sections.

### §2.1. `SyncMap` orphan API (§1 of the file)

| Name | Statement |
|---|---|
| `SyncMap.IsOrphan f i` | `f.partner i = none` — the decidable orphan predicate |
| `SyncMap.decidableIsOrphan` | `Decidable (f.IsOrphan i)` — **discharges "make the undefined case decidable"** |
| `SyncMap.orphans` | `Finset (Fin nA)` of chain-tail orphans |
| `SyncMap.mem_orphans` | `i ∈ f.orphans ↔ f.partner i = none` |
| `SyncMap.not_mem_orphans_iff_mem_domain` | orphan set and domain are complementary |
| `SyncMap.orphans_eq_compl_domain` | `f.orphans = f.domainᶜ` |
| `SyncMap.card_domain_add_card_orphans` | `f.domain.card + f.orphans.card = nA` — every index classified |
| `SyncMap.exists_partner_of_mem_domain` | a defined index has an explicit partner |

### §2.2. Domain extension (§2 of the file)

| Name | Statement |
|---|---|
| `SyncMap.onDomain` | `f.domain → Fin nB` — the partial map as a genuine total function on its domain |
| `SyncMap.partner_eq_some_onDomain` | `onDomain` is a section of `partner` |
| `SyncMap.onDomain_le_onDomain` | weak monotonicity, raw form |
| `SyncMap.onDomain_monotone` | **`Monotone f.onDomain`** — packaged monotonicity |
| `SyncMap.extend` | `Fin nA → Fin nB` — total extension with a fallback `d` |
| `SyncMap.extend_eq_onDomain` / `_eq_default_of_isOrphan` | `extend` agrees with `onDomain` on the domain, hits `d` on orphans |
| `SyncMap.extend_monotone_of_orphans_empty` | no orphans ⇒ `extend` is `Monotone` on all of `Fin nA` |

### §2.3. `ChainLiftData` orphan inclusion + wired maps (§3–§5)

| Name | Statement |
|---|---|
| `ChainLiftData.refOrphans` | band-anchor orphans = `fAB.orphans ∪ fAC.orphans` |
| `ChainLiftData.refOrphans_card_le` | unconditional card bound |
| `ChainLiftData.fAB_mem_domain_of_not_refOrphan` | off `refOrphans`, `f_AB` is total (likewise `fAC_…`) |
| `ChainLiftData.BoundedSyncOrphans` | the paper's `|X^exc_sync| ≤ K_bw`, as an explicit hypothesis (§3) |
| `ChainLiftData.orphan_count_le_of_bounded` | `BoundedSyncOrphans ⇒ Σ orphans ≤ 3·K_bw` (paper item (i)) |
| `ChainLiftData.fABwired` / `fACwired` | the band-assembly-ready total maps on `X \ X^exc_sync` |
| `ChainLiftData.fABwired_monotone` / `fACwired_monotone` | wired-map monotonicity propagated to the poset order — the (L4) input |

### §2.4. Non-triviality on the F7a witness (§6)

Eight `gridChainLiftData` certificates: `f_AB`/`f_BC` orphan-free;
`f_AC` has a **genuine** chain-tail orphan (`…_fAC_has_orphan`,
`…_fAC_orphan_card = 1`, `…_fAC_orphan_zero`); `BoundedSyncOrphans`
holds and is tight; `orphan_count ≤ 3·K_bw`; the wired maps are
total off the orphan set and **non-constant** (`…_fABwired_genuine`).

All declarations depend only on `propext`/`Classical.choice`/`Quot.sound`.

---

## §3. The block-and-report — `|X^exc_sync| ≤ K_bw` is ill-posed against the bare structure

The ticket mandates: *"Block-and-report on any ill-posed obligation."*
There is exactly one.

**The obligation.** Paper item (i) / the scoping §2.3 hold-the-line
risk 2 require `|X^exc_sync| ≤ K_bw` per chain (`step8.tex:2053`).

**Why it is ill-posed against the bare `ChainLiftData`.** The bare
structure (`ChainPotentials.lean:328`) is `triple + pot + K_bw + fAB
+ fAC + fBC` with **no field** relating an orphan count to `K_bw`.
`K_bw` is a free `ℕ`; the sync maps are arbitrary weakly-monotone
partial maps. A `ChainLiftData` with `K_bw = 0` and every index an
orphan is a perfectly valid inhabitant. So `f.orphans.card ≤ D.K_bw`
is a **false proposition** for some inhabitants — not provable. This
is the MA-Sig §11.3 bare-structure soundness gap, localised to the
sync maps.

**Resolution taken — A (domain-pin), per the Piece-3 design note.**
The obligation is **not fabricated** and **not** discharged by a sham
proof. It is **made explicit** as `ChainLiftData.BoundedSyncOrphans`
— a named, decidable `Prop` — to be supplied downstream as a
hypothesis pinned at the bridge call site via `hCex` (Resolution A),
or upgraded to a soundness field of a strengthened structure
(Resolution B) if S7-F-C's L2 verification cannot close from the
bare structure. The half of paper item (i) that *is* well-posed
against bare data — "the orphan count *bounds* `|X^exc_sync|`",
`orphan_count_le_of_bounded` and `refOrphans_card_le` — is proved
unconditionally / from that hypothesis. `BoundedSyncOrphans` is
proved to **hold** on the genuine F7a witness
(`gridChainLiftData_boundedSyncOrphans`), so it is a satisfiable,
non-vacuous hypothesis, not a disguised `False`.

This matches the design note exactly: *default to Resolution A;
escalate to B only if S7-F-C's L2 verification cannot close.*

---

## §4. Scope boundary — what S7-F-B does *not* deliver

* **The ground-set `X^exc_sync : Finset α`** is **sub-ticket
  S7-F-A's** deliverable (scoping §2.3: "mg-S7-F-A … define
  `X^exc_mono, X^exc_band, X^exc_sync` as `Finset α`"). Building it
  is the chain image of `refOrphans` (under `triple.A.elem`) and
  `fBC.orphans` (under `triple.B.elem`); the image needs
  `DecidableEq α`, so it is correctly scoped to S7-F-A, which owns
  the whole `X^exc`. S7-F-B delivers the **chain-index** orphan sets
  and the decidable classification S7-F-A consumes. No name
  collision: `X^exc_mono`/`X^exc_band`/`X^exc_sync` are all S7-F-A's.
* **The band map / `LayeredDecomposition`** is S7-F-C. S7-F-B
  delivers the wired maps `fABwired`/`fACwired` and their
  monotonicity; S7-F-C uses them to define `band : α → ℕ` and verify
  (L1)–(L4).
* **The L2/L4 verification proper** (`step8.tex:2127-2167`) needs the
  chain potential and the bandwidth argument — S7-F-C. S7-F-B
  supplies the monotonicity half.

---

## §5. Acceptance bars

- [x] Read-first set consumed: onboarding doc; scoping §2.3;
  state-S7F-R1; state-S7F-Checkpoint3; `step8.tex:2009-2167`.
- [x] Sync maps `f_AB/f_AC/f_BC` **wired** from the `ChainLiftData`
  (input, not constructed) — `onDomain`, `extend`, `fABwired`,
  `fACwired`.
- [x] **Monotonicity proved** — `onDomain_monotone` (`Monotone`),
  `fABwired_monotone`/`fACwired_monotone` (poset order).
- [x] **Domain extended** — `onDomain` (total on domain), `extend`
  (total on `Fin nA`).
- [x] **Orphan inclusion decidable** — `IsOrphan` + `decidableIsOrphan`,
  `orphans` `Finset`, `refOrphans`.
- [x] Non-triviality bar cleared — eight certificates on the F7a
  witness `gridChainLiftData`, including a genuine chain-tail orphan.
- [x] Ill-posed obligation (`|X^exc_sync| ≤ K_bw`) block-and-reported
  (§3) — made explicit as `BoundedSyncOrphans`, not fabricated.
- [x] No `sorry`, no new axiom (`#print axioms`: only
  `propext`/`Classical.choice`/`Quot.sound`).
- [x] `SyncMaps.lean` builds; imported into `OneThird.lean`; full
  `OneThird` build green.

---

## §6. Cross-reference index

### §6.1. Lean (this session)

* `lean/OneThird/Step8/SyncMaps.lean` (NEW) — the deliverable;
  namespaces `OneThird.Step8.SyncMap`, `…ChainLiftData`,
  `…GridChainLift`.
* `lean/OneThird.lean` — adds the `SyncMaps` import.

### §6.2. Lean (consumed, unmodified)

* `lean/OneThird/Step8/ChainPotentials.lean:211/328` — `SyncMap`,
  `ChainLiftData` (the wired structures); `:226` `SyncMap.domain`.
* `lean/OneThird/Step8/ConcreteChainLiftData.lean` —
  `gridChainLiftData` (F7a witness, mg-974c) the §6 certificates use.

### §6.3. Predecessor docs / work items

* `docs/state-S7F-R1-Session1.md` (mg-974c) — the concrete
  `ChainLiftData`; the F7a witness.
* `docs/state-S7F-Checkpoint3-Session1.md` (mg-ca83) — Checkpoint 3;
  the `LayeredWidth3 ≠ LayeredDecomposition` re-scope.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 — Piece 3
  sub-arc decomposition.
* `docs/state-MA-Sig-Session1.md` §11.3 — the bare-structure
  soundness gap (Resolution A vs B); §3 above localises it to the
  sync maps.
* `docs/PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #9 — the
  Checkpoint-3 standing lesson.

### §6.4. Paper

* `step8.tex:2009-2089` — `lem:layered-from-step7`.
* `step8.tex:2050-2055` — `X^exc_sync` / chain-tail orphans.
* `step8.tex:2102-2106` — the sync maps' weak monotonicity.
* `step8.tex:2108-2111` — the band assembly.
* `step8.tex:2153-2167` — the (L4) cross-band-direction verification
  (consumes `fABwired_monotone`/`fACwired_monotone`).

---

## §7. Maintenance contract

This file is the state record for FULL REFACTOR Phase-2 Piece-3
sub-arc B (mg-120d). It owns the Lean file `Step8/SyncMaps.lean`.
Supersede it only if a later session changes that file's deliverable.
If Piece 3 adopts MA-Sig §11.3 resolution (B) and strengthens the
`ChainLiftData` structure, `BoundedSyncOrphans` should become a field
of the strengthened structure and §3 here re-evaluated; record that
in the same commit.
