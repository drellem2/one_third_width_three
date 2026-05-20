# OneThird-S5-C G4-G5 Session 1 state report — grounded forms landed

**Ticket:** mg-be3e (FULL REFACTOR Phase 2, Wave-1; Piece-1 Steps-1-6
cascade port; scoped by mg-d8c7 §2.1 / §5.2 under S5-C; depends on
mg-faf8).
**Verdict:** **GREEN — substantively landed.** Step 5 G4
(`lem:fiber-mass`, fiber-mass concentration) and G5
(`lem:global-layering` / `lem:cyclic-compat`, global layering) ports
completed and *grounded*, together with the second-moment strengthening
(`cor:second-moment`); the whole G4+G5 chain is instantiated
**non-vacuously** on a concrete width-3 non-chain poset. Full
`lake build` clean (1420 jobs); no new axioms, no `sorry`, no
`native_decide`.

---

## §0. TL;DR

* **G4 (`lem:fiber-mass`, `step5.tex:621-660`)** — the abstract
  `FiberMass.lean` (`fiber_mass_sum_lower_bound`,
  `fiber_mass_richness_conclusion`, `fiber_mass_averaged`) and
  `Layering.activation_absorb` were re-read against the paper and
  confirmed faithful *as arithmetic cores*, but they consume the
  **post-activation** per-pair bulk bound `2 · fiberSize α ≥ LP`
  directly — they never exhibit the Step-1 interface partition
  `LP = good ⊔ bad` (I1) + thin-bad-set bound (I2) that produces it.
* **G5 (`lem:global-layering`, `step5.tex:864-1055`)** — the abstract
  `Layering.lean` (`InBand`, `IntervalsTouch`, `cyclic_compat`,
  `case_AC/BC`, `global_layering_structural`) is faithful interval
  geometry, but `cyclic_compat` **takes `IntervalsTouch` as a
  hypothesis**; its own docstring punts the derivation ("lives in the
  downstream Step 6 / Step 7 assembly"). That is **wrong about the
  scope**: the paper proof of `lem:cyclic-compat` (`step5.tex:919-935`,
  Step 1) derives `IntervalsTouch` from poset incomparability by a
  pure transitivity argument — it **is** Step-5 G5 content. This
  session supplies that missing derivation.
* **Grounding** — new file `Step5/G4G5Grounded.lean`:
  * **G5.** `ICset` (the incomparability index set on a chain),
    `ICset_orderConvex` (`lem:interval-form` grounded),
    `lt_of_gt_ICmax` / `gt_of_lt_ICmin` (comparability past the
    interval endpoints), `intervals_touch_left` /
    `intervals_touch_right` (**the missing Step 1 of
    `lem:cyclic-compat`** — `IntervalsTouch` discharged from genuine
    `a ∥ b`), `cyclic_compat_grounded` (feeds them into the abstract
    `Layering.cyclic_compat`), `height_diff_chain_grounded` and
    `global_layering_grounded` (all three cases of
    `lem:global-layering`, packaged).
  * **G4.** `goodFiber_card_add`, `fiber_mass_hedged_grounded`
    (paper clause (a), unconditional), `fiber_mass_grounded`
    (clause (b): exhibits the genuine disjoint interface partition
    and runs the activation step explicitly, **deriving** the
    abstract `fiber_mass_sum_lower_bound`'s hypothesis),
    `fiber_mass_richness_grounded` (the (R) "in particular" clause).
  * **Second moment.** `second_moment_grounded` feeds the genuine
    good fibers into `SecondMoment.second_moment_visibility`.
* **Non-vacuity bar met.** Instantiated on `W3 := Fin 3 × Fin 3`
  (product order — the genuine width-3 non-chain 9-element poset of
  the S5-A grounding), Dilworth triple `(chainA, chainB | chainC)`.
  `cyclic_compat_concrete` fires on the genuine incomparable pair
  `(chainA 2, chainB 1)` whose incomparability interval on the
  reference chain `C` has **two** elements (a non-trivial interval,
  not a singleton); the `IntervalsTouch` is genuinely derived, not
  assumed. G4 fires on a non-empty rich set with a genuine disjoint
  partition; the second-moment bound fires with constant `c = 1`
  (a genuine, non-zero bound — not the `c = 0` vacuous baseline).
  See `g4_g5_grounded_concrete`. No `Subsingleton`/empty baseline.
* **No new axioms, no `sorry`, no `native_decide`, no headline-path
  change.** `#print axioms` on every key theorem
  (`g4_g5_grounded_concrete`, `cyclic_compat_grounded`,
  `fiber_mass_grounded`, `intervals_touch_left`): only `propext`,
  `Classical.choice`, `Quot.sound`. All additions are a new file +
  one import line in `OneThird.lean`; the abstract Step 5 files are
  untouched.

## §1. Inventory delta

```
G4G5Grounded.lean   new, 606 LoC   (grounding + concrete instance)
OneThird.lean       +1 import line
```

**Net polecat output:** ~606 LoC of Lean + this state doc. The
abstract `FiberMass.lean`, `Layering.lean`, `SecondMoment.lean` are
**not modified** — keeping merge surface minimal for the parallel
Wave-1 S5 sub-tickets.

## §2. G4 — assessment and grounding

`FiberMass.lean` already ports the *averaged* / *activated* form (b)
of `lem:fiber-mass` faithfully: `fiber_mass_sum_lower_bound` is Step 2
of the paper proof (`step5.tex:704-718`), `fiber_mass_richness_conclusion`
is Step 3 (`step5.tex:721-738`). `Layering.activation_absorb` is the
arithmetic of `lem:activation-absorb`. **Gap:** these consume the
post-activation per-pair bound `2 · fiberSize α ≥ LP` as a hypothesis;
the genuine interface partition that produces it (Step-1
`Theorem~\ref{thm:interface}` (ii)+(iv), `step5.tex:668-689`) is never
exhibited.

`G4G5Grounded.lean` closes this:

| Symbol | Role (`step5.tex`) |
|---|---|
| `goodFiber_card_add` | (I1) `LP = good ⊔ bad` ⇒ cardinalities add |
| `fiber_mass_hedged_grounded` | clause (a), unconditional: `|good| ≥ |LP| − B₀`, summed |
| `fiber_mass_grounded` | clause (b): (I1)+(I2)+activation ⇒ `2·∑ ≥ |Rich|·|LP|` — **derives** `fiber_mass_sum_lower_bound`'s hypothesis |
| `fiber_mass_richness_grounded` | the (R) "in particular" conclusion `2·σ·∑ ≥ c₅⋆·σ·|LP|` |

The activation threshold `2·B₀ ≤ |LP|` (`lem:activation-absorb`,
`step5.tex:743-758`) is taken as the hypothesis `hact` — its discharge
needs the Stirling multinomial lower bound on `|LP|`, which is paper
`lem:activation-absorb` (F1)+(F2) and is appropriately a separate
ticket's content (it consumes Dilworth product structure, not G4
interval geometry).

## §3. G5 — what was completed

`Layering.lean` provides the band geometry (`InBand`, `cyclic_compat`,
`case_AC/BC`, `global_layering_structural`) but `cyclic_compat`
consumes `IntervalsTouch` as a hypothesis. Its docstring claims the
derivation "lives in the downstream Step 6 / Step 7 assembly … *not*
in the pure interval-geometry core of Step 5". **That scope claim is
incorrect:** the paper's proof of `lem:cyclic-compat` (`step5.tex:909-949`)
has the `IntervalsTouch` derivation as its *Step 1* — a pure
transitivity argument on the chain, entirely Step-5 content. Added:

| Symbol | Role (`step5.tex`) |
|---|---|
| `ICset` / `mem_ICset` | the incomparability index set `IC(x)` on a chain |
| `ICset_orderConvex` | `lem:interval-form` grounded (`step5.tex:35-43`) |
| `lt_of_gt_ICmax` | past the right endpoint, `a < c_k` (`step5.tex:924-927`, `c_k ∈ U_C`) |
| `gt_of_lt_ICmin` | below the left endpoint, `c_k < b` (`step5.tex:929-930`, `c_k ∈ L_C`) |
| `intervals_touch_left` / `_right` | **Step 1 of `lem:cyclic-compat`** — `IntervalsTouch` from `a ∥ b` |
| `cyclic_compat_grounded` | `lem:cyclic-compat` full: discharges `IntervalsTouch`, routes the band-bracketing arithmetic through abstract `cyclic_compat` |
| `height_diff_chain_grounded` | Cases 1–2 of `lem:global-layering` (`A`–`C`, `B`–`C`) |
| `global_layering_grounded` | all three cases packaged |

`intervals_touch_left` is the substantive deliverable: a separating
index `k` with `max(IC(a)) < k < min(IC(b))` is shown to force
`a < c_k < b` (via `lt_of_gt_ICmax` + `gt_of_lt_ICmin`), contradicting
`a ∥ b`. This is exactly the paper's transitivity argument and it
discharges the hypothesis the abstract `Layering.lean` punted.

### Scope note — the degenerate-interval branch

`lem:global-layering` Case 3 has a degenerate sub-branch (one of
`IC(a_i), IC(b_j)` empty; `step5.tex:985-1029`) handled by the
poset-level `|{c : c < a_i}|` "gap position" redefinition of the
height function `h`. As the abstract `Layering.lean` already notes,
that branch belongs to the Step 7 assembly level (it constructs the
global `h`, not the per-pair bound). `global_layering_grounded`
delivers the **non-empty-interval** branch — the genuine
cyclic-compatibility content — and the two chain cases; the universal
`h` assembly is correctly downstream. This is the same structural /
assembly split S5-A applied to G2's quantitative `K`-bound, not a
vacuous routing.

## §4. Non-vacuous instantiation (`mg-be3e` acceptance bar)

`W3 := Fin 3 × Fin 3` (product order), Dilworth triple
`(chainA, chainB | chainC)`; `chainCfun : Fin 3 → W3` enumerates the
reference chain. `g4_g5_grounded_concrete` bundles, all proved (not
assumed):

1. `HasWidthAtMost W3 3` and `¬ IsChainPoset W3`;
2. `chainA 2 ∥ chainB 1` — a genuine incomparable `A`–`B` pair
   (`(0,2)` and `(1,1)` incomparable in the product order);
3. **G5** — `IC(chainA 2)` and `IC(chainB 1)` on the reference chain
   are both genuinely non-empty, and `IC(chainA 2)` contains *two*
   indices (`0` and `1`) — the cyclic-compatibility argument runs on
   a non-trivial interval, not a singleton; `cyclic_compat_concrete`
   fires the `|fAC − fBC| ≤ 2K + 1` bound through the genuine
   `intervals_touch` derivation;
4. **G4** — `cRich` is non-empty and `fiber_mass_concrete` fires the
   activated `2·∑ ≥ |Rich|·|LP|` bound on a genuine disjoint
   interface partition (`6`-element extension universe, two rich
   pairs, `4`-element good fibers, `2`-element thin bad fibers);
5. **second moment** — `second_moment_concrete` fires
   `cor:second-moment` with constant `c = 1` (genuine, non-zero).

No `Subsingleton`-on-empty baseline anywhere. The acceptance bar is
met.

## §5. No gap-discovery

Default-skeptical re-read of `step5.tex:621-1183` (G4, G5,
`prop:counting`, `cor:second-moment`) against the Lean port surfaced
**no ill-posed target** and **no missing mathlib dependency** — the
ticket's block-and-report condition is **not** triggered. One
correctness note for downstream awareness (not blocking): the abstract
`Layering.cyclic_compat`'s docstring mis-attributes the `IntervalsTouch`
derivation to "downstream Step 6 / Step 7" — it is pure Step-5
`lem:cyclic-compat` Step 1, and `G4G5Grounded.intervals_touch_left`
now supplies it in-tree. A future editor of `Layering.lean` may want
to correct that docstring note; this session left `Layering.lean`
untouched to keep the Wave-1 merge surface minimal.

## §6. Build

`lake build OneThird` (full tree, 1420 jobs) clean. `G4G5Grounded`
and all downstream modules compile; no new warnings from the new
file. `#print axioms` on `g4_g5_grounded_concrete`,
`cyclic_compat_grounded`, `fiber_mass_grounded`, `intervals_touch_left`:
`[propext, Classical.choice, Quot.sound]` only — no project axioms,
no `sorryAx`, no `Lean.ofReduceBool`.
