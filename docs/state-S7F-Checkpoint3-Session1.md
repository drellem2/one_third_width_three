# State — S7-F Checkpoint 3 — Session 1: hold-the-line audit of Piece 2 `L_S7E` vs the Piece-3 S7-F bridge input shape

**Ticket:** mg-ca83 (OneThird-S7F-Checkpoint3 — hold-the-line audit:
does Piece 2 `L_S7E` concretely match the Piece-3 S7-F bridge input
shape).
**Type:** audit / go-no-go gate.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §3.3 Checkpoint 3
+ §2.3 Piece 3; mg-6ab8 §4.3 Checkpoint 3.
**Predecessors read:** `docs/PROOF-STRUCTURE-ONBOARDING.md`;
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 + §3.3;
`docs/state-MA-Sig-Session1.md` §4.2 §E/§G + §10 (the mg-faf8
re-pinned bridge contract); `docs/state-S7-Conc-D-Session1.md`
(the Piece-2 Conc-D deliverable).

---

## §0. Verdict — **RED — `L_S7E` does NOT match the S7-F bridge input shape**

**Checkpoint 3 fails. Do NOT dispatch Piece 3 (the S7-F bridge,
sub-arcs mg-S7-F-A … mg-S7-F-Z) against the current Piece-2
deliverable.** Re-scope Piece 2's concretisation target **and**
reconcile the bridge contract first.

The core finding is a **structural object mismatch**, not an adapter
gap:

* **Piece 2 delivers** `L_S7E : Step7.LayeredWidth3 (richPairs :
  Finset (α × α))` — a five-field record on the **rich-pair space**
  `α × α`: a `bandwidth : ℕ` and a partition of `richPairs` into
  `richPairsIn ⊔ richPairsOut` (`Step7/Assembly.lean:302-312`).
* **The S7-F bridge** `lem:layered-from-step7` must **output**
  `LayeredDecomposition {a : α // a ∉ Xexc}` — a genuine **ground-set**
  poset layered decomposition with a band map `band : α → ℕ`,
  per-band antichain/size invariants, and the order-theoretic
  (L2)/(L4) fields (`Step8/LayeredReduction.lean:113-147`); and to
  build it the bridge **consumes** a potential `a : X → ℝ`, a
  threshold `c`, a Dilworth triple `A ⊔ B ⊔ C`, the synchronization
  maps `f_AB, f_AC, f_BC`, and the `lem:bandwidth` constant `K_bw`
  (paper `lem:layered-from-step7`, `step8.tex:2009-2089`).

`LayeredWidth3` and `LayeredDecomposition` are **unrelated types**.
`L_S7E` carries **none** of the five genuine bridge inputs: no
potential, no threshold, no Dilworth triple, no synchronization maps;
and its one nominal contribution — `bandwidth ≤ 4` — is **inert**
(`bandwidth` is a free threshold parameter `c₀` fixed to the literal
`4`; `L_S7E.bandwidth ≤ 4` reduces to `4 ≤ 4` — see §3.2). The
concrete witness `L_S7E_antichain3` is additionally **degenerate**:
it runs with the constant BFS potential, zero budget,
`richPairsOut = ∅` — so even the one genuine quantitative conjunct of
`prop:72` is discharged at the trivial value.

This is exactly the Checkpoint-2 failure mode (`PROOF-STRUCTURE-ONBOARDING.md`
§0 mg-e996 bullet): **type-compatible but content-empty**. Per the
Checkpoint-2 lesson the audit probed *satisfiability*, not
type-compatibility — and `L_S7E` does not survive the probe.

The in-tree evidence is decisive and independent of the (not-yet-in-tree)
bridge: the **only** existing `LayeredWidth3 → LayeredDecomposition`
conversion, `Step8.layeredFromBridges` (`Step8/LayeredBridges.lean:181-291`),
is a **documented sham** — it cannot use `bandwidth ≤ 4`, it inflates
`w` to `|α| + 1`, and it makes the paper's (L2) axiom *vacuous*. Its
own docstring states a genuine conversion "requires formalising the
chain-potential + sync-map alignment of `rem:layered-from-step7`"
(`LayeredBridges.lean:164-170`) — i.e. the data `L_S7E` does not
carry.

**Forward action.** §6. Two things must change before Piece 3:
(1) re-point Piece 2's concretisation deliverable away from
`LayeredWidth3` and toward the object the bridge actually consumes
(a concrete `ChainLiftData α` — Dilworth triple + chain potential +
sync maps + `K_bw`, `Step8/ChainPotentials.lean:328-340` — for `α`
arising as a minimal γ-counterexample); (2) reconcile the bridge
contract, which is currently **pinned inconsistently** across the
two READ-FIRST documents (MA-Sig §4.2 §E consumes an abstract
`Step5R ∨ Step5C` disjunction; scoping §2.3 says it consumes
`L_S7E` — §5).

No Lean source is changed in this session. Deliverable is this
report plus the §0/§3 onboarding-doc updates and the §3.3 scoping-doc
Checkpoint-3 outcome entry.

---

## §1. What Checkpoint 3 gates, and what was audited

Checkpoint 3 is the FULL REFACTOR's highest-risk hold-the-line gate
(scoping doc §3.3: *"This is the highest-risk checkpoint — the prior
failure of this audit at the call-site architecture is exactly what
triggered mg-d8c7"*). It fires **before** any Piece-3 sub-arc
(mg-S7-F-A …) is dispatched, and asks one question:

> Does Piece 2's `L_S7E` deliver the bridge's input hypotheses
> **concretely** — synchronization maps defined, exceptional-set
> inputs present, the corrected three-cap form supplied, no residual
> free hypotheses, no placeholders?

Piece 2 is reported complete: Conc-A (mg-4ce6), -B (mg-8f9c),
-C (mg-5f3e), -D (mg-3f00) landed; Conc-D delivered `L_S7E` via
`Step7/S7EAssembly.lean`, verified sorry-free and axiom-free
(`state-S7-Conc-D-Session1.md` §0). The audit takes that at face
value at the *build* level (the file is sorry-free) and probes the
*content* level: whether the object that builds is the object Piece 3
needs.

**Method.** Per `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2's
three checks and the explicit Checkpoint-2 lesson ("parametric
fiction does not pass; probe satisfiability, not type-compatibility"):
read the actual Lean structure definitions, the actual assembly
theorem body, the actual concrete witness, the only in-tree
`LayeredWidth3 → LayeredDecomposition` conversion, and the paper
statement of `lem:layered-from-step7`. Every claim below is cited to
`file:line`.

---

## §2. The two objects, side by side

### §2.1. What Piece 2 delivers — `L_S7E : LayeredWidth3 (richPairs)`

`Step7/Assembly.lean:302-312`:

```lean
structure LayeredWidth3 (richPairs : Finset Pair) where
  bandwidth   : ℕ
  richPairsIn  : Finset Pair
  richPairsOut : Finset Pair
  partition : richPairsIn ∪ richPairsOut = richPairs
  disjoint  : Disjoint richPairsIn richPairsOut
```

That is the **entire** structure. `L_S7E` is the
`Step7/S7EAssembly.lean` instance of it (`lemS7E_groundSet:195`,
concrete `lemS7E_antichain3:289`, witness term `L_S7E_antichain3:325`)
at `Pair := α × α`, `richPairs ⊆ α × α`.

Semantically `LayeredWidth3` is a **rich-pair window-confinement
packaging**: `richPairsIn` = rich pairs whose potential-gradient
`Δ < c₀` (inside the interaction window), `richPairsOut` = rich pairs
with `Δ ≥ c₀` (`richLargeDeltaPairs`, `Step7/Bandwidth.lean:225-227`).
It carries **no poset-structural data whatsoever**: no map from
ground elements to bands, no antichain property, no comparability
invariant.

### §2.2. What the S7-F bridge must output — `LayeredDecomposition`

`Step8/LayeredReduction.lean:113-147`:

```lean
structure LayeredDecomposition (α) [PartialOrder α] [Fintype α] where
  K : ℕ
  w : ℕ
  band : α → ℕ
  band_pos  : ∀ x, 1 ≤ band x
  band_le   : ∀ x, band x ≤ K
  band_size : ∀ k, (univ.filter (band · = k)).card ≤ 3          -- (L1a)
  band_antichain : ∀ k, IsAntichain (·≤·) (band ⁻¹' {k})        -- (L1b)
  forced_lt : ∀ x y, band x + w < band y → x < y                -- (L2)
  cross_band_lt_upward : ∀ x y, x < y → band x ≤ band y         -- (L4)
```

This is a genuine **ground-set** layered decomposition. Crucially
`w` is **load-bearing**: it appears inside `forced_lt`. A proof of
`L.w ≤ 4` is therefore a proof that *every* far-apart pair
(`band x + 4 < band y`) is forced comparable — a strong structural
fact about the poset.

### §2.3. What the bridge must consume (paper `lem:layered-from-step7`)

`step8.tex:2009-2089` (`lem:layered-from-step7`), inputs:

* `P` width-3, with a **Dilworth decomposition** `X = A ⊔ B ⊔ C`
  into three chains;
* **either** (a) Step 5(C) collapse data, **or** (b) Step 7(ii)
  globalization data: a **potential `a : X → ℝ`**, a **threshold
  `c ∈ ℝ`**, and the **bandwidth constant `K_bw = K(T) = O_T(1)`**;
* the **synchronization maps `f_AB, f_AC, f_BC`** (`step8.tex:2038-2040`).

The exceptional set is *defined from these*:
`X^exc = X^exc_mono ∪ X^exc_band ∪ X^exc_sync`, where `X^exc_mono`
is the potential's non-monotonicity locus, `X^exc_band` the
`K_bw`-excess rich endpoints under `f_••`, `X^exc_sync` the
sync-map domain orphans (`step8.tex:2042-2053`). The band assembly
is *defined from these* too — `step8.tex:2108-2111`:

```
L_k := { a_k, b_{f_AB(k)}, c_{f_AC(k)} }
```

i.e. the bridge builds the `LayeredDecomposition.band` map directly
out of the potential `a` (which yields `f_AB, f_AC` via
`f_AB(i) := argmin_j |a(a_i) − a(b_j)|`, `step8.tex:2102-2105`) and
the Dilworth chains.

**The bridge's genuine inputs are: the potential, the threshold, the
Dilworth triple, the sync maps, and `K_bw`.** Compare §2.1: `L_S7E`
supplies none of them.

---

## §3. Audit findings

### §3.1. Finding A — `LayeredWidth3` ≠ `LayeredDecomposition`; `L_S7E` carries zero ground-set structure

`L_S7E` lives on the **pair space** `α × α`; the bridge output lives
on the **ground set** subtype `{a : α // a ∉ Xexc}`. `L_S7E`'s only
fields are a number and a partition of a pair-finset. It has:

* **no band map** `band : α → ℕ` — so it cannot supply
  `LayeredDecomposition.band`, `band_pos`, `band_le`;
* **no antichain / band-size data** — so it cannot supply
  `band_size` (L1a) or `band_antichain` (L1b);
* **no comparability invariant** — so it cannot supply `forced_lt`
  (L2) or `cross_band_lt_upward` (L4).

This is not a defect *of* Piece 2 in isolation — `LayeredWidth3` is
sound **Step 7 internal scaffolding** (the rich-pair window-confinement
count bound of `prop:72` + `lem:bandwidth`). The defect is that it
was scoped as the **Piece-3 bridge input** when it is structurally
the wrong object for that role.

`GroundSet.lean` even states the gap in its own header
(`Step7/GroundSet.lean:26-29`):

> *"Downstream consumers … need these forms at concrete carrier
> types so they can build a `LayeredDecomposition α` … ; a
> `LayeredWidth3` packaging over an abstract `Pair` cannot be
> converted into a ground-set `LayeredDecomposition α`."*

…and then claims (`GroundSet.lean:235-237`) that fixing
`Pair := α × α` makes `L_S7E` *"the concrete object the S7-F bridge
… consumes to build a `LayeredDecomposition α` with `w ≤ 4`."*
**That inference is the over-claim.** Making the `Pair` *type*
concrete is necessary but nowhere near sufficient: the missing
content (band map, potential, sync maps, exceptional set) is
independent of whether `Pair` is an abstract type variable or
`α × α`. Type-concreteness ≠ content-deliverability.

### §3.2. Finding B — `L_S7E.bandwidth ≤ 4` is an inert chosen constant, not a derived width bound

`prop_72` (`Step7/Assembly.lean:329-348`) produces
`L.bandwidth = c₀`, where `c₀ : ℕ` is a **free input parameter**
with the *only* constraint `hc₀ : 0 < c₀`. `lem_bandwidth_le_four`
(`Step7/Prop71_Prop72_LemBandwidth.lean:356-361`) calls
`prop_72_grounded … 4 (by decide) …`, obtains `hbw : L.bandwidth = 4`,
and discharges the goal `L.bandwidth ≤ 4` by `rw [hbw]` — i.e. the
"bandwidth ≤ 4 deliverable" is definitionally **`4 ≤ 4`**.

`LayeredWidth3` has **no field or invariant** tying `bandwidth` to
any band map, any interaction window, or any poset comparability.
It is a bare `ℕ`. Contrast `LayeredDecomposition.w`, which is
load-bearing inside `forced_lt`. So `L_S7E.bandwidth ≤ 4` carries
**no structural content** that the bridge could lift into a genuine
`LayeredDecomposition.w ≤ 4`. The bridge would have to *re-prove*
`forced_lt` for `w = 4` from scratch — and that proof needs the
potential `a` and the sync maps, which `L_S7E` discards.

The genuine quantitative content of `prop:72` is **not** the
`bandwidth` field but the *second conjunct* of `lemS7E_groundSet`
(`S7EAssembly.lean:222-226`):
`4·c_n·(b_d·|richPairsOut|)·M₀ ≤ c_d·(b_n·M₀)` — the o(1)-mass
bound on the exceptional rich pairs. That is real Step-7 math, but
(i) it is a **mass bound on pairs**, not a structural (L2)
guarantee, and (ii) on the concrete witness it is discharged
degenerately — see Finding D.

### §3.3. Finding C — the only in-tree `LayeredWidth3 → LayeredDecomposition` conversion is a documented sham that *cannot* use `bandwidth ≤ 4`

`Step8.layeredFromBridges` (`Step8/LayeredBridges.lean:181-291`) is
the existing prior-art conversion. It is instructive precisely
because it shows what goes wrong:

* it feeds `prop:72` the threshold `c₀ := Fintype.card α + 1`, so the
  resulting `Lwidth3.bandwidth = |α| + 1` — **not** `≤ 4`
  (`LayeredBridges.lean:208-217`);
* it threads `w := Lwidth3.bandwidth` into the `LayeredDecomposition`
  *verbatim* (`LayeredBridges.lean:249`), giving `w = |α| + 1`;
* with that inflated `w`, `forced_lt` (L2) is proved **vacuously**:
  `band x + w ≥ 1 + (|α|+1) > |α| ≥ band y`, so the hypothesis
  never holds (`LayeredBridges.lean:272-284`);
* bands are forced to **singletons** via a Szpilrajn extension
  (`K = |α|`, `LayeredBridges.lean:246-263`).

The file's docstring is explicit (`LayeredBridges.lean:50-63`,
`164-170`): the `bandwidth` must be raised to `≥ |α| − 1` *exactly
to keep (L2) Lean-sound*; a genuine `w = O_T(1)` decomposition with
non-vacuous (L2) "requires formalising the chain-potential +
sync-map alignment of `rem:layered-from-step7` using F7a's
`ChainLiftData`".

**This is the audit's hard evidence.** The one conversion that
exists demonstrates, in tree, that `LayeredWidth3.bandwidth` *cannot*
be threaded into a genuine `LayeredDecomposition.w ≤ 4`. To get
`w ≤ 4` with a real (L2) you need the chain potential + sync maps —
the very data `L_S7E` does not carry. `L_S7E`'s `bandwidth ≤ 4`
buys the bridge nothing.

### §3.4. Finding D — the concrete `L_S7E_antichain3` is degenerate

`lemS7E_antichain3` (`S7EAssembly.lean:289-316`) — the only fully
closed `L_S7E` term — runs the assembly with:

* `signedWeight := fun _ => 0`, `path := fun _ => []` — the
  **constant BFS potential** (`S7EAssembly.lean:299-300`);
* `exceptionalMass := 0`, `hModel`/`hBound` closed at `0`
  (`S7EAssembly.lean:307, 313-316`).

Consequently the rich-pair variational budget is genuinely `0` and
`richPairsOut = ∅` — the strongest-but-vacuous "all rich pairs
confined" case. The state doc discloses this itself
(`state-S7-Conc-D-Session1.md` §2.3 "Scope disclosure", §6). So the
*one* genuine conjunct of `prop:72` (the o(1)-mass bound, Finding B)
is, on the concrete witness, the trivial `0 ≤ …`. The concrete
`L_S7E` has never been exercised against a positive interaction
budget. It is type-correct and sorry-free, but its mathematical
content on the headline carrier is empty — the Checkpoint-2 pattern
exactly.

### §3.5. Finding E — `lemS7E_groundSet` is *not* free of hypotheses

The general assembly theorem `lemS7E_groundSet`
(`S7EAssembly.lean:195-231`) threads **`hModel`** and
**`hBound : b_d · exceptionalMass ≤ b_n · LP.card`** as free
hypotheses. `state-S7-Conc-D-Session1.md` §3 discloses that deriving
`hBound` from the Step 6 cascade's `M`-denominated output is "the
genuine `lem:budget-var` index conversion — new theorem-proving …
deferred to Piece 3". So even on its own terms Piece 2 is "complete"
only modulo a hypothesis explicitly punted into Piece 3. Only the
degenerate `Antichain3` instance (Finding D) is hypothesis-free, and
only because every budget quantity is `0`.

---

## §4. The four mandated checks

| # | Mandated check | Result |
|---|---|---|
| 1 | **Synchronization maps defined?** | **Not in `L_S7E`.** `f_AB, f_AC, f_BC` exist in tree only as fields of `ChainLiftData` (`SyncMap`, `Step8/ChainPotentials.lean:336-340`) — a *separate* structure `L_S7E` has no connection to. The bridge gets sync maps from `ChainLiftData`, not from Piece 2's deliverable. |
| 2 | **Exceptional-set inputs present?** | **No.** The bridge needs `Xexc : Finset α` = `X^exc_mono ∪ X^exc_band ∪ X^exc_sync` on the **ground set**, defined from the potential + sync maps (`step8.tex:2029-2053`). `L_S7E` offers `richPairsOut : Finset (α × α)` — a set of **rich pairs** with a **mass** bound, wrong carrier and wrong bound-shape (o(1)-mass vs. absolute `O_T(1)` cardinality). Not convertible. |
| 3 | **Three-cap form supplied** (`Xexc.card ≤ C_exc T`, band-nonempty, `L.w ≤ 4`)? | **None of the three.** `Xexc.card ≤ C_exc T`: `L_S7E` supplies no `Xexc : Finset α` at all (§4 #2). Band-nonempty `∀ k ∈ [1,K], (bandSet k).Nonempty`: `L_S7E` has no `band`, no `K`, no `bandSet`. `L.w ≤ 4`: `L_S7E.bandwidth ≤ 4` is an inert `4 ≤ 4` (§3.2), not a genuine `LayeredDecomposition.w` bound (§3.3). |
| 4 | **Genuinely concrete; no free hypotheses, no placeholders?** | **Partial / degenerate.** `lemS7E_groundSet` carries free hypotheses (`hModel`, `hBound`; §3.5). The closed `lemS7E_antichain3` is hypothesis-free only via the degenerate constant-potential / zero-budget choice (§3.4). `bandwidth = 4` is hard-coded (§3.2). |

All four checks fail. The mismatch is total, not marginal.

---

## §5. The bridge contract is pinned inconsistently across the two READ-FIRST documents

A second, independent Checkpoint-3 finding: the bridge's *own input
shape* is not consistently pinned.

* **MA-Sig §4.2 §E** (`state-MA-Sig-Session1.md:460-508`, the
  mg-faf8 re-pinned contract) gives `lem_layered_from_step7` the
  hypotheses `γ, hγ_pos, T, hP, hI, hCex, hCascade : Step5R α γ T ∨
  Step5C α T, ih`. **`L_S7E` is not a parameter.** The bridge
  consumes an *abstract Step-5 dichotomy disjunction*.
* **Scoping doc §2.3** (`OneThird-...-scoping.md:467-583`) says the
  bridge *"consumes `L_{S7E}`"* and lists "Step 7(ii) globalization
  data … from piece 2's `L_{S7E}`" among its inputs.

These cannot both be the contract. Either:

* (a) MA-Sig §4.2 §E is authoritative → the bridge consumes
  `Step5R ∨ Step5C`, and `L_S7E` is meant to be *the content behind*
  the `Step5R` disjunct. But `L_S7E : LayeredWidth3` is neither
  `Step5R` nor `Step5C` (MA-Sig §4.1 pins both as `Prop`s on `ℕ`
  arguments; the closest in-tree definitions, `Step5.Step5Richness`
  / `Step5.Step5Collapse`, `Step5/Dichotomy.lean:148/165`, are
  unrelated `Prop`s). There is **no in-tree wiring** from
  `LayeredWidth3` to `Step5R`/`Step5C`. Gap.
* (b) Scoping §2.3 is authoritative → the bridge takes `L_S7E`
  directly, and the MA-Sig §4.2 §E signature is missing that
  parameter. Gap.

Either way the bridge's input shape is unresolved. **Checkpoint 3
cannot be GREEN while the contract it audits against is itself
ambiguous.** Note also: even reading (b) charitably, §3 above shows
`L_S7E` does not carry what a `lem:layered-from-step7` *body* needs;
fixing the signature would not fix the content.

---

## §6. Forward action — what must change before Piece 3

This is **RED**, so per the ticket the action is "re-scope Piece 2
or the bridge contract before Piece 3 dispatches". Both, concretely:

**(R1) Re-point Piece 2's concretisation deliverable.** The bridge's
genuine Step-7(ii) input is *not* a `LayeredWidth3` — it is the
**potential + threshold + Dilworth triple + sync maps + `K_bw`**
bundle, which in tree is the structure `ChainLiftData α`
(`Step8/ChainPotentials.lean:328-340`: fields `triple`, `pot`,
`K_bw`, `fAB`, `fAC`, `fBC`). Piece 2's job — "concretise the
S7-A–E grounded forms to the ground set of the headline" — should
deliver a **concrete `ChainLiftData α`** (or the genuine
`prop:71`/`prop:72` quantitative output that the bridge's `X^exc`
construction and (L2) verification consume), for `α` arising as a
minimal γ-counterexample. Whether a concrete `ChainLiftData α` is
itself constructible is an open F7a question that must be settled
*as part of* the re-scope (the structure exists; no concrete
instance was found in tree — `grep` shows it referenced only in
`LayeredBridges.lean` / `MainAssembly.lean` / its own defining
file, never instantiated).

**(R2) Reconcile the bridge contract.** Resolve §5: decide whether
`lem_layered_from_step7` consumes `Step5R ∨ Step5C` (MA-Sig §4.2 §E)
or the concrete Step-7(ii) bundle (scoping §2.3), and make the two
documents agree. The current `LayeredWidth3`-shaped `L_S7E` should
be **dropped** as a Piece-3 input under either reading; the
scoping §2.3 wording "from piece 2's `L_{S7E}`" is the part that is
wrong.

**(R3) Keep `LayeredWidth3` / `prop:72` / `lem_bandwidth_le_four`
as Step-7 internal scaffolding.** They are sound and faithful to
`prop:72` + `lem:bandwidth` — they are simply *not the bridge input*.
No deletion; just re-label their role (Step-7 internal, not
Piece-3 boundary). The mg-4584/9331/1069/d135/516f S7-A–E pilot
work is unaffected.

**(R4) Carry forward the degeneracy disclosure.** Any re-scoped
Piece 2 must produce a witness exercised against a **positive**
interaction budget (Finding D) — the constant-potential /
`richPairsOut = ∅` instance is not an acceptance certificate.

**Budget note.** The scoping doc's Piece-3 budget (4–6 sessions,
1.0M–1.5M) assumed `L_S7E` as a usable input. Under R1–R2 the
Piece-2/Piece-3 boundary moves: the work to build a concrete
`ChainLiftData α` (currently nobody's piece) lands either as a
Piece-2 re-scope or a new Piece-3 sub-arc upstream of mg-S7-F-A.
Re-estimation is for the scoping owner; this audit only gates.

---

## §7. Relation to the prior S7-F audits — this is the same surface failing again

The S7-F bridge has now failed a hold-the-line audit **three times**,
each time for a *call-site / input-shape* reason, never for the
bridge's internal math:

* **mg-5fbd** (S7-F Session 1, `state-S7-F-bridge-Session1.md`) —
  RED: `caseC_canonicalLayered` cap-5 unsatisfiable at the call site
  (onboarding §3 pitfall #5).
* **mg-0bd1** (S7-F Session 2, `state-S7-F-bridge-Session2.md`) —
  RED: the MA-Sig §4.2 §E *signature* was unsatisfiable for large α
  (onboarding §3 pitfall #6); corrected by mg-faf8's re-pin.
* **mg-ca83** (this audit) — RED: the corrected contract type-checks
  and is satisfiable *as a proposition* (MA-Sig §10), but **Piece 2
  does not produce the object that proposition's hypotheses range
  over**. The re-pin fixed the contract; it did not make `L_S7E`
  match it.

The recurring lesson (onboarding §3 pitfall #7 standing lesson):
*a structure named after a paper object can carry none of that
object's content.* `LayeredWidth3` is named to evoke "layered
decomposition"; it is a rich-pair partition with an inert `ℕ`. The
count of vacuity/gap discoveries is tracked inconsistently across
docs (the S7-Conc-D doc says 8; onboarding pitfall #7/#8 imply 9
then 10) — this audit does not adjudicate the count; it records a
**fresh Checkpoint-3 gap** and leaves the numbering to the
onboarding-doc owner.

---

## §8. Acceptance bars

- [x] Read-first set consumed: onboarding doc; scoping §2.3 + §3.3;
  MA-Sig §4.2 §E/§G + §10; Conc-D state doc.
- [x] `L_S7E` structure, assembly body, and concrete witness read at
  source (`Step7/Assembly.lean`, `Step7/S7EAssembly.lean`,
  `Step7/GroundSet.lean`, `Step7/Prop71_Prop72_LemBandwidth.lean`).
- [x] Bridge output type read at source
  (`Step8/LayeredReduction.lean`); paper `lem:layered-from-step7`
  read at source (`step8.tex:2009-2111`).
- [x] The only in-tree `LayeredWidth3 → LayeredDecomposition`
  conversion (`Step8/LayeredBridges.lean`) read and assessed.
- [x] Synchronization maps: located (`ChainLiftData`,
  `ChainPotentials.lean`), confirmed absent from `L_S7E`.
- [x] Exceptional-set inputs: confirmed absent / wrong-carrier.
- [x] Three-cap form: confirmed none of the three supplied.
- [x] Concreteness: free hypotheses (`hModel`/`hBound`) and
  degenerate witness identified.
- [x] Checkpoint-2 lesson applied — satisfiability probed, not
  type-compatibility; the type-clean-but-content-empty pattern is
  the finding.
- [x] Clear verdict section (§0) with go/no-go and re-scope action.

---

## §9. Cross-reference index

### §9.1. Lean (audited, unmodified)

* `lean/OneThird/Step7/Assembly.lean:302-348` — `LayeredWidth3`
  structure; `prop_72` (`L.bandwidth = c₀`, `c₀` free).
* `lean/OneThird/Step7/S7EAssembly.lean` — `lemS7E_groundSet:195`,
  `lemS7E_antichain3:289`, `L_S7E_antichain3:325`,
  `L_S7E_antichain3_bandwidth:331`.
* `lean/OneThird/Step7/GroundSet.lean:26-29, 235-262` — the
  concretisation; the `LayeredWidth3`-vs-`LayeredDecomposition`
  header note and the over-claim.
* `lean/OneThird/Step7/Prop71_Prop72_LemBandwidth.lean:337-361` —
  `lem_bandwidth_le_four` fixes `c₀ := 4`.
* `lean/OneThird/Step7/Bandwidth.lean:225-227` — `richLargeDeltaPairs`
  (= `richPairsOut`).
* `lean/OneThird/Step8/LayeredReduction.lean:113-147` —
  `LayeredDecomposition` structure (the bridge output type).
* `lean/OneThird/Step8/LayeredBridges.lean:181-291` —
  `layeredFromBridges`, the sham conversion.
* `lean/OneThird/Step8/ChainPotentials.lean:328-340` —
  `ChainLiftData` (potential + `K_bw` + `fAB/fAC/fBC`).
* `lean/OneThird/Step8/LayeredBalancedFull.lean:284-288` — Piece 6
  consumes `LayeredDecomposition` with `L.w ≤ 4`.

### §9.2. Paper

* `step8.tex:1983-2007` — `def:layered`.
* `step8.tex:2009-2089` — `lem:layered-from-step7` (statement +
  inputs).
* `step8.tex:2096-2111` — band assembly `L_k := {a_k, b_{f_AB(k)},
  c_{f_AC(k)}}` from the potential and chains.

### §9.3. Predecessor docs / work items

* `docs/state-MA-Sig-Session1.md` (mg-a22b / mg-faf8) — §4.2 §E/§G
  bridge contract, §10 satisfiability verification.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7) —
  §2.3 Piece 3, §3.3 Checkpoint 3.
* `docs/state-S7-Conc-D-Session1.md` (mg-3f00) — the Piece-2
  deliverable audited here.
* `docs/state-S7-F-bridge-Session1.md` (mg-5fbd),
  `docs/state-S7-F-bridge-Session2.md` (mg-0bd1) — prior S7-F RED
  audits (§7).
* `docs/PROOF-STRUCTURE-ONBOARDING.md` — §3 pitfall #2 (the
  three-check skeptical lens), pitfall #7 (the "named-but-empty"
  standing lesson).

---

## §10. Maintenance contract

This file is the state record for FULL REFACTOR Phase-2 Checkpoint 3
(mg-ca83). It is an audit snapshot — it does **not** own any Lean
source. Supersede it only with a later Checkpoint-3 re-audit after
the §6 re-scope (R1–R2) is executed. If a future polecat re-points
Piece 2 to deliver `ChainLiftData α`, record the new
Piece-2/Piece-3 boundary here and flip the verdict.
