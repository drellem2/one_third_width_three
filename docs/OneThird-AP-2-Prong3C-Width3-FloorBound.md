# OneThird — AP-2 Prong 3C: analytic inf Q on width-3 (is 14/39 the floor, or does Q descend toward 1/3?)

*Work item **mg-8bd6**. Follow-up to mg-3b16 (AP-2 Prong 3B-gamma, Family C order-polytope / Ehrhart probe), whose width-3 sweep surfaced `Q = 14/39 ≈ 0.358974` at `n = 7` (below the `4/11` seed) and asked the open question this prong addresses: does `min Q(n)` descend further below `14/39` toward `1/3`, or does `14/39` plateau as the next floor? Date 2026-05-29.*

*Read-first: [`OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md`](OneThird-AP-2-Prong3B-gamma-FamilyC-Probe.md) (the NEW-TERRITORY-BELOW-4/11 verdict + the 4/11-seed extraction template + the Wall Lemma §3.2 Ehrhart-dilation `Q`-invariance proof); [`OneThird-AP-2-Prong3A-SP-FloorBound.md`](OneThird-AP-2-Prong3A-SP-FloorBound.md) (the `8/21` analytic theorem; the structural template); [`OneThird-AP-2-Prong3B-beta-FamilyD-Probe.md`](OneThird-AP-2-Prong3B-beta-FamilyD-Probe.md); [`OneThird-AP-2-Prong2-FamilyB-SP-Probe.md`](OneThird-AP-2-Prong2-FamilyB-SP-Probe.md); [`OneThird-AP-2-Prong1-SelfDual-LowerBound.md`](OneThird-AP-2-Prong1-SelfDual-LowerBound.md) (the Outcome-4 wall-and-name pattern); [`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md) §§3C,4C,6,8; [`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md).*

*Deliverable script: [`scripts/onethird_ap2_prong3c_width3_floor_verify.py`](../scripts/onethird_ap2_prong3c_width3_floor_verify.py) — reuses the mg-3b16 five-engine harness (M1 order-ideal DP, M2 AP-0 kernel, M3 minimal-element-removal recursion, M4 brute permutations, MC Ehrhart order-polynomial) verbatim, adds the three extracted witnesses (4/11 seed, 14/39 witness + its n=8 trivial-top companion, the 6/17 refutation witness), checks the descent-ladder identities, and re-runs the exhaustive small-`n` width-3 floor + the §8.2 guard. Clean run ≈ a few seconds; a clean exit is the five-engine agreement + ladder identities + guard clearing.*

---

## 0. Headline

**VERDICT: REFUTATION — `14/39` is NOT the width-3 floor. `min Q` descends below it.**

A width-**exactly-3** poset at `n = 10` attains, in exact rational arithmetic and verified through all **five** inherited engines,

```
Q = 6/17 ≈ 0.352941   <   14/39 ≈ 0.358974   (still > 1/3 by 0.0196),
```

so the mg-3b16 working hypothesis "`14/39` is the next floor" is **false**. The live counterexample-hunt corridor narrows from `(1/3, 14/39]` to `(1/3, 6/17]`.

The minima sit on a clean rational **descent ladder**:

| `n` (first appearance) | `Q` | `3Q − 1` | `k = 1/(3Q−1)` | binding `Pr = (2k−1)/(3k)` | `Q − 1/3` |
|---:|---|---|---:|---|---|
| `5` (seed) | **`4/11`** | `1/11` | `11` | `7/11 ≈ 0.6364` | `1/33` |
| `7` | **`14/39`** | `1/13` | `13` | `25/39 ≈ 0.6410` | `1/39` |
| `10` | **`6/17`** | `1/17` | `17` | `11/17 ≈ 0.6471` | `1/51` |

Every minimum satisfies `3Q − 1 = 1/k` with `k` integral (`11, 13, 17`), i.e.

```
Q = 1/3 + 1/(3k) = (k+1)/(3k),     binding-pair  Pr[x<y] = (2k−1)/(3k) → 2/3.
```

The binding incomparable pair's balance creeps toward the `(1/3, 2/3)` value of the width-2 tight gadget `point ‖ (y<z)`. The ladder therefore **points to `inf Q = 1/3`** — the 1/3–2/3 conjecture asymptotically sharp at width exactly 3, consistent with the working hypothesis.

**But the descent stalls at `6/17` under search.** Three independent searches — two single-element-extension beam searches (from the seed and from the `6/17` witness) and a randomized hill-climb / anneal, all pushed to `n ≈ 14` with hundreds of restarts — find **nothing strictly below `6/17`**. The descent moved `4/11 → 14/39 → 6/17` in discrete *jumps* (at `n = 5, 7, 10`), plateauing between jumps; the searches cannot cross the jump beyond `6/17`. So `6/17` is the **new plateau / floor candidate** — exactly the role `14/39` played going into this prong, and `8/21` for width-3 SP in Prong 3A. Whether a further jump below `6/17` exists (descent → `1/3`) or `6/17` is a genuine analytic floor is the **re-opened Prong-3D question**.

**The n=8 "plateau" of mg-3b16 was a measurement artifact.** Its `n = 8` argmin is the `n = 7` `14/39` witness with a single **global top point** adjoined. A global max is forced last in every linear extension, so it adds only comparable pairs and leaves `e(P)` and every incomparable-pair balance unchanged — `Q` is preserved (the order-polytope analogue of Prong-3A Lemma B, "series = max"). The `n = 8` equality is therefore *not* a floor signal; the genuine descent resumes at `n = 10`. This removes the main empirical support that had suggested `14/39` was a true plateau.

**§8.2 anti-Cheeger guard (INHERITED STRICT) does NOT fire.** The lowest `Q` anywhere is `6/17 > 1/3`; no `Q ≤ 1/3` candidate exists. The `6/17` refutation witness has `Q > 1/3`, so it requires only the five already-used engines (M1–M4, MC) — **no sixth codebase is triggered** (that trigger is reserved for a `Q ≤ 1/3` claim). The single `Q = 1/3` boundary touch is the satisfied width-2 gadget (a theorem), reconfirmed.

---

## (i) Vision alignment (V2 + V4) — verbatim from the ticket

- **V2 (computable Q):** *leverages the GENUINE Ehrhart engine + the closed-form-Q-in-combinatorial-type identity Q(P) = max over incomparable pairs of min(e(P + x<y), e(P + y<x)) / e(P) — both delivered as theorems by mg-3b16. The analytic argument is the natural next layer once V2 is empirically validated.*
- **V4 (sharpness-or-pivot signal):**
  - *Strong success: prove Q ≥ 14/39 for all width-3 posets, all n, SHARP at the n=7 / n=8 witness. Mirror of Prong 3A's 8/21 sharp theorem; would convert the corridor (1/3, 14/39] into the corridor (1/3, 14/39] with 14/39 as a genuine analytic floor on width-3 (not just width-3 SP).*
  - *Partial success: prove Q ≥ c for some 1/3 < c ≤ 14/39 (e.g., Q ≥ 9/25, Q ≥ 7/19, Q ≥ 3/8); name the gap to 14/39 sharpness and the structural obstruction.*
  - *Refutation: exhibit a width-3 poset with Q < 14/39 (an analytic argument or a constructive descent ray). The polecat doc and mayor's dispatch guidance both suggest a continuous-relaxation / Lawrence-Varchenko volume-formula approach to descent rays — if successful, this narrows the corridor further.*
  - *Wall (Outcome 4): clean negative diagnosis — name precisely which combinatorial type blocks the bound and what additional structure would close it.*

**Which V4 branch fired:** the **third — Refutation**, plus the **fourth — clean Outcome-4 diagnosis** for the re-opened floor question. The Strong-success branch (`Q ≥ 14/39` for all width-3) is **definitively closed negatively**: the explicit, five-engine-verified `6/17` witness shows `14/39` is not a lower bound. A constructive descent witness `< 14/39` is exhibited (the refutation), and the descent ladder localises the structural mechanism; the Partial-success branch is not taken (no `c ∈ (1/3, 14/39]` lower bound is proved — see §5 for why), and §6 gives the clean diagnosis of what blocks both a `6/17` floor proof and a `k → ∞` descent construction. On V2 the closed-form-`Q`-in-combinatorial-type identity is the workhorse throughout (every `Q` and every `Pr[x<y]` is an exact order-polytope volume ratio `e(P + x<y)/e(P)`).

---

## 1. Setup, the `Q` metric, and the order-polytope identity (carry-forward)

For a finite poset `P`, under the uniform distribution on linear extensions,
```
Q(P) = max over incomparable pairs {x,y} of  min( Pr[x<y], Pr[y<x] )
     = 1/2 − min over incomparable pairs of |Pr[x<y] − 1/2|.
```
The 1/3–2/3 conjecture asserts `Q(P) ≥ 1/3`; for width 3 this is a **theorem** (the repo's paper, `thm:main`). This prong studies the *sharp infimum* of `Q` over width-exactly-3 posets — `1/3`, `14/39`, `6/17`, or some other value.

**The order-polytope identity (Stanley 1986; mg-3b16 §1, reused verbatim).** The order polytope `O(P) = {f : P → [0,1] | f(a) ≤ f(b) when a ≤ b}` triangulates into `e(P)` unit simplices, so `vol O(P) = e(P)/n!`. For incomparable `x,y`, `O(P) ∩ {f(x) ≤ f(y)}` is exactly `O(P + x<y)`, whence
```
Pr[x<y] = vol(O(P) ∩ {f(x)≤f(y)}) / vol O(P) = e(P + x<y) / e(P),
Q(P)    = max over incomparable {x,y} of min( e(P+x<y), e(P+y<x) ) / e(P).
```
Every `Q` claim is thus a counting inequality on linear extensions of refined posets — the V2 reduction, realised exactly. (Per Wall Lemma §3.2 of mg-3b16, the Ehrhart **dilation** parameter `t` is `Q`-invariant, so the closed form lives in the *combinatorial type*, never in `t`.) Reference bars: `1/3 ≈ 0.3333` (global tight, width-2 gadget), `8/21 ≈ 0.3810` (Prong-3A width-3 SP theorem, sharp at `T*`), `4/11 ≈ 0.3636` (graded-3-level seed), `2/5 = 0.4` (Family D floor).

---

## 2. The extracted `14/39` witness + five-engine verification

**The witness (mg-3b16 broader-probe `n = 7` argmin, extracted explicitly here).** On `{0,…,6}` with cover relations
```
0 < 2,   0 < 3,   1 < 4,   1 < 5,   2 < 4,   2 < 5,   3 < 6,   4 < 6,
```
i.e. levels `L0 = {0,1}`, `L1 = {2,3}`, `L2 = {4,5}`, `L3 = {6}` (height 4; **not** graded — element `1` jumps `L0 → L2`). Hasse diagram:

```
            6              (top)
           / \
          3   4            L1 elt 3, L2 elt 4
          |  /|\
          | / | \
   5      |/  |  \          5 is a second L2 elt (over {1,2})
  /|\     /   |   \
 / | \   /    |    \
1  2  (2,3 over 0; 4,5 over {1,2}; 6 over {3,4})
 \ |
  \|
   0                       (0,1 minimal)
```

- `e(P) = 39`,  `vol O(P) = e/7! = 39/5040 = 13/1680`.
- The binding incomparable pair is the **near-twin pair `{1,2}`**: both have the identical up-set `{4,5,6}`, but `2` carries the element `0` below it while `1` is minimal. The down-asymmetry biases the order (`2` must wait for `0`, so `1` tends to precede `2`):
```
Pr[1<2] = e(P + 1<2)/e(P) = 25/39 = (2·13 − 1)/(3·13),
Q(P)    = min(25/39, 14/39) = 14/39 = (13+1)/(3·13)   (k = 13).
```

**Five-engine cross-check (the acceptance gate, roadmap §4).**

| engine | mechanism | `e` | `Q` |
|---|---|---:|---|
| **M1** primary | order-ideal DP | 39 | 14/39 |
| **M2** AP-0 | generic width-3 kernel `Q_via_dp` | 39 | 14/39 |
| **M3** independent | minimal-element-removal recursion | 39 | 14/39 |
| **M4** brute | full linear-extension permutation enumeration | 39 | 14/39 |
| **MC** Family C | Ehrhart order-polynomial leading coefficient | 39 | 14/39 |

All five agree exactly (script §3).

**The `n = 8` plateau companion is a trivial top-extension.** The mg-3b16 `n = 8` argmin is this witness with one **global top** point `7` (above all `0,…,6`) adjoined. A global maximum is forced last in every linear extension, so `e(P)` and every incomparable-pair balance are unchanged: `e = 39`, `Q = 14/39` again — the order-polytope analogue of Prong-3A's Lemma B (`series = max`, `Q` preserved by appending a comparable element). **This means the mg-3b16 "plateau at `n = 8`" carried no information about the floor** — it is the same poset plus a forced point. The genuine `min Q(n)` resumes descending at `n = 10`. (Verified: script §3 asserts element `7` is a global top and `e, Q` unchanged.)

---

## 3. The `6/17` refutation witness (the headline result)

A width-**exactly-3** poset at `n = 10`, found by beam-search descent from the seed and verified through all five engines. On `{0,…,9}` with cover relations
```
0<2,  0<3,  1<8,  1<9,  2<9,  3<6,  3<8,  4<6,  4<7,  7<5,  8<5,  9<4.
```
- `e(P) = 187 = 11·17`,  width `= 3` (largest antichain size 3).
- Binding incomparable pair `{3,9}`:
```
Pr[3<9] = e(P + 3<9)/e(P) = 121/187 = 11/17 = (2·17 − 1)/(3·17),
Q(P)    = min(11/17, 6/17) = 6/17 = (17+1)/(3·17)   (k = 17).
```

| engine | `e` | `Q` |
|---|---:|---|
| M1 / M2 / M3 / M4 / MC | 187 | **6/17** |

All five agree (script §4). Since `Q = 6/17 > 1/3`, the §8.2 guard does **not** fire and **no sixth codebase is required** — the guard's fresh-codebase trigger is reserved for a `Q ≤ 1/3` claim, and this witness *satisfies* the conjecture. It is nonetheless a rigorous, exact-arithmetic proof that

```
inf over width-exactly-3 posets of Q  ≤  6/17  <  14/39,
```

which **refutes** the hypothesis that `14/39` is the width-3 floor and narrows the live corridor to `(1/3, 6/17]`.

---

## 4. The descent ladder and the drop-vs-plateau evidence

### 4.1 The ladder identity

The three minimum-`Q` witnesses (`4/11` at `n ≤ 6`, `14/39` at `n = 7`, `6/17` at `n = 10`) satisfy the single Diophantine relation
```
3·Q − 1 = 1/k      with k = 11, 13, 17 integral,
```
equivalently `Q = (k+1)/(3k) = 1/3 + 1/(3k)` and binding-pair `Pr[x<y] = (2k−1)/(3k)`. As `k → ∞`, `Q → 1/3⁺` and `Pr → 2/3⁻` — the binding pair approaches the exact `(1/3, 2/3)` balance of the width-2 tight gadget `point ‖ (y<z)`. **Mechanistically**, each witness's binding pair is a *near-twin* pair `{x,y}` sharing one side (a common up-set or down-set) and differing on the other by a single chain element whose "weight" pulls the balance away from `1/2`; lengthening / tuning that weight within the width-3 budget moves the balance toward `2/3`. This is the order-polytope realisation of "make the third strand contribute a forced, near-`2/3` pair", and it points to `inf Q = 1/3`.

### 4.2 The descent moves in discrete jumps; search stalls at `6/17`

The minimum jumps at specific sizes and plateaus between them:

| `n` | best `Q` found (exhaustive where marked ✓, else search upper bound) | `k` |
|---:|---|---:|
| 5–6 | `4/11` ✓ (exhaustive, mg-3b16) | 11 |
| 7 | `14/39` ✓ (exhaustive, 40,916 posets) | 13 |
| 8 | `14/39` (= `n=7` witness `⊕` top point — trivial) | 13 |
| 9 | `14/39` (beam upper bound; exhaustive deferred, §6) | 13 |
| 10 | **`6/17`** (beam; five-engine verified) | 17 |
| 11–14 | `6/17` (two beams + anneal, no descent below) | 17 |

Three independent searches — (a) a single-element-extension beam from the seed, (b) a single-element-extension beam re-seeded from the `6/17` witness, (c) a randomized hill-climb / anneal at `n = 11..14` with ~160 restarts — **all bottom out at exactly `6/17`** and find nothing below it. The earlier jumps each required adding 2–3 elements *at once* (the intermediate posets do not lower `Q`), so a greedy single-step search cannot cross them; this explains the stall without settling whether a further jump exists. Hence the honest reading: **`6/17` is the new plateau / floor candidate**, with the *same drop-then-plateau signature* that `14/39` had (and that `8/21` had for SP) — and which this prong just showed was not, for `14/39`, a genuine floor.

### 4.3 Naive descent families do not work (why the construction is hard)

Straightforward parametric families fail to descend, which sharpens the obstruction:
- *Lengthening the top/bottom chain of the seed* (more "weight" above/below the heavy twin) over-shoots: a different pair (e.g. a chain element vs the light twin) becomes more balanced and `Q` jumps **up** (to `3/7`, `8/17`, …), not down.
- *Ordinal sums / series stacking* of gadgets preserve `Q = max` (Lemma-B analogue), so they cannot descend below a component.
- *A width-2 `Q = 1/3` tower (`G^{⊕m}`) made width-3 by inserting one element incomparable to a gadget's antichain* creates a **balanced** pair (`Pr = 1/2`, the inserted element twins a gadget point), jumping `Q` to `1/2`.

So the descent witnesses are *delicately balanced* — every incomparable pair tuned simultaneously so the most-balanced one is just above `1/3` — which is exactly why a clean `k → ∞` family is not immediate and why the searches stall. (Script-tested; the families are in the prong's scratch exploration, summarised here.)

---

## 5. Why no partial lower bound `Q ≥ c` is claimed (honest scoping)

The Partial-success V4 branch (prove `Q ≥ c` for some `1/3 < c ≤ 14/39`, all width-3) is **not** taken, for a precise reason. A clean analytic lower bound `> 1/3` for *all* width-3 posets would be a strict strengthening of the repo's width-3 theorem (`Q ≥ 1/3`), and the descent ladder shows any such `c` must satisfy `c ≤ 6/17` and, if the ladder reaches `1/3`, `c = 1/3` is the only valid uniform bound — i.e. **there may be no `c > 1/3`**. Concretely: the `6/17` witness already rules out every `c > 6/17`, and the `(k+1)/(3k)` ladder threatens to rule out every `c > 1/3`. Proving a *finite* floor (some `c > 1/3`) is therefore not a sub-goal of the present evidence but its *opposite* — it would require first **disproving** the descent (showing the ladder terminates), which the searches neither establish nor refute. Claiming a partial `c > 1/3` now would be unsupported. The one rigorous floor available is the **finite-class** result inherited from mg-3b16: over the *graded 3-level* width-3 family (each rank an antichain, `≤ 9` elements, exhaustive) `Q ≥ 4/11`, sharp at the seed — but the `14/39` and `6/17` witnesses escape that class (they have height ≥ 4), so `4/11` is not a floor for general width-3.

---

## 6. Outcome-4 clean diagnosis (the re-opened floor question)

Per the §8 / Prong-1 / Prong-3B "name the wall" discipline, the precise state of the corridor `(1/3, 6/17]`:

**What is settled.** `14/39` is not the width-3 floor (refuted by the exact `6/17` witness). The `n = 8` "plateau" was a `Q`-preserving top-adjunction, not a floor. The descent ladder `3Q−1 = 1/k` (`k = 11, 13, 17`) with binding `Pr → 2/3` is real and exact on the known minima.

**The two open horns and what each needs.**
1. **Descent → 1/3 (ladder continues).** Needs an explicit family `P_m` with `Q(P_m) = (k_m+1)/(3k_m)`, `k_m → ∞`. The obstruction: the witnesses are not single-parameter deformations of one another (the `k = 13` and `k = 17` minimal witnesses have *different* binding-pair geometries), and naive 1-parameter families either over-shoot (a chain pair becomes balanced) or create a `1/2`-balanced twin. A successful construction must add the "third-strand weight" so that, simultaneously, (i) the near-twin binding pair's `Pr` rises toward `2/3`, and (ii) **no** other incomparable pair drops its `min(Pr,1−Pr)` below the binding value. The Lawrence–Varchenko / continuous-relaxation route (roadmap §6.3, mg-3b16 §6) is the natural analytic tool: express `Q` of a continuously-relaxed width-3 shape as a signed sum of order-polytope sub-volumes and take the descent limit. This is the recommended Prong-3D attack.
2. **Genuine floor at `6/17` (ladder terminates).** Needs a proof that `Q ≥ 6/17` for all width-3 posets, sharp at the `n = 10` witness — the exact analogue of Prong-3A's `8/21` SP theorem, but for the full (non-SP) width-3 family. The obstruction: Prong-3A's proof rests on the SP-tree recursion (Lemma A cross-pair reduction), which does **not** exist for general width-3 posets; one needs a replacement reduction of the general-width-3 `Q` to a bounded set of "binding pair classes" (the near-twin pairs of §4.1), then a `6/17` bound on that class. No such reduction is known.

The searches (beam ×2 + anneal, `n ≤ 14`) discriminate weakly: they support a `6/17` plateau *up to `n = 14`*, but each prior jump needed a +2/+3 element gadget that greedy search could not assemble, so absence-of-descent-under-search is **not** evidence of a floor. The corridor is genuinely `(1/3, 6/17]` with the drop-vs-plateau verdict undecided — but with the working hypothesis (`inf = 1/3`) now better supported than the plateau hypothesis, because the one concrete plateau signal (`14/39` at `n = 7,8`) was shown to be an artifact.

---

## 7. Routine checks (ticket ROUTINE CHECKS) — all via the closed-form / five-engine route

The verification script asserts each:
- **`14/39` witness:** `e(P) = 39`, `e(P + 1<2) = 25`, ratio `25/39`, `Q = 14/39`; `vol O(P) = 13/1680`. ✓ (five engines)
- **`6/17` witness:** `e(P) = 187`, `e(P + 3<9) = 121`, ratio `11/17`, `Q = 6/17`. ✓ (five engines)
- **`4/11` seed:** `e = 11`, `e(P + b0<b1) = 7`, ratio `7/11`, `Q = 4/11`; `vol O(P) = 11/120`. ✓ (five engines)
- **Width-2 tight gadget `point ‖ (y<z)`:** `e = 3`, `e(P + x<y) = 1`, `Pr[x<y] = 1/3`, `Q = 1/3` (satisfied boundary). ✓
- **Ladder identities:** `3Q − 1 = 1/k`, `Q = (k+1)/(3k)`, binding `Pr = (2k−1)/(3k)` for `k = 11, 13, 17`. ✓
- **Exhaustive small-`n` width-3 floor:** `4/11` at `n ≤ 6`, `14/39` at `n = 7` (40,916 posets) — reproduces mg-3b16. ✓
- **§8.2 guard:** every swept `Q > 1/3`; lowest is `6/17`; guard does not fire; no sixth-codebase halt. ✓

---

## 8. Suggested Prong 3D brief (gated on this REFUTATION verdict)

`14/39` is refuted; the corridor is `(1/3, 6/17]`. Prong 3D should resolve the drop-vs-plateau horn at `6/17`, in recommended order:

**Prong 3D-α (recommended) — the constructive descent ray toward `1/3`.** Build an explicit width-3 family `P_m` with `Q(P_m) = (k_m+1)/(3k_m)`, `k_m → ∞`, via the Lawrence–Varchenko / continuous-relaxation volume formula on the near-twin binding-pair mechanism (§6 horn 1). Success proves `inf Q = 1/3` over width-exactly-3 (the 1/3–2/3 conjecture asymptotically sharp at width 3, beyond the width-2 gadget) — a clean, citable result and the strongest possible outcome. Concrete seed: the `k = 13` and `k = 17` minimal witnesses of §2–§3; find the *jump operator* that took `k = 11 → 13 → 17` (sizes `5 → 7 → 10`) and iterate it analytically.

**Prong 3D-β (the floor alternative) — attempt `Q ≥ 6/17`.** If 3D-α stalls, attempt the SP-analogue floor theorem `Q ≥ 6/17` for all width-3, sharp at the `n = 10` witness (§6 horn 2). The missing input is a cross-pair reduction for *general* (non-SP) width-3 replacing Prong-3A Lemma A — reducing `Q` to the near-twin pair class. A negative result here (no such reduction) is itself a clean Outcome-4 deliverable.

**Prong 3D-γ (cheap, rigour) — exhaustive `n = 9, 10` confirmation.** Pin the exact per-`n` floor at `n = 9` (deferred here; beam upper bound `14/39`) and `n = 10` (beam upper bound `6/17`) via iso-reduced exhaustive enumeration, to confirm `6/17` is the true `n = 10` minimum and chart the jump sizes precisely — directly informing whether the `k`-sequence `11, 13, 17, …` continues.

*(Parked / out of scope per NON-GOALS: no Cheeger/cut-and-window; no `Q ≤ 1/3` claim without a sixth codebase per §8.2 STRICT — not reached here since lowest `Q = 6/17 > 1/3`; no Lean / LaTeX / main.tex; Monte-Carlo never source of truth; no Family A/B/D re-sweep; no `t`-dilation analytic argument (proven `Q`-invariant); no formal closure of Prong-3A's φ4/T lemmas.)*

---

## Carry-forwards (for the next polecat)

- **Verdict:** `14/39` is **NOT** the width-3 floor. Exact, five-engine-verified width-3 poset at `n = 10` with `Q = 6/17 ≈ 0.3529 < 14/39` (still `> 1/3`). Corridor narrowed `(1/3, 14/39] → (1/3, 6/17]`. (REFUTATION + Outcome-4 diagnosis of the re-opened floor.)
- **The descent ladder (reusable):** the known minima satisfy `3Q − 1 = 1/k`, `Q = (k+1)/(3k)`, binding `Pr = (2k−1)/(3k) → 2/3`, with `k = 11 (n=5), 13 (n=7), 17 (n=10)`. Points to `inf Q = 1/3`. The binding pair is always a **near-twin pair** (shared up- or down-set, asymmetric single-chain weight on the other side).
- **The n=8 "plateau" debunked:** mg-3b16's `n = 8` argmin is the `n = 7` `14/39` witness `⊕` a global top point — `Q`-preserving (Prong-3A Lemma-B analogue), not a floor signal. Removes the main support for a `14/39` plateau.
- **The new plateau candidate:** `6/17`. Three searches (2 beams + anneal, `n ≤ 14`) find nothing below it; the descent moves in +2/+3-element jumps that greedy search cannot cross, so the stall is *not* proof of a floor. Drop-vs-plateau at `6/17` is the open Prong-3D question.
- **Reusable instrument:** [`scripts/onethird_ap2_prong3c_width3_floor_verify.py`](../scripts/onethird_ap2_prong3c_width3_floor_verify.py) — reuses the mg-3b16 five-engine `verify_C` harness + §8.2 guard, adds the three witnesses (`witness_14_39_n7`, `witness_14_39_n8_trivial`, `witness_6_17_n10`), the ladder checker (`k_of`), and the exhaustive small-`n` floor. Clean run ≈ seconds.
- **Reference bars:** `1/3` (global tight), `8/21` (width-3 SP theorem), `4/11` (graded-3-level seed), `14/39` (mg-3b16 `n=7`, now NOT a floor), and **`6/17 ≈ 0.3529`** (the new lowest width-3 `Q`, the Prong-3D plateau/floor target).
- **Guard discipline (INHERITED STRICT):** lowest `Q = 6/17 > 1/3`; the `6/17` refutation needs only M1–M4 + MC (all `> 1/3`). A `Q ≤ 1/3` claim would still require a fresh SIXTH codebase (M1–M4, MC all used) + brute force.
