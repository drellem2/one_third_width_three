# OneThird — AP-2 Prong 1: analytic Q lower bound on the Family A self-dual rule — sharpness or pivot signal

*Follow-up to AP-1b′ (mg-106e), which discovered the self-dual rule
`μ₃=0, λ₃=λ₁−μ₁, μ₂=λ₁−λ₂` and triple-confirmed the empirical floor
`min Q = 27/70` at `n=8`, rising into a `~0.42–0.47` band for `n ≥ 9`.
Work item **mg-9597**.*

*Inputs (read-first):
[`OneThird-AP-1b-followup-FamilyA-extended-sweep.md`](OneThird-AP-1b-followup-FamilyA-extended-sweep.md)
(the rule + triple-confirm, mg-106e);
[`OneThird-AP-1a-FamilyA-SmallK-Snapshot.md`](OneThird-AP-1a-FamilyA-SmallK-Snapshot.md)
(mg-746f);
[`OneThird-AP-0-FamilyA-Viability-Probe.md`](OneThird-AP-0-FamilyA-Viability-Probe.md)
(mg-98a6);
[`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md)
§§5, 6, 8; canonical
[`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md)
(vision-parts 3 + 4).*

*Reproducible cross-checks:
[`scripts/onethird_ap2_prong1_selfdual_lowerbound.py`](../scripts/onethird_ap2_prong1_selfdual_lowerbound.py)
— reuses the AP-0 engine verbatim (`skew_cells`, `build_poset`,
`count_linear_extensions_dp`, `augment_relation`, `naruse_count`,
`enumerate_linear_extensions`, `try_realise_as_skew_shape`, `probe_shape`). Pure
Python / stdlib; full run < 1 min. Re-run with
`python3 scripts/onethird_ap2_prong1_selfdual_lowerbound.py` (`--quick` skips the
`n=19` witness and the heavy enumerations).*

---

## 0. Vision alignment & non-goals

This ticket realises **vision-part 3** in its *analytic* mode (study the algebraic
structure of the data-corrected family rather than sweep wider) and sharpens
**vision-part 4** into a **SHARPNESS-OR-PIVOT** signal: either prove the self-dual
floor is structurally bounded above `1/3` (a clean bounded-null deliverable), or
surface exactly where the bound fails (gating the Prong 2 pivot to a non-skew
Family B test).

Non-goals honoured (roadmap §8): **no** Cheeger / cut-and-window re-litigation;
**no** counterexample claim; **no** Lean, LaTeX, or `main.tex`; **width-3 only**;
**Monte-Carlo never the source of truth**. The deliverable is this Markdown
math-doc plus a Python cross-check script. No new compute sweep — the script only
performs the routine numerical confirmations the analytic argument rests on.

**GUARD (roadmap §8.2, anti-Cheeger).** No `Q ≤ 1/3` arises anywhere below;
the family-wide record stays `27/70 ≈ 0.386` (`n=8`). Were `Q ≤ 1/3` ever to
surface (e.g. from a relaxation bounding below `Q`), it would be **not** a
counterexample claim: §8.2 mandates independent reimplementation in a separate
codebase plus brute force before any claim. The AP-0/AP-1a/AP-1b′ three-engine
agreement is **not** independent code.

---

## 1. The object and the precise statement attempted

A self-dual 3-row skew shape is `λ/μ` with

> `μ₃ = 0`,  `λ₃ = λ₁ − μ₁`,  `μ₂ = λ₁ − λ₂`,

a 3-parameter family in `(C = λ₁, λ₂, μ₁)`, `n = 2(λ₁−μ₁) + (2λ₂−λ₁)`. Its
cell-poset `P` (cells `(i,j)`, `μ_i < j ≤ λ_i`, product order) has width ≤ 3, and
the balance constant is `Q(P) = max` over incomparable pairs `(x,y)` of
`min(Pr[x<y], Pr[y<x])` under the uniform distribution on linear extensions.

The **180° box rotation** `ρ(i,j) = (4−i, C+1−j)` (where `C = λ₁` is the box
width and rows run `1..3`) is the symmetry that *defines* the family: it is a
bijection of the cell set that **reverses** the product order, so `P ≅ Pᵒᵖ`
(self-dual).

The targets, in decreasing strength:

- **Goal 1.** `Q ≥ 27/70` for all `n` on the self-dual family.
- **Goal 2.** `Q > 1/3` for all `n` on the self-dual family.
- **Outcome 4.** If neither is reachable: identify precisely which
  incomparable-pair class blocks the bound and what additional structure is
  needed.

**This document's result is Outcome 4: neither Goal 1 nor Goal 2 is reachable
from the box-rotation symmetry. We prove exactly *why* the symmetry is
insufficient, isolate the single quantity an analytic bound must control, and
record the precise missing lemma.** All structural claims (C1–C6 below) are
machine-verified by the companion script across the per-`n` self-dual minimisers
`n ∈ [7,16]` plus the three carry-forward witnesses (`n = 8, 13, 19`).

---

## 2. The analytic structure: the central-symmetry pair identity

This is the real, positive content the box-rotation buys — made fully rigorous.

> **Theorem 1 (central-symmetry pair identity).** Let `P` be the cell-poset of a
> self-dual 3-row skew shape and `ρ` its box rotation. For *every* incomparable
> pair `(x,y)`,
> `  Pr[x < y] = Pr[ρy < ρx].`

**Proof.** First, `ρ` is an order-reversing bijection of the cell set
(claim **C1**). Algebraically, `(i,j) ≤ (i′,j′) ⟺ i ≤ i′ ∧ j ≤ j′ ⟺
4−i′ ≤ 4−i ∧ C+1−j′ ≤ C+1−j ⟺ ρ(i′,j′) ≤ ρ(i,j)`; equivalently
`x ≤ y ⟺ ρy ≤ ρx`. (The script also checks `ρ` maps the cell set onto itself,
which is exactly the three self-dual identities of §1.)

Let `E` be the set of linear extensions, `e = |E|`, each `σ ∈ E` a bijection
cells → `{1,…,n}` with `x < y ⟹ σ(x) < σ(y)`. Define the **extension
involution** `Φ : E → E` by
`  (Φσ)(c) = n + 1 − σ(ρc).`
`Φσ` is a linear extension: if `x < y` then `ρy < ρx` (order-reversal), so
`σ(ρy) < σ(ρx)`, so `n+1−σ(ρy) > n+1−σ(ρx)`, i.e. `(Φσ)(y) > (Φσ)(x)`. And
`Φ² = id` because `ρ² = id` and `n+1−(n+1−t) = t`; hence `Φ` is a bijection of `E`.

Now, for incomparable `x,y`,
`(Φσ)(x) < (Φσ)(y) ⟺ n+1−σ(ρx) < n+1−σ(ρy) ⟺ σ(ρy) < σ(ρx)`. Therefore
`|{σ : (Φσ)(x) < (Φσ)(y)}| = |{σ : σ(ρy) < σ(ρx)}| = e·Pr[ρy < ρx]`. But `Φ` is a
bijection, so `{Φσ : σ ∈ E} = E` and the left side also equals
`|{τ ∈ E : τ(x) < τ(y)}| = e·Pr[x < y]`. Dividing by `e` gives the claim. ∎

> **Corollary (orbit relation, C3).** Applying Theorem 1 to `(ρx,ρy)` and using
> `ρ² = id` gives `Pr[ρx < ρy] = Pr[y < x] = 1 − Pr[x<y]`. So in the `ρ`-orbit
> `{(x,y), (ρx,ρy)}` the two pairs carry probabilities `p` and `1−p`, hence
> **equal balance** `min(p, 1−p)`.

The box-rotation invariance therefore acts on the incomparable pairs, splitting
them into orbits of size 1 or 2 that carry a single balance value. This is the
clean structural payoff — and as §3–4 show, it is also where the payoff stops.

**Verified (C2, C3):** Theorem 1 and its corollary hold for every incomparable
pair of every shape in the test bank (the script asserts `Pr[x<y] = Pr[ρy<ρx]`
and `Pr[ρx<ρy] = 1−Pr[x<y]` inline).

---

## 3. The self-symmetric pairs and the Q-realiser

A pair `{x,y}` is **fixed by `ρ`** (an orbit of size 1) iff `ρx = y` (so
`ρy = x`). For a self-dual 3-row shape these `ρ`-**swapped** pairs are exactly the
row-1 ↔ row-3 cells

> `(1,j) ↔ (3, C+1−j)`  with  `2j > C+1`

(the inequality is the incomparability condition; row-2 self-pairs `(2,j)↔(2,C+1−j)`
are in the same row, hence comparable, never incomparable). The canonical one,
present for every member with `C ≥ 2`, is the **corner pair** `(1,λ₁) ∥ (3,1)`
(`(1,λ₁)` is the unique maximal cell of row 1, `(3,1)` a minimal cell of row 3).

Empirically (script, and AP-0/AP-1b′):

| `n` | self-dual minimiser | `Q` | Q-realising pair | pair type |
|-----|---------------------|-----|------------------|-----------|
| 8 | `(4,4,2)/(2,0,0)` | `27/70` | `(1,4) ∥ (3,1)` | **ρ-swapped corner** |
| 7 | `(5,5,1)/(4,0,0)` | `12/29` | `(1,5) ∥ (2,3)` | orbit-2 (row1↔row2) |
| 13 | `(5,5,4)/(1,0,0)` | `3/7` | `(1,2) ∥ (2,1)` | orbit-2 (row1↔row2) |
| 19 | `(13,8,8)/(5,5,0)` | `2307921/5088542` | `(1,8) ∥ (2,6)` | orbit-2 (row1↔row2) |

So at the *record* `n=8` the Q-realiser is the central ρ-swapped corner pair; for
every larger member it is a generic orbit-2 row1↔row2 pair. **Either way, the
balance of the Q-realiser is precisely the quantity we would need to bound.** The
next two sections show the symmetry bounds neither.

---

## 4. The wall: the symmetry pins no pair's balance

There are two routes by which a symmetry can force a balanced pair, and the
self-dual family closes both.

> **Lemma 2 (signed-gap invariance — C4).** For a `ρ`-swapped incomparable pair
> `{x, ρx}`, the signed gap `g(σ) = σ(ρx) − σ(x)` is invariant under the
> extension involution: `g(Φσ) = g(σ)` for all `σ ∈ E`.

**Proof.** `(Φσ)(x) = n+1−σ(ρx)` and `(Φσ)(ρx) = n+1−σ(ρ²x) = n+1−σ(x)`, so
`g(Φσ) = (Φσ)(ρx) − (Φσ)(x) = (n+1−σ(x)) − (n+1−σ(ρx)) = σ(ρx) − σ(x) = g(σ)`. ∎

Consequently the *entire distribution* of `g` (hence `Pr[x<ρx] = Pr[g>0]`) is
`Φ`-invariant — the involution permutes the extensions **within** each level set
of `g`. The one probabilistic lever self-duality supplies, `Φ`, therefore acts
trivially on exactly the self-symmetric pairs: it neither forces `Pr[x<ρx] = 1/2`
nor bounds it away from `0` or `1`. (Numerically the corner pair runs from
`27/70 ≈ 0.386` at `n=8` to `64/39559 ≈ 0.0016` at `n=14` — wildly biased — all
the while `Φ`-symmetric. The symmetry simply does not see the bias.)

This is the heart of the matter and worth stating plainly: **an order-*reversing*
involution that swaps `x` and `y` does NOT balance the pair.** (Contrast an
order-*preserving* automorphism swapping `x,y`, which forces `Pr = 1/2`
immediately.) Self-duality is anti-symmetry; it relates `(x,y)` to its mirror but
fixes the bias of the self-symmetric pairs.

> **Claim 3 (trivial automorphism route — C5).** No order-*automorphism* of `P`
> swaps an incomparable pair, so the `Pr = 1/2`-by-automorphism route is empty.

**Verification.** An automorphism `α` swapping incomparable `x,y` would give
`Pr[x<y] = 1/2` (relabel each extension by `α`). The script confirms **no**
incomparable pair has `Pr = 1/2` on any bank shape (indeed `Q < 1/2` throughout),
so `Aut(P)` contains no such swap. Structurally these skew cell-posets are rigid:
the grid coordinates `(i,j)` are order-invariants (row = height of the principal
up-set chain, etc.), so `Aut(P)` is trivial and `ρ` is the *only* non-identity
symmetry.

**Therefore the box-rotation symmetry alone yields no lower bound on
`Q = max balance`:** it organises the pairs (Theorem 1, Corollary) but pins none
of their balances (Lemma 2, Claim 3).

---

## 5. The reduction, and the single missing quantity

To prove a lower bound `Q ≥ b` it suffices to exhibit **one** incomparable pair
`(x,y)` with `min(Pr[x<y], Pr[y<x]) ≥ b`. For any candidate pair,

> `Pr[x<y] = e(P + (x<y)) / e(P)`,

a ratio of two standard-Young-tableau counts (`e(P)` of the shape, `e(P+(x<y))`
of the poset with the relation `x<y` forced and transitively closed).

The count `e(P)` itself **is** closed-form (Naruse). But the **numerator is not**:
by AP-1b′ §5 the forced poset `P+(x<y)` is essentially never again a skew shape
on this family (closed-form fraction ≈ 0), and the script confirms (**C6**) that
for the *Q-realising* pair specifically neither forced direction realises as a
skew shape at any bank `n`. So `e(P+(x<y))` is a genuine width-3 order-ideal-DP
quantity with **no closed form** on the self-dual family.

Theorem 1 relates this ratio to its mirror (`Pr[ρx<ρy] = 1−Pr[x<y]`) but **does
not evaluate or bound it**. The symmetry has no further purchase: it has already
been fully spent organising the pairs.

So the analytic argument reduces cleanly to a single missing input:

> **Missing Lemma (what would close Family A).** A counting inequality on
> forced-relation skew-SYT ratios — for the right incomparable pair `(x,y)` of a
> self-dual 3-row shape,
> `   ⅓ · e(P)  ≤  e(P + (x<y))  ≤  ⅔ · e(P)`
> (Goal 2), or the sharper `27/70`-window (Goal 1). Equivalently: an
> excited-diagram / hook-walk / Naruse-sum estimate that bounds
> `e(P+(x<y))/e(P)` into the balanced band for at least one pair per shape.

This is a self-contained analytic-combinatorics problem about skew-SYT counts of
*forced* (non-skew) width-3 posets. It is genuinely hard — it is a special case
of the **open** width-3 1/3–2/3 conjecture the repo is otherwise proving by the
Cheeger/Lean route — and the box-rotation symmetry, the only family-specific tool
the rule came with, provably does not provide it (§4).

---

## 6. Where exactly the argument fails — the blocking pair class

- **Blocking class:** the **orbit-2 row1↔row2 pairs** (the Q-realiser for every
  `n ≥ 9` in the bank), and at the record `n=8` the **ρ-swapped corner pair**
  `(1,λ₁)∥(3,1)`. These are the most-balanced incomparable pairs; bounding `Q`
  from below is exactly bounding *their* balance.
- **Why symmetry can't reach them:** the swapped pairs are `Φ`-signed-gap-invariant
  (Lemma 2) so their bias is symmetry-free; the orbit-2 pairs are only mirrored to
  a partner of equal balance (Corollary) — the symmetry never produces an *equation*
  or *inequality* pinning the common value. And there is no automorphism route
  (Claim 3).
- **What additional structure is needed:** the Missing Lemma of §5 — a
  forced-relation skew-SYT ratio bound (log-concavity / hook-content /
  excited-sum). Not derivable from self-duality; no closed form available
  (AP-1b′ §5; C6).

This is a *clean negative diagnosis*, the explicitly-sanctioned Outcome 4: the
box-rotation route to a Family-A sharpness result terminates here, at a named,
self-contained, out-of-scope lemma.

---

## 7. Context: the best off-the-shelf bound is below 1/3

For perspective on the size of the gap: the strongest *unconditional* lower bound
for the balance constant of an arbitrary non-chain finite poset is
`δ ≥ (5−√5)/10 ≈ 0.2764` (Brightwell–Felsner–Trotter, 1995). This applies to our
family but sits **below `1/3`**, so it cannot deliver Goal 2 — and the distance
from `0.2764` to the empirical self-dual floor `0.386` is precisely the
family-specific content the symmetry fails to supply. (Cited as context only; not
load-bearing for any claim here, and not a substitute for the §5 Missing Lemma,
which targets `1/3`, not `0.2764`.)

---

## 8. Routine checks (numerical confirmation)

The companion script confirms, with a clean exit *being* the two-method gate plus
the structural-claim suite passing:

**Witness re-verification (AP-0 kernel, cross-checked vs mg-106e).**

| `n` | witness | `e` | `Q` (re-derived) | mg-106e | gate |
|-----|---------|-----|------------------|---------|------|
| 8 | `(4,4,2)/(2,0,0)` | 140 | `27/70` | `27/70` ✔ | M1==M2 brute; `e`==Naruse |
| 13 | `(5,5,4)/(1,0,0)` | 6006 | `3/7` | `3/7` ✔ | M1==M2 brute; `e`==Naruse |
| 19 | `(13,8,8)/(5,5,0)` | 5088542 | `2307921/5088542` | `2307921/5088542` ✔ | DP==Naruse(`e`); `Q` by validated DP |

> **Ticket-body correction (flagged, not silent).** The mg-9597 brief lists the
> `n=19` witness `(13,8,8)/(5,5,0)` with "`Q = 943/2074`". That value
> (`≈ 0.45468`) is the **old cap-12 argmin** `(12,7,4)/(3,1,0)` from AP-1a, *not*
> the cap-stable `(13,8,8)/(5,5,0)` shape. The correct value for
> `(13,8,8)/(5,5,0)` is `2307921/5088542 ≈ 0.45355`, exactly as recorded in
> mg-106e §1/§3 and confirmed here. The brief's "`943/2074`" is a transcription
> slip carried from the superseded argmin.

**Structural claims C1–C6** (asserted for `n ∈ {7,…,16} ∪ {19}`):

- **C1** `ρ` is an order-reversing bijection (anti-automorphism). ✔ all shapes.
- **C2** central-symmetry pair identity `Pr[x<y] = Pr[ρy<ρx]`. ✔ all pairs.
- **C3** orbit relation `Pr[ρx<ρy] = 1−Pr[x<y]`. ✔ all pairs.
- **C4** signed-gap invariance for ρ-swapped pairs (the wall). ✔ (brute
  enumeration; checked for `e ≤ 50000`).
- **C5** no incomparable pair has `Pr = 1/2` (trivial automorphism route). ✔.
- **C6** the Q-realising augmented poset is not a skew shape (DP-bound, no closed
  form). ✔ all shapes.

GUARD: `Q > 1/3` at every shape tested; no `Q ≤ 1/3` anywhere.

---

## 9. Verdict and Prong 2 recommendation

### Verdict: **AMBER — clean negative diagnosis (Outcome 4). The box-rotation symmetry is exhausted as a lower-bound lever; Goal 1 and Goal 2 are not reachable from it.**

> AP-2 Prong 1 clears its scope as a *sharpness-or-pivot* signal. The positive
> deliverable is **Theorem 1** (the central-symmetry pair identity, the rigorous
> probabilistic form of the 180° box-rotation invariance) and its orbit
> corollary. The negative deliverable — the actual signal — is **Lemma 2 +
> Claim 3**: the symmetry pins no incomparable pair's balance (signed-gap
> invariance for swapped pairs; trivial automorphism group), so it yields **no**
> lower bound on `Q`. The bound reduces to a forced-relation skew-SYT ratio
> (`§5`), which has no closed form on this family (AP-1b′ §5; C6) and which the
> symmetry cannot bound. The blocking pair class is the orbit-2 row1↔row2 pairs
> (and the ρ-swapped corner pair at `n=8`).

### Prong 2 verdict: **PROCEED TO PRONG 2 (width-3 non-skew Family B test).**

The self-dual Family A floor is **empirically** bounded above `1/3` (≥ `27/70`,
plateau/rise — AP-1b′), but it is **not analytically sharply bounded** by the tool
the rule was discovered through. Because the wall (§4–6) is the *generic*
incomparable-pair balance — nothing peculiar to self-duality — the box-rotation
invariance is genuinely spent; no further symmetry argument will close it.
Two reasons to pivot rather than push:

1. **Prong 1 has extracted everything the symmetry yields.** Theorem 1 + Corollary
   are the complete probabilistic content of the box rotation; Lemma 2 + Claim 3
   show there is no more to take. Continuing on Family A would mean attacking the
   §5 Missing Lemma — a hard, self-contained skew-SYT-counting problem (a special
   case of the open width-3 conjecture), larger than a polecat and orthogonal to
   the program's cheap-parameter-sweep thrust.
2. **A non-skew Family B test answers the live cross-family question.** It would
   tell us whether the `27/70` floor is a *skew-shape artifact* or a genuine
   width-3 obstruction — exactly the sharpness datum the program wants, and
   reachable by the same closed-form/DP `Q`-kernel without the skew-SYT wall.

**If a future ticket wants to close Family A analytically**, the precise input is
recorded in §5: a counting inequality `⅓·e(P) ≤ e(P+(x<y)) ≤ ⅔·e(P)` for one
incomparable pair per self-dual shape (Goal 2), or the `27/70`-window form
(Goal 1) — i.e. a log-concavity / excited-diagram estimate on forced-relation
width-3 skew-SYT ratios. Self-duality does not supply it.

**No counterexample is claimed or expected** (§8.2). The honest reading: Family A
self-dual is a solid *empirical* bounded-null; Prong 1 converts its *defining
symmetry* into a rigorous structural theorem but proves that same symmetry cannot
turn the empirical floor into a proof. The value delivered is the identity, the
exact location of the wall, and a clean gate to Prong 2.

---

## Appendix — reproduction

```
python3 scripts/onethird_ap2_prong1_selfdual_lowerbound.py           # witnesses (incl. n=19) + C1-C6 on n in [7,16] u {19} (< 1 min)
python3 scripts/onethird_ap2_prong1_selfdual_lowerbound.py --quick   # n=8,13 witnesses + C1-C3,C5,C6 (skips n=19 and heavy C4 enums)
```

The script reuses the AP-0 engine
(`scripts/onethird_ap0_familyA_skew_probe.py`) verbatim and asserts every
cross-check inline (Naruse == DP == brute for `e` where feasible; brute == DP for
`Q`; Theorem 1, Corollary, Lemma 2, Claims 3/C6), so a clean exit *is* the
two-method-agreement gate plus the structural-claim suite passing.
