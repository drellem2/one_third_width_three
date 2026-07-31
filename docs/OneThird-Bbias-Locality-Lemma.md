# OneThird — the (B-bias) locality lemma: pinned, re-priced, redirected — and (B) implies LIB

**Work item:** mg-a58f (high, repo `one_third_width_three`). Lever 2 at the L1b crux: prove that
under freezing `max_x Σ_{y ∥ x} Pr[{x,y} inverts] = O(1)`. mg-0ed7's residual / mg-dcae Prop. 5.4's
hypothesis / mg-dbd1 §5 recommendation 1 — the same statement, reached three times independently.

**Constraints honored.** Paper-and-pencil only. **No computation was run for this document** — no
scripts, no datasets, no enumerations, no delta-engine calls. Every numeric statement below is a
closed-form hand derivation, and every one is re-checkable in under a minute with pencil (the
worked micro-checks at `m = 1, 2` are given inline so a reader can confirm without a machine). No
Stanley, no Alexandrov–Fenchel, no Ma–Shenfeld, no combinatorial atlas is used anywhere.

---

## 0. Verdict

> **RED for the lever as briefed · AMBER redirect.**
>
> **RED.** The (B-bias) locality lemma is **not** an elementary reserve route *below* the crux. It
> **implies** L1b. Precisely (Theorem 3.2, one line): the per-element inversion masses satisfy
> `Σ_x m_x = 2 E[inv_e]` identically, so a uniform bound `max_x m_x ≤ C` forces
> `E[inv_e] ≤ Cn/2` — which **is LIB**, in its strongest (`γ`-free) form — and hence, by mg-210d's
> master bound, `1 − λ_std ≤ 3Cn/(n²−1) = O(1/n) → 0`, which is L1b's conclusion. So the lemma is at
> least as strong as the whole wall. **It cannot be a cheap first step toward (B), because it makes
> (B) unnecessary.** All three arcs that recommended it (mg-dbd1 §5.1, mg-dcae §7.2, mg-0ed7 §7.5)
> mis-priced it; none states this implication.
>
> **Worse, in the program's own terms:** mg-8201 explicitly *retired* the requirement
> `E[inv_e] = O(n)` as "structurally unnecessary" and built the (A)+(B) certificate route precisely
> to tolerate `E[inv_e] = Θ(n²)`. The recommended "cheap" lemma silently re-imposes that retired
> requirement, in a strictly stronger per-element form.
>
> **The same re-pricing applies one level up, and this is the bigger finding (Theorem 3.3).**
> **(B) itself implies LIB.** By the lower half of Diaconis–Graham and Cauchy–Schwarz,
> `E[inv_e] ≤ E[Σ_x|disp|] ≤ √(n·E[Σ_x disp²])`, so (B) with constant `C` forces
> `E[inv_e] ≤ Cn`. Four corrections follow: **`STATE.md`'s "the two faces are logically independent"
> is false in one direction** ((B) is the stronger face); **mg-dbd1 §2.1's "(B) is weaker than LIB"
> is REFUTED**; the advertised regime of the (A)+(B) route — *"tolerating quadratic `E[inv_e]`"* —
> is **empty**, so the stated reason for abandoning LIB does not hold; and given (B), the wall
> follows from the mg-210d master bound alone, with **(A) SPREAD and `Λ = O(1)` both off the critical
> path**. Net (Finding 3.4): **LIB is the weakest _of the three_ sufficient conditions on the table
> and alone suffices; both objects the (A)+(B) route has attacked since mg-8201 — (B), and the
> locality lemma offered as a step toward it — are strictly-at-least-as-strong surrogates for it.**
> And LIB is not the floor even among those three — `STATE.md`'s stated conclusion `λ_std → 1`
> needs only **(LIB-weak)** `E[inv_e] = o(n²)`, which no arc has ever attacked. Whether the program
> needs the limit or a rate is a scoping question I flag for pm-onethird rather than settle (§3.4).
>
> *(Both quantifiers narrowed 2026-07-31, mg-fccb, per the mg-d112 audit §4.1 — see §13. The
> unrestricted forms said more than §3.4 proves.)*
>
> **AMBER.** The mis-pricing is **one identifiable lossy step**, and removing it yields a strictly
> weaker replacement that does the same job. Both mg-dbd1 §2.3 and mg-dcae §5.4 bound the per-element
> **bias** `b_x := |E[pos_σ(x)] − rank_e(x)|` by the per-element **inversion mass** `m_x`, and only
> *then* take the max. `b_x` is a **signed** sum of the same inversion probabilities and `m_x` is
> their **unsigned** sum; the discarded cancellation is exactly what makes the max-form as strong as
> the wall. Taking the max on `b_x` instead gives
>
> > **(EQ) — expected-rank equidistribution.** `max_x |E[pos_σ(x)] − rank_e(x)| = O(1)`.
>
> (EQ) closes **(B-bias)** by the same one-line argument (Theorem 5.1, and *unconditionally* — the
> frozen hypothesis is not needed for that step), additionally closes mg-dbd1 §3.4's auxiliary
> `Λ = O(1)` gap (Theorem 5.3), and is **provably strictly weaker** than the locality lemma
> (Theorem 6.2: an explicit witness satisfies (EQ) with constant `1` while `max_x m_x = Θ(n)`). It is
> also exactly the negation, *at every element*, of mg-dbd1 §3.1's named (B)-falsifier — which
> mg-dbd1 stated only at the `e`-minimal element.
>
> **Named residuals for the next tickets, in priority order:** (i) the *routing* question of §3.4 —
> pin whether the program consumes `λ_std → 1` or the rate `1 − λ_std ≤ C/(γn)`, since that decides
> whether the live target is (LIB-weak) or LIB. It is a read of the merged record, not new
> mathematics. (ii) prove **(EQ)** under freezing — elementary, Stanley-free, AF-free (genuinely so
> this time) and, unlike the locality lemma, not known to imply LIB.

**What this does and does not kill.** *No mathematics is refuted.* Every `[PROVEN]` claim this
document touches stays true: Prop. 5.4 is a correct implication (its hypothesis is over-strong);
(A) SPREAD is a genuine unconditional theorem (it is merely off one critical path); (B) remains
sufficient for the wall. What is refuted is **pricing and framing** — three claims about the
*relative strength* of statements (§3.3 corrections 1–3) and one about which machinery is needed
(correction 4). It does **not** touch **(B-cov)**, **(R)** (mg-210d's frozen-density ceiling), or the
blocked n=7 overlap test; of the three routes converging on the crux it closes none and reopens none.
Net: the side-door two arcs recommended is removed, the program's target *ordering* is corrected, and
two smaller doors in the same wall are handed back.

---

## 1. Pinning the target statement (before any proof attempt)

The ticket requires the target to be restated from source and each of three ambiguities resolved
explicitly. Doing that first, as required.

### 1.1 Sources, verbatim

- **`STATE.md` (onethird_program @400f474), attempt-index row mg-dcae:**
  *"`(B-bias)` is a new obligation with a clean first lemma (**Prop 5.4:** `max_x Σ_{y∥x} Pr[{x,y} inverts] = O(1)` — no Stanley/AF input)"*, and in the narrative: *"the concrete target is no longer 'build a stability tool' but: prove (B-bias) — `max_x Σ_{y∥x} Pr[{x,y} inverts] = O(1)` (Prop 5.4, no Stanley input)."*
- **mg-dcae, `OneThird-k1-Stanley-Stability-Scoping.md` §7.2 item 2**, the primary source:
  *"under (H), `max_x Σ_{y ∥ x} Pr[{x,y} inverts against e] = O(1)`."*
- **mg-0ed7, `OneThird-MaShenfeld-NearSandwich-Stability.md` §7.5**, the different statement `(LOC)`:
  `Λ = Σ_{z∥x} Pr[y⁻ <_σ z <_σ y⁺] = O(1)`.
- **mg-dbd1, `OneThird-L1b-Spread-Locality.md` §5, recommendation 1:** *"show `max_x m_x = O(1)` under frozen width-3."*

### 1.2 Is there a disagreement between STATE.md and mg-0ed7? — **No.**

The ticket instructs me to stop and report if STATE.md and mg-0ed7's residual disagree on the
target. **They do not disagree; STATE.md has already adjudicated, and mg-0ed7 concedes the point in
its own text.**

- mg-0ed7 §7.5 claims `(LOC)` is *"up to notation"* mg-dcae's lemma, and calls this a convergence of
  two routes on one statement.
- mg-0ed7's *own* "Honest caveat on the reduction" (§7.5, immediately following) says: *"I did not
  prove the equivalence and label it [HEURISTIC] in §8"*, and its §8 status table records the row
  `(LOC) ⟺ mg-dcae's max_x Σ_{y∥x} Pr[inverts] = O(1)` as **HEURISTIC**.
- `STATE.md` records the same, as a correction: *"same-shape but counts different events … they
  coincide only under (H), up to constants. So the two routes land on two **analogous** `O(1)`
  locality lemmas, **not one proven-identical lemma**."*

So the record is consistent: **two analogous statements, equivalence unproven.** The ticket's title
("sum over `y` incomparable to `x` of `Pr[pair inverts]`") names the **(B-bias)** form unambiguously.
That is the target of this document. `(LOC)` is *not* attacked here, and nothing below should be read
as a statement about it. (Note also that `(LOC)`'s consumer, mg-0ed7 Finding 7.5, is independently
**REFUTED** by mg-8f56 for an inequality-direction error, so `(LOC)` currently has no live consumer
anyway. §8.4 records a second, independent defect in the same chain.)

### 1.3 Control or equality? — **Control.**

The deliverable is an **upper bound by an absolute constant**: there exists `C < ∞`, independent of
`n` and of `P`, with `max_x m_x ≤ C` for every `P` in the frozen class. Not an asymptotic, not a
sharp constant, not a two-sided estimate. All results below are stated in that currency. Where a
constant is available it is reported (Theorem 3.2 tracks `C` explicitly, because the re-pricing is
quantitative: the constant propagates to the `λ_std` rate).

### 1.4 Which measure, and which chain? — **The static stationary marginal. Uniform on `L(P)`.**

`σ` is uniform on `L(P)`, the linear extensions of `P`; `Pr` and `E` are with respect to that
measure. `m_{xy} := Pr_σ[{x,y} appears opposite to `e`]`. This is the **static** object — a
functional of the stationary measure — and **not** the BK adjacent-transposition chain's dynamical
generator gap `λ₂^BK`. Three reasons this is the right and only reading, all from the merged record:

1. **Source definitions.** mg-dbd1 §0 fixes `σ` uniform on `L(P)`; mg-dcae §5.2 writes
   `p_{yx} := Pr[y ≺_σ x]` in that same measure. There is no chain in either statement.
2. **`λ₂^BK ≠ λ_std` in general** (mg-4a86, audit-corrected): the dynamical and static objects are
   not interchangeable, so the reading must be pinned rather than left implicit.
3. **The obstruction is provably not dynamical.** Leake–Lindberg–Oveis Gharan 2025
   (arXiv:2503.01005) gives poly mixing for linear extensions of *every* poset, so mixing is
   universal and blind to `δ`; the `δ` obstruction lives purely in the stationary marginal
   (`STATE.md`, 2026-07-19 reference note). A dynamical reading of the target would therefore be
   attacking an object that provably cannot carry the obstruction.

**Every probability in this document is `Pr_σ` with `σ` uniform on `L(P)`. No dynamical object
appears anywhere below.**

### 1.5 What does "under freezing" quantify over? — **The whole poset, every pair, one distinguished order.**

**Hypothesis (H) (verbatim in force, from mg-dbd1 §0).** There is a linear extension `e` of `P` such
that every **incomparable** pair `{x,y}` with `x <_e y` has `Pr[x <_σ y] > 2/3`; equivalently
`δ(P) < 1/3`, the `>2/3`-orientation being acyclic and realized by `e`. Existence of `e` is not an
assumption but a theorem (the 3-cycle anchor, `STATE.md` "Why 1/3"; re-derived independently in
mg-210d).

So: **(H) is a hypothesis on the whole poset**, quantifying over *all* incomparable pairs, not on the
pair `{x,y}` or on the element `x`. The required bound is **uniform in `x`, in `n`, and in `P`** over
the class of posets satisfying (H). It is *not* enough to prove it for the specific freezing "the
crux needs": the crux needs it for an arbitrary minimal counterexample, of which we know only (H).

### 1.6 A consequence of the pinning that constrains the possible outcomes

Under (H), if `P` has any incomparable pair at all, then `P` is a counterexample to the 1/3–2/3
conjecture. Hence:

> **Observation 1.1 [PROVEN, conditional on the 1/3–2/3 conjecture].** If the conjecture is true, the
> frozen class contains only chains, on which `m_x = 0` for every `x`, so the locality lemma holds
> vacuously with `C = 0`.

This is not a joke; it fixes the outcome space and it is why the ticket's three outcome labels need
care:

- **RED-by-counterexample is unavailable.** Exhibiting a frozen poset with `max_x m_x` large would
  refute the conjecture outright. Nobody is going to reach that by accident on this ticket.
- **GREEN-by-verification is unavailable.** No computation can support the lemma: every frozen poset
  is a chain if the conjecture holds, and none is known regardless (mg-dbd1 §4: 20 000 dense width-3
  trials at `n ≤ 9` produced **zero** posets with `δ < 1/3`). mg-0ed7 flags the same about its
  Thm 6.1: frozen-conditional ⟹ untestable.
- **Class-restricted proofs carry no information.** On any class where the conjecture is *known*
  (width ≤ 2, by Linial and Sah), the lemma is vacuously true, and proving it there tells us nothing
  about the frozen class.

**Therefore the only informative outcomes are a structural proof or a structural barrier**, and a
"barrier" here means a *relative* statement — the lemma implies something already known to be hard.
That is exactly what §3 delivers, and it is why the RED in §0 is a re-pricing rather than a
refutation.

---

## 2. Notation and the standing facts used (all cited, none re-derived except where marked)

`P` a finite poset on `n` elements, `e` the distinguished linear extension of (H), `σ` uniform on
`L(P)`. Positions are 0-indexed: `pos_σ(x) = #{z : z <_σ x}`, `rank_e(x) = #{z : z <_e x}`.

| symbol | definition |
|---|---|
| `x ∥ y` | `x, y` incomparable in `P` |
| `m_{xy}` | `Pr_σ[{x,y} ordered opposite to e]` (`= 0` for comparable pairs, since `e` extends `P`) |
| `m_x` | `Σ_{y ∥ x} m_{xy}` — the **per-element inversion mass** (mg-dbd1's "inversion degree"; mg-dcae's `M_x`) |
| `h(x)` | `E[pos_σ(x)]` |
| `b_x` | `\|h(x) − rank_e(x)\|` — the **per-element bias** |
| `E[inv_e]` | `Σ_{{x,y}, x ∥ y} m_{xy}` |
| `disp_σ(x)` | `pos_σ(x) − rank_e(x)` |

**Standing facts imported (not re-derived):**

- **(F1)** `Σ_x m_x = 2 E[inv_e]`. *(mg-dbd1 §2.3 line 176; mg-dcae §5.4. Immediate: each incomparable pair is counted at both of its endpoints.)*
- **(F2) Master bound (mg-210d Thm 2.4, `[proven]` there, proof re-read this session):*
  `1 − λ_std ≤ 3E[F]/(n²−1) ≤ 6E[inv]/(n²−1)`, `F` the Spearman footrule. Sharp: equality at the
  antichain.
- **(F3)** `λ_std = 1 ⟺ P` is an ordinal sum. *(`STATE.md` ledger row 1.)*
- **(F4)** LIB, as the program states it: `E[inv_e] = O(n/γ)`, and (mg-7ae7, via
  `OneThird-LIB-Correlation-Inequality-Scoping.md` §0) the whole transport transfer is
  **equivalent** to it: the target `1 − λ_std ≤ C/(γn)` holds **iff** `E[inv_e] = O(n/γ)`.
- **(F5)** mg-8201's retirement of LIB: *"the prefix/LIB route's linear-inversions requirement is
  lossy in the sense that matters — unnecessary — because the expected-rank certificate certifies
  `λ_std` directly and tolerates quadratic `E[inv_e]`."*
  (`OneThird-L1b-ExpectedRank-Certificate.md` §2, step-1 conclusion.)

---

## 3. The re-pricing theorem — the locality lemma implies the wall

### 3.1 The exact local identity

> **Identity 3.1 [PROVEN, new to the corpus as an identity, elementary].** For every `x`,
> `m_x = E[ |σ_{<x} Δ D_x| ]`, where `σ_{<x} = {z : z <_σ x}`, `D_x = {z : z <_e x}` is the `e`-prefix
> at `x`, and `Δ` is symmetric difference.

*Proof.* Take `z ∈ D_x ∖ σ_{<x}`: then `z <_e x` and `x <_σ z`. `z` cannot satisfy `z <_P x` (that
would force `z <_σ x`) nor `x <_P z` (that would force `x <_e z`), so `z ∥ x`, and `{x,z}` is
inverted. Symmetrically `z ∈ σ_{<x} ∖ D_x` gives `x <_e z`, `z <_σ x`, `z ∥ x`, inverted. Conversely
every inverted partner of `x` lies in exactly one of the two differences. Hence
`|σ_{<x} Δ D_x| = #{y ∥ x : {x,y} inverted}`, whose expectation is `Σ_{y∥x} m_{xy} = m_x`. ∎

So `m_x` is the **expected interface leak of the `e`-prefix cut taken through `x`**, and the locality
lemma reads: *every one of the `n` prefix cuts of `e` leaks `O(1)` simultaneously.* That is a far
stronger statement than the interface-thinness `Δ₁ → 0` of `STATE.md`'s Axis 1, which permits a leak
of `o(n)` per cut.

### 3.2 The implication

> **Theorem 3.2 (re-pricing) [PROVEN, elementary, one line].** Suppose `max_x m_x ≤ C`. Then
> 1. `E[inv_e] ≤ Cn/2`;
> 2. `1 − λ_std ≤ 6·(Cn/2)/(n²−1) = 3Cn/(n²−1) = O(1/n) → 0`, i.e. `λ_std → 1`.
>
> *In particular the locality lemma implies LIB with a `γ`-free constant — hence LIB in a form
> strictly stronger than the `O(n/γ)` the program asks for — and hence L1b's conclusion.*

*Proof.* (1) is (F1): `2E[inv_e] = Σ_x m_x ≤ Cn`. (2) is (F2) applied to (1). ∎

**That is the whole content of the RED.** The proof is three symbols long, which is precisely why it
is worth writing down: the statement recommended by three separate arcs as the elementary first step
*below* the wall implies the wall, and the derivation is short enough that its absence from all three
documents is a pricing oversight rather than a mathematical subtlety.

### 3.3 The same phenomenon, one level up: **(B) itself implies LIB**

The locality lemma is not an anomaly. The identical re-pricing applies to **(B)**, the program's
chosen face of the wall — and this is the more consequential finding of the two.

> **Theorem 3.3 [PROVEN, new, elementary, unconditional].** For any finite poset `P`, any linear
> extension `e`, and `σ` uniform on `L(P)`:
> $$E[\mathrm{inv}_e] \;\le\; E\Big[\sum_x |\mathrm{disp}_σ(x)|\Big] \;\le\; \sqrt{\,n\cdot E\Big[\sum_x \mathrm{disp}_σ(x)^2\Big]\,}.$$
> **Consequently, if (B) holds with constant `C` — i.e. `E[Σ_x disp²] ≤ C·E[inv_e]` — then**
> $$E[\mathrm{inv}_e] \;\le\; C\,n .$$

*Proof.* The first inequality is the **lower** half of Diaconis–Graham, `I(σ) ≤ D(σ)` pointwise
(quoted in mg-dbd1 §2.1 as `I(σ) ≤ D(σ) ≤ 2I(σ)`), applied to the permutation `rank_e ↦ pos_σ`;
comparable pairs never invert, so its inversion count *is* `inv_e(σ)`. The second is Cauchy–Schwarz
`(Σ_x|d_x|)² ≤ n Σ_x d_x²` pointwise, followed by Jensen `E[√X] ≤ √(E[X])`. Now substitute
(B): `E[inv_e] ≤ √(n·C·E[inv_e])`, so `E[inv_e]² ≤ Cn·E[inv_e]`, so `E[inv_e] ≤ Cn`. ∎

*Numerical sanity check on the `n`-antichain (by hand, both sides in closed form).* `σ` uniform on
`S_n`; `E[Σ|disp|] = (n²−1)/3` and `E[Σ disp²] = n(n²−1)/6`, so the middle and right terms are
`≈ 0.333n²` and `√(n·n³/6) ≈ 0.408n²` — the inequality holds, and not by much, so it is not
slack enough to be hiding a sign error. `E[inv] = C(n,2)/2 ≈ 0.25n²` ✓.

**Four corrections to merged work follow immediately.** Each is stated against verbatim source text.

1. **`STATE.md` line 102 — "The two faces are logically independent; either alone suffices" — is
   false in one direction.** `(B) ⟹ LIB`. Either alone does suffice (that part is right), but they
   are ordered, not independent: **(B) is the stronger face.**
2. **mg-dbd1 §2.1's "(B) is weaker than LIB" is REFUTED.** Verbatim: *"This is the precise sense in
   which (B) is 'weaker than LIB but still substantive': LIB demanded `E[inv_e] = O(n)` (the
   conclusion); (B) demands only that squared displacement be linearly controlled by inversions."*
   By Theorem 3.3, (B) demands `E[inv_e] = O(n)` **too** — it just does not say so on its face. The
   `L1`-vs-`L2` framing is correct; the strength comparison drawn from it is backwards.
3. **The "tolerates quadratic `E[inv_e]`" claim is vacuous.** mg-dbd1 §0/§5 and mg-8201 §2 (F5) both
   sell the (A)+(B) certificate on tolerating `E[inv_e] = Θ(n²)` — mg-dbd1 §5 verbatim: *"with no
   thin prefix and tolerating quadratic `E[inv_e]`"*. The implication is formally valid but its
   advertised regime is **empty**: (B) is never satisfiable when `E[inv_e] = ω(n)`. So the stated
   reason for abandoning LIB in favour of (A)+(B) does not hold.
4. **Given (B), the certificate machinery is not needed at all.** (B) `⟹` LIB `⟹` (F2)
   `1 − λ_std ≤ 6Cn/(n²−1) = O(1/n)` — the same conclusion the certificate reaches, **without (A)
   SPREAD and without `Λ = O(1)`**. Both remain true and (A) remains a genuine unconditional theorem
   of mg-dbd1; they are simply off the critical path from (B) to the wall. *(This is not a criticism
   of mg-dbd1: the master bound (F2) is mg-210d, 2026-07-19, and postdates the certificate. It is a
   later tool obsoleting earlier machinery, which is worth recording precisely so the machinery is
   not re-invoked.)*

### 3.4 The resulting strength ladder, and the weakest sufficient condition

Everything above assembles into one ordering. Write `⟹` for proven implication:

```
  locality (max_x m_x = O(1))   ⟹  LIB (E[inv_e] = O(n))   ⟹  λ_std → 1        [Thm 3.2, F2]
  (B)     (E[Σdisp²] = O(E[inv]))⟹  LIB                    ⟹  λ_std → 1        [Thm 3.3, F2]
  LIB is implied by both, and none of the reverse implications is known.
```

`Σ_x m_x = 2E[inv_e]` says LIB is the **average** statement `avg_x m_x = O(1)` while the locality
lemma is the **max** statement (§6.1 confirms the gap is a genuine factor `n`). So:

> **Finding 3.4 [PROVEN, given Thms 3.2/3.3 and (F2)].** **LIB is the weakest of the three
> sufficient conditions the program has on the table, and it alone suffices. Both objects the program
> has attacked since mg-8201 — (B), and the locality lemma offered as a step toward it — are
> strictly-at-least-as-strong surrogates for it.**

**And LIB itself is not the floor.** (F2) reads `1 − λ_std ≤ 6E[inv_e]/(n²−1)`, so for L1b's
conclusion **exactly as `STATE.md` states it** (`λ_std → 1`, a limit, not a rate) it is enough that

> **(LIB-weak):** `E[inv_e] = o(n²)` under freezing,

which is weaker than LIB by a whole factor of `n`. Under (H) every incomparable pair contributes
`< 1/3`, so `E[inv_e] < C(n,2)/3` automatically — (LIB-weak) asks only that freezing beat that
trivial bound by any factor tending to infinity.

> **Scoping question raised, not resolved [OPEN — for pm-onethird].** `STATE.md` states the wall's
> conclusion as `λ_std → 1`, for which (LIB-weak) suffices; but mg-7ae7 (via the LIB-scoping doc §0)
> states the program's operative target as the **rate** `1 − λ_std ≤ C/(γn)`, for which
> `E[inv_e] = O(n/γ)` is **equivalent**. Those two readings differ by a factor `n` in the inversion
> requirement, and which one L4 and the downstream steps actually consume is not something this
> ticket can settle from the merged record. **If `λ_std → 1` is genuinely what is needed, the live
> target should be (LIB-weak), which no arc on this program has ever attacked.** I flag this rather
> than pick, because picking silently is the failure mode this ticket's brief warns about.

**Against the "convergence" narrative.** mg-0ed7 §7.5 and mg-dcae §7.2 converging on the locality
lemma is real, but what they converged on sits *above* the wall. Convergence of two routes on a
statement is evidence about that statement's centrality, not about its cheapness.

---

## 4. Locating the lossy step exactly

Both prior derivations run the same three moves. mg-dbd1 §2.3:

```
Σ_x E[disp(x)]² ≤ Σ_x m_x² ≤ (max_x m_x)·Σ_x m_x = 2(max_x m_x)·E[inv_e]
```

and mg-dcae §5.4 identically, with `M_x` for `m_x`. Both are correct. The first inequality is where
everything is lost.

> **Identity 4.1 [PROVEN, elementary, and — worth noting — unconditional: (H) is not used].**
> For any poset `P` and any linear extension `e`,
> $$h(x) - rank_e(x) \;=\; \sum_{y ∥ x,\; x <_e y} m_{xy} \;-\; \sum_{y ∥ x,\; y <_e x} m_{xy}.$$

*Proof.* `h(x) = Σ_{y ≠ x} Pr[y <_σ x] = #{y <_P x} + Σ_{y ∥ x} Pr[y <_σ x]`, and
`rank_e(x) = #{y <_P x} + #{y ∥ x : y <_e x}` (comparable `y` sit on the same side in `e` as in
`P`). Subtract. For `y ∥ x` with `x <_e y`, inversion means `y <_σ x`, so `Pr[y <_σ x] = m_{xy}`; for
`y ∥ x` with `y <_e x`, inversion means `x <_σ y`, so `Pr[y <_σ x] − 1 = −m_{xy}`. ∎

*(Remark: mg-dcae §5.4 states this "under (H)". (H) is not needed — only that `e` is a linear
extension. Minor, recorded for the ledger.)*

So `b_x` is the **signed** sum of exactly the quantities whose **unsigned** sum is `m_x`:

$$b_x \;\le\; m_x, \qquad\text{with equality iff all of }x\text{'s inversion mass is on one side of }x\text{ in }e.$$

**The lossy step is `b_x ≤ m_x` applied *before* the max is taken.** Cancellation between the
`e`-above and `e`-below inversion mass at `x` is discarded, and §6 shows that discarded cancellation
is worth a factor of `n`: there are posets with `b_x ≤ 1` for every `x` and `m_x = Θ(n)`.

---

## 5. The redirect: (EQ), and what it buys

> **(EQ) — expected-rank equidistribution.** *Under (H), `max_x |E[pos_σ(x)] − rank_e(x)| = O(1)`.*

### 5.1 (EQ) closes (B-bias), by the same one line

> **Theorem 5.1 [PROVEN, elementary, unconditional].** If `max_x b_x ≤ C₀` then
> `(B-bias) = Σ_x (h(x) − rank_e(x))² ≤ 2C₀·E[inv_e] = O(E[inv_e])`.

*Proof.* `Σ_x b_x² ≤ (max_x b_x)·Σ_x b_x ≤ C₀·Σ_x m_x = 2C₀ E[inv_e]`, using `b_x ≤ m_x` (Identity
4.1) *after* the max, and (F1). ∎

Note it needs no (H): the frozen hypothesis is what one hopes will *prove* (EQ), not what makes (EQ)
sufficient.

### 5.2 (EQ) is exactly the negation of mg-dbd1's named falsifier, at every element

mg-dbd1 §3.1 identifies the (B)-falsifier: with `x` the `e`-minimal element, `B_x = 0`, so
`d_1 := E[A_x] = h(x)` is `x`'s whole displacement, and *"if `d_1 = Θ(n)` while `E[inv_e] = Θ(n)`,
lemma (B) is false"*. At the `e`-minimal element `rank_e(x) = 0` and all inversion mass is on one
side, so `b_x = m_x = d_1`.

> **Observation 5.2 [PROVEN].** At the `e`-extremes, `b_x = m_x`. Hence (EQ) restricted to the
> `e`-minimal element is *precisely* the negation of mg-dbd1 §3.1's bimodal-chain-cross falsifier,
> and (EQ) is that negation extended to every element.

This is the strongest structural argument that (EQ), not the locality lemma, is the right object: the
program's own named falsifier is a statement about `b`, not about `m`, and it becomes a statement
about `m` only at the two elements where the two coincide.

### 5.3 (EQ) also closes the auxiliary `Λ = O(1)` gap

mg-dbd1 §3.4 leaves open, as a separate obligation, that the **sorted** expected-rank vector
`w_1 ≤ … ≤ w_n` has no `ω(1)` consecutive gap (`Λ := max_k (w_{k+1} − w_k) = O(1)`), needed by the
certificate chain.

> **Theorem 5.3 [PROVEN, elementary].** `max_x b_x ≤ C₀` ⟹ `Λ ≤ 2C₀ + 1`.

*Proof.* Index by `e`-rank, so the hypothesis reads `h_k ∈ [k − C₀, k + C₀]` for `k = 0,…,n−1`. Let
`w_0 ≤ ⋯ ≤ w_{n−1}` be the `h_k` sorted, and fix `j`. Counting from above:
`#{k : h_k ≤ j + C₀} ≥ #{k : k + C₀ ≤ j + C₀} = #{k ≤ j} = j+1`, so at least `j+1` of the
values are `≤ j + C₀`, forcing `w_j ≤ j + C₀`. Counting from below:
`#{k : h_k ≥ j − C₀} ≥ #{k : k − C₀ ≥ j − C₀} = #{k ≥ j} = n − j`, so at most `j` values are
`< j − C₀`, forcing `w_j ≥ j − C₀`. Hence `|w_j − j| ≤ C₀`, and
`w_{j+1} − w_j ≤ (j + 1 + C₀) − (j − C₀) = 2C₀ + 1`. ∎

So (EQ) delivers three of the four sub-obligations on the certificate route — (A) SPREAD (already
proven independently, but (EQ) re-derives `‖r‖² = Θ(n³)` immediately), (B-bias), and `Λ = O(1)` —
leaving **(B-cov)** alone as the residual. That is the same residual `STATE.md` already names as the
program's sharp edge, reached without over-shooting.

---

## 6. The separations — (EQ) is strictly weaker than the locality lemma

One explicit witness does all the separating. It is fully hand-computable and I give the micro-checks.

### 6.1 The witness: a chain plus a free point

Let `W_m := C_m ⊔ C_1` — the chain `c_1 <_P ⋯ <_P c_m` together with one element `z` incomparable to
everything. `n = m + 1`. `|L(W_m)| = m + 1`: `z` is inserted into one of `m+1` slots, uniformly.

**Exact quantities (all by hand).** Write `s := ⌊m/2⌋`.

- `Pr[z <_σ c_i] = i/(m+1)` — `z` precedes `c_i` iff its slot is one of the first `i`.
  *(check `m = 1`: LEs `zc₁`, `c₁z`, so `Pr = 1/2 = 1/(1+1)` ✓. check `m = 2`: LEs `zc₁c₂`, `c₁zc₂`, `c₁c₂z`; `Pr[z<c₁] = 1/3` ✓, `Pr[z<c₂] = 2/3` ✓.)*
- **`e`** is the majority order: `c_i <_e z` iff `Pr[z <_σ c_i] < 1/2` iff `i < (m+1)/2`. So
  `rank_e(z) = t := #{i : i < (m+1)/2} = ⌈(m−1)/2⌉`, and `e = c_1 ⋯ c_t z c_{t+1} ⋯ c_m`.
- **`m_{z c_i} = min(i, m+1−i)/(m+1)`**, since `m` is the minority side of `Pr[z <_σ c_i] = i/(m+1)`.
- **`m_z = Σ_{i=1}^m min(i, m+1−i)/(m+1)`.** For `m = 2s` even this is `s(s+1)/(2s+1)`, so
  `m_z = Θ(m) = Θ(n)`. *(check `m = 2`, `s = 1`: `m_z = 1·2/3 = 2/3`; directly `1/3 + 1/3 = 2/3` ✓.)*
- **`E[pos_σ(z)] = m/2`** (slot uniform on `{0,…,m}`), so
  **`b_z = |m/2 − ⌈(m−1)/2⌉| ≤ 1`.** *(check `m = 2`: `E[pos(z)] = (0+1+2)/3 = 1`, `rank_e(z) = 1`, `b_z = 0` ✓.)*
- **`b_{c_i} ≤ 1`:** `E[pos_σ(c_i)] = (i−1) + i/(m+1)`, while `rank_e(c_i) = i−1` for `i ≤ t` and
  `= i` for `i > t`. So `b_{c_i} = i/(m+1) ≤ 1` in the first case and `1 − i/(m+1) ≤ 1` in the second.
- **`E[inv_e] = m_z = Θ(n)`:** by (F1), `2E[inv_e] = Σ_x m_x = m_z + Σ_i m_{z c_i} = 2 m_z`.

> **Theorem 6.2 (separations) [PROVEN, exact, hand-checkable].** For `W_m`:
> `max_x b_x ≤ 1` while `max_x m_x = Θ(n)` and `E[inv_e] = Θ(n)`. Consequently, **as inequalities
> between these quantities over all posets:**
> 1. **(EQ) does not imply the locality lemma** — the gap is a factor `Θ(n)`;
> 2. **LIB does not imply the locality lemma** — `W_m` satisfies `E[inv_e] = O(n)` with `max_x m_x = Θ(n)`, so the max-form is strictly stronger than the average-form (§3.3 confirmed);
> 3. **(EQ) does not re-price into the wall the way the locality lemma and (B) do** — the derivations
>    of Theorems 3.2 and 3.3 both fail on (EQ): `W_m` satisfies (EQ) with constant `1` while
>    `E[inv_e] = Θ(n)` is *forced by nothing about (EQ)*, and (EQ) supplies no bound on `E[Σdisp²]`
>    (on `W_m`, `Σ_x E[disp²] = Θ(n²)` with `max_x b_x ≤ 1`). Stated as an absence, not a theorem —
>    see §9's caveat.

**The caveat, stated plainly.** `W_m` has `δ = 1/2` (the pair `{z, c_t}` is nearly balanced): it is
maximally *un*frozen, as any explicit poset must be (Observation 1.1). So Theorem 6.2 separates the
statements **as inequalities between the quantities**, not as *frozen-conditional* statements — the
frozen-conditional versions of all of these are, conditional on the 1/3–2/3 conjecture, vacuously
true and therefore equivalent. **What Theorem 6.2 rules out is a proof of the locality lemma that
goes through (EQ) or through LIB by a general argument** — no such derivation exists, because the
implications fail at the level of the quantities. That is the operative content, and it is exactly
what is needed: it establishes that (EQ) is a genuinely smaller target, not a restatement.

**Second reading of the same witness — where (B) actually fails on it.** `Var(pos_σ(z)) = m(m+2)/12 = Θ(n²)`
while `E[inv_e] = Θ(n)`, so `W_m` violates (B) by a factor `Θ(n)` — and it does so entirely in the
**variance / (B-cov)** term, with `(B-bias) = Σ_x b_x² ≤ n = O(E[inv_e])` perfectly healthy. The
witness therefore also illustrates, concretely, that (B-bias) is the easy half and (B-cov) is where
(B) dies — corroborating `STATE.md`'s location of the crux from a completely elementary direction.

### 6.3 A second witness, for the record

`C_p ⊕ A_k ⊕ C_p` (two chains with an antichain of size `k` between them), `k = ⌊√n⌋`: every antichain
pair is balanced, so `m_x = (k−1)/2 = Θ(√n)` for `x` in the antichain, and
`E[inv_e] = C(k,2)/2 = Θ(n)`. This separates LIB from the locality lemma as well, but *not*
(EQ) from it — here `b_x = |(k−1)/2 − (i−1)|` is also `Θ(√n)`, so (EQ) fails too. Recorded because the
contrast is informative: it is the **cancellation**, not the mere presence of a large incomparable
set, that distinguishes the two hypotheses. `W_m` has cancellation; the antichain block does not.

---

## 7. The local structure of the locality lemma (what a proof would have to produce)

These are the sharpest necessary conditions I can extract by hand. They are recorded because they
describe the shape of any future proof, and because two of them are tight on `W_m`.

### 7.1 Conditional uniformity and the insertion window

Fix `x`, and let `τ := σ|_{P∖{x}}`. The map `σ ↦ (τ, slot)` is a bijection from `L(P)` onto pairs
where `slot` ranges over the valid insertion positions of `x` into `τ`; those form a **contiguous**
interval `I_x(τ)` (from just after the last element of `D_P(x) = {z : z <_P x}` in `τ`, to just
before the first element of `U_P(x)`; contiguous because `τ` places all of `D_P(x)` before all of
`U_P(x)`). Uniformity on `L(P)` therefore makes `slot` **uniform on `I_x(τ)` conditional on `τ`**.
*(This is the conditional-uniformity insertion law of mg-a1ec, used here in its elementary form.)*
Write `W_x(τ) := |I_x(τ)| ≥ 1`. Every element strictly inside the window is incomparable to `x` (an
element of `D_P(x)` or `U_P(x)` cannot sit there).

> **Lemma 7.1 (window lower bound) [PROVEN, elementary, new].**
> `E[ N_x | τ ] ≥ Σ_{i=1}^{W−1} min(i, W−i)/W ≥ (W−1)/4`,  where `W := W_x(τ)` and `N_x` = the number of `x`-inversions.
> Hence **the locality lemma implies `E[W_x] ≤ 4C + 1` for every `x`**: every element's insertion
> window has bounded expected length.

*Proof.* Let `w_1, …, w_{W−1}` be the in-window elements in `τ`-order, `W = W_x(τ)`. If `x` takes slot
`j` (uniform on `{0,…,W−1}`), then `w_i` is inverted with `x` iff (`i ≤ j` and `x <_e w_i`) or
(`i > j` and `w_i <_e x`). So `w_i` contributes `Pr[j ≥ i] = (W−i)/W` in the first case and
`Pr[j < i] = i/W` in the second; either way at least `min(i, W−i)/W`. Out-of-window inversions only
add. For the final bound: `Σ_{i=1}^{W−1} min(i, W−i)` equals `m²` when `W = 2m` and `m(m+1)` when
`W = 2m+1`. In the first case `m² ≥ m(2m−1)/2 = W(W−1)/4`; in the second
`m(m+1) ≥ m(2m+1)/2 = W(W−1)/4`. Dividing by `W` gives `≥ (W−1)/4`. ∎

**Tightness.** On `W_m` at `x = z`: `D_P(z) = U_P(z) = ∅`, so `W_z ≡ m+1` and there are no
out-of-window inversions; and since `e` places `z` in the middle of the `c_i`, the bound's summand
`min(i, W−i)/W` is *exactly* `m_{z c_i}`. Lemma 7.1 holds **with equality**. That the bound is
attained by the canonical witness is a strong check on both.

### 7.2 The out-of-window transfer

> **Lemma 7.2 (transfer) [PROVEN, elementary, new].** Pointwise in `σ`, with `τ = σ|_{P∖{x}}`,
> `z⁻` the `τ`-last element of `D_P(x)` and `z⁺` the `τ`-first element of `U_P(x)` (terms omitted
> when the sets are empty),
> $$N_x(σ) \;\le\; \big(W_x(τ) - 1\big) \;+\; N_{z⁻}(σ) \;+\; N_{z⁺}(σ),$$
> where `N_u(σ)` is the number of `u`-inversions.

*Proof.* In-window inversions number at most `W_x(τ) − 1`. Let `y` be an out-of-window inversion on
the low side: `y ∥ x`, `y <_σ x`, `x <_e y`, and `y` before the window, i.e. `y <_τ z⁻`. Then
`z⁻ <_P x <_e y` gives `z⁻ <_e y`, while `y <_σ z⁻` — so `{y, z⁻}` is inverted, and `y ↦ y` injects
the low-side out-of-window inversions of `x` into the inversions of `z⁻`. The high side is
symmetric. ∎

**What this does and does not give.** It says the locality lemma splits into a *window* part and a
*boundary transfer* part, and that the transfer only ever moves mass to the two `P`-neighbours of `x`
along `τ`. It does **not** close anything: taking expectations and maxima gives
`max_x m_x ≤ E[W]−1 + 2max_x m_x`, which is vacuous. Recorded as structure, not as progress.

### 7.3 The window condition is necessary but **not** sufficient

`W_m` again: at `x = z`, `E[W_z] = m+1` is large, consistent with `m_z` large. But consider two
disjoint chains `C_m ⊔ C_m`: there `E[W_{a_i}] = O(1)` (the expected number of `b`'s that `τ` places
between two consecutive `a`'s is `O(1)`) while `m_{a_i} = E|K_i − (i−1)| = Θ(√m)`, where `K_i` is the
number of `b`'s preceding `a_i` — all of that mass being **out-of-window** and routed by Lemma 7.2.
So bounded expected windows is a strictly weaker condition, and a proof cannot stop there.

*(The `Θ(√m)` is the standard order-statistic deviation of `K_i` for a uniform interleaving and is
quoted here only as an order of magnitude in a remark that carries no load — the necessary-not-
sufficient point already follows from `m_{a_i} = E|K_i − (i−1)| > 0` being unbounded, which the
identity `m_{a_i} = E|K_i − (i−1)|` makes evident. Labelled **[HEURISTIC]** as to the exact rate.)*

> **⚠️ ANNOTATION (2026-07-29, mg-1fdb) — the parenthetical above overstates.** `m_{a_i} > 0` gives
> **positivity, not unboundedness**, and the insufficiency claim needs unboundedness. The only ground
> for unboundedness on offer is the `Θ(√m)` rate, which is labelled **[HEURISTIC]** — so contrary to
> the parenthetical, the rate *does* carry load here. The §10 ledger row for §7.3 is downgraded from
> **PROVEN** to **PLAUSIBLE** on the insufficiency claim accordingly (mg-d112 audit §3.1).
> **Consequence: nil.** §7.3 is a structural remark in a section flagged "recorded as structure, not
> as progress"; nothing in §0, §3, §5 or §6 depends on it. Done for the ledger's accuracy.

---

## 8. Obstructions — why the elementary marginal tools are inert on this target

### 8.1 The two-atom law (re-derivation in the locality coordinate)

Let `μ` put mass `1−ε` on `e` and `ε` on the reverse of `e`. Every pair inverts with probability
exactly `ε`, so every pair is frozen for `ε < 1/3`, and `m_x = ε(n−1) → ∞`. So **the locality lemma
is false for abstract frozen laws**, and any proof must use that `σ` ranges over a real poset's
linear extensions. *(This is `STATE.md`'s obstruction 4 and mg-7ae7's witness, re-derived here in the
`m_x` coordinate; no novelty claimed.)*

### 8.2 The 3-element inequalities are inert

The only universal constraints available from pairwise marginals of an order-valued random variable
are the 3-element inequalities `Pr[u<v] + Pr[v<w] + Pr[w<u] ≤ 2`. For `x <_e y <_e z` these reduce to
exactly one non-trivial statement:

> **Observation 8.1 [PROVEN, elementary].** For `x <_e y <_e z`: `m_{xz} ≤ m_{xy} + m_{yz}`, and the
> reverse cyclic instance is vacuous. (Substitute `Pr[x<_σ y] = 1 − m_{xy}` etc.)

This is the subadditivity of balances that probe A (mg-61bb) already identified. It is a system of
**upper** bounds satisfied by the constant assignment `m ≡ ε`, which is the §8.1 witness. So the full
3-element system, together with `δ < 1/3`, is consistent with `m_x = Θ(n)`:

> **Corollary 8.2 [PROVEN].** No argument using only the pairwise inversion marginals and the
> 3-element inequalities can prove the locality lemma. Moreover subadditivity is **wrong-signed** for
> the natural attack: it bounds far-pair inversion mass *above* by sums of near-pair mass, which
> permits `m_{xy}` to stay bounded away from `0` at all distances, rather than forcing decay.

### 8.3 The decay reformulation, and why it does not help by itself

Since `rank_e` is a bijection onto `{0,…,n−1}`, at most **two** elements sit at each `e`-distance
`d` from `x`. Hence

> **Observation 8.3 [PROVEN, elementary].** `m_x ≤ 2 Σ_{d ≥ 1} m̄_d(x)`, where `m̄_d(x)` is
> the larger of the (at most two) inversion probabilities at `e`-distance `d`. So the locality lemma
> **is** the statement that inversion probabilities are *summable* in `e`-distance, uniformly.

This is the per-element form of what the LIB scoping arc already established for the sum
(`OneThird-LIB-Correlation-Inequality-Scoping.md` Fact B: *"LIB ⟺ geometric decay of the
backward-probability matrix along chains"*). It is a restatement, not a tool — and by §8.2 the
elementary system cannot deliver the decay. FKG/XYZ push the wrong way (positive correlation ⟹
*slower* decay), which that arc already scored RED.

### 8.4 A second, independent defect in mg-0ed7's Finding 7.5 chain

*(Recorded for the cross-doc ledger; it does not affect anything above.)* mg-8f56 refuted Finding 7.5
via the between-window variance term. Independently, the *within*-window half needed a **second**
moment: conditional on `τ`, `pos_σ(x)` is uniform on the window (§7.1), so
`Var(pos_σ(x) | τ) = (W_x(τ)² − 1)/12`, and controlling `E[Var(· | τ)]` requires `E[W_x²]`,
which no first-moment locality bound supplies (`E[W²] ≥ (E[W])²` is the wrong direction). So even a
valid `Φ`-to-within-window-variance step would have needed a hypothesis strictly stronger than any
`O(1)` locality bound. **[PROVEN as stated; labelled as an observation about what the chain would
have required, not as an additional refutation — Finding 7.5 is already refuted.]**

---

## 9. Verdict, routing, and the next ticket

**Verdict: RED for the lever as briefed, AMBER redirect.** Restated against the ticket's three
outcome definitions:

- Not **GREEN**: the lemma is not proven, and §1.6 shows it cannot be verified.
- Not **RED-by-falsity**: the lemma is not false; conditional on the conjecture it is vacuously true.
- **RED-by-walling**, in the ticket's second sense: the route is walled, because the target sits
  *above* the wall it was supposed to undercut (Theorem 3.2). The brief's premise — *"the elementary
  reserve route at that wall … needs no Stanley and no AF, which is exactly what makes it worth
  swinging at"* — is correct about the tools and wrong about the difficulty. Being Stanley-free and
  AF-free does not make a statement weaker than L1b; this one is stronger.
- **AMBER** on the redirect: (EQ) is named precisely, is proven to do (B-bias)'s job and `Λ`'s job,
  and is proven strictly weaker than the walled target.

**Which of the three routes to the crux does this kill?** *None of the three.* The three routes
(mg-0ed7 Stanley-stability, mg-dcae variance/covariance, mg-8f56 spectral implications) converge on
**(B-cov)** / `ρ_s ≈ 1` / the between-window location term, and this document does not touch that
object. What it kills is the **side-door** two of them recommended:

- **mg-dcae §7.2 recommendation 2** ("the recommended first lemma") — the recommendation is
  withdrawn; Prop. 5.4 itself stands as a correct implication.
- **mg-0ed7 §7.5's forward recommendation** — the convergence claim was already `[HEURISTIC]` and
  its consumer already REFUTED; this adds that the converged-upon statement is wall-strength.
- **mg-dbd1 §5 recommendation 1** (same statement, earliest occurrence) — same.

**What it does change about the program's routing** (Theorem 3.3, §3.3–3.4): the (A)+(B) certificate
route's advertised advantage over LIB is empty, so the *ordering of targets* is wrong. This does not
kill (B) — (B) remains sufficient — but it removes the reason to prefer it over LIB, and it takes
(A) SPREAD and `Λ = O(1)` off the critical path from (B) to the wall.

**The next tickets, stated so they can be attacked directly.** Two, in priority order.

**(i) The routing ticket — cheap, and it comes first.** Pin whether L4 and the downstream steps
consume `λ_std → 1` (a limit) or `1 − λ_std ≤ C/(γn)` (a rate). This is a read of the merged record,
not new mathematics, and it decides whether the live target is **(LIB-weak)** `E[inv_e] = o(n²)` or
**LIB** `E[inv_e] = O(n/γ)`. If it is the limit, (LIB-weak) is by a wide margin the weakest open
statement on this program and has never been attacked.

**(ii) The mathematical ticket:**

> **(EQ).** *Let `P` satisfy (H) with distinguished order `e`, `σ` uniform on `L(P)`. Show there is
> an absolute constant `C₀` with*
> $$\max_x \Big| E[pos_σ(x)] - rank_e(x) \Big| \;\le\; C₀ ,$$
> *equivalently (Identity 4.1)* `max_x | Σ_{y ∥ x, x <_e y} m_{xy} − Σ_{y ∥ x, y <_e x} m_{xy} | ≤ C₀`
> *— the `e`-above and `e`-below inversion masses at every element cancel to within `O(1)`.*

Why it is a better target than the one it replaces: it is strictly weaker (Theorem 6.2); it closes
(B-bias) and `Λ = O(1)` (Theorems 5.1, 5.3); it is the exact negation of the program's own named
falsifier at every element (Observation 5.2); it is not known to imply LIB, so it does not
self-evidently re-price into the wall; and it is a **cancellation/equidistribution** statement rather
than a decay statement, which puts it outside the family §8.2 proves inert. *(Honest caveat: I have
**not** proven that (EQ) fails to imply the wall — `W_m` does not separate them, since `W_m` also has
`λ_std → 1`. "Not known to imply LIB" is exactly what is claimed, and it is claimed as an absence, not
a theorem. Anyone taking the (EQ) ticket should re-run §3's re-pricing check against (EQ) first; that
check is now cheap and should become standard.)*

**A process suggestion, from how this one went.** Theorems 3.2 and 3.3 are each one line, and between
them they invalidate a recommendation that survived three independent arcs and a design rationale
that has stood since mg-8201 and is repeated in `STATE.md`. Neither needed a new idea — only the
habit of running the proposed hypothesis *forward* to see what it already implies. Offered to
pm-onethird as a candidate addition to the Appendix A audit template (§4 SCOPE CHECK):

> **"Strength check. If the deliverable proposes a hypothesis, sub-lemma, or 'first lemma' as a
> target, derive what that hypothesis implies before assessing it. Verify it is weaker than the
> theorem it is a step toward. A sufficient condition that implies the goal is not progress toward
> the goal."**

The reason it is worth a template line rather than a note: this class of error is invisible to every
existing audit question. All the claims involved were correctly proven and correctly labelled; the
defect was in the *pricing*, and nothing in the current template asks about pricing.

---

## 10. Claim ledger (exhaustive — boxed results *and* in-prose reductions)

Per the ticket: every claim asserted anywhere in this document, including reductions made in prose.

| § | claim | status |
|---|---|---|
| 1.2 | STATE.md and mg-0ed7 do **not** disagree on the target; `(LOC) ≠ (B-bias)`, equivalence unproven and so labelled in both sources | **PROVEN by citation** (mg-0ed7 §7.5 caveat + §8 table; STATE.md correction) |
| 1.3 | target currency is control by an absolute constant, not equality/asymptotics | **PINNING** (a decision, recorded) |
| 1.4 | the measure is `σ` uniform on `L(P)` (static marginal), **not** the BK chain | **PINNING**, justified from mg-dbd1 §0, mg-dcae §5.2, mg-4a86, LLO 2025 |
| 1.5 | (H) quantifies over all incomparable pairs of the whole poset; bound required uniform in `x, n, P` | **PINNING**, verbatim from mg-dbd1 §0 |
| 1.6 | Obs. 1.1 — conditional on the 1/3–2/3 conjecture the frozen class is chains only, so the lemma is vacuously true | **PROVEN conditional on the conjecture** |
| 1.6 | consequences: RED-by-counterexample and GREEN-by-verification are both unavailable; class-restricted proofs (width ≤ 2) carry no information | **PROVEN** (from Obs. 1.1) |
| 2 | (F1) `Σ_x m_x = 2E[inv_e]` | **CITED** (mg-dbd1 §2.3, mg-dcae §5.4); trivially re-derivable |
| 2 | (F2) master bound `1 − λ_std ≤ 6E[inv]/(n²−1)` | **CITED** (mg-210d Thm 2.4); proof re-read this session, not re-derived |
| 2 | (F4) LIB ⟺ the transport transfer | **CITED** (mg-7ae7 via LIB-scoping §0); **not** re-verified |
| 2 | (F5) mg-8201 retired `E[inv_e] = O(n)` as unnecessary | **CITED VERBATIM** (ExpectedRank-Certificate §2 step-1 conclusion) |
| 3.1 | **Identity 3.1** — `m_x = E|σ_{<x} Δ D_x|`; `m_x` is the expected leak of the `e`-prefix cut through `x` | **PROVEN**, new, elementary |
| 3.1 | in-prose: the lemma is therefore strictly stronger than interface thinness `Δ₁ → 0` | **PROVEN** (Δ₁ permits `o(n)` leak per cut; the lemma demands `O(1)`) |
| 3.2 | **Theorem 3.2** — `max_x m_x ≤ C` ⟹ `E[inv_e] ≤ Cn/2` ⟹ `1 − λ_std ≤ 3Cn/(n²−1) → 0` | **PROVEN**, new, one line, **the headline** |
| 3.2 | in-prose: this is LIB with a `γ`-free constant, hence stronger than the `O(n/γ)` the program asks | **PROVEN** (`γ ≤ 1/3` so `O(n) ⊆ O(n/γ)`) |
| 3.3 | **Theorem 3.3** — `E[inv_e] ≤ E[Σ\|disp\|] ≤ √(n E[Σdisp²])`; hence **(B) with constant `C` ⟹ `E[inv_e] ≤ Cn`** | **PROVEN**, new, elementary, unconditional; **the largest state-change here** |
| 3.3 | antichain sanity check `0.25n² ≤ 0.333n² ≤ 0.408n²` | **PROVEN** by hand (closed forms `E[Σ\|disp\|] = (n²−1)/3`, `E[Σdisp²] = n(n²−1)/6`) |
| 3.3 | correction 1: `STATE.md` line 102 "the two faces are logically independent" is **false in one direction**; (B) is the stronger face | **PROVEN** (Thm 3.3) |
| 3.3 | correction 2: mg-dbd1 §2.1's "(B) is weaker than LIB" is **REFUTED** | **PROVEN** (Thm 3.3); the `L1`-vs-`L2` framing it rests on is correct, only the strength comparison is backwards |
| 3.3 | correction 3: the "tolerates quadratic `E[inv_e]`" rationale (mg-dbd1 §0/§5, mg-8201 §2 = F5) is **vacuous** — the regime is empty | **PROVEN** (Thm 3.3) |
| 3.3 | correction 4: given (B), (A) SPREAD and `Λ = O(1)` are **off the critical path** to the wall | **PROVEN** (Thm 3.3 + F2); (A) remains a true unconditional theorem, and (F2) postdates the certificate |
| 3.4 | **Finding 3.4** — LIB is the weakest of {locality, (B), LIB} and alone suffices | **PROVEN** given Thms 3.2/3.3 + F2 |
| 3.4 | **(LIB-weak)** `E[inv_e] = o(n²)` suffices for `λ_std → 1` as `STATE.md` states it | **PROVEN** (F2) |
| 3.4 | the limit-vs-rate scoping question (`λ_std → 1` vs `1 − λ_std ≤ C/(γn)`) is unresolved in the merged record | **[OPEN]** — flagged for pm-onethird, deliberately not picked |
| 3.4 | LIB is the average-form, the lemma the max-form, of the same quantity | **PROVEN** (from F1) |
| 3.4 | in-prose: Prop. 5.4's hypothesis is stronger than the theorem its conclusion was a step toward | **PROVEN** (Thm 3.2 vs F2) |
| 4 | **Identity 4.1** — `h(x) − rank_e(x) = Σ_{x<_e y} m_{xy} − Σ_{y<_e x} m_{xy}`; **unconditional**, (H) not needed | **PROVEN**, elementary; corrects mg-dcae §5.4's "under (H)" framing (minor) |
| 4 | `b_x ≤ m_x`, equality iff all inversion mass is on one side | **PROVEN** (triangle inequality on 4.1) |
| 4 | in-prose: the lossy step is `b_x ≤ m_x` applied *before* the max | **PROVEN** as a diagnosis, given Thm 6.2 quantifies the loss as `Θ(n)` |
| 5.1 | **Theorem 5.1** — `max_x b_x ≤ C₀` ⟹ `(B-bias) ≤ 2C₀E[inv_e]`; unconditional | **PROVEN**, elementary |
| 5.2 | **Observation 5.2** — `b_x = m_x` at the `e`-extremes; (EQ) at the `e`-min is exactly the negation of mg-dbd1 §3.1's falsifier | **PROVEN** |
| 5.3 | **Theorem 5.3** — `max_x b_x ≤ C₀` ⟹ `Λ ≤ 2C₀ + 1` | **PROVEN**, elementary |
| 5.3 | in-prose: (EQ) ⟹ `‖r‖² = Θ(n³)`, re-deriving (A) SPREAD | **PROVEN** (immediate from `\|h_k − k\| ≤ C₀`); (A) is independently proven in mg-dbd1, so this is corroboration only |
| 5.3 | in-prose: (EQ) leaves **(B-cov)** as the sole residual on the certificate route | **PROVEN** given Thms 5.1/5.3 + mg-dbd1's (A) + the certificate's four obligations as mg-dbd1 lists them |
| 6.1 | `W_m = C_m ⊔ C_1` exact values: `Pr[z <_σ c_i] = i/(m+1)`; `rank_e(z) = ⌈(m−1)/2⌉`; `m_{zc_i} = min(i,m+1−i)/(m+1)`; `m_z = s(s+1)/(2s+1)` at `m = 2s`; `E[pos_σ(z)] = m/2`; `b_z ≤ 1`; `b_{c_i} ≤ 1`; `E[inv_e] = m_z` | **PROVEN** by hand, with `m = 1, 2` micro-checks inline |
| 6.2 | **Theorem 6.2** — `W_m` has `max_x b_x ≤ 1`, `max_x m_x = Θ(n)`, `E[inv_e] = Θ(n)`; hence (EQ) ⇏ locality and LIB ⇏ locality **as inequalities between quantities** | **PROVEN** |
| 6.2 | the caveat: `W_m` has `δ = 1/2`, so this does **not** separate the *frozen-conditional* statements (which are vacuously equivalent under the conjecture); what it rules out is a general derivation of locality from (EQ) or LIB | **PROVEN**, and load-bearing — the theorem is stated in its scope |
| 6.2 | second reading: `W_m` violates (B) by `Θ(n)`, entirely in the variance/(B-cov) term, with (B-bias) healthy | **PROVEN** (`Var(pos_σ z) = m(m+2)/12`, uniform on `{0,…,m}`) |
| 6.3 | `C_p ⊕ A_k ⊕ C_p` with `k = ⌊√n⌋` separates LIB from locality but **not** (EQ) from locality | **PROVEN** by hand |
| 7.1 | conditional uniformity: `pos_σ(x)` is uniform on the contiguous window `I_x(τ)` given `τ`; in-window elements are all `∥ x` | **PROVEN** (elementary; the law itself is mg-a1ec's, used not re-claimed) |
| 7.1 | **Lemma 7.1** — `E[N_x \| τ] ≥ Σ_i min(i,W−i)/W ≥ (W−1)/4`; hence locality ⟹ `E[W_x] ≤ 4C+1` | **PROVEN**, new, elementary |
| 7.1 | Lemma 7.1 holds with **equality** on `W_m` at `x = z` | **PROVEN** (both sides equal `Σ_i min(i,m+1−i)/(m+1)`) |
| 7.2 | **Lemma 7.2** — `N_x ≤ (W_x−1) + N_{z⁻} + N_{z⁺}` pointwise | **PROVEN**, new, elementary |
| 7.2 | Lemma 7.2 does **not** close anything (the max-form recursion is vacuous) | **PROVEN**, stated as a limitation |
| 7.3 | bounded expected windows is necessary but **not** sufficient; `C_m ⊔ C_m` witnesses this via `m_{a_i} = E\|K_i − (i−1)\|` | **PROVEN** for the identity; **PLAUSIBLE** for the insufficiency — *downgraded 2026-07-29 (mg-1fdb) per the mg-d112 audit §3.1*: insufficiency needs `m_{a_i}` **unbounded**, and the stated non-heuristic ground (`m_{a_i} > 0`) gives positivity, not unboundedness; the unboundedness comes only from the `Θ(√m)` rate, which is **HEURISTIC**. So the rate *does* carry load here. Consequence: **nil** — §7.3 is explicitly "recorded as structure, not as progress", and nothing in §0, §3, §5 or §6 depends on it |
| 8.1 | two-atom law ⟹ the lemma is false for abstract frozen laws | **PROVEN**; **re-derivation**, credited to STATE.md obstruction 4 / mg-7ae7 |
| 8.2 | **Observation 8.1** — the 3-element system reduces on `e`-ordered triples to `m_{xz} ≤ m_{xy} + m_{yz}`, the reverse instance vacuous | **PROVEN**, elementary; the subadditivity itself is probe A's (mg-61bb) |
| 8.2 | **Corollary 8.2** — pairwise marginals + 3-element inequalities cannot prove the lemma; subadditivity is wrong-signed for decay | **PROVEN** (constant assignment `m ≡ ε` satisfies the system and is realized by §8.1's law) |
| 8.3 | **Observation 8.3** — `m_x ≤ 2Σ_d m̄_d(x)`; the lemma **is** summable decay in `e`-distance | **PROVEN**, elementary; the sum-form is the LIB arc's Fact B, credited |
| 8.4 | within-window variance needs `E[W²]`, not a first-moment locality bound — a second, independent defect in the Finding 7.5 chain | **PROVEN** as stated (conditional variance of a uniform on a window is `(W²−1)/12`); not an additional refutation, 7.5 is already refuted by mg-8f56 |
| 9 | verdict RED-by-walling + AMBER redirect; the three convergent routes to (B-cov) are untouched; three recommendations withdrawn; the (A)+(B)-over-LIB target ordering is corrected | **PROVEN** given Thms 3.2/3.3 + F2, modulo the routing recommendation being a judgement call |
| 9 | (EQ) is "not known to imply LIB" — an **absence**, explicitly not a theorem; `W_m` does not separate (EQ) from `λ_std → 1` | **[OPEN / labelled as absence]** — the one place a future ticket must re-check |

**Nothing in this document is tagged CONDITIONAL except Observation 1.1** (conditional on the
1/3–2/3 conjecture, and stated as such), **and the two [HEURISTIC] items are §7.3's rate and §9's
"not known to imply LIB" absence.** Everything else is PROVEN, elementary, and self-contained —
*with one correction (2026-07-29, mg-1fdb): §7.3's **insufficiency** claim is **PLAUSIBLE**, not
PROVEN, because it rests on that HEURISTIC rate (mg-d112 audit §3.1). Nil consequence downstream.*

---

## 11. Self-audit (what I did not do, and where a skeptical reader should push)

Written for the independent auditor who will rebuild the instrument rather than read the prose.

1. **Re-derive Theorems 3.2 and 3.3 first; they are where the state change is.** They rest on three
   imports: (F1), one line, in two merged docs; the lower half of Diaconis–Graham (`I ≤ D`), which I
   did **not** re-prove — it is quoted in mg-dbd1 §2.1 and is the standard 1977 result, and it is the
   single external fact Theorem 3.3 depends on, so it is the first thing to check; and (F2),
   mg-210d's master bound, whose proof I read but did not re-derive. **If (F2) is wrong, the second
   halves of Theorems 3.2/3.3 fail and only `E[inv_e] ≤ Cn/2` and `E[inv_e] ≤ Cn` survive — which is
   still LIB, so the RED verdict and all four §3.3 corrections survive (F2) failing.** Both verdicts
   are robust to their weakest import; check that claim.
   **Where I would attack Theorem 3.3 if I wanted to break it:** the identification of `inv_e(σ)`
   with the inversion count of the permutation `rank_e ↦ pos_σ`. It is valid because `e` extends `P`,
   so comparable pairs are never inverted and contribute `0` to both sides — but if that step were
   wrong, Theorem 3.3 and all four corrections collapse, and nothing else in the document would
   notice.
2. **Check the direction of every inequality in §5.** The pattern that broke mg-0ed7's Finding 7.5 is
   exactly the pattern here (max-then-sum). Theorem 5.1's chain is
   `Σ b² ≤ (max b)(Σ b) ≤ (max b)(Σ m) = 2(max b)E[inv]` — every step an upper bound on the target,
   which is the correct direction for a sufficiency claim. Theorem 5.3's sorting step (`|w_j − j| ≤ C₀`)
   is the one place I would look hardest for an off-by-one.
3. **Recompute `W_m` independently.** Everything in §6 is a two-line hand computation; the `m = 1`
   and `m = 2` cases are given so they can be checked against a full LE enumeration by hand (2 and 3
   linear extensions respectively). If `b_z ≤ 1` fails, Theorem 6.2 and the whole AMBER redirect fail
   with it. The RED verdict does **not** depend on §6.
4. **Scope check I ran on myself.** Theorem 3.2 does *not* say the locality lemma is false, does *not*
   say (B) or (B-cov) is false, and does *not* say the three routes are dead. It says one recommended
   hypothesis is stronger than the theorem it was a step toward. The §0 headline is written to that
   scope; if it reads as more, that is a defect and I want it flagged.
5. **Novelty claims, stated conservatively.** Identity 3.1, Theorems 3.2 and 3.3, Identity 4.1's *use*,
   Theorems 5.1/5.3, Observation 5.2, Theorem 6.2, Lemmas 7.1/7.2 are new to my reading of the
   corpus. §8.1, §8.2's subadditivity, and §8.3's sum-form are **re-derivations** of prior work and are
   credited as such. I searched `docs/` for `max_x m_x`, `max_x M_x`, `inversion degree`, and `2E[inv`
   and found the identity (F1) in two places but the implication (Thm 3.2) in none. **A cross-doc
   miss here is the most likely error in this document**, and mg-dcae §5.4's Prop. 5.4 is itself
   substantially a rediscovery of mg-dbd1 §2.3 (both derive `Σ_x b_x² ≤ (max_x m_x)·2E[inv_e]`; mg-dcae
   labels it "new"), which shows the corpus is already prone to it.
6. **Computation:** none, as required. The only numbers here are closed forms and two enumerations of
   2 and 3 linear extensions done by hand.
7. **What I did not attempt.** I did not attack `(LOC)`, did not attempt (B-cov), did not attempt (EQ)
   itself (it is named as the next ticket, not begun here), and did not attempt the `(LOC)`-vs-(B-bias)
   equivalence that mg-0ed7 flagged as a prerequisite. Given §1.6, I also made no attempt to search for
   or construct frozen witnesses — that is not a limitation of the no-computation constraint but a
   consequence of the conjecture.

---

## 12. Proposed `STATE.md` update (for pm-onethird)

`STATE.md` lives in `/Users/daniel/research/onethird_program`, a **different repository** from this
worktree, and per Appendix A pm-onethird owns it. I therefore cannot land the edit through this
ticket's refinery submit. The exact text is provided here and mailed to pm-onethird.

**Attempt-index row to add:**

> | **RED-for-lever · AMBER-redirect · CORRECTS MERGED WORK (mg-a58f)** | (B-bias) `O(1)` locality lemma (doc: `OneThird-Bbias-Locality-Lemma.md`) | **⚠️ Largest item first — (B) IMPLIES LIB (Thm 3.3, elementary, unconditional):** `E[inv_e] ≤ E[Σ\|disp\|] ≤ √(n·E[Σdisp²])` by the lower half of Diaconis–Graham + Cauchy–Schwarz, so (B) with constant `C` forces `E[inv_e] ≤ Cn`. **Four corrections:** (1) **this row's own §"single lemma" line — "the two faces are logically independent" — is false in one direction**; (B) is the *stronger* face. (2) mg-dbd1 §2.1's "(B) is weaker than LIB" is **REFUTED**. (3) The (A)+(B) route's advertised advantage — "tolerating quadratic `E[inv_e]`" (mg-dbd1 §0/§5, mg-8201 §2) — is **vacuous**: (B) is unsatisfiable when `E[inv_e] = ω(n)`, so the stated reason for abandoning LIB does not hold. (4) Given (B), the mg-210d master bound alone yields `1−λ_std = O(1/n)`, so **(A) SPREAD and `Λ = O(1)` are off the critical path** (both still true; (F2) simply postdates the certificate). **Net: LIB is the weakest _of the three_ sufficient conditions on the table and alone suffices; both objects the (A)+(B) route has attacked since mg-8201 — (B), and the locality lemma — are strictly-at-least-as-strong surrogates.** And `λ_std → 1` as stated here needs only **(LIB-weak)** `E[inv_e] = o(n²)` — never attacked by any arc. **Scoping question flagged, not picked:** STATE.md states the conclusion as a limit, mg-7ae7 states the operative target as the rate `1−λ_std ≤ C/(γn)`; those differ by a factor `n` in the inversion requirement and pm-onethird should pin which one L4 consumes. **On the ticket's own target: the lemma implies the wall.** `Σ_x m_x = 2E[inv_e]` identically, so `max_x m_x ≤ C` ⟹ `E[inv_e] ≤ Cn/2` = **LIB** (γ-free) ⟹ (mg-210d master bound) `1 − λ_std ≤ 3Cn/(n²−1) → 0` = L1b's conclusion. So it is **not** an elementary reserve route below the crux; it is at least as strong as the crux, and it silently re-imposes the `E[inv_e] = O(n)` requirement mg-8201 retired as "structurally unnecessary". All three arcs that recommended it (mg-dbd1 §5.1, mg-dcae §7.2, mg-0ed7 §7.5) mis-priced it. **The lossy step is located exactly:** both derivations bound the per-element **bias** `b_x = \|E[pos_σ x] − rank_e x\|` by the per-element **inversion mass** `m_x` *before* taking the max, discarding the cancellation between `e`-above and `e`-below inversion mass — worth a factor `n` (witness `C_m ⊔ C_1`: `max b_x ≤ 1`, `max m_x = Θ(n)`, `E[inv_e] = Θ(n)`, all exact by hand). **Redirect — (EQ):** `max_x \|E[pos_σ(x)] − rank_e(x)\| = O(1)`. Proven here: (EQ) ⟹ (B-bias) (unconditionally); (EQ) ⟹ mg-dbd1 §3.4's auxiliary `Λ = O(1)`; (EQ) is exactly the negation *at every element* of mg-dbd1 §3.1's named (B)-falsifier (which was stated only at the `e`-min, where `b_x = m_x`); (EQ) is strictly weaker than the locality lemma. Leaves **(B-cov)** as the sole residual on the certificate route — the same edge STATE.md already names, reached without over-shooting. Also new: `m_x = E\|σ_{<x} Δ D_x\|` (per-element leak identity); conditional-uniformity window bound `locality ⟹ E[W_x] = O(1)`; the 3-element system is provably inert (satisfied by the two-atom law with `m ≡ ε`). Kills none of the three routes to (B-cov); withdraws the side-door three arcs recommended. Zero computation. |

**Narrative line to add after the mg-8f56 paragraph:**

> **The target ordering was wrong, and the (B-bias) side-door is closed (mg-a58f, no computation).**
> Two elementary re-pricings, both unconditional. **(B) implies LIB** (Diaconis–Graham `I ≤ D` plus
> Cauchy–Schwarz: `E[inv_e] ≤ √(n·E[Σdisp²])`), so the two "logically independent faces" are ordered
> rather than independent, (B) is the stronger, and the (A)+(B) certificate's advertised tolerance of
> quadratic `E[inv_e]` describes an empty regime. **LIB is therefore the weakest of the three
> sufficient conditions we hold on this route — LIB, (B), and the `O(1)` locality lemma — and it
> alone suffices** — and for the `λ_std → 1` form stated above, `E[inv_e] = o(n²)`
> already does it. Separately, the `O(1)` locality lemma that
> mg-dbd1, mg-dcae and mg-0ed7 each independently recommended as the cheap, Stanley-free first step
> **also implies L1b** — `Σ_x m_x = 2E[inv_e]`, so a uniform per-element bound *is* LIB, γ-free. Being
> AF-free does not make a statement weaker than the wall. The replacement, **(EQ)**
> `max_x |E[pos_σ x] − rank_e x| = O(1)`, does the same two jobs (closes (B-bias) and `Λ = O(1)`) and
> is provably strictly weaker; it is the negation of the program's own named (B)-falsifier at every
> element rather than only at the `e`-minimum. Two residuals become three, correctly ordered:
> **(B-cov)** (the sharp edge, untouched), **(R)** (mg-210d, elementary), **(EQ)** (new, elementary,
> and the only one of the three that is a *cancellation* statement rather than a decay statement —
> which places it outside the family the 3-element inequalities are proven inert on).

---

## 13. Disposition of the mg-d112 independent audit (added 2026-07-31, mg-fccb)

`docs/OneThird-Bbias-Locality-Lemma-IndependentAudit.md` (mg-d112, landed `cd261b9`) returned
**CONFIRMED** on the mathematics — 45/47 claims CONFIRMED, 2 PLAUSIBLE, **0 BROKEN** — with six
routed actions. All six are now closed. Recorded here because the audit lives in a separate file and
a reader of *this* document had no way to tell which of its findings had been acted on.

| # | audit finding | disposition | where |
|---|---|---|---|
| 1 | Accept the mathematics; nothing withdrawn | no action needed | — |
| 2 | **OVERSTATEMENT** — "the weakest sufficient condition on the table" drops the body's "of the three"; "everything attacked since mg-8201 is a surrogate" is a **false universal** | **closed** — quantifiers narrowed at all three sites (§0, §12 row, §12 narrative); **not** to a form identical with the body's — see the correction below | this doc, mg-fccb; corrected mg-069f |
| 3 | **CROSS-DOC MISS** — `STATE.md`:86 already asserted `LIB ⟺ (B)`, contradicting :102; reconcile **both**, not just :102 | **closed** — reconciled in `onethird_program`, both sites together | `STATE.md`, pm-onethird |
| 4 | **CROSS-DOC MISS** — unflagged inequality-direction error in mg-dbd1 §2.3, and §3.2's "Equivalently" | **closed** — annotated (mg-1fdb, `b169561`); erroneous sentence struck at the site, re-derived independently, and its §5 consumers annotated (mg-fccb) | `OneThird-L1b-Spread-Locality.md` |
| 5 | **LABEL** — downgrade §7.3's insufficiency row PROVEN → PLAUSIBLE | **closed** (mg-1fdb, `b169561`) | `OneThird-L1b-Spread-Locality.md` |
| 6 | Adopt the "strength check" + falsifier-quantifier check in Appendix A | **closed** — Appendix A step 4b | `STATE.md`, pm-onethird |

> **CORRECTION to row 2 (2026-07-31, mg-069f — mg-8a71 finding F4).** Row 2 said the quantifiers were
> restored *"to the body's Finding 3.4 form"* at all three sites. **They were narrowed, but not to the
> body's form, and the three sites do not agree with each other.** Read at the far end, verbatim:
>
> | site | what it says | vs the body |
> |---|---|---|
> | body, Finding 3.4 (§3.4) | *"the weakest of the three sufficient conditions **the program has** on the table … Both objects **the program** has attacked since mg-8201"* | — |
> | §0 | *"the weakest **of the three** sufficient conditions on the table … both objects **the (A)+(B) route** has attacked since mg-8201"* | **narrower** |
> | §12 attempt-index row | same phrasing as §0: *"both objects **the (A)+(B) route** has attacked since mg-8201"* | **narrower** |
> | §12 narrative | *"the weakest of the three sufficient conditions we hold **on this route**"*; the *"both objects … since mg-8201"* clause is **absent entirely** | **narrower still** |
>
> **Nothing here overstates** — every site is at most as strong as what §3.4 proves, which is the
> direction that matters and is why this is a LOW finding and not a reopening of finding 2. What was
> wrong is only row 2's description of the fix. mg-8a71 recorded this for §0 alone and stated that
> *"§12's row and narrative match the body"*; re-read at the far end, **the §12 row does not either**
> — it carries the same *"(A)+(B) route"* as §0 — and the §12 narrative dropped the clause rather than
> matching it. The finding is confirmed and slightly wider than reported. **Left as is** rather than
> re-widened to *"the program"*: three narrower-than-proven statements are a correct record, and
> editing proven-safe text a third time to chase verbal uniformity is the over-correction risk this
> audit family exists to name.

**On finding 2, the substance.** The audit's counterexamples to the universal were re-verified at the
far end by mg-fccb, and all four arcs postdate mg-8201 (2026-07-13): **mg-4a86**
(`OneThird-StandardDominance-ComparisonRoute.md`) attacks the *dynamical* `λ₂^BK`-vs-`λ_std`
comparison and is not an inversion-counting condition at all; **mg-210d**'s residual **(R)**
(`probe-lambda-constant-bound.md` §5) yields only a constant floor `λ_std > 1 − D`, not `λ_std → 1`,
and is not known to imply LIB; the **entropy probes** (mg-61bb, mg-f82f, mg-92e6, mg-e2de) target the
Kahn–Saks/BFT `0.2764` bound and `δ` directly. None is a LIB surrogate, so the universal was false.
The restricted claim — **two** objects, (B) and the locality lemma — is what §3.4 proves and is what
now stands at every site.

**On finding 3, what the far end now says.** `STATE.md` ledger row 8 now reads *"Sufficient
conditions, **one-way**: **(B) ⟹ LIB ⟹ `λ_std→1`**. The reverse arrows are **UNPROVEN — not merely
absent**"*, and the § *The single lemma to prove* line now reads *"the two faces are **not** logically
independent (corrected 2026-07-29; mg-a58f Thm 3.3, audited mg-d112 CONFIRMED)"* and closes *"Both
this line and ledger row 8 previously asserted an equivalence; they are reconciled together here."*
The `W_m` caveat (`δ = 1/2`, so it separates the **quantities**, not the frozen-conditional
**statements**) is carried there correctly. **The internal inconsistency the audit found is gone.**

---

*Deliverable for mg-a58f. LaTeX-first rule honored (written proof + self-audit; no Lean). Subject to
the standing independent pre-PM-review audit stage, `STATE.md` Appendix A.*
