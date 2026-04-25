/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Tactic.NormNum

/-!
# Step 8 — Case-3 residual enumeration: shared helpers
(`lean/scripts/enum_case3.py`, `lean/scripts/enum_case3_certificate.json`)

This file carries the shared Lean infrastructure for the
`native_decide` port of the Python residual Case-3 enumeration of
`mg-307c`.  The four per-`w` theorems
`case3_balanced_w{1,2,3,4}` live in sibling files
`OneThird.Step8.Case3Enum.W{1,2,3,4}` so that Lake can build their
native-decide evaluations in parallel; the combined certificate is
in `OneThird.Step8.Case3Enum.Certificate`.

## Encoding

Each configuration is encoded as a list of predecessor bitmasks:
element indices `0, …, n − 1` are laid out in band-major order
(band 1 elements, then band 2, …), and bit `u` of `pred[v]` is
set iff `u < v` in the transitive closure.  All validity checks
and the balanced-pair test operate on this bitmask representation,
mirroring the Python enumerator byte-for-byte.

## Scope note

The statement produced in the companion files is the Bool-level
enumeration certificate — the computational evidence that every
`(w, K = 3, band_sizes, predecessor-mask)` tuple in scope admits
a balanced pair.  The lift of this certificate to an abstract
`∀ (L : LayeredDecomposition α), … → HasBalancedPair α` statement
requires an encoding argument (choose element labelling within
each band; prove probability invariance under relabelling) that
is deferred to a separate work item on the F5 recursion.

## References

`step8.tex` §G4 `rem:residual-base`, Lemma
`lem:bounded-irreducible-balanced`; `lean/scripts/enum_case3.py`,
`lean/scripts/README.md`, `lean/scripts/enum_case3_certificate.json`.
-/

namespace OneThird
namespace Step8
namespace Case3Enum

/-! ### §1 — Bitmask primitives on `Nat` / `Array Nat` -/

/-- `bit i` is the `Nat` with only bit `i` set. -/
@[inline] def bit (i : Nat) : Nat := 1 <<< i

/-- Test bit `i` of `m`. -/
@[inline] def testBit' (m i : Nat) : Bool := (m &&& bit i) != 0

/-- Bitwise complement of `m` truncated to `n` bits: the `n`-bit
value `(2^n − 1) ^^^ m`. -/
@[inline] def lnotN (m n : Nat) : Nat := ((1 <<< n) - 1) ^^^ m

/-- Warshall's transitive-closure pass.  Input: `pred : Array Nat`
of length `n` such that bit `u` of `pred[v]` encodes the relation
`u < v`.  Output: the transitive closure of the same relation. -/
def warshall (pred : Array Nat) (n : Nat) : Array Nat := Id.run do
  let mut out := pred
  for k in [0:n] do
    let bitK := bit k
    let pk := out.getD k 0
    for v in [0:n] do
      if ((out.getD v 0) &&& bitK) != 0 then
        out := out.set! v ((out.getD v 0) ||| pk)
  return out

/-! ### §2 — Structural validity checks -/

/-- `irreducible pred offsets`: layer-ordinal-sum irreducible.  For
every cut `k ∈ {1, …, K−1}`, there exists `b` in bands `k+1..K`
incomparable to some element of bands `1..k`. -/
def irreducible (pred : Array Nat) (offsets : Array Nat) : Bool := Id.run do
  let K := offsets.size - 1
  for k in [1:K] do
    let offk := offsets.getD k 0
    let offK := offsets.getD K 0
    let lowerMask : Nat := (1 <<< offk) - 1
    let mut foundIncomp := false
    for b in [offk:offK] do
      let pv := pred.getD b 0
      if (pv &&& lowerMask) != lowerMask then
        foundIncomp := true
        break
    if !foundIncomp then return false
  return true

/-- `hasAdjacentIncomp pred offsets`: exists `(u, v) ∈ M_s × M_{s+1}`
with `u` and `v` incomparable. -/
def hasAdjacentIncomp (pred : Array Nat) (offsets : Array Nat) : Bool := Id.run do
  let K := offsets.size - 1
  for s in [0:K-1] do
    let lo := offsets.getD s 0
    let hi := offsets.getD (s + 1) 0
    let hi2 := offsets.getD (s + 2) 0
    let lowMask : Nat := (1 <<< lo) - 1
    let hiMask : Nat := (1 <<< hi) - 1
    let bandMask : Nat := hiMask ^^^ lowMask
    for b in [hi:hi2] do
      let pv := pred.getD b 0
      if (pv &&& bandMask) != bandMask then
        return true
  return false

/-- Build the band-offset array `[0, n₁, n₁+n₂, …]` from a list of
band sizes. -/
def offsetsOf (bandSizes : List Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[0]
  let mut acc : Nat := 0
  for s in bandSizes do
    acc := acc + s
    out := out.push acc
  return out

/-- `closureCanonical closed mask freeUV`: every bit of `mask` matches
the corresponding closure bit; i.e. the closure adds no new free-pair
edges beyond those in `mask`. -/
def closureCanonical (closed : Array Nat) (mask : Nat)
    (freeUV : Array (Nat × Nat)) : Bool := Id.run do
  let m := freeUV.size
  for k in [0:m] do
    let (u, v) := freeUV.getD k (0, 0)
    let closedBit : Bool := testBit' (closed.getD v 0) u
    let maskBit : Bool := testBit' mask k
    if closedBit != maskBit then return false
  return true

/-! ### §3 — Balanced-pair: symmetric-pair fast path -/

/-- Compute successor bitmasks: bit `v` of `succ[u]` is set iff
`u < v`.  We iterate bit positions explicitly (rather than using the
`lsb & -lsb` two's-complement trick, which is unavailable on `Nat`). -/
def successorMasks (pred : Array Nat) (n : Nat) : Array Nat := Id.run do
  let mut succ : Array Nat := Array.replicate n 0
  for v in [0:n] do
    let pv := pred.getD v 0
    for u in [0:n] do
      if testBit' pv u then
        succ := succ.set! u ((succ.getD u 0) ||| bit v)
  return succ

/-- Find an incomparable `(x, y)` such that `swap x y` is a poset
automorphism: `pred` and `succ` agree on `x, y` after masking out
bits `x, y`. -/
def findSymmetricPair (pred : Array Nat) (n : Nat) : Option (Nat × Nat) := Id.run do
  let succ := successorMasks pred n
  for x in [0:n] do
    for y in [x+1:n] do
      let px := pred.getD x 0
      let py := pred.getD y 0
      if testBit' py x then continue
      if testBit' px y then continue
      let cMask : Nat := lnotN (bit x ||| bit y) n
      if (px &&& cMask) != (py &&& cMask) then continue
      let sx := succ.getD x 0
      let sy := succ.getD y 0
      if (sx &&& cMask) != (sy &&& cMask) then continue
      return some (x, y)
  return none

/-! ### §4 — Balanced-pair: fallback linear-extension DP -/

/-- Enumerate the set of element indices represented by a bitmask
of width `n`. -/
def bitsOf (m n : Nat) : List Nat := Id.run do
  let mut out : List Nat := []
  for i in [0:n] do
    if testBit' m i then out := out ++ [i]
  return out

/-- The DP transition: given the partial DP table `f` and a subset
encoded by `placed ≥ 1`, sum `f[placed \ {e}]` over all `e ∈ placed`
whose predecessors are already in `placed \ {e}` (the only `e`
positions whose placement at the end of a length-`|placed|` prefix
can extend a valid linear-extension prefix). -/
def cleStep (pred : Array Nat) (n placed : Nat) (f : Array Nat) : Nat :=
  (List.range n).foldl
    (fun acc e =>
      if testBit' placed e then
        let prev : Nat := placed ^^^ bit e
        let pe := pred.getD e 0
        if (pe &&& prev) == pe then acc + f.getD prev 0
        else acc
      else acc) 0

/-- Count linear extensions of the poset given by `pred` on `n`
elements via subset DP: `f[∅] = 1`, `f[S] = Σ_{x ∈ S minimal in S}
f[S \ {x}]`.

Functional form: `(List.range N).foldl` over the table-fill loop with
the entry at index `0` initialised to `1`.  The original imperative
formulation is recovered up to definitional equality of `Id.run do`
(a series of `f := f.set! placed total` updates in placed-ascending
order). -/
def countLinearExtensions (pred : Array Nat) (n : Nat) : Nat :=
  let N : Nat := 1 <<< n
  let f₀ : Array Nat := (Array.replicate N 0).set! 0 1
  let final : Array Nat :=
    (List.range N).foldl
      (fun (f : Array Nat) (placed : Nat) =>
        if placed = 0 then f
        else f.set! placed (cleStep pred n placed f)) f₀
  final.getD (N - 1) 0

/-- Add the edge `u < v` to `pred` and take transitive closure. -/
def addEdgeClose (pred : Array Nat) (n u v : Nat) : Array Nat :=
  let p := pred.set! v ((pred.getD v 0) ||| bit u)
  warshall p n

/-- `hasBalancedPairSlow pred n`: search all incomparable pairs for
one with `Pr[x <_L y] ∈ [1/3, 2/3]`.  Used as a fallback when the
symmetric-pair fast path fails. -/
def hasBalancedPairSlow (pred : Array Nat) (n : Nat) : Bool := Id.run do
  let total := countLinearExtensions pred n
  for x in [0:n] do
    for y in [x+1:n] do
      let px := pred.getD x 0
      let py := pred.getD y 0
      if testBit' py x then continue
      if testBit' px y then continue
      let pred' := addEdgeClose pred n x y
      let cnt := countLinearExtensions pred' n
      -- `1/3 ≤ cnt / total ≤ 2/3`  iff  `3·cnt ≥ total ∧ 3·cnt ≤ 2·total`.
      if 3 * cnt >= total && 3 * cnt <= 2 * total then return true
  return false

/-- Fast balanced-pair check: try the `O(n²)` symmetric-pair path,
fall back to the `O(2ⁿ·n)` linear-extension DP. -/
def hasBalancedPair (pred : Array Nat) (n : Nat) : Bool :=
  match findSymmetricPair pred n with
  | some _ => true
  | none => hasBalancedPairSlow pred n

/-! ### §5 — Enumerate all pred-masks over free pairs for a fixed
`(w, band_sizes)` tuple. -/

/-- For a fixed `(w, band_sizes)` tuple, enumerate every closure-
canonical mask, filter to irreducible posets with an adjacent-incomp
cross-pair, and return `true` iff every surviving configuration
admits a balanced pair. -/
def enumPosetsFor (w : Nat) (bandSizes : List Nat) : Bool := Id.run do
  let offsets := offsetsOf bandSizes
  let K := bandSizes.length
  let n : Nat := offsets.getD K 0
  -- Partition cross-band pairs into `free` (band-gap ≤ w) and
  -- `forced` (band-gap > w).
  let mut freeUV : Array (Nat × Nat) := #[]
  let mut forcedUV : Array (Nat × Nat) := #[]
  for i in [0:K] do
    for j in [i+1:K] do
      let offI := offsets.getD i 0
      let offI1 := offsets.getD (i + 1) 0
      let offJ := offsets.getD j 0
      let offJ1 := offsets.getD (j + 1) 0
      for a in [offI:offI1] do
        for b in [offJ:offJ1] do
          if j - i > w then
            forcedUV := forcedUV.push (a, b)
          else
            freeUV := freeUV.push (a, b)
  let nfree := freeUV.size
  -- `nfree ≤ 27` by the Python script; in the certified scope
  -- `nfree ≤ 18`.  Refuse enumeration on larger-than-supported
  -- inputs (should never trigger in the certified scope).
  if nfree > 27 then return false
  for mask in [0:1 <<< nfree] do
    -- Allocate `pred` fresh each mask (owned refcount, so subsequent
    -- `set!` calls mutate in place).
    let mut pred : Array Nat := Array.replicate n 0
    for uv in forcedUV do
      let (u, v) := uv
      pred := pred.set! v ((pred.getD v 0) ||| bit u)
    for k in [0:nfree] do
      if testBit' mask k then
        let (u, v) := freeUV.getD k (0, 0)
        pred := pred.set! v ((pred.getD v 0) ||| bit u)
    pred := warshall pred n
    if !closureCanonical pred mask freeUV then continue
    -- Fast path: a symmetric pair exists — accept (the config is
    -- balanced regardless of whether it satisfies irreducibility/
    -- adjacent-incomp).  This discharges the vast majority of
    -- masks; the remaining asymmetric ones fall through to the full
    -- validity-then-DP path.
    if (findSymmetricPair pred n).isSome then continue
    if !irreducible pred offsets then continue
    if !hasAdjacentIncomp pred offsets then continue
    if !hasBalancedPairSlow pred n then return false
  return true

/-! ### §6 — Band-sizes generator and top-level check -/

/-- All tuples `[n₁, …, n_K]` with `n_i ∈ {1, 2, 3}` and sum
`≤ maxTotal`. -/
def bandSizesGen : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | K + 1, maxTotal =>
    let rest := bandSizesGen K maxTotal
    ((rest.map (fun t => 1 :: t)) ++
      (rest.map (fun t => 2 :: t)) ++
      (rest.map (fun t => 3 :: t))).filter
      (fun t => t.foldr (· + ·) 0 ≤ maxTotal)

/-- Top-level check: for every 3-band tuple `bandSizes` with sum
`≤ sizeLimit`, every irreducible layered config with an adjacent
incomparable cross-pair admits a balanced pair. -/
def allBalanced (w : Nat) (sizeLimit : Nat) : Bool := Id.run do
  for bs in bandSizesGen 3 sizeLimit do
    if !enumPosetsFor w bs then return false
  return true

end Case3Enum
end Step8
end OneThird
