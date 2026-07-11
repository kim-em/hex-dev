/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Var
-- `import all` so `decide` reduces the sanity checks below in the kernel.
-- `signVar` (in `Var.lean`) is a plain, non-`@[expose]` def, so its body is
-- opaque across the module boundary; `import all` exposes it. The Möbius
-- pipeline itself only calls `@[expose]` `DensePoly`/`ZPoly` operations, whose
-- bodies are already visible. The `Array`-equality `import all` is the same
-- kernel-`decide` workaround as `Chain.lean`/`Var.lean`, needed because the
-- array-literal assertions compare `ZPoly` (hence `Array Int`) values.
import all Init.Data.Array.DecidableEq
import all HexRealRoots.Var

public section

/-!
The integer Möbius transform and the Descartes variation count.

`mobiusTransform p (a, b]` returns an integer polynomial whose positive real
roots correspond bijectively, with multiplicity, to the real roots of `p` in
the open interval `(a, b)`. It is the numerator of `(1 + x)^{deg p} ·
p((a + bx)/(1 + x))` after clearing the dyadic denominators — a power of two.
The pipeline is a sequence of integer coordinate changes, each `O(n²)` integer
operations on the coefficient array (Taylor shift based, no rational
arithmetic), so a whole transform costs `O(n²)`.

`descartesVar p` counts the sign variations of `p`'s coefficient list. Combined
with the transform, `descartesVar (mobiusTransform p I)` is the Descartes bound
on the number of real roots of `p` in the open interval `I`: it equals that
count modulo 2 and dominates it, so a value of `0` certifies "no roots in the
open interval" (the discard row of the Descartes engine's dispatch table). The
engine trusts the count only as a search heuristic; every candidate it produces
is re-certified by an exact Sturm count.
-/
namespace Hex

/-- The `(numerator, denominator-exponent)` pair of a dyadic value: `ofOdd n k`
is `n · 2^{-k}`, and zero is `(0, 0)` (the exponent is irrelevant to a zero
numerator). Used to put an interval's two endpoints over a common power-of-two
denominator. -/
private def dyadicNumExp : Dyadic → Int × Int
  | .zero => (0, 0)
  | .ofOdd n k _ => (n, k)

/-- Put an interval's endpoints over a common power-of-two denominator.

From `I.lower = a = nₐ·2^{-kₐ}` and `I.upper = b = n_b·2^{-k_b}` compute the
common exponent `s = max(0, kₐ, k_b)` and the integer numerators `α = a·2^s`,
`β = b·2^s`, so `a = α·2^{-s}` and `b = β·2^{-s}` with `α, β : ℤ` and `s : ℕ`.
Because `s ≥ kₐ, k_b` the two scalings `2^{s-kₐ}`, `2^{s-k_b}` are genuine
integers, and because `a < b` the result satisfies `α < β`. Returns
`(α, β, s)`. -/
private def mobiusEndpoints (I : DyadicInterval) : Int × Int × Nat :=
  let (na, ka) := dyadicNumExp I.lower
  let (nb, kb) := dyadicNumExp I.upper
  let sInt := max 0 (max ka kb)
  let α := na * (2 : Int) ^ (sInt - ka).toNat
  let β := nb * (2 : Int) ^ (sInt - kb).toNat
  (α, β, sInt.toNat)

/-- The integer Möbius transform of `p` relative to `(a, b]`: the numerator of
`(1 + x)^{deg p} · p((a + bx)/(1 + x))` after clearing the dyadic denominators
(a positive power of two). Its positive real roots correspond bijectively, with
multiplicity, to the real roots of `p` in the open interval `(a, b)`.

The pipeline, with `n = deg p` fixed up front and `(α, β, s)` from
`mobiusEndpoints` (so `a = α·2^{-s}`, `b = β·2^{-s}`):

* **(b) clear the dyadic denominator.** Replace `x` by `x·2^{-s}`, i.e. form
  `2^{s·n}·p(x·2^{-s})`: coefficient `aᵢ ↦ aᵢ·2^{s·(n−i)}`. This scales every
  root by `2^s`, so the interval becomes `(α, β]` with *integer* endpoints.
* **(c) Taylor shift to the origin.** `q ↦ q(x + α)` via `compose` with the
  degree-one argument `x + α`; the interval's roots now lie in `(0, β−α]`.
* **(d) rescale the interval to `(0, 1]`.** `dilate (β−α)` evaluates at
  `(β−α)·x`, dividing every root by `β−α`, so roots in `(0, β−α)` map to
  `(0, 1)`.
* **(e) reverse at the *original* degree `n`.** Build the coefficient array of
  length `n+1` with entry `i` equal to `coeff (n − i)` and renormalize; this is
  the `x ↦ 1/x` homogenization `(1+x)^{deg p}` of the SPEC contract, sending
  `(0, 1)` to `(1, ∞)`. Reversing at `n` rather than the *current* degree is
  essential: when `p(a) = 0` the shifted constant term vanishes and the current
  degree drops, and that dropped root correctly disappears (its image is `∞`).
* **(f) shift back to the positive axis.** `r ↦ r(x + 1)` via `compose`, sending
  `(1, ∞)` to `(0, ∞)`. The positive real roots of the result are exactly the
  images of `p`'s roots in the open `(a, b)`.

No content/`primitivePart` division is taken anywhere: sign variations are
scale-invariant, so a content gcd would be pure cost against the `O(n²)`
per-node budget.

For `deg p ≤ 0` (`p` constant or zero) there is no interval structure to
transform; `p` is returned unchanged as a documented junk value (no theorem
reads it). -/
def mobiusTransform (p : ZPoly) (I : DyadicInterval) : ZPoly :=
  if p.size ≤ 1 then p else
  let n := p.size - 1
  let (α, β, s) := mobiusEndpoints I
  -- (b) `x ↦ x·2^{-s}`: `aᵢ ↦ aᵢ·2^{s·(n−i)}`, i.e. `2^{s·n}·p(x·2^{-s})`.
  let cleared := DensePoly.ofCoeffs
    ((List.range p.size).map (fun i => p.coeff i * (2 : Int) ^ (s * (n - i)))).toArray
  -- (c) Taylor shift `q(x + α)` (`compose` with the degree-one `x + α`).
  let shifted := DensePoly.compose cleared (DensePoly.ofCoeffs #[α, (1 : Int)])
  -- (d) rescale `(0, β−α) ↦ (0, 1)` by evaluating at `(β−α)·x`.
  let scaled := ZPoly.dilate (β - α) shifted
  -- (e) reverse at the ORIGINAL degree `n`: entry `i` is `coeff (n−i)`.
  let reversed := DensePoly.ofCoeffs
    ((List.range (n + 1)).map (fun i => scaled.coeff (n - i))).toArray
  -- (f) shift back `r(x + 1)`, mapping `(1, ∞) ↦ (0, ∞)`.
  DensePoly.compose reversed (DensePoly.ofCoeffs #[(1 : Int), 1])

/-- Sign variations of the coefficient list: the Descartes bound. Each stored
coefficient is reduced to its exact sign in `{−1, 0, 1}` and the resulting list
is fed to `signVar` (zero-skipping sign-variation count). -/
def descartesVar (p : ZPoly) : Nat :=
  signVar (p.toArray.toList.map Int.sign)

/-! Sanity checks (kept light; conformance lives in the shared sub-project).
Each transform below is hand-verified in the comment; sign variations are
invariant under overall sign and under the reversal orientation, so a pipeline
result may be a negative multiple or the coefficient-reverse of the textbook
`(1+x)^n·p((a+bx)/(1+x))` while carrying the same variation count. -/

-- `descartesVar` basics.
-- `x² − 3x + 2` has coefficients `#[2,-3,1]` → signs `(+,−,+)` → 2 variations.
example : descartesVar (DensePoly.ofCoeffs #[(2 : Int), -3, 1]) = 2 := by decide
-- `x² + 1` → signs `(+,0,+)` → 0.
example : descartesVar (DensePoly.ofCoeffs #[(1 : Int), 0, 1]) = 0 := by decide
-- `x − 1` → signs `(−,+)` → 1.
example : descartesVar (DensePoly.ofCoeffs #[(-1 : Int), 1]) = 1 := by decide

-- `mobiusTransform (x − 1)` on `(0, 2]`. `n = 1`, `α = 0`, `β = 2`, `s = 0`.
-- (b) `x−1` → (c) `(x+0)−1 = x−1` → (d) `dilate 2`: `2x−1` → (e) reverse at 1:
-- `2 − x` → (f) `2 − (x+1) = 1 − x`, array `#[1,-1]` (`= −(x−1)`). Root `1 ∈ (0,2)`
-- of `x−1` gives the one positive root; signs `(+,−)` → 1.
example : mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 1])
    (DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2) (by decide))
    = DensePoly.ofCoeffs #[(1 : Int), -1] := by decide
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 1])
    (DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2) (by decide))) = 1 := by decide

-- `mobiusTransform (x² − 3)` on `(1, 2]`. `n = 2`, `α = 1`, `β = 2`, `s = 0`.
-- (b) `x²−3` → (c) `(x+1)²−3 = x²+2x−2` → (d) `dilate 1`: unchanged → (e) reverse
-- at 2: `−2x²+2x+1` → (f) `−2(x+1)²+2(x+1)+1 = −2x²−2x+1`, array `#[1,-2,-2]`.
-- This is the coefficient-reverse of the textbook `x²−2x−2`; both count 1
-- variation. `√3 ∈ (1,2)` is a root of `x²−3`; signs `(+,−,−)` → 1.
example : mobiusTransform (DensePoly.ofCoeffs #[(-3 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt 1) (Dyadic.ofInt 2) (by decide))
    = DensePoly.ofCoeffs #[(1 : Int), -2, -2] := by decide
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(-3 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt 1) (Dyadic.ofInt 2) (by decide))) = 1 := by decide

-- Boundary-root case (the off-by-degree trap). `mobiusTransform (x − 1)` on
-- `(1, 3]`: `p(1) = 0`, so the root sits on the *excluded* left endpoint and is
-- NOT in the open `(1,3)`. `n = 1`, `α = 1`, `β = 3`, `s = 0`. (c) `(x+1)−1 = x`
-- → (d) `dilate 2`: `2x` → (e) reverse at 1: `#[2,0]` renormalizes to the
-- constant `2` (the degree drop, handled correctly) → (f) constant `2`. Signs
-- `(+)` → 0: no root in the open interval.
example : mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 1])
    (DyadicInterval.mk (Dyadic.ofInt 1) (Dyadic.ofInt 3) (by decide))
    = DensePoly.ofCoeffs #[(2 : Int)] := by decide
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 1])
    (DyadicInterval.mk (Dyadic.ofInt 1) (Dyadic.ofInt 3) (by decide))) = 0 := by decide

-- Half-dyadic endpoint. `mobiusTransform (2x − 1)` on `(0, 1]`: root `1/2 ∈ (0,1)`.
-- `n = 1`, `α = 0`, `β = 1`, `s = 0`. (c) `2x−1` → (d) `dilate 1`: unchanged →
-- (e) reverse: `2 − x` → (f) `1 − x`, array `#[1,-1]`; signs `(+,−)` → 1.
example : mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 2])
    (DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 1) (by decide))
    = DensePoly.ofCoeffs #[(1 : Int), -1] := by decide
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 2])
    (DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 1) (by decide))) = 1 := by decide

-- Same polynomial `2x − 1` on `(1/2, 1]`: the root `1/2` is now the *excluded*
-- left endpoint, so the open `(1/2, 1)` has no root. Here `s = 1`: the common
-- denominator is `2`, `α = 1`, `β = 2`, and (b) rescales `2x−1 ↦ 2x−2`. (c)
-- `2(x+1)−2 = 2x` → (d) `dilate 1` → (e) `#[2,0]` renormalizes to `2` → (f) `2`.
-- Signs `(+)` → 0.
example : mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 2])
    (DyadicInterval.mk ((Dyadic.ofInt 1) >>> (1 : Int)) (Dyadic.ofInt 1) (by decide))
    = DensePoly.ofCoeffs #[(2 : Int)] := by decide
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 2])
    (DyadicInterval.mk ((Dyadic.ofInt 1) >>> (1 : Int)) (Dyadic.ofInt 1) (by decide))) = 0 := by decide

-- No-root polynomial `x² + 1` on `(−2, 2]`. `x²+1` has no real roots, so the
-- open interval contains none and `descartesVar` must be *even* and an upper
-- bound (Descartes): the transform's positive-root count is `0`, so `V ∈
-- {0,2,4,…}`. `n = 2`, `α = −2`, `β = 2`, `s = 0`. (c) `(x−2)²+1 = x²−4x+5` →
-- (d) `dilate 4`: `16x²−16x+5` → (e) reverse at 2: `5x²−16x+16` → (f)
-- `16 − 16(x+1) + 5(x+1)² = 5x²−6x+5`, array `#[5,-6,5]` — exactly the textbook
-- transform `(−2+2x)²+(1+x)²`. Signs `(+,−,+)` → 2. This interval is *wide*
-- relative to the imaginary root pair `±i`, so the Descartes count
-- over-estimates by 2 — sound (an even over-count), but not a `V = 0` discard.
-- NOTE: the directive's expected `V = 0` here is a hand-computation slip; the
-- true count on `(−2,2]` is 2, and `V = 0` on this polynomial needs an interval
-- away from `±i` (see the next check).
example : mobiusTransform (DensePoly.ofCoeffs #[(1 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 2) (by decide))
    = DensePoly.ofCoeffs #[(5 : Int), -6, 5] := by decide
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(1 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 2) (by decide))) = 2 := by decide
-- A genuine discard case for `x² + 1`: on `(3, 4]`, far from `±i`, the count is
-- `0` (textbook transform `(3+4x)²+(1+x)² = 17x²+26x+10`, signs `(+,+,+)`).
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(1 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt 3) (Dyadic.ofInt 4) (by decide))) = 0 := by decide

-- Cross-check on `(2x−1)(x−2) = 2x² − 5x + 2` (roots `1/2` and `2`): the
-- Descartes counts on `(0,1]`, `(1,4]`, `(0,4]` are `1`, `1`, `2`.
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(2 : Int), -5, 2])
    (DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 1) (by decide))) = 1 := by decide
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(2 : Int), -5, 2])
    (DyadicInterval.mk (Dyadic.ofInt 1) (Dyadic.ofInt 4) (by decide))) = 1 := by decide
example : descartesVar (mobiusTransform (DensePoly.ofCoeffs #[(2 : Int), -5, 2])
    (DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 4) (by decide))) = 2 := by decide

end Hex
