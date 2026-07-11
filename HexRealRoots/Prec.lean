/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ

public section

/-!
Bounds and depths for real root isolation: a power-of-two Cauchy root
bound, a closed-form separation precision derived from the Mahler bound,
and the bisection depth at which both isolation engines stop.

Everything here is closed-form integer arithmetic on the coefficients of
`p ∈ ℤ[x]`: `sepPrec` and `rootBound` are `O(n · h)` integer operations
in the degree `n` and coefficient height `h`. No discriminant, no root,
and no floating point is ever computed. `Dyadic` comes from Lean core
(`Init.Data.Dyadic`); the two ceiling-logarithm helpers below are the
only rounding primitives, and every rounding is conservative (it can
only enlarge `rootBound`, `sepPrec`, and `isolationDepth`).
-/
namespace Hex

/-- The exact dyadic `2^k` for an integer exponent `k`, as `1` shifted
left by `k` (a right shift when `k < 0`). -/
@[expose] def twoPow (k : Int) : Dyadic := (1 : Dyadic) <<< k

/-- The least `k` with `m ≤ 2^k`, for `m ≥ 1`; `0` for `m ≤ 1`.

For `m ≥ 2` we have `m ≤ 2^k ⟺ m − 1 < 2^k ⟺ ⌊log₂ (m − 1)⌋ < k`, so
the least such `k` is `⌊log₂ (m − 1)⌋ + 1`. The `m ≤ 1` branch returns
`0`, the least `k` with `1 ≤ 2^k`. -/
@[expose] def ceilLog2Nat (m : Nat) : Nat := if m ≤ 1 then 0 else (m - 1).log2 + 1

/-- The least integer `e` with `x ≤ 2^e`, for a positive dyadic `x`;
junk value `0` for `x ≤ 0` (documented, never read).

A nonzero dyadic is `ofOdd n k` with value `n · 2^{−k}`. For `n > 0`,
`n · 2^{−k} ≤ 2^e ⟺ n ≤ 2^{e + k} ⟺ e + k ≥ ceilLog2Nat n ⟺
e ≥ ceilLog2Nat n − k`, so the least such `e` is `ceilLog2Nat n − k`.
Both `zero` (value `0`) and `ofOdd n k` with `n ≤ 0` (value `≤ 0`) are
outside the `x > 0` domain and return the junk value `0`. -/
def ceilLog2Dyadic : Dyadic → Int
  | .zero => 0
  | .ofOdd n k _ => if n ≤ 0 then 0 else (ceilLog2Nat n.toNat : Int) - k

/-- A power of two strictly exceeding the Cauchy root bound
`1 + max_{i < n} |aᵢ| / |aₙ|`, so every real root of `p` lies in
`(−rootBound p, rootBound p]`. Integer arithmetic only.

With `c := |aₙ|` the leading coefficient and `A := max_{i < n} |aᵢ|` the
largest non-leading coefficient in absolute value, the result is
`twoPow (ceilLog2Nat (⌊A / c⌋ + 2))`. Since `2^k ≥ ⌊A / c⌋ + 2 >
1 + A / c ≥ 1 + max |aᵢ| / |aₙ|`, this power of two strictly exceeds the
Cauchy bound. For `deg p ≤ 0` there are no roots to bound and the SPEC
junk value `1` is returned; no theorem reads it. -/
@[expose] def rootBound (p : ZPoly) : Dyadic :=
  match p.degree? with
  | none | some 0 => Dyadic.ofInt 1
  | some d =>
    let c := p.leadingCoeff.natAbs
    let A := (List.range d).foldl (fun acc i => max acc (p.coeff i).natAbs) 0
    twoPow (ceilLog2Nat (A / c + 2) : Int)

/-- `rootBound` on a polynomial with no degree is the junk value `1`. -/
theorem rootBound_of_degree?_none {p : ZPoly} (h : p.degree? = none) :
    rootBound p = Dyadic.ofInt 1 := by simp only [rootBound, h]

/-- `rootBound` on a degree-zero polynomial is the junk value `1`. -/
theorem rootBound_of_degree?_zero {p : ZPoly} (h : p.degree? = some 0) :
    rootBound p = Dyadic.ofInt 1 := by simp only [rootBound, h]

/-- The defining equation of `rootBound` on a polynomial of positive degree. -/
theorem rootBound_of_degree?_pos {p : ZPoly} {d : Nat} (h : p.degree? = some (d + 1)) :
    rootBound p = twoPow (ceilLog2Nat
      ((List.range (d + 1)).foldl (fun acc i => max acc (p.coeff i).natAbs) 0
        / p.leadingCoeff.natAbs + 2) : Int) := by simp only [rootBound, h]

/-- Separation precision: for squarefree `p` of degree `n ≥ 2`,
`2^{−sepPrec p} < sep(p) / 4`, where `sep(p) := min_{i ≠ j} |αᵢ − αⱼ|`
over the distinct complex roots. The contract is pairwise, hence vacuous
for `deg p ≤ 1`, which is exactly when nothing needs it (SPEC junk `0`).

Derivation of the closed form (the companion's proof script). The Mahler
separation bound (Mahler 1964) gives

  sep(p) ≥ √3 · n^{−(n+2)/2} · |disc p|^{1/2} · M(p)^{−(n−1)}.

For a squarefree integer polynomial `disc p` is a nonzero integer, so
`|disc p| ≥ 1`, and `√3 ≥ 1`; dropping both factors keeps a lower bound.
Landau's inequality bounds the Mahler measure `M(p) ≤ ‖p‖₂ ≤ L`, where
`L := coeffL2NormBound p` is the conservative integer L2-norm bound from
`HexPolyZ.Mignotte`. Hence

  sep(p) ≥ n^{−(n+2)/2} · L^{−(n−1)}
         = 2^{−((n+2)/2 · log₂ n + (n−1) · log₂ L)}.

Rounding each logarithm up: `⌈(n+2)/2 · log₂ n⌉ ≤ ⌈((n+2) · ⌈log₂ n⌉ +
1) / 2⌉`, realised by the integer form `((n + 2) * ceilLog2Nat n + 1) / 2`
(the `+1` before the halving makes the truncating division round the
half-integer exponent up), and `(n−1) · log₂ L ≤ (n − 1) · ceilLog2Nat L`.
This yields `sep(p) ≥ 2^{−(E)}` with

  E = ((n + 2) * ceilLog2Nat n + 1) / 2 + (n − 1) * ceilLog2Nat L.

Finally `sepPrec p := E + 3`, where `+2` provides the `/4` margin
(`2^{−(E+2)} = 2^{−E} / 4 ≤ sep(p) / 4`) and `+1` makes the inequality
strict. Every rounding enlarges `sepPrec`, so the bound is conservative. -/
@[expose] def sepPrec (p : ZPoly) : Nat :=
  match p.degree? with
  | none => 0
  | some n =>
    if n ≤ 1 then 0
    else
      let L := ZPoly.coeffL2NormBound p
      ((n + 2) * ceilLog2Nat n + 1) / 2 + (n - 1) * ceilLog2Nat L + 3

/-- The fixed slack added to the separation-driven bisection depth. -/
def depthSlack : Nat := 8

/-- The bisection depth at which both isolation engines stop: enough
halvings to shrink the initial interval `(−rootBound p, rootBound p]`
(width `2 · rootBound p`) below `2^{−sepPrec p}`, plus `depthSlack`.

For positive degree the depth is `sepPrec p +
(ceilLog2Dyadic (2 · rootBound p)).toNat + depthSlack`. The `.toNat` is
lossless: `2 · rootBound p ≥ 2` (a positive power of two doubled), so its
ceiling logarithm is `≥ 1 > 0`. For `deg p ≤ 0` the SPEC contract is that
`isolationDepth` returns `depthSlack`; that branch is special-cased,
since the junk `rootBound` value `1` would otherwise contribute a
spurious `ceilLog2Dyadic 2 = 1`. -/
def isolationDepth (p : ZPoly) : Nat :=
  match p.degree? with
  | none | some 0 => depthSlack
  | some _ =>
    sepPrec p + (ceilLog2Dyadic (Dyadic.ofInt 2 * rootBound p)).toNat + depthSlack

/-! Sanity checks (kept light; conformance lives in the shared
sub-project). -/

-- `twoPow` produces the exact power of two, for negative exponents too.
example : twoPow 0 = Dyadic.ofInt 1 := by decide
example : twoPow 3 = Dyadic.ofInt 8 := by decide
example : twoPow (-2) = (Dyadic.ofInt 1) >>> (2 : Int) := by decide

-- `ceilLog2Nat` is the least `k` with `m ≤ 2^k` for `m ≥ 1` (and the
-- junk value `0` at `m = 0`).
example : ceilLog2Nat 0 = 0 := by decide
example : ceilLog2Nat 1 = 0 := by decide
example : ceilLog2Nat 2 = 1 := by decide
example : ceilLog2Nat 3 = 2 := by decide
example : ceilLog2Nat 4 = 2 := by decide
example : ceilLog2Nat 5 = 3 := by decide
example : ceilLog2Nat 8 = 3 := by decide
example : ceilLog2Nat 9 = 4 := by decide

-- `ceilLog2Dyadic` is the least `e` with `x ≤ 2^e`: `1 = 2^0`,
-- `2 = 2^1`, `3/2 ≤ 2^1`, `1/4 = 2^{−2}`, `5 ≤ 2^3`.
example : ceilLog2Dyadic (Dyadic.ofInt 1) = 0 := by decide
example : ceilLog2Dyadic (Dyadic.ofInt 2) = 1 := by decide
example : ceilLog2Dyadic ((Dyadic.ofInt 3) >>> (1 : Int)) = 1 := by decide
example : ceilLog2Dyadic ((Dyadic.ofInt 1) >>> (2 : Int)) = -2 := by decide
example : ceilLog2Dyadic (Dyadic.ofInt 5) = 3 := by decide
-- A small dyadic far below `1`: `1/1024 = 2^{−10}`.
example : ceilLog2Dyadic ((Dyadic.ofInt 1) >>> (10 : Int)) = -10 := by decide

-- `rootBound` of `x² − 3`: `c = 1`, `A = 3`, `⌊A/c⌋ + 2 = 5`, `2^3 = 8`.
example : rootBound (DensePoly.ofCoeffs #[(-3 : Int), 0, 1]) = twoPow 3 := by decide
-- `rootBound` of the monic linear `x − 1`: `A = 1`, `⌊A/c⌋ + 2 = 3`, `2^2 = 4`.
example : rootBound (DensePoly.ofCoeffs #[(-1 : Int), 1]) = twoPow 2 := by decide
-- `rootBound` with `c > A` (the floor is `0`): `2x + 1` gives
-- `⌊1/2⌋ + 2 = 2`, `2^1 = 2`, still strictly above `1 + 1/2`.
example : rootBound (DensePoly.ofCoeffs #[(1 : Int), 2]) = twoPow 1 := by decide
-- `rootBound` with `c ∤ A`: `3x² + 7` gives `⌊7/3⌋ + 2 = 4`, `2^2 = 4`,
-- strictly above `1 + 7/3`.
example : rootBound (DensePoly.ofCoeffs #[(7 : Int), 0, 3]) = twoPow 2 := by decide

-- `sepPrec` is `0` below degree 2 (the pairwise contract is vacuous):
-- constants and linears alike.
example : sepPrec (DensePoly.ofCoeffs #[(7 : Int)]) = 0 := by decide
example : sepPrec (DensePoly.ofCoeffs #[(-1 : Int), 1]) = 0 := by decide
-- Hand computation for the degree-2 case `x² − 3`, verified above at the
-- component level: `n = 2`; `coeffNormSq = 9 + 0 + 1 = 10`, so
-- `L = coeffL2NormBound = ceilSqrt 10 = 4` and `ceilLog2Nat 4 = 2`;
-- `ceilLog2Nat 2 = 1`; hence
-- `sepPrec = ((2 + 2) · 1 + 1) / 2 + (2 − 1) · 2 + 3 = 2 + 2 + 3 = 7`.
-- (This equality is not a `decide` check because `coeffL2NormBound`
-- routes through the non-`@[expose]` `ceilSqrt`, which the kernel does
-- not reduce across the module boundary.)

-- `isolationDepth` junk value is `depthSlack = 8` for constants and the
-- zero polynomial.
example : isolationDepth (DensePoly.ofCoeffs #[(7 : Int)]) = 8 := by decide
example : isolationDepth (DensePoly.ofCoeffs (#[] : Array Int)) = 8 := by decide

end Hex
