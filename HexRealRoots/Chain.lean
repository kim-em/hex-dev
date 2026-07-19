/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Basic
-- Needed so `decide` over `DensePoly`/`Array` equality reduces in the kernel:
-- the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public section

/-!
The Sturm chain of an integer polynomial, built from a sign-managed
pseudo-remainder.

The chain drives the root-counting witness: `s₀ = primitivePart p`,
`s₁ = primitivePart p'`, and each further element is the negated
primitive part of the pseudo-remainder of the previous two. Every element
is a positive rational multiple of the classical signed-remainder chain of
`(p, p')` over `ℚ`, which is the invariant the companion's counting
theorem needs. Coefficients stay in `ℤ` throughout: the content division
inside `primitivePart` keeps them as small as any pseudo-remainder scheme
allows.
-/
namespace Hex

namespace ZPoly

/-- One reduction step of the sign-managed pseudo-remainder, applied to a
remainder `r` with `deg r ≥ deg g` and `g` nonconstant.

Writing `cg = lc g`, `lr = lc r`, `|cg| = if cg < 0 then -cg else cg`, and
`sign(cg)·lr = if cg < 0 then -lr else lr`, the step returns

    scale |cg| r − scale (sign(cg)·lr) (shift (deg r − deg g) g).

The two leading terms are both at degree `deg r`, with coefficients
`|cg|·lr` and `sign(cg)·lr·cg = |cg|·lr`, so they cancel exactly and the
degree strictly drops. The multiplier introduced is `|cg| > 0`, so
iterating multiplies the true rational remainder by a positive integer. -/
@[expose]
def spemStep (g r : ZPoly) : ZPoly :=
  let cg := DensePoly.leadingCoeff g
  let lr := DensePoly.leadingCoeff r
  let absCg := if cg < 0 then -cg else cg
  let sgnLr := if cg < 0 then -lr else lr
  let k := (DensePoly.degree? r).getD 0 - (DensePoly.degree? g).getD 0
  DensePoly.scale absCg r - DensePoly.scale sgnLr (DensePoly.shift k g)

/-- The reduction loop for `spem`, driven by structural `fuel`.

Each iteration stops when the remainder is zero or has degree below `deg g`;
otherwise it applies `spemStep` and recurses on one less fuel. Because every
`spemStep` drops the degree by at least one, `fuel = f.size = deg f + 1` at
the top level is always sufficient and the fuel never truncates: the loop
reaches a genuine stopping state (zero, or degree below `deg g`) before it
runs out. -/
@[expose]
def spemAux (g : ZPoly) : Nat → ZPoly → ZPoly
  | 0, r => r
  | fuel + 1, r =>
      if r.isZero then r
      else if (DensePoly.degree? r).getD 0 < (DensePoly.degree? g).getD 0 then r
      else spemAux g fuel (spemStep g r)

/-- The sign-managed pseudo-remainder of `f` by `g`.

The reduction loop repeatedly subtracts a `shift`ed, `scale`d copy of `g`
from `f`, each step multiplying by `|lc g|` (see `spemStep`), so the result
is a **positive** integer multiple of the rational remainder `f mod g`. The
accumulated multiplier is a product of `|lc g|` factors, hence positive;
this differs from the SPEC's `(lc g)^δ` pseudo-remainder (with
`δ = deg f − deg g + 1`, negated when `(lc g)^δ < 0`) only by a positive
scalar, which the `primitivePart` in `sturmChain` erases. That is why the
per-step `|lc g|` scheme meets the SPEC's `spem` contract.

Junk values, per the SPEC's input-contract convention:

- `spem f 0 = f` (the loop never starts: `g` has no degree).
- `spem f g = 0` when `g` is a nonzero constant (a constant divides
  everything, so the remainder is `0`).
- `spem f g = f` when `deg f < deg g` (the loop returns `f` on its first
  test). -/
@[expose]
def spem (f g : ZPoly) : ZPoly :=
  match DensePoly.degree? g with
  | none => f
  | some 0 => 0
  | some _ => spemAux g f.size f

/-- The chain-extension loop for `sturmChain`, driven by structural `fuel`.

Given the two most recent elements `prev`, `cur` and the accumulator `acc`,
it computes `r := spem prev cur`; if `r = 0` the chain is complete, otherwise
it pushes `next := −primitivePart r` and recurses. `primitivePart` divides by
the nonnegative content without sign-normalizing, so the explicit negation
carries exactly the SPEC's sign. The degree of `cur` strictly decreases along
the recursion, so `fuel = p.size` at the top level never truncates. -/
@[expose]
def sturmChainAux : Nat → ZPoly → ZPoly → Array ZPoly → Array ZPoly
  | 0, _, _, acc => acc
  | fuel + 1, prev, cur, acc =>
      let r := spem prev cur
      if r.isZero then acc
      else
        let next := -(primitivePart r)
        sturmChainAux fuel cur next (acc.push next)

/-- The Sturm chain of `p`.

For `deg p ≤ 0` the chain is empty (there is nothing to count). Otherwise
`s₀ = primitivePart p`, `s₁ = primitivePart p'`, and each further element is
`−primitivePart (spem sᵢ₋₁ sᵢ)` while the pseudo-remainder is nonzero. Every
element is a positive rational multiple of the classical signed-remainder
chain of `(p, p')` over `ℚ`, the invariant the counting theorem needs. The
last element is a nonzero constant exactly when `p` is squarefree of positive
degree. The structural fuel `p.size` never truncates: the degree strictly
decreases along the chain, so it terminates before the fuel is exhausted. -/
@[expose]
def sturmChain (p : ZPoly) : Array ZPoly :=
  match DensePoly.degree? p with
  | none => #[]
  | some 0 => #[]
  | some _ =>
      let s₀ := primitivePart p
      let s₁ := primitivePart (DensePoly.derivative p)
      sturmChainAux p.size s₀ s₁ #[s₀, s₁]

/-- A `decide`-checkable squarefreeness certificate: `p` has positive degree and
the last entry of its Sturm chain is a nonzero constant (`size == 1`). When this
is `true`, `p` is squarefree over `ℚ` — proved as
`squareFreeRat_of_hasSquarefreeSturmChain` in the Mathlib companion, whence a
concrete `SquareFreeRat p` is dischargeable by `by decide` on this test.

This is a one-way certificate, not a decision procedure: it returns `false` on
the zero polynomial and on nonzero constants (empty chain), even though
`SquareFreeRat` is vacuously/trivially true there. -/
@[expose]
def hasSquarefreeSturmChain (p : ZPoly) : Bool :=
  match (sturmChain p).toList.getLast? with
  | some z => z.size == 1
  | none   => false

end ZPoly

/-! Sanity checks (kept light; conformance lives in the shared
sub-project). -/

-- `sturmChain (x² − 1) = [x² − 1, x, 1]`: primitive `p`, its primitive
-- derivative `x`, and the terminal nonzero constant `1`.
example : ZPoly.sturmChain (DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    = #[DensePoly.ofCoeffs #[(-1 : Int), 0, 1],
        DensePoly.ofCoeffs #[(0 : Int), 1],
        DensePoly.ofCoeffs #[(1 : Int)]] := by decide

-- Sign management with a negative leading coefficient in `g`:
-- `f = x² + 1`, `g = −2x + 1`. The rational remainder `f mod g = 5/4`; the
-- multiplier is `|lc g| = 2` applied twice, i.e. `4`, so `spem f g = 4·(5/4)
-- = 5`, a positive multiple of the remainder.
example : ZPoly.spem (DensePoly.ofCoeffs #[(1 : Int), 0, 1])
    (DensePoly.ofCoeffs #[(1 : Int), -2]) = DensePoly.ofCoeffs #[(5 : Int)] := by decide

-- A nonzero constant and the zero polynomial both have the empty chain.
example : ZPoly.sturmChain (DensePoly.ofCoeffs #[(7 : Int)]) = #[] := by decide
example : ZPoly.sturmChain (DensePoly.ofCoeffs (#[] : Array Int)) = #[] := by decide

-- A degree-3 squarefree example, `x³ − x` (roots `−1, 0, 1`). The classical
-- Sturm chain has length 4: `[x³ − x, 3x² − 1, x, 1]`, ending in a nonzero
-- constant. (The `s₂` step: `spem (x³−x) (3x²−1) = −2x`, whose negated
-- primitive part is `x`.)
example : ZPoly.sturmChain (DensePoly.ofCoeffs #[(0 : Int), -1, 0, 1])
    = #[DensePoly.ofCoeffs #[(0 : Int), -1, 0, 1],
        DensePoly.ofCoeffs #[(-1 : Int), 0, 3],
        DensePoly.ofCoeffs #[(0 : Int), 1],
        DensePoly.ofCoeffs #[(1 : Int)]] := by decide

-- The squarefree certificate: `x⁴ − 2` and `x³ − x` pass; a nonzero constant,
-- the zero polynomial, and the non-squarefree `(x − 1)²` all fail.
example : ZPoly.hasSquarefreeSturmChain (DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 0, 1]) := by decide
example : ZPoly.hasSquarefreeSturmChain (DensePoly.ofCoeffs #[(0 : Int), -1, 0, 1]) := by decide
example : ZPoly.hasSquarefreeSturmChain (DensePoly.ofCoeffs #[(7 : Int)]) = false := by decide
example : ZPoly.hasSquarefreeSturmChain (DensePoly.ofCoeffs #[(1 : Int), -2, 1]) = false := by decide

end Hex
