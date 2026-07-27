/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ

public section

/-!
Basic data for complex root isolation: the dyadic-square geometry the
subdivision algorithm works on, the Gaussian-dyadic arithmetic its
witnesses are built from, and the small dyadic helpers (`abs`, `min`,
`max`, ceiling base-2 logarithms) the rest of the library uses.

A `DyadicSquare` is an axis-aligned square in the complex plane with a
Gaussian-dyadic centre and power-of-two half-width `2^{−prec}`; its
circumscribed disc has radius `2^{−prec}·√2`. `GaussDyadic` is `ℤ[i]`
extended to dyadic coefficients: exact centres, exact Taylor
coefficients, exact witness comparisons. `encSquare` computes the
smallest power-of-two square containing a component of squares, and
`HasOnlySimpleRoots` decides squarefreeness over `ℚ[x]`.

Every value here is exact: dyadic comparisons and integer counts, no
floats and no error budget. `Dyadic` comes from Lean core
(`Init.Data.Dyadic`); the helpers below live in namespace `Hex` (and
`Hex.Dyadic`) so they never shadow the core `Dyadic` API, and must be
called fully qualified. All data-level defs are `@[expose]` so kernel
`decide` reduces the witnesses across module boundaries.
-/
namespace Hex

/-! ### Dyadic helpers

`Dyadic` in Lean core carries no `abs`/`min`/`max`; these supply them.
They are placed in namespace `Hex.Dyadic`, so `Hex.Dyadic.abs` etc.
name them; a bare `Dyadic.abs` on a term would instead try (and fail)
to resolve against the core `Dyadic` namespace by dot notation. -/

/-- Absolute value of a dyadic number. -/
@[expose] def Dyadic.abs (x : Dyadic) : Dyadic := if x < 0 then -x else x

/-- The larger of two dyadic numbers. -/
@[expose] def Dyadic.max (x y : Dyadic) : Dyadic := if x ≤ y then y else x

/-- The smaller of two dyadic numbers. -/
@[expose] def Dyadic.min (x y : Dyadic) : Dyadic := if x ≤ y then x else y

/-- Smallest `t` with `n ≤ 2^t` (junk `0` for `n ≤ 1`). -/
@[expose] def ceilLog2 (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

/-- For `x > 0`: smallest `t : Int` with `x ≤ 2^t`; junk `0` for `x ≤ 0`.
    For `x = n·2^{−k}` with odd `n > 0`: `ceilLog2 n − k`. -/
@[expose] def Dyadic.ceilLog2 : Dyadic → Int
  | .zero => 0
  | .ofOdd n k _ => if n < 0 then 0 else (Hex.ceilLog2 n.toNat : Int) - k

/-! ### Gaussian dyadics

`GaussDyadic` is a pair `(re, im)` of dyadic numbers standing for the
Gaussian-dyadic number `re + im·i`. It carries no typeclass instances:
declaring, say, `Add (Dyadic × Dyadic)` would leak componentwise
addition onto every `Dyadic × Dyadic` pair in the codebase. The
operations below are therefore named functions in the `GaussDyadic`
namespace. -/

/-- A Gaussian dyadic number `re + im·i`, represented as the pair
    `(re, im)`. -/
abbrev GaussDyadic := Dyadic × Dyadic

namespace GaussDyadic

/-- The Gaussian dyadic `i + 0·i` for an integer `i`. -/
@[expose] def ofInt (i : Int) : GaussDyadic := (Dyadic.ofInt i, 0)

/-- Sum of two Gaussian dyadics, `(a+bi) + (c+di) = (a+c) + (b+d)i`. -/
@[expose] def add (z w : GaussDyadic) : GaussDyadic := (z.1 + w.1, z.2 + w.2)

/-- Difference of two Gaussian dyadics, `(a+bi) − (c+di) = (a−c) + (b−d)i`. -/
@[expose] def sub (z w : GaussDyadic) : GaussDyadic := (z.1 - w.1, z.2 - w.2)

/-- Complex conjugate `a − b·i` of `a + b·i`. -/
@[expose] def conj (z : GaussDyadic) : GaussDyadic := (z.1, -z.2)

/-- Product of two Gaussian dyadics,
    `(a+bi)(c+di) = (ac − bd) + (ad + bc)i`. -/
@[expose] def mul (z w : GaussDyadic) : GaussDyadic :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The squared modulus `a² + b²` of `a + b·i`, an exact dyadic. -/
@[expose] def normSq (z : GaussDyadic) : Dyadic := z.1 * z.1 + z.2 * z.2

/-- The squared distance `|z − w|²` between two Gaussian dyadics, an
    exact dyadic. -/
@[expose] def distSq (z w : GaussDyadic) : Dyadic := normSq (sub z w)

end GaussDyadic

/-! ### Dyadic squares

A `DyadicSquare` is the closed axis-aligned square centred at
`re + im·i` with half-width `2^{−prec}`. Its circumscribed disc (the
region the Pellet tests run on) has radius `2^{−prec}·√2`. `prec` is an
`Int`: the initial Cauchy-bound square has `prec` negative whenever the
root bound exceeds 1. -/

/-- A closed axis-aligned dyadic square in the complex plane: centre
    `re + im·i`, half-width `2^{−prec}`, circumscribed disc radius
    `2^{−prec}·√2`. -/
structure DyadicSquare where
  /-- Real part of the centre. -/
  re : Dyadic
  /-- Imaginary part of the centre. -/
  im : Dyadic
  /-- Base-2 exponent of the half-width `2^{−prec}`. -/
  prec : Int
deriving DecidableEq

/-- The Gaussian-dyadic centre `re + im·i` of the square. -/
@[expose] def DyadicSquare.center (s : DyadicSquare) : GaussDyadic := (s.re, s.im)

/-- The half-width `2^{−prec}` of the square, an exact dyadic. -/
@[expose] def DyadicSquare.halfWidth (s : DyadicSquare) : Dyadic := .ofIntWithPrec 1 s.prec

/-- The circumscribed discs of `s` and `t` intersect (closed discs):
    `distSq centres ≤ (r_s + r_t)²` with `r = √2·2^{−prec}`, so
    `(r_s + r_t)² = 2·4^{−p_s} + 2·4^{−p_t} + 4·2^{−p_s−p_t}`, all exact dyadics. -/
@[expose] def DyadicSquare.discsMeet (s t : DyadicSquare) : Bool :=
  let a : Dyadic := .ofIntWithPrec 1 (2 * s.prec)      -- 4^{−p_s}
  let b : Dyadic := .ofIntWithPrec 1 (2 * t.prec)      -- 4^{−p_t}
  let c : Dyadic := .ofIntWithPrec 1 (s.prec + t.prec) -- 2^{−p_s−p_t}
  let rhs : Dyadic := (2 : Dyadic) * a + (2 : Dyadic) * b + (4 : Dyadic) * c
  decide (GaussDyadic.distSq s.center t.center ≤ rhs)

/-- The circumscribed disc of `s` contains the Gaussian-dyadic point `z`,
including boundary contact. Squaring the radius removes the irrational `√2`,
so the test is one exact dyadic comparison. -/
@[expose] def DyadicSquare.discContains (s : DyadicSquare) (z : GaussDyadic) : Bool :=
  let radiusSq : Dyadic := (2 : Dyadic) * .ofIntWithPrec 1 (2 * s.prec)
  decide (GaussDyadic.distSq s.center z ≤ radiusSq)

/-- `inner`'s circumscribed disc is contained in `outer`'s:
    `r_i ≤ r_o` (i.e. `outer.prec ≤ inner.prec`) and
    `distSq centres ≤ (r_o − r_i)² = 2·4^{−p_o} + 2·4^{−p_i} − 4·2^{−p_o−p_i}`. -/
@[expose] def DyadicSquare.discInside (inner outer : DyadicSquare) : Bool :=
  let a : Dyadic := .ofIntWithPrec 1 (2 * outer.prec)          -- 4^{−p_o}
  let b : Dyadic := .ofIntWithPrec 1 (2 * inner.prec)          -- 4^{−p_i}
  let c : Dyadic := .ofIntWithPrec 1 (outer.prec + inner.prec) -- 2^{−p_o−p_i}
  let rhs : Dyadic := (2 : Dyadic) * a + (2 : Dyadic) * b - (4 : Dyadic) * c
  decide (outer.prec ≤ inner.prec ∧ GaussDyadic.distSq inner.center outer.center ≤ rhs)

/-- `inner`'s closed square is contained in `outer`'s closed square:
    `max |Δre| |Δim| + 2^{−p_i} ≤ 2^{−p_o}` (exact dyadics). -/
@[expose] def DyadicSquare.squareInside (inner outer : DyadicSquare) : Bool :=
  let dre : Dyadic := Hex.Dyadic.abs (inner.re - outer.re)
  let dim : Dyadic := Hex.Dyadic.abs (inner.im - outer.im)
  decide (Hex.Dyadic.max dre dim + inner.halfWidth ≤ outer.halfWidth)

/-! ### Enclosing squares, balls, and components -/

/-- A complex ball with dyadic data, the output type of numerical
    evaluation here and in `hex-number-field`. -/
structure DyadicComplexBall where
  /-- Real part of the centre. -/
  re     : Dyadic
  /-- Imaginary part of the centre. -/
  im     : Dyadic
  /-- Radius of the ball. -/
  radius : Dyadic

/-- An uncertified component in the refinement worklist: an
    edge-connected set of grid squares at a common `prec`, plus the root
    count of its most recently certified ancestor. `candidateK` only
    selects the order of the speculative Newton step; it is never
    trusted, since every output is re-certified. -/
structure Component where
  /-- The component's grid squares: nonempty, common `prec`,
      edge-connected. -/
  squares    : Array DyadicSquare
  /-- Root count carried from the most recently certified ancestor;
      an untrusted hint for step ordering. -/
  candidateK : Nat

/-- Exact axis-aligned bounds used to enclose an array of dyadic squares. -/
structure SquareBounds where
  /-- Lower real-coordinate bound. -/
  xmin : Dyadic
  /-- Upper real-coordinate bound. -/
  xmax : Dyadic
  /-- Lower imaginary-coordinate bound. -/
  ymin : Dyadic
  /-- Upper imaginary-coordinate bound. -/
  ymax : Dyadic

/-- The exact coordinate bounds contributed by one dyadic square. -/
@[expose] def DyadicSquare.bounds (s : DyadicSquare) : SquareBounds :=
  let hw := s.halfWidth
  ⟨s.re - hw, s.re + hw, s.im - hw, s.im + hw⟩

/-- Extend exact coordinate bounds by one dyadic square. -/
@[expose] def SquareBounds.merge (b : SquareBounds) (s : DyadicSquare) : SquareBounds :=
  let sb := s.bounds
  ⟨Hex.Dyadic.min b.xmin sb.xmin, Hex.Dyadic.max b.xmax sb.xmax,
    Hex.Dyadic.min b.ymin sb.ymin, Hex.Dyadic.max b.ymax sb.ymax⟩

/-- Add one square to an optional bounding box. -/
@[expose] def SquareBounds.extend (b : Option SquareBounds)
    (s : DyadicSquare) : Option SquareBounds :=
  match b with
  | none => some s.bounds
  | some b => some (b.merge s)

/-- Exact bounding box of an array of dyadic squares. -/
@[expose] def boundingBox (squares : Array DyadicSquare) : Option SquareBounds :=
  squares.foldl (init := none) SquareBounds.extend

/-- The smallest square with power-of-two half-width, centred at the
    bounding-box centre, containing every square. Junk `⟨0,0,0⟩` on the
    empty array (callers keep components nonempty).

    Each square contributes its own half-width to the bounding box
    (robust to mixed `prec`), the centre is the exact midpoint of the
    box (a right shift by one bit), and the result `prec` is chosen so
    that its half-width `2^{−q}` is the smallest power of two at least
    the box half-width. On a single square input this returns that
    square exactly. -/
@[expose] def encSquare (squares : Array DyadicSquare) : DyadicSquare :=
  match boundingBox squares with
  | none => ⟨0, 0, 0⟩
  | some b =>
      let cx := (b.xmin + b.xmax) >>> (1 : Int)
      let cy := (b.ymin + b.ymax) >>> (1 : Int)
      let w := Hex.Dyadic.max ((b.xmax - b.xmin) >>> (1 : Int))
        ((b.ymax - b.ymin) >>> (1 : Int))
      let q := -(Hex.Dyadic.ceilLog2 w)
      ⟨cx, cy, q⟩

/-! ### Squarefreeness -/

/-- `p` has only simple complex roots: the executable rational gcd of
    `p` and `p'` is constant. Defeq to `ZPoly.SquareFreeRat`; the
    companion relates it to `Squarefree` (for `p ≠ 0`). -/
@[expose] def HasOnlySimpleRoots (p : ZPoly) : Prop := ZPoly.SquareFreeRat p

instance (p : ZPoly) : Decidable (HasOnlySimpleRoots p) :=
  inferInstanceAs
    (Decidable ((DensePoly.gcd (ZPoly.toRatPoly p)
      (DensePoly.derivative (ZPoly.toRatPoly p))).size ≤ 1))

end Hex
