/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.DistinctDegree

public section

/-!
# Degree patterns without splitting

The *degree pattern* of a monic square-free `f` over `F_p` is the multiset of
degrees of its irreducible factors.  It is strictly less information than a
factorization and it is much cheaper: the distinct-degree loop separates `f`
into one product per factor degree, and a degree-`d` product of degree `m`
records `m / d` irreducible factors of degree `d`.  Neither the Berlekamp
matrix nor any equal-degree splitting is needed.

A *partial* pattern is already useful.  After degree `d` has been separated,
every irreducible factor still in the residual has degree at least `d`, so a
residual of degree `m` carries between one and `m / d` factors.  Those two
bounds pin the factor count from both sides and tighten as `d` grows.  A caller
that only wants to know whether there are at most `t` irreducible factors is
therefore answered as soon as the factors already separated reach `t`, however
much of the polynomial is left: `scoutDegreePattern` abandons the pattern at
exactly that point, and completes it otherwise.

Two further exits keep the loop short: a unit residual is finished, and a
residual of degree below `2 * d` is itself irreducible, because it is too small
to be a product of two factors of degree at least `d`.  The loop therefore
stops at the largest factor degree rather than at `deg f`.

This is a *prediction* surface.  Nothing here is a certificate: callers that
need factors call {name}`Hex.Berlekamp.berlekampFactor`, and callers that need
the separated degree products call
{name}`Hex.Berlekamp.distinctDegreeFactor`.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/--
What a bounded distinct-degree pass learned about the irreducible factors of a
monic square-free polynomial.
-/
structure DegreePattern where
  /-- Degrees of the irreducible factors already separated, ascending. -/
  separated : Array Nat
  /-- Degree of the part not separated; `0` when the pattern is complete. -/
  residual : Nat
  /-- Every irreducible factor of the unseparated part has at least this
  degree.  Always positive. -/
  minResidualDegree : Nat
deriving Repr, DecidableEq

namespace DegreePattern

/-- A complete pattern separated the whole polynomial. -/
@[expose]
def complete (pattern : DegreePattern) : Bool :=
  pattern.residual == 0

/-- Fewest irreducible factors the polynomial can have: those already
separated, plus at least one more if anything is left. -/
@[expose]
def lowerBound (pattern : DegreePattern) : Nat :=
  pattern.separated.size + (if pattern.residual = 0 then 0 else 1)

/-- Most irreducible factors the polynomial can have: those already separated,
plus the residual degree divided by the smallest degree any unseparated factor
can have. -/
@[expose]
def upperBound (pattern : DegreePattern) : Nat :=
  pattern.separated.size + pattern.residual / pattern.minResidualDegree

end DegreePattern

/--
One degree-pattern step against the residual carrying `X^(p^d) - X mod f`.

The returned degrees are `m / d` copies of `d`, where `m` is the degree of the
gcd; for square-free input whose factors all have degree at least `d`, that gcd
is exactly the product of the degree-`d` irreducible factors of the residual.
-/
@[expose]
def degreePatternStep (d : Nat) (diff residual : FpPoly p) :
    Array Nat × FpPoly p :=
  let candidate := DensePoly.gcd residual diff
  if isUnitPolynomial candidate then
    (#[], residual)
  else
    (Array.replicate ((candidate.degree?.getD 0) / d) d, residual / candidate)

/-- Whether `k` separated factors and a nonempty residual already put the
factor count above `target`.  The residual carries at least one more factor, so
the count is at least `k + 1`, and `target ≤ k` settles it. -/
@[expose]
def aboveTarget : Option Nat → Nat → Bool
  | none, _ => false
  | some target, k => decide (target ≤ k)

/--
Fuel-bounded degree-pattern loop, maintaining the Frobenius power
`X^(p^d) mod f` across degrees exactly as `distinctDegreeFactor` does.
`prevFrob` is `X^(p^(d-1)) mod f`, so the next power is computed only when the
loop has decided to separate another degree.

With `target = some t` the loop abandons the pattern as soon as the factors it
has separated show that `f` has more than `t` of them; otherwise, and always
with `target = none`, it runs until the pattern is complete.
-/
def degreePatternLoop (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (xMod : FpPoly p) (target : Option Nat) :
    Nat → Nat → FpPoly p → FpPoly p → Array Nat → DegreePattern
  | 0, d, _, residual, found => ⟨found, residual.degree?.getD 0, max d 1⟩
  | fuel + 1, d, prevFrob, residual, found =>
      let m := residual.degree?.getD 0
      if residual.isZero || m == 0 then
        ⟨found, 0, max d 1⟩
      else if m < 2 * d then
        -- Too small to be a product of two factors of degree at least `d`.
        ⟨found.push m, 0, max d 1⟩
      else if aboveTarget target found.size then
        ⟨found, m, d⟩
      else
        let currentFrob := FpPoly.powModMonic prevFrob f hmonic p
        let (extracted, residual) :=
          degreePatternStep d (currentFrob - xMod) residual
        degreePatternLoop f hmonic xMod target fuel (d + 1) currentFrob residual
          (found ++ extracted)

/--
Separate the monic square-free `f` by irreducible-factor degree, abandoning the
pattern as soon as it is clear that `f` has more than `target` irreducible
factors.

So a `complete` result records the exact degree multiset, and an incomplete one
records that the factor count exceeds `target` -- its `lowerBound` is the
witness.  Work is bounded by one Frobenius power and one gcd per separated
degree, and by the largest factor degree overall.
-/
@[expose]
def scoutDegreePattern (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (target : Nat) : DegreePattern :=
  let xMod := FpPoly.modByMonic f FpPoly.X hmonic
  degreePatternLoop f hmonic xMod (some target) (basisSize f + 1) 1 xMod f #[]

/--
Degrees of the irreducible factors of a monic square-free `f` over `F_p`, with
multiplicity, in ascending order, obtained without splitting any equal-degree
product.

`none` when the bounded loop did not separate the whole input.  The degrees sum
to `deg f` whenever the result is `some`.
-/
@[expose]
def degreePattern? (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Option (Array Nat) :=
  let xMod := FpPoly.modByMonic f FpPoly.X hmonic
  let pattern :=
    degreePatternLoop f hmonic xMod none (basisSize f + 1) 1 xMod f #[]
  if pattern.complete then some pattern.separated else none

end Berlekamp

end Hex
