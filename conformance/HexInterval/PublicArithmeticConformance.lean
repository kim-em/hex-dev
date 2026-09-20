/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval

/-!
# Public arithmetic for exact coefficient consumers

Oracle: exact rational arithmetic in Lean core; no external oracle.
Mode: always.
Covered operations:
- checked construction, singleton division, intersection and addition;
- multiplication, regularization, and zero-cut classification.
Covered properties:
- rational containment and dyadic-grid width;
- Horner containment and independently calculated cuts;
- exact cancellation, intersection openness, and outward rounding.
Covered edge cases:
- negative/zero coefficients, open zero and zero-containing intervals;
- empty intersections, huge precision, endpoint/alignment and product growth.
Only the ordinary public umbrella is imported. These checks exercise the
consumer composition without defining a second interval or Horner API.
-/

namespace Hex.Interval.PublicArithmeticConformance

private def limits : Arithmetic.PrecisionLimits :=
  { endpoint := ⟨4096, 2048⟩
    maxPrecisionMagnitude := 1024
    maxPrecisionBits := 11
    maxTemporaryBits := 8192 }

private def built : BuildResult → Option Hex.Interval
  | .ready value => some value
  | .resourceLimit _ => none

private def computed : Arithmetic.Result → Option Hex.Interval
  | .ready value => some value
  | .resourceLimit _ => none

private def singleton (n : Int) : Option Hex.Interval :=
  built (singletonWithin limits.endpoint (Dyadic.ofInt n))

/-- The caller supplies a nonzero rational denominator; interval division
itself follows Lean's total division convention at zero. -/
private def coefficient (n : Int) (d : Nat) (precision : Int) : Option Hex.Interval := do
  if d == 0 then none else do
    let numerator ← singleton n
    let denominator ← singleton d
    computed (divWithin limits precision numerator denominator)

private def contains (interval : Hex.Interval) (q : Rat) : Bool :=
  match interval.view with
  | .empty => false
  | .bounds (.finite lo ls) (.finite hi hs) =>
      (if ls then lo.toRat < q else lo.toRat ≤ q) &&
      (if hs then q < hi.toRat else q ≤ hi.toRat)
  | _ => false

private def enclosure (n : Int) (d : Nat) (p : Nat) : Bool :=
  match coefficient n d p with
  | none => false
  | some interval =>
      contains interval (mkRat n d) &&
      match interval.view with
      | .bounds (.finite lo _) (.finite hi _) =>
          hi.toRat - lo.toRat ≤ mkRat 1 (2 ^ p)
      | _ => false

#guard [0, 1, 8, 32, 128].all fun p =>
  [(-7, 3), (-1, 2), (0, 3), (1, 3), (8, 4), (17, 7)].all fun (n, d) =>
    enclosure n d p
#guard (do
  let one ← singleton 1
  let zero ← singleton 0
  let quotient ← computed (divWithin limits 8 one zero)
  pure (quotient == zero)) == some true

#guard (do
  let one ← singleton 1
  let three ← singleton 3
  pure (match divWithin limits 1000000000 one three with
    | .resourceLimit (.precision _) => true
    | _ => false)) == some true

private def interval (lo : Int) (ls : Bool) (hi : Int) (hs : Bool) :
    Option Hex.Interval :=
  built (betweenWithin limits.endpoint (Dyadic.ofInt lo) ls (Dyadic.ofInt hi) hs)

#guard (do
  let a ← interval 0 false 2 true
  let b ← interval 0 true 2 false
  let c ← built (intersectWithin limits.endpoint a b)
  pure (c.view == .bounds (.finite 0 true) (.finite 2 true))) == some true

#guard (do
  let a ← interval 0 false 1 true
  let b ← interval 1 false 2 false
  let c ← built (intersectWithin limits.endpoint a b)
  pure (c.view == .empty)) == some true

-- (x / 3 - 1/2) * x + 1/4 on [1,2]. The coefficient cuts are
-- 21845/65536 and 21846/65536. Interval Horner therefore gives lower
-- 2*(21845/65536 - 1/2) + 1/4 = -5462/65536 and upper
-- 2*(2*21846/65536 - 1/2) + 1/4 = 38232/65536.
#guard (do
  let x ← interval 1 false 2 false
  let a ← coefficient 1 3 16
  let b ← coefficient (-1) 2 16
  let c ← coefficient 1 4 16
  let ax ← computed (mulWithin limits.endpoint a x)
  let axb ← built (addWithin limits.endpoint ax b)
  let axbx ← computed (mulWithin limits.endpoint axb x)
  let result ← built (addWithin limits.endpoint axbx c)
  pure (result.view == .bounds
    (.finite (Dyadic.ofIntWithPrec (-5462) 16) false)
    (.finite (Dyadic.ofIntWithPrec 38232 16) false) &&
    [4, 5, 6, 7, 8].all fun n =>
      let q := mkRat n 4
      contains result ((q / 3 - mkRat 1 2) * q + mkRat 1 4))) == some true

#guard (do
  let a ← singleton 7
  let b ← singleton (-7)
  let c ← built (addWithin limits.endpoint a b)
  pure (c.view == .bounds (.finite 0 false) (.finite 0 false))) == some true

#guard (do
  let a ← interval (-1) true 1 true
  let z ← singleton 0
  let c ← computed (mulWithin limits.endpoint a z)
  pure (c.view == .bounds (.finite 0 false) (.finite 0 false))) == some true

#guard (do
  let positive ← interval 0 true 1 false
  let negative ← interval (-1) false 0 true
  match positive.view, negative.view with
  | .bounds lo _, .bounds _ hi =>
      pure (Raw.strictlyPositive lo && Raw.strictlyNegative hi)
  | _, _ => none) == some true

#guard Raw.strictlyPositive (.finite 0 true)
#guard !Raw.strictlyPositive (.finite 0 false)
#guard Raw.strictlyNegative (.finite 0 true)
#guard !Raw.strictlyNegative (.finite 0 false)
#guard !Raw.strictlyPositive (.finite (-1) false)
#guard !Raw.strictlyNegative (.finite 1 false)

-- 1/3 rounded on the 2^-8 grid is [85/256, 86/256]. Moving to
-- the 2^-2 grid gives (1/4, 1/2), with both moved endpoints strict.
#guard (do
  let a ← coefficient 1 3 8
  let b ← computed (regularizeWithin limits 2 a)
  let c ← computed (regularizeWithin limits 2 b)
  pure (b == c && b.view == .bounds
    (.finite (Dyadic.ofIntWithPrec 1 2) true)
    (.finite (Dyadic.ofIntWithPrec 1 1) true))) == some true

private def far : Dyadic := .ofOdd 1 1000000000 (by decide)
#guard match betweenWithin limits.endpoint 1 false far false with
  | .resourceLimit cost => !cost.lower.allowed limits.endpoint || !cost.upper.allowed limits.endpoint
  | _ => false

-- Both endpoint heights pass; this failure is specifically alignment.
#guard match betweenWithin limits.endpoint 1 false
    (Dyadic.ofIntWithPrec 1 3000) false with
  | .resourceLimit cost => cost.lower.allowed limits.endpoint &&
      cost.upper.allowed limits.endpoint && cost.alignmentShift == 3000
  | _ => false

#guard (do
  let a ← singleton 255
  pure (match mulWithin ⟨8, 0⟩ a a with
    | .resourceLimit (.growth _) => true
    | _ => false)) == some true

end Hex.Interval.PublicArithmeticConformance
