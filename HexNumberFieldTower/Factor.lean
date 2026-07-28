/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Embed
public import HexNumberFieldTower.FactorRaw
public meta import HexNumberFieldTower.Embed
public meta import HexNumberFieldTower.FactorRaw

public section

/-!
# Checked fixed-tower polynomial factorization

Runtime Yun and recursive Trager machinery lives in `FactorRaw`; this module
re-indexes its candidates by a certified public `NumberTower` and performs the
single full executable certificate replay.
-/
namespace Hex.NumberTower

namespace Factor

/-- Checked Yun decomposition in a fixed tower. -/
@[expose]
def yun? (T : NumberTower) (f : Poly T) : Option (Array (Poly T × Nat)) :=
  let input := f.toArray.map coeffs
  let components := yunRaw T.levels.toList input
  if checkYun T.levels.toList input components then
    some <| components.map fun component =>
      (DensePoly.ofCoeffs (component.1.map (ofCoeffs T)), component.2)
  else
    none

#guard
    match yun? rat (0 : Poly rat) with
    | some components => components.isEmpty
    | none => false

end Factor

/-- Reconstruct and recursively certify a proposed public factorization. -/
@[expose]
def checkFactorization {T : NumberTower} (f : Poly T) (scalar : Elem T)
    (factors : Array (Poly T × Nat)) : Bool :=
  Factor.check T.levels.toList
    (f.toArray.map coeffs) (coeffs scalar)
    (factors.map fun factor =>
      (factor.1.toArray.map coeffs, factor.2))

/-- A checked complete factorization in a fixed tower. -/
structure Factorization (T : NumberTower) (f : Poly T) where
  scalar : Elem T
  factors : Array (Poly T × Nat)
  checked : checkFactorization f scalar factors = true

/-- Complete irreducible factorization with multiplicity. -/
def factor? (T : NumberTower) (f : Poly T) : Option (Factorization T f) := do
  let raw ← Factor.factorRaw? T.levels.toList (f.toArray.map coeffs)
  let scalar := ofCoeffs T raw.scalar
  let factors := raw.factors.map fun factor =>
    (DensePoly.ofCoeffs (factor.1.map (ofCoeffs T)), factor.2)
  if h : checkFactorization f scalar factors then
    some ⟨scalar, factors, h⟩
  else
    none

/-! Compiled public dependent-result regression. -/

private def factorSqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def factorSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def factorSqrtTwoRep : RefinedIsolation factorSqrtTwoPoly :=
  ⟨⟨factorSqrtTwoSquare, by decide⟩, by decide⟩

private def factorSqrtTwoRoot : SimpleRoot factorSqrtTwoPoly :=
  SimpleRoot.mk factorSqrtTwoRep

#guard
    if hirred : ZPoly.isIrreducible factorSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible factorSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots factorSqrtTwoPoly then
        let extension := ofQAdjoin (x := factorSqrtTwoRoot)
          hsimple factorSqrtTwoRep rfl
        let f : Poly extension.tower := DensePoly.ofCoeffs
          #[ofRat extension.tower (-2), 0, 1]
        match factor? extension.tower f,
            factor? extension.tower 0,
            factor? extension.tower (DensePoly.C (ofRat extension.tower 5)) with
        | some result, some zeroResult, some constantResult =>
            result.factors.size = 2 &&
              coeffs result.scalar = #[1, 0] &&
              zeroResult.factors.isEmpty &&
              isZero zeroResult.scalar &&
              constantResult.factors.isEmpty &&
              coeffs constantResult.scalar = #[5, 0]
        | _, _, _ => false
      else
        false
    else
      false

end Hex.NumberTower
