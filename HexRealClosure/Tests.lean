/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Basic

public section

namespace Hex.RealClosure.Tests

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def head : DensePoly Rat :=
  (DensePoly.ofCoeffs #[-2, 0, 1]) * (x - DensePoly.C 3)

private def raw : SignDet.RawDescriptor Rat Nat :=
  { context := 7, head, lower := .finite 1, upper := .finite 2,
    indices := [], signs := [] }

/-- The interval selects √2 from a squarefree, reducible polynomial. -/
private def sample : Option (Int × Int × Int × Int × Int × Int) := do
  let d ← Root.validate 7 raw
  let a : Expression d := ⟨x⟩
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let equation : Expression d := ⟨head⟩
  let sa ← a.sign?.toOption
  let sb ← below.sign?.toOption
  let se ← equation.sign?.toOption
  let inv? ← below.inverse?.toOption
  let inv ← inv?
  let si ← inv.sign?.toOption
  let squareMinusTwo := Expression.sub (Expression.mul a a)
    (Expression.ofPoly (DensePoly.C 2))
  let sz ← squareMinusTwo.sign?.toOption
  let expectedInverse : Expression d :=
    ⟨DensePoly.scale (-(1 / 7 : Rat)) (x + DensePoly.C 3)⟩
  let same ← (Expression.sub inv expectedInverse).sign?.toOption
  return (sa, sb, se, si, sz, same)

#eval sample
#guard sample == some (1, -1, 0, -1, 0, 0)
private def stale : Bool := (Root.validate 8 raw).isNone
#eval stale
#guard stale
example : Root.validate 8 raw = none :=
  Root.validate_context raw (by decide)

private def nonmonic : Option (Int × Int × Int × Int) := do
  let d ← Root.validate 9 { raw with context := 9, head := DensePoly.scale 2 head }
  let a : Expression d := ⟨x⟩
  let sa ← a.sign?.toOption
  let sz ← (Expression.sub a a).sign?.toOption
  let scalar ← (Expression.ofPoly (d := d) (DensePoly.C 6)).sign?.toOption
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let inv? ← below.inverse?.toOption
  let inv ← inv?
  let si ← inv.sign?.toOption
  return (sa, sz, scalar, si)

#eval nonmonic
#guard nonmonic == some (1, 0, 1, -1)

private def zeroInverse : Option (Bool × Bool) := do
  let d ← Root.validate 7 raw
  let literal ← (Expression.zero (d := d)).inverse?.toOption
  let selected ← (Expression.ofPoly (d := d) (x * x - DensePoly.C 2)).inverse?.toOption
  return (literal.isNone, selected.isNone)

#eval zeroInverse
#guard zeroInverse == some (true, true)

private def splitDegree : Nat :=
  (DensePoly.gcd head (x - DensePoly.C 3)).natDegree

#eval splitDegree
#guard splitDegree == 1

private def constantGcd : Option (Nat × Int × Int) := do
  let d ← Root.validate 7 raw
  let a : Expression d := ⟨x⟩
  let inv? ← a.inverse?.toOption
  let inv ← inv?
  let si ← inv.sign?.toOption
  let expected : Expression d := ⟨DensePoly.scale (1 / 2 : Rat) x⟩
  let diff ← (Expression.sub inv expected).sign?.toOption
  return (a.inverseFactor.1.natDegree, si, diff)

#eval constantGcd
#guard constantGcd == some (0, 1, 0)

private def splitTransport : Option (Int × Int × Int × Int × Nat × Nat) := do
  let d ← Root.validate 7 raw
  let q := x - DensePoly.C 3
  let below : Expression d := ⟨q⟩
  let r? ← (below.split? 8 (.finite 1) (.finite 2)).toOption
  let r ← r?
  let a : Expression d := ⟨x⟩
  let inv? ← below.inverse?.toOption
  let inv ← inv?
  let oldSign ← a.sign?.toOption
  let newSign ← (Expression.transport r.encoding a).sign?.toOption
  let reboundSign ← (Expression.refine r a).sign?.toOption
  let inverseSign ← (Expression.refine r inv).sign?.toOption
  return (oldSign, newSign, reboundSign, inverseSign,
    r.binding.target.raw.head.natDegree, r.binding.target.raw.context)

#eval splitTransport
#guard splitTransport == some (1, 1, 1, -1, 2, 8)

/-- A cofactor with no selected root cannot produce a refinement. -/
private def rejectedSplit : Option Bool := do
  let d ← Root.validate 7 raw
  let selectedZero : Expression d := ⟨x * x - DensePoly.C 2⟩
  let result ← (selectedZero.split? 8 (.finite 1) (.finite 2)).toOption
  return result.isNone

#eval rejectedSplit
#guard rejectedSplit == some true

/-- Splitting a non-monic definition retains its leading scalar. -/
private def nonmonicSplit : Option (Rat × Nat × Int) := do
  let d ← Root.validate 9 { raw with context := 9, head := DensePoly.scale 2 head }
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let r? ← (below.split? 10 (.finite 1) (.finite 2)).toOption
  let r ← r?
  let sa ← (Expression.refine r (Expression.ofPoly x)).sign?.toOption
  return (r.binding.target.raw.head.leadingCoeff,
    r.binding.target.raw.head.natDegree, sa)

#eval nonmonicSplit
#guard nonmonicSplit == some (2, 2, 1)

/-- The selected-root cofactor yields a nonzero constant Bézout result. -/
private def splitBezout : Option (Nat × Rat) := do
  let d ← Root.validate 7 raw
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let eg := DensePoly.xgcdLeft below.polynomial below.inverseFactor.2
  return (eg.gcd.natDegree, eg.gcd.leadingCoeff)

#eval splitBezout
#guard splitBezout == some (0, 7)

/-- Inverting a representative above the defining degree exercises the first
Euclidean reduction before the constant gcd is found. -/
private def highDegreeInverse : Option (Nat × Int × Int) := do
  let d ← Root.validate 7 raw
  let a : Expression d := ⟨x * x * x⟩
  let inv? ← a.inverse?.toOption
  let inv ← inv?
  let si ← inv.sign?.toOption
  let expected : Expression d := ⟨DensePoly.scale (1 / 4 : Rat) x⟩
  let diff ← (Expression.sub inv expected).sign?.toOption
  return (a.polynomial.natDegree, si, diff)

#eval highDegreeInverse
#guard highDegreeInverse == some (3, 1, 0)

end Hex.RealClosure.Tests
