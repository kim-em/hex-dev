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
private def sample : Option (Int × Int × Int × Int × Int) := do
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
  return (sa, sb, se, si, sz)

#eval sample
#guard sample == some (1, -1, 0, -1, 0)
private def stale : Bool := (Root.validate 8 raw).isNone
#eval stale
#guard stale
example : Root.validate 8 raw = none :=
  Root.validate_context raw (by decide)

private def nonmonic : Option (Int × Int) := do
  let d ← Root.validate 9 { raw with context := 9, head := DensePoly.scale 2 head }
  let a : Expression d := ⟨x⟩
  let sa ← a.sign?.toOption
  let sz ← (Expression.sub a a).sign?.toOption
  return (sa, sz)

#eval nonmonic
#guard nonmonic == some (1, 0)

private def zeroInverse : Option Bool := do
  let d ← Root.validate 7 raw
  let result ← (Expression.ofPoly (d := d) head).inverse?.toOption
  return result.isNone

#eval zeroInverse
#guard zeroInverse == some true

private def splitDegree : Nat :=
  (DensePoly.gcd head (x - DensePoly.C 3)).natDegree

#eval splitDegree
#guard splitDegree == 1

private def splitTransport : Option (Int × Int × Nat) := do
  let d ← Root.validate 7 raw
  let q := x - DensePoly.C 3
  let g := DensePoly.monicize (DensePoly.gcd head q)
  let h := (DensePoly.divMod head g).1
  let r? ← (d.buildReencoding h (.finite 1) (.finite 2)).toOption
  let r ← r?
  let a : Expression d := ⟨x⟩
  let oldSign ← a.sign?.toOption
  let newSign ← (Expression.transport r a).sign?.toOption
  return (oldSign, newSign, r.target.raw.head.natDegree)

#eval splitTransport
#guard splitTransport == some (1, 1, 2)

end Hex.RealClosure.Tests
