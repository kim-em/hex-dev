/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Roots
public import HexNumberField.IntegerRoots
public section

/-! Convert canonical numbers to one chosen or computed common number field. -/
namespace Hex.QAdjoin

/-- Consecutive powers used by coordinate recovery. Certification cannot fail. -/
@[expose] def powerTable (a : AlgebraicNumber) : Array AlgebraicNumber :=
  (AlgebraicPoly.Common.powers? a (2 * a.p.natDegree - 2)).getD
    (Hex.panicWith #[] "QAdjoin: power table certification failed")

/-- Express `b` in the power basis of `a`, or return `none` when `b ∉ ℚ(a)`.
This does not enlarge the chosen field. A real generator rejects nonreal
values before coordinate recovery. -/
@[expose] def ofAlgebraic? (a b : AlgebraicNumber) : Option (QAdjoin a) :=
  if a.isReal && !b.isReal then none
  else AlgebraicPoly.Common.coordinates? a b (powerTable a)

/-- Convert a collection to one chosen field, sharing its power table.
The output preserves input order and records nonmembership separately for each entry. -/
@[expose] def ofAlgebraics? (a : AlgebraicNumber) (bs : Array AlgebraicNumber) :
    Array (Option (QAdjoin a)) :=
  let powers := powerTable a
  bs.map fun b => if a.isReal && !b.isReal then none
    else AlgebraicPoly.Common.coordinates? a b powers

/-- One primitive generator and the input values in its rational power basis.
The public `entries` name describes arbitrary input collections independently of
`AlgebraicPoly.Common.Presentation`, whose `coefficients` field serves polynomial construction. -/
structure Presentation where
  generator : AlgebraicNumber
  entries : Array (QAdjoin generator)

/-- Find one number field containing every input, preserving order and duplicates.
Empty and all-zero collections use `ℚ(0) = ℚ`. The primitive-element search can
be expensive; subsequent arithmetic in the resulting `QAdjoin` uses rational
coordinates without further root isolation. -/
@[expose] def common (bs : Array AlgebraicNumber) : Presentation :=
  if bs.all (fun b => b.isZero) then
    ⟨0, bs.map fun _ => 0⟩
  else
    match AlgebraicPoly.Common.presentation? bs with
    | some p => ⟨p.generator, p.coefficients⟩
    | none => Hex.panicWith ⟨0, #[]⟩ "QAdjoin.common: certification failed"

end Hex.QAdjoin
