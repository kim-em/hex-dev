/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealAlgebraic.FieldSign
public meta import HexRealAlgebraic.FieldSign
public import HexRealAlgebraic.Roots
public meta import HexRealAlgebraic.Roots
public import HexNumberField.CommonField
public meta import HexNumberField.CommonField

namespace Hex.RealAlgebraicNumber.FieldSignConformance

private def quarticPass : Bool :=
  (do
    let a ← sqrt? (ofRat 2)
    let b ← sqrt? (ofRat 3)
    let common := QAdjoin.common #[a.toAlgebraic, b.toAlgebraic]
    if real : common.generator.isReal = true then
      let generator := ofAlgebraic common.generator real
      let left ← common.entries[0]?
      let right ← common.entries[1]?
      let values : Array (QAdjoin common.generator) :=
        #[0, 1, -1, left, right, left - right, right - left, left + right,
          (left - right) ^ 20]
      let results ← values.mapM fun value => do
        let native ← ofAlgebraic? value.toAlgebraicNumber
        return generator.signField value == native.sign
      return common.generator.p.natDegree == 4 && results.all id
    else none) == some true

#guard quarticPass

private def selectedPass (input : AlgebraicNumber) : Bool :=
  (do
    if real : input.isReal = true then
      let generator := ofAlgebraic input real
      let x := input.toQAdjoin
      let values : Array (QAdjoin input) := #[0, 1, -1, x, -x, x - 1, x + 2,
        x ^ 3 - 2, (x - 1) ^ 80]
      let signs ← values.mapM fun value => do
        let native ← ofAlgebraic? value.toAlgebraicNumber
        return generator.signField value == native.sign
      return signs.all id
    else none) == some true

#guard selectedPass (ZPoly.rootNear #p[-2, 0, 1] 1.4)
#guard selectedPass (ZPoly.rootNear #p[-2, 0, 1] (-1.4))
#guard selectedPass (ZPoly.rootNear #p[-2, 0, 0, 1] 1.3)

end Hex.RealAlgebraicNumber.FieldSignConformance
