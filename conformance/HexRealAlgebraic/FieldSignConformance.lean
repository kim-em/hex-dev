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
public import HexRealAlgebraicMathlib.FieldSign

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

/-- Exercise the exact fallback on a nonconstant coordinate too small for both probes. -/
private def fallbackPass : Bool :=
  let input := ZPoly.rootNear #p[-2, 0, 0, 1] 1.3
  if real : input.isReal = true then
    let generator := ofAlgebraic input real
    let value := (input.toQAdjoin - 1) ^ 80
    let rep := input.rep
    let first := PolyQuot.evalRatBall value.coeffs rep.1.square
      (Max.max (16 : Int) rep.1.square.prec)
    let second := (value.approx rep input.rep_mk 32).2
    value.coeffs.size > 1 && ballSign? first == none && ballSign? second == none &&
      generator.signField value == 1
  else false

#guard fallbackPass

/-- info: 'Hex.RealAlgebraicNumber.signField_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signField_spec

/-- info: 'Hex.RealAlgebraicNumber.signField_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signField_eq

end Hex.RealAlgebraicNumber.FieldSignConformance
