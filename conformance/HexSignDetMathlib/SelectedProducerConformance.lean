/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.SelectedProducer
public import HexRCF.RealCoefficients.CubeTwo
public import HexRealRootsMathlib.RealClosed
public import HexRealAlgebraicMathlib.Order
public meta import HexSignDet
public meta import HexRealAlgebraic
public meta import HexNumberField
public meta import HexRCF.RealCoefficients.CubeTwo
public meta import HexRCF.RealCoefficients.Coefficients

public section

/-! Selected signs over the actual cubic number field, including exact input
bindings and the generic constructor's success/correctness specialization.
Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.SelectedProducerConformance

open Hex Hex.SignDet Hex.RCF.RealCoefficients HexPolyMathlib.Interpret

abbrev generator := CubeTwo.realAlgebraic
abbrev CubicField := QAdjoin generator.toAlgebraic

def alpha : CubicField := generator.toAlgebraic.toQAdjoin

/-- Ordinary real-algebraic conversion computes the selected cubic field's
sign; the conversion retains its real embedding. -/
def fieldSign (a : CubicField) : Int := (Coefficients.ofField generator a).sign

def xPoly : DensePoly CubicField := DensePoly.ofList [0, 1]
def head : DensePoly CubicField :=
  (xPoly - DensePoly.C alpha) * (xPoly + DensePoly.C alpha)
abbrev queries : List (DensePoly CubicField) :=
  [xPoly - 1, xPoly - DensePoly.C 2, xPoly.natPow 3 - DensePoly.C 2, xPoly - 1]
def raw : RawDescriptor CubicField Nat :=
  ⟨7, head, .negInf, .posInf, [1], [1]⟩

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The derivative word selects +∛2 rather than the other root −∛2. Query
order and repetitions are retained; a nonzero cubic query vanishes there. -/
def selectedPasses : Bool :=
  match Descriptor.build fieldSign 7 raw with
  | .ok (.ok d) =>
    match d.buildSigns queries, d.buildSigns [] with
    | .ok s, .ok empty =>
      s.values.toList == [1, -1, 0, 1] && empty.values.toList == [] &&
        d.checkSigns queries s.values s.evidence &&
        !d.checkSigns queries #v[-1, -1, 0, 1] s.evidence &&
        !d.checkSigns [xPoly - DensePoly.C 2, xPoly - 1, xPoly.natPow 3 - DensePoly.C 2, xPoly - 1]
          s.values s.evidence &&
        !({raw with context := 8}).check fieldSign 7 d.evidence &&
        !({raw with head := head + 1}).check fieldSign 7 d.evidence &&
        !({raw with indices := [0]}).check fieldSign 7 d.evidence
    | _, _ => false
  | _ => false

#guard generator.toAlgebraic.p.natDegree = 3
#guard selectedPasses

abbrev rep := generator.toAlgebraic.rep
theorem real : rep.root.im = 0 :=
  (AlgebraicNumber.isReal_iff generator.toAlgebraic).mp generator.property
theorem binding : SimpleRoot.mk rep = generator.toAlgebraic.x :=
  generator.toAlgebraic.rep_mk

theorem sign_spec (a : CubicField) :
    fieldSign a = (SignType.sign (Field.value rep a) : Int) := by
  rw [fieldSign, RealAlgebraicNumber.sign_eq, Field.ofField_value]
  by_cases hn : Field.value rep a < 0
  · simp only [hn, ↓reduceIte, sign_eq_neg_one_iff.mpr hn]
    rfl
  · by_cases hz : Field.value rep a = 0
    · simp [hz]
    · have hp : 0 < Field.value rep a := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp only [hn, hz, ↓reduceIte, sign_eq_one_iff.mpr hp]
      rfl

/-- The semantic guarantee applies to every validated descriptor and every
finite query list over this genuinely cubic field, using its actual total
operations and selected real embedding. -/
theorem cubic_success (d : Descriptor CubicField Nat fieldSign 7)
    (qs : List (DensePoly CubicField)) :
    ∃ s : SelectedSigns d qs, d.buildSigns qs = .ok s ∧
      s.values.toList = signsAt (Field.value rep)
        (Field.value_eq_zero rep binding real) qs
        (d.root (Field.value rep) (Field.value_eq_zero rep binding real)
          (Field.value_one rep binding real) (Field.value_add rep binding real)
          (Field.value_sub rep binding real) (Field.value_mul rep binding real)
          (Field.value_natCast rep binding real) sign_spec) := by
  apply d.buildSigns_roots (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec
  · intro a
    apply Complex.ofReal_injective
    rw [Complex.ofReal_neg, Field.value_complex rep binding real,
      Field.value_complex rep binding real, PolyQuot.map_neg]
  · exact Field.value_inv rep binding real

/-- info: 'Hex.SignDetMathlib.SelectedProducerConformance.sign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_spec

/-- info: 'Hex.SignDetMathlib.SelectedProducerConformance.cubic_success' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cubic_success

end Hex.SignDetMathlib.SelectedProducerConformance
