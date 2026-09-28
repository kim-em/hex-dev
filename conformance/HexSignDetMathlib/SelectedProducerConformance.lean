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
        !raw.checkSigns fieldSign 8 queries s.values s.evidence &&
        !({raw with context := 8}).checkSigns fieldSign 8 queries s.values s.evidence &&
        !({raw with head := head + 1}).checkSigns fieldSign 7 queries s.values s.evidence &&
        !({raw with indices := [0]}).checkSigns fieldSign 7 queries s.values s.evidence &&
        !({raw with indices := [2]}).checkSigns fieldSign 7 queries s.values s.evidence &&
        !({raw with signs := [-1]}).checkSigns fieldSign 7 queries s.values s.evidence &&
        !({raw with context := 8}).check fieldSign 7 d.evidence &&
        !({raw with context := 8}).check fieldSign 8 d.evidence &&
        !({raw with head := head + 1}).check fieldSign 7 d.evidence &&
        !({raw with indices := [0]}).check fieldSign 7 d.evidence &&
        !({raw with indices := [2]}).check fieldSign 7 d.evidence
    | _, _ => false
  | _ => false

#guard generator.toAlgebraic.p.natDegree = 3
#guard ({raw with indices := [2]}).wellFormed
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard selectedPasses

/-- Finite bounds isolate the same positive cubic root. Zero and constant
queries retain their signs; another valid interval cannot reuse this replay. -/
def finitePasses : Bool :=
  let bounded : RawDescriptor CubicField Nat :=
    {raw with lower := .finite 1, upper := .finite 2}
  let qs : List (DensePoly CubicField) := [0, DensePoly.C (-2), 1, xPoly]
  match Descriptor.build fieldSign 7 bounded with
  | .ok (.ok d) =>
    match d.buildSigns qs with
    | .ok s =>
      s.values.toList == [0, -1, 1, 1] &&
        d.checkSigns qs s.values s.evidence &&
        !({bounded with lower := .finite 0}).checkSigns fieldSign 7 qs s.values s.evidence
    | _ => false
  | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard finitePasses

/-- Ordinary total calls over the actual cubic field, with a nonzero
polynomial vanishing at the selected root as well as both strict signs. -/
def totalSignsPasses : Bool :=
  match Descriptor.validate fieldSign 7 raw with
  | some d =>
    d.signAt (xPoly - 1) == 1 &&
      d.signAt (xPoly - DensePoly.C 2) == -1 &&
      d.signAt (xPoly.natPow 3 - DensePoly.C 2) == 0 &&
      d.signAt 0 == 0 &&
      (match d.buildSigns [xPoly.natPow 3 - DensePoly.C 2] with
      | .ok s => s.value == 0
      | .error _ => false) &&
      (match d.buildSigns [0] with
      | .ok s => s.value == 0
      | .error _ => false)
  | none => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard totalSignsPasses

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

/-- Negation respects the selected real embedding of the actual cubic field. -/
theorem value_neg (a : CubicField) : Field.value rep (-a) = -Field.value rep a := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg, Field.value_complex rep binding real,
    Field.value_complex rep binding real, PolyQuot.map_neg]

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
  · exact value_neg
  · exact Field.value_inv rep binding real

/-- The total operation has the selected real embedding's evaluation sign
for every validated descriptor and polynomial in the cubic field. -/
theorem cubic_sign (d : Descriptor CubicField Nat fieldSign 7)
    (q : DensePoly CubicField) :
    d.signAt q = (SignType.sign ((interpret (Field.value rep)
      (Field.value_eq_zero rep binding real) q).eval
      (d.root (Field.value rep) (Field.value_eq_zero rep binding real)
        (Field.value_one rep binding real) (Field.value_add rep binding real)
        (Field.value_sub rep binding real) (Field.value_mul rep binding real)
        (Field.value_natCast rep binding real) sign_spec)) : Int) := by
  exact d.signAt_correct (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real) q

/-- info: 'Hex.SignDetMathlib.SelectedProducerConformance.cubic_sign' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cubic_sign

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
