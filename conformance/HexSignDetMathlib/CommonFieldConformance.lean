/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ComparisonProducer
public import HexSignDetMathlib.TableProducer
public import HexSignDetMathlib.SelectedProducer
public import HexSignDet.RootList
public import HexSignDet.CommonField
public meta import HexSignDet.CommonField
public import HexRCF.RealCoefficients.Field
public meta import HexSignDet
public meta import HexNumberField
public meta import HexRealAlgebraic
public meta import HexRCF.RealCoefficients.Coefficients

public section

/-! Decisions using two independently constructed real algebraic coefficients
in their actual common number field. Computational conformance owner:
`HexSignDet`. -/
namespace Hex.SignDetMathlib.CommonFieldConformance

open Hex Hex.SignDet Hex.RCF.RealCoefficients
open HexPolyMathlib.Interpret HexRealRootsMathlib

def inputs : Array AlgebraicNumber := #[
  ZPoly.rootNear #p[-2, 0, 1] 1.4,
  ZPoly.rootNear #p[-3, 0, 1] 1.7]

def fieldSign (generator : RealAlgebraicNumber)
    (a : QAdjoin generator.toAlgebraic) : Int :=
  Hex.SignDet.CommonField.sign a

/-- The Mathlib-free fixture conversion retains exactly the selected value
of the existing proved conversion; its nonreal fallback cannot be reached. -/
theorem value_eq (generator : RealAlgebraicNumber)
    (a : QAdjoin generator.toAlgebraic) :
    Hex.SignDet.CommonField.value a = Coefficients.ofField generator a := by
  have hit := (RealAlgebraicNumber.ofAlgebraic?_eq_some a.toAlgebraicNumber
    (Coefficients.ofField generator a)).mpr rfl
  simp [Hex.SignDet.CommonField.value, hit]

/-- The sign uses the common generator's selected embedding, rather than
choosing a conjugate independently for each coordinate. -/
theorem sign_spec (generator : RealAlgebraicNumber)
    (a : QAdjoin generator.toAlgebraic) :
    fieldSign generator a =
      (SignType.sign (Field.value generator.toAlgebraic.rep a) : Int) := by
  rw [fieldSign, Hex.SignDet.CommonField.sign, value_eq,
    RealAlgebraicNumber.sign_eq, Field.ofField_value]
  rcases lt_trichotomy (Field.value generator.toAlgebraic.rep a) 0 with hn | hz | hp
  · simp [hn, sign_eq_neg_one_iff.mpr hn]
  · simp [hz]
  · have hn := not_lt_of_gt hp
    have hz := ne_of_gt hp
    simp [hn, hz, sign_eq_one_iff.mpr hp]

theorem real (generator : RealAlgebraicNumber) :
    generator.toAlgebraic.rep.root.im = 0 :=
  (AlgebraicNumber.isReal_iff generator.toAlgebraic).mp generator.property

private theorem value_neg (generator : RealAlgebraicNumber)
    (a : QAdjoin generator.toAlgebraic) :
    Field.value generator.toAlgebraic.rep (-a) =
      -Field.value generator.toAlgebraic.rep a := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg,
    Field.value_complex generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator),
    Field.value_complex generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator),
    PolyQuot.map_neg]

/-- The mathematical root in the field's selected real embedding. -/
noncomputable def selected (generator : RealAlgebraicNumber)
    (d : Descriptor (QAdjoin generator.toAlgebraic) Nat (fieldSign generator) 7) : ℝ :=
  d.root (Field.value generator.toAlgebraic.rep)
    (Field.value_eq_zero generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_one generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_add generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_sub generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_mul generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_natCast generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (sign_spec generator)

/-- Complete table counts for the actual selected embedding of a common
number field, including words not present in the sparse table. -/
theorem table_correct (generator : RealAlgebraicNumber)
    (p : DensePoly (QAdjoin generator.toAlgebraic))
    (lo hi : Endpoint (QAdjoin generator.toAlgebraic))
    (qs : List (DensePoly (QAdjoin generator.toAlgebraic)))
    (table : SignTable qs.length)
    (h : determine (fieldSign generator) 7 p lo hi qs = some table) :
    HexSturmMathlib.Domain (Field.value generator.toAlgebraic.rep)
      (Field.value_eq_zero generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
      p lo hi ∧ ∀ word,
      table.count word =
        ((Tarski.rootsIn
          (interpret (Field.value generator.toAlgebraic.rep)
            (Field.value_eq_zero generator.toAlgebraic.rep
              generator.toAlgebraic.rep_mk (real generator)) p)
          (lo.map (Field.value generator.toAlgebraic.rep))
          (hi.map (Field.value generator.toAlgebraic.rep))).filter
          (fun x => signsAt (Field.value generator.toAlgebraic.rep)
            (Field.value_eq_zero generator.toAlgebraic.rep
              generator.toAlgebraic.rep_mk (real generator)) qs x = word)).card := by
  exact determine_correct (Field.value generator.toAlgebraic.rep)
    (Field.value_eq_zero generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_one generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_add generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_sub generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_mul generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_natCast generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (value_neg generator)
    (Field.value_inv generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (fieldSign generator) (sign_spec generator) 7 p lo hi qs true table h

/-- The public one-query operation at a selected common-field root equals its
real evaluation sign under that field's selected embedding. -/
theorem signAt_correct (generator : RealAlgebraicNumber)
    (d : Descriptor (QAdjoin generator.toAlgebraic) Nat (fieldSign generator) 7)
    (q : DensePoly (QAdjoin generator.toAlgebraic)) :
    d.signAt q = (SignType.sign
      ((interpret (Field.value generator.toAlgebraic.rep)
        (Field.value_eq_zero generator.toAlgebraic.rep
          generator.toAlgebraic.rep_mk (real generator)) q).eval
        (selected generator d)) : Int) := by
  simpa only [selected] using d.signAt_correct (Field.value generator.toAlgebraic.rep)
    (Field.value_eq_zero generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_one generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_add generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_sub generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_mul generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_natCast generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (sign_spec generator) (value_neg generator)
    (Field.value_inv generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator)) q

/-- Specialize the total comparison theorem to the actual coordinate field
of any selected real generator, including a generator returned by `common`.
All interpretation laws come from its existing, proved real embedding. -/
theorem comparison (generator : RealAlgebraicNumber)
    (left right : Descriptor (QAdjoin generator.toAlgebraic) Nat (fieldSign generator) 7) :
    left.compare right =
      (if selected generator left < selected generator right then .lt
       else if selected generator right < selected generator left then .gt else .eq) := by
  exact left.compare_correct (Field.value generator.toAlgebraic.rep)
    (Field.value_eq_zero generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_one generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_add generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_sub generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_mul generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_natCast generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (sign_spec generator) (value_neg generator)
    (Field.value_inv generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator))
    (Field.value_div generator.toAlgebraic.rep generator.toAlgebraic.rep_mk (real generator)) right

/-- At a=√2 and b=√3, the two root rows have signs (0,−,−) and
(+,0,−). Enumeration and cross-polynomial comparison use those same actual
coordinates. Fresh re-encoding must preserve a, and copied evidence rejects. -/
def passes : Bool := Id.run do
  let common := QAdjoin.common inputs
  if common.entries.map (·.toAlgebraicNumber) != inputs then return false
  if common.generator.p.natDegree != 4 then return false
  if hr : common.generator.isReal = true then
    let generator := RealAlgebraicNumber.ofAlgebraic common.generator hr
    let sign := fieldSign generator
    let some a := common.entries[0]? | return false
    let some b := common.entries[1]? | return false
    let x : DensePoly (QAdjoin common.generator) := DensePoly.ofList [0, 1]
    let qa := x - DensePoly.C a
    let qb := x - DensePoly.C b
    let head := qa * qb
    let queries := [qa, qb, DensePoly.C (a - b)]
    let some table := determine sign 7 head .negInf .posInf queries | return false
    if table.rows.toList != [([0, -1, -1], 1), ([1, 0, -1], 1)] then return false
    if table.count [0, 0, -1] != 0 then return false
    let .ok (some roots) := Descriptor.buildRoots sign 7 head .negInf .posInf | return false
    if roots.map (fun d => d.raw.signs) != [[-1, 1], [1, 1]] then return false
    if roots.map (fun d => d.signAt qa) != [0, 1] then return false
    if roots.map (fun d => d.signAt qb) != [-1, 0] then return false
    let rawA : RawDescriptor (QAdjoin common.generator) Nat :=
      ⟨7, head, .negInf, .posInf, [1], [-1]⟩
    let rawB : RawDescriptor (QAdjoin common.generator) Nat :=
      ⟨7, qb, .negInf, .posInf, [1], [1]⟩
    let some left := Descriptor.validate sign 7 rawA | return false
    let some right := Descriptor.validate sign 7 rawB | return false
    if left.compare right != .lt || right.compare left != .gt then return false
    let .ok (some same) := left.buildReencoding qa .negInf .posInf | return false
    let square := x * x - DensePoly.C (a * a)
    let some squareRoot := Descriptor.validate sign 7
      (⟨7, square, .negInf, .posInf, [1], [1]⟩ :
        RawDescriptor (QAdjoin common.generator) Nat) | return false
    return left.compare same.target == .eq &&
      same.target.compare squareRoot == .eq &&
      squareRoot.compare same.target == .eq &&
      same.target.signAt qa == 0 && same.target.signAt qb == -1 &&
      left.checkReencoding same.target qa .negInf .posInf same.evidence &&
      !same.target.raw.check sign 7 left.evidence &&
      !same.target.raw.check sign 8 same.target.evidence
  else return false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
#guard passes

/-- A nonreal common generator is rejected before coefficient signs are used. -/
private def rejectsNonreal : Bool :=
  ((Hex.SignDet.CommonField.fixture #[AlgebraicNumber.I, inputs[0]!]).getObjValAs?
    String "error") == .ok "nonreal generator"

#guard rejectsNonreal

/-- info: 'Hex.SignDetMathlib.CommonFieldConformance.sign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_spec

/-- info: 'Hex.SignDetMathlib.CommonFieldConformance.table_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms table_correct

/-- info: 'Hex.SignDetMathlib.CommonFieldConformance.signAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signAt_correct

/-- info: 'Hex.SignDetMathlib.CommonFieldConformance.comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comparison

end Hex.SignDetMathlib.CommonFieldConformance
