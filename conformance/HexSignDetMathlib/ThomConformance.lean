/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ThomReencoding
public import HexSignDetMathlib.ReencodingConformance
public meta import HexSignDetMathlib.ReencodingConformance
public meta import HexSignDet
public meta import HexNumberField
public meta import HexRCF.RealCoefficients.Coefficients

public section

/-! Thom correspondence and re-encoding to a different defining polynomial.
Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.ThomConformance

open Hex Hex.SignDet Hex.SignDetMathlib.SelectedProducerConformance
open Hex.RCF.RealCoefficients HexPolyMathlib.Interpret HexRealRootsMathlib

/-- The target includes the selected cubic value and may also include roots
outside the original interval. Both evidence layers retain the target head. -/
def reencoded (target : DensePoly CubicField) (signs : List Int) : Bool :=
  let source : RawDescriptor CubicField Nat :=
    {raw with lower := .finite 0, upper := .finite 2, indices := [], signs := []}
  match Descriptor.validate fieldSign 7 source with
  | none => false
  | some d =>
    match d.buildReencoding target .negInf .posInf with
    | .ok (some r) =>
      r.target.raw.head == target && r.target.raw.lower == .negInf &&
        r.target.raw.upper == .posInf && r.target.raw.signs == signs &&
        r.target.signAt (xPoly - DensePoly.C alpha) == 0 &&
        r.target.raw.check fieldSign 7 r.target.evidence &&
        r.target.evidence.check fieldSign 7 target .negInf .posInf r.target.raw.queries &&
        !r.target.evidence.check fieldSign 7 source.head .negInf .posInf r.target.raw.queries &&
        d.checkReencoding r.target target .negInf .posInf r.evidence
    | _ => false

-- A different degree, and a target interval larger than the source interval.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard reencoded (xPoly - DensePoly.C alpha) [1]

-- The extra target root −1 was not a root of the original head or in its interval.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard reencoded ((xPoly - DensePoly.C alpha) * (xPoly + 1)) [1, 1]

namespace Noncanonical

open Hex.SignDetMathlib.ReencodingConformance.Noncanonical
open HexPoly.InterpretTests

/-- The producer theorem is instantiated with the actual noninjective stored
carrier. No field instance on that carrier, head equality or old-domain
containment is supplied. -/
theorem reencoding (d : Descriptor Rep Nat Hex.TarskiTests.Noncanonical.sign 7)
    (head : DensePoly Rep) (a b : Endpoint Rep)
    (hdom : HexSturmMathlib.Domain realValue zero head a b)
    (hmem : d.root realValue zero one add sub mul natCast sign ∈
      Tarski.rootsIn (interpret realValue zero head) (a.map realValue) (b.map realValue)) :
    ∃ r : Reencoding d head a b,
      d.buildReencoding head a b = .ok (some r) ∧
      r.target.root realValue zero one add sub mul natCast sign =
        d.root realValue zero one add sub mul natCast sign := by
  exact d.buildReencoding_success realValue zero one add sub mul natCast sign neg inv
    head a b hdom hmem

end Noncanonical

/-- info: 'Polynomial.thomEncoding_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.thomEncoding_injOn

/-- info: 'Polynomial.lt_iff_derivativeSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.lt_iff_derivativeSign

/-- info: 'TauCeti.RealClosure.polynomialRolle_of_isRealClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TauCeti.RealClosure.polynomialRolle_of_isRealClosed

/-- info: 'Hex.SignDet.RawDescriptor.full_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.full_unique

/-- info: 'Hex.SignDet.RawDescriptor.full_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.full_fiber

/-- info: 'Hex.SignDet.RawDescriptor.full_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.full_lt

/-- info: 'Hex.SignDet.RawDescriptor.full_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.full_order

/-- info: 'Hex.SignDet.RawDescriptor.full_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.full_lt_iff

/-- info: 'Hex.SignDet.Descriptor.full_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.full_signs

/-- info: 'Hex.SignDet.Descriptor.fullOrder_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.fullOrder_root

/-- info: 'Hex.SignDet.Comparison.order_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Comparison.order_root

/-- info: 'Hex.SignDet.Descriptor.buildReencoding_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildReencoding_success

/-- info: 'Hex.SignDetMathlib.ThomConformance.Noncanonical.reencoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDetMathlib.ThomConformance.Noncanonical.reencoding

end Hex.SignDetMathlib.ThomConformance
