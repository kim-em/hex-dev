/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RootList
public import HexSignDetMathlib.SelectedProducerConformance
public import HexRealRootsMathlib.TarskiTests
public meta import HexSignDet
public meta import HexSignDetMathlib.SelectedProducerConformance
public meta import HexRealRoots.TarskiTests
public meta import HexNumberField
public meta import HexRCF.RealCoefficients.Coefficients

public section

/-! Root enumeration over rational, noncanonical and cubic coefficients.
Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.RootListConformance

open Hex Hex.SignDet Hex.SignDetMathlib.SelectedProducerConformance
open Hex.RCF.RealCoefficients HexPolyMathlib.Interpret

/-- Require actual successful enumeration, full words and literal bindings.
An error or absent domain cannot pass as an empty root list. -/
def rootsAs {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E]
    [Mul E] [NatCast E] [Neg E] [Inv E]
    (sign : E → Int) (p : DensePoly E) (a b : Endpoint E)
    (words : List (List Int)) : Bool :=
  match Descriptor.buildRoots sign 7 p a b with
  | .ok (some roots) =>
    roots.map (fun d => d.raw.signs) == words &&
      roots.all (fun d => d.raw.context == 7 && d.raw.head == p &&
        d.raw.lower == a && d.raw.upper == b &&
        d.raw.indices == List.range' 1 p.natDegree &&
        d.raw.check sign 7 d.evidence &&
        !d.raw.check sign 8 d.evidence) &&
      decide (roots.Pairwise (fun d e => d.fullOrder e = some .lt))
  | _ => false

def ratX : DensePoly Rat := DensePoly.ofList [0, 1]
def ratHead : DensePoly Rat := ratX * ratX - 1

#guard rootsAs Sturm.orderSign ratHead .negInf .posInf [[-1, 1], [1, 1]]
#guard rootsAs Sturm.orderSign (-ratHead) .negInf .posInf [[1, -1], [-1, -1]]
#guard rootsAs Sturm.orderSign ratHead (.finite 0) .posInf [[1, 1]]
#guard rootsAs Sturm.orderSign ratHead .negInf (.finite 0) [[-1, 1]]
#guard rootsAs Sturm.orderSign ratHead (.finite (-2)) (.finite 2) [[-1, 1], [1, 1]]
#guard rootsAs Sturm.orderSign (ratX * ratX + 1) .negInf .posInf []
#guard rootsAs Sturm.orderSign (DensePoly.C (2 : Rat)) .negInf .posInf []
def invalidDomain (p : DensePoly Rat) (a b : Endpoint Rat) : Bool :=
  match Descriptor.buildRoots Sturm.orderSign 7 p a b with
  | .ok none => true
  | _ => false

#guard invalidDomain 0 .negInf .posInf
#guard invalidDomain (ratHead * ratHead) .negInf .posInf
#guard invalidDomain ratHead (.finite 1) (.finite 2)

-- The coefficient carrier has canonical zero and several representations of
-- nonzero values. Enumeration needs ordinary operations, not a field instance.
#guard rootsAs Hex.TarskiTests.Noncanonical.sign Hex.TarskiTests.Noncanonical.head
  .negInf .posInf [[-1, 1], [1, 1]]

#guard rootsAs fieldSign (DensePoly.C (2 : CubicField)) .negInf .posInf []

def cubicHead : DensePoly CubicField := head * xPoly

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard rootsAs fieldSign head .negInf .posInf [[-1, 1], [1, 1]]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard rootsAs fieldSign cubicHead .negInf .posInf [[1, -1, 1], [-1, 0, 1], [1, 1, 1]]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard rootsAs fieldSign (-cubicHead) .negInf .posInf [[-1, 1, -1], [1, 0, -1], [-1, -1, -1]]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard rootsAs fieldSign cubicHead (.finite 1) (.finite 2) [[1, 1, 1]]

/-- The actual cubic-field output covers precisely the mathematical roots,
without repetitions. This theorem does not assume a Thom order theorem or
claim that enumeration succeeds on every valid domain. -/
theorem cubic_coverage (p : DensePoly CubicField) (a b : Endpoint CubicField)
    (out : List (Descriptor CubicField Nat fieldSign 7))
    (h : Descriptor.buildRoots fieldSign 7 p a b = .ok (some out)) :
    (∀ x, x ∈ HexRealRootsMathlib.Tarski.rootsIn
      (interpret (Field.value rep) (Field.value_eq_zero rep binding real) p)
      (a.map (Field.value rep)) (b.map (Field.value rep)) ↔
      x ∈ out.map (fun d => d.root (Field.value rep)
        (Field.value_eq_zero rep binding real) (Field.value_one rep binding real)
        (Field.value_add rep binding real) (Field.value_sub rep binding real)
        (Field.value_mul rep binding real) (Field.value_natCast rep binding real) sign_spec)) ∧
    (out.map (fun d => d.root (Field.value rep)
      (Field.value_eq_zero rep binding real) (Field.value_one rep binding real)
      (Field.value_add rep binding real) (Field.value_sub rep binding real)
      (Field.value_mul rep binding real) (Field.value_natCast rep binding real) sign_spec)).Nodup := by
  exact Descriptor.buildRoots_coverage (Field.value rep)
    (Field.value_eq_zero rep binding real) (Field.value_one rep binding real)
    (Field.value_add rep binding real) (Field.value_sub rep binding real)
    (Field.value_mul rep binding real) (Field.value_natCast rep binding real) sign_spec h

/-- info: 'Hex.SignDet.Descriptor.buildRoots_ofEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.buildRoots_ofEmpty
/-- info: 'Hex.SignDet.Descriptor.buildRoots_empty' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.buildRoots_empty
/-- info: 'Hex.SignDet.Descriptor.buildRoots_constant_success' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.buildRoots_constant_success

/-- info: 'Hex.SignDet.Descriptor.buildRoots_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.buildRoots_domain

/-- info: 'Hex.SignDet.Descriptor.buildRoots_coverage' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.buildRoots_coverage

/-- info: 'Hex.SignDetMathlib.RootListConformance.cubic_coverage' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cubic_coverage

end Hex.SignDetMathlib.RootListConformance
