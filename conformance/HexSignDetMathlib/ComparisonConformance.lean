/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ComparisonProducer
public import HexSignDetMathlib.ThomConformance
public meta import HexSignDetMathlib.ThomConformance
public import HexSignDet.Infinitesimal
public meta import HexSignDet.Infinitesimal
public meta import HexSignDet

public section

/-! Actual common-head construction and total comparison, including partial
words, shared roots and noninjective coefficients. Computational conformance
owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.ComparisonConformance

open Hex Hex.SignDet HexPolyMathlib.Interpret HexRealRootsMathlib

/-- Every stage must succeed. Check the retained literal bindings and both
joint replays, then exercise the total operation in both argument orders. -/
def compares {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
    [NatCast E] [Neg E] [Inv E] [Div E] (sign : E → Int)
    (left right : RawDescriptor E Nat) (expected : Ordering) : Bool :=
  match Descriptor.validate sign 7 left, Descriptor.validate sign 7 right with
  | some l, some r =>
    match l.buildComparison r with
    | .ok c =>
      c.order == expected && l.compare r == expected && r.compare l == expected.swap &&
        c.common.check 7 left.head right.head &&
        !c.common.check 8 left.head right.head &&
        c.common.left == left.head && c.common.right == right.head &&
        c.leftEncoding.target.raw.head == c.common.head &&
        c.rightEncoding.target.raw.head == c.common.head &&
        l.checkReencoding c.leftEncoding.target c.common.head .negInf .posInf
          c.leftEncoding.evidence &&
        r.checkReencoding c.rightEncoding.target c.common.head .negInf .posInf
          c.rightEncoding.evidence
    | _ => false
  | _, _ => false

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def positive : RawDescriptor Rat Nat :=
  ⟨7, x * x - 1, .finite 0, .finite 2, [], []⟩
private def linear : RawDescriptor Rat Nat := ⟨7, x - 1, .negInf, .posInf, [1], [1]⟩
private def negative : RawDescriptor Rat Nat :=
  ⟨7, x * x - 1, .finite (-2), .finite 0, [], []⟩

-- The same mathematical root selected by different-degree polynomials.
#guard compares Sturm.orderSign positive linear .eq
-- Two empty partial words distinguish roots by their original intervals.
#guard compares Sturm.orderSign negative positive .lt
-- Negative leading coefficients require the reversed Thom sign rule.
#guard compares Sturm.orderSign {negative with head := -(x * x - 1)}
  {positive with head := -(x * x - 1)} .lt
-- The right selected root is exactly the left descriptor's upper endpoint.
#guard compares Sturm.orderSign positive
  ⟨7, (x - 1) * (x - 2), .finite (3/2), .finite 3, [], []⟩ .lt
-- Bad source bindings must fail, not count as successful absence or equality.
#guard !compares Sturm.orderSign {positive with context := 8} linear .eq

private def commonPasses (p q : DensePoly Rat) (degree : Nat) : Bool :=
  match CommonProduct.build 7 p q with
  | .ok c => c.val.check 7 p q && c.val.head.natDegree == degree && !c.val.check 8 p q
  | _ => false

-- Constants and zero inputs use the ordinary total division kernel.
#guard commonPasses 0 0 0
#guard commonPasses 0 (x - 1) 0
#guard commonPasses (x - 1) 0 0
#guard commonPasses 2 3 0
-- Removing a common factor produces a squarefree quadratic, not a cubic.
#guard commonPasses (x * x - 1) (x - 1) 2

open Hex.SignDetMathlib.SelectedProducerConformance

private def cubicPositive : RawDescriptor CubicField Nat :=
  {raw with lower := .finite 0, upper := .finite 2, indices := [], signs := []}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard compares fieldSign cubicPositive
  ⟨7, xPoly - DensePoly.C alpha, .negInf, .posInf, [1], [1]⟩ .eq

-- Actual QAdjoin cubic coefficients; common α and the old upper endpoint 2.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard compares fieldSign cubicPositive
  ⟨7, (xPoly - DensePoly.C alpha) * (xPoly - DensePoly.C 2),
    .finite (3/2), .finite 3, [], []⟩ .lt

namespace Noncanonical

open Hex.SignDetMathlib.ReencodingConformance.Noncanonical
open HexPoly.InterpretTests

theorem div (a b : Rep) : realValue (a / b) = realValue a / realValue b := by
  simp [realValue, value_div, Rat.cast_div]

private def positive : RawDescriptor Rep Nat :=
  ⟨7, HexPoly.InterpretTests.x * HexPoly.InterpretTests.x - DensePoly.C root,
    .finite 0, .finite 2, [], []⟩
private def linear : RawDescriptor Rep Nat :=
  ⟨7, HexPoly.InterpretTests.x - DensePoly.C (1 : Rep), .negInf, .posInf, [1], [1]⟩

-- Stored root and literal 1 differ, while their mathematical values agree.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard compares Hex.TarskiTests.Noncanonical.sign positive linear .eq

/-- Closed specialization to the actual carrier with canonical zero and
noninjective nonzero storage. No field instance on `Rep` is provided. -/
theorem comparison (left right : Descriptor Rep Nat Hex.TarskiTests.Noncanonical.sign 7) :
    left.compare right =
      (if left.root realValue zero one add sub mul natCast sign <
          right.root realValue zero one add sub mul natCast sign then .lt
       else if right.root realValue zero one add sub mul natCast sign <
          left.root realValue zero one add sub mul natCast sign then .gt else .eq) := by
  exact left.compare_correct realValue zero one add sub mul natCast sign neg inv div right

end Noncanonical

open Hex.SignDet.Infinitesimal

-- No positive rational lies between these two distinct infinitesimal roots.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard compares firstSign
  ⟨7, (Hex.SignDet.Infinitesimal.x : DensePoly First), .negInf, .posInf, [1], [1]⟩
  ⟨7, Hex.SignDet.Infinitesimal.x - DensePoly.C epsilon, .negInf, .posInf, [1], [1]⟩ .lt

/-- info: 'Hex.SignDet.CommonProduct.build_of_check' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.CommonProduct.build_of_check
/-- info: 'Hex.SignDet.CommonProduct.build_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.CommonProduct.build_success
/-- info: 'Hex.SignDet.CommonProduct.build_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.CommonProduct.build_squarefree
/-- info: 'Hex.SignDet.Descriptor.buildReencoding_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildReencoding_full
/-- info: 'Hex.SignDet.Descriptor.buildComparison_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildComparison_success
/-- info: 'Hex.SignDet.Descriptor.compare_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.compare_success
/-- info: 'Hex.SignDet.Descriptor.compare_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.compare_correct
/-- info: 'Hex.SignDet.Descriptor.compare_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.compare_eq_iff
/-- info: 'Hex.SignDet.Descriptor.compare_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.compare_lt_iff
/-- info: 'Hex.SignDet.Descriptor.compare_gt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.compare_gt_iff
/-- info: 'Hex.SignDetMathlib.ComparisonConformance.Noncanonical.comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDetMathlib.ComparisonConformance.Noncanonical.comparison

end Hex.SignDetMathlib.ComparisonConformance
