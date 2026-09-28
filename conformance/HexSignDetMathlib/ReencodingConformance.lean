/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ReencodingProducer
public import HexRealRootsMathlib.TarskiTests
public meta import HexRealRootsMathlib.TarskiTests
public import HexSignDetMathlib.SelectedProducerConformance
public meta import HexSignDetMathlib.SelectedProducerConformance
public meta import HexSignDet
public meta import HexNumberField
public meta import HexRCF.RealCoefficients.Coefficients

public section

/-! Actual absence results for re-encoding over the cubic coefficient field.
Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.ReencodingConformance

open Hex Hex.SignDet Hex.SignDetMathlib.SelectedProducerConformance
open Hex.RCF.RealCoefficients HexPolyMathlib.Interpret HexRealRootsMathlib

/-- Internal errors and failed source validation must fail the test, rather
than being mistaken for the absence of the selected root. -/
def absentAs (source : RawDescriptor CubicField Nat) (target : DensePoly CubicField)
    (a b : Endpoint CubicField) : Bool :=
  match Descriptor.validate fieldSign 7 source with
  | none => false
  | some d =>
    match d.buildReencoding target a b with
    | .ok none => true
    | _ => false

-- The target contains the other root of the source head, namely −∛2.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw (xPoly + DensePoly.C alpha) .negInf .posInf

-- The same target head loses the selected root when its interval is restricted.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw head (.finite (-2)) (.finite 0)

-- An upper finite endpoint and an infinite lower endpoint still exclude +∛2.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw head .negInf (.finite 0)

-- A root-free finite interval and a root-free head use genuine successful BKR tables.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw head (.finite 2) (.finite 3)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw (xPoly.natPow 2 + 1) .negInf .posInf

-- Nonzero constants prepare successfully but have no target roots.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw (DensePoly.C 2) .negInf .posInf

-- Invalid targets are also ordinary absence results, before joint determination.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw (0 : DensePoly CubicField) .negInf .posInf
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw ((xPoly - DensePoly.C alpha).natPow 2) .negInf .posInf
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw head (.finite 2) (.finite 1)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs raw head (.finite alpha) .posInf

-- Empty source words are valid on singleton intervals and retain their bounds.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard absentAs {raw with lower := .finite 1, upper := .finite 2, indices := [], signs := []}
  (xPoly + DensePoly.C alpha) .negInf .posInf

/-- A target containing the source root succeeds, distinguishing the tests
above from an implementation that always returns absence. -/
def presentPasses : Bool :=
  match Descriptor.validate fieldSign 7 raw with
  | none => false
  | some d =>
    let target := xPoly - DensePoly.C alpha
    match d.buildReencoding target .negInf .posInf with
    | .ok (some r) =>
      d.checkReencoding r.target target .negInf .posInf r.evidence &&
        r.target.raw.head == target
    | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard presentPasses

-- Failed source validation cannot pass an absence test.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard !absentAs {raw with signs := [0]} (DensePoly.C 2) .negInf .posInf

/-- Different nonzero representations of the same coefficient are processed
by ordinary arithmetic. The carrier has canonical zero and no field instance. -/
def noncanonicalPasses : Bool :=
  let x := HexPoly.InterpretTests.x
  let one := HexPoly.InterpretTests.root
  let source : RawDescriptor HexPoly.InterpretTests.Rep Nat :=
    ⟨7, x*x - DensePoly.C one, .negInf, .posInf, [1], [1]⟩
  match Descriptor.validate Hex.TarskiTests.Noncanonical.sign 7 source with
  | none => false
  | some d =>
    let absentHead := match d.buildReencoding (x + DensePoly.C one) .negInf .posInf with
      | .ok none => true
      | _ => false
    let absentInterval := match d.buildReencoding source.head .negInf (.finite 0) with
      | .ok none => true
      | _ => false
    let constantHead := match d.buildReencoding (DensePoly.C one) .negInf .posInf with
      | .ok none => true
      | _ => false
    absentHead && absentInterval && constantHead

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard noncanonicalPasses

/-- The generic theorem specializes to the ordinary operations and selected
real embedding of ℚ(∛2), without an assumed successful query or target output. -/
theorem cubic_absent (d : Descriptor CubicField Nat fieldSign 7)
    (target : DensePoly CubicField) (a b : Endpoint CubicField)
    (habsent : d.root (Field.value rep) (Field.value_eq_zero rep binding real)
        (Field.value_one rep binding real) (Field.value_add rep binding real)
        (Field.value_sub rep binding real) (Field.value_mul rep binding real)
        (Field.value_natCast rep binding real) sign_spec ∉
      Tarski.rootsIn (interpret (Field.value rep) (Field.value_eq_zero rep binding real) target)
        (a.map (Field.value rep)) (b.map (Field.value rep))) :
    d.buildReencoding target a b = .ok none := by
  exact d.buildReencoding_absent (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real) target a b habsent

/-- info: 'Hex.SignDet.Descriptor.constraints_at_root' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.constraints_at_root
/-- info: 'Hex.SignDet.Descriptor.constraints_iff' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.constraints_iff
/-- info: 'Hex.SignDet.Descriptor.buildReencoding_absent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildReencoding_absent
/-- info: 'Hex.SignDetMathlib.ReencodingConformance.cubic_absent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_absent

end Hex.SignDetMathlib.ReencodingConformance
