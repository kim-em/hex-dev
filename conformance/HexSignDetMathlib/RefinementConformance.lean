/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ReencodingRefinement
public import HexSignDetMathlib.ReencodingConformance
public meta import HexSignDetMathlib.ReencodingConformance
public meta import HexSignDet
public meta import HexNumberField
public meta import HexRCF.RealCoefficients.Coefficients
public import HexSignDet.Infinitesimal
public meta import HexSignDet.Infinitesimal

public section

/-! Interval refinement over the actual cubic field and noninjective stored
coefficients. Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.RefinementConformance

open Hex Hex.SignDet Hex.SignDetMathlib.SelectedProducerConformance
open Hex.RCF.RealCoefficients HexPolyMathlib.Interpret HexRealRootsMathlib

/-- The actual output has the new interval, a complete word, the expected
selected-root signs, and fresh evidence. Old interval evidence is rejected. -/
def retained (source : RawDescriptor CubicField Nat) (a b : Endpoint CubicField)
    (positive : Bool := true) : Bool :=
  match Descriptor.validate fieldSign 7 source with
  | none => false
  | some d =>
    match d.buildReencoding source.head a b with
    | .ok (some r) =>
      r.target.raw.lower == a && r.target.raw.upper == b &&
        r.target.raw.head == source.head && r.target.raw.context == 7 &&
        r.target.raw.indices == [1, 2] &&
        r.target.raw.signs == (if positive then [1, 1] else [-1, 1]) &&
        r.target.signAt (xPoly.natPow 3 - DensePoly.C 2) == (if positive then 0 else -1) &&
        r.target.raw.check fieldSign 7 r.target.evidence &&
        !r.target.raw.check fieldSign 7 d.evidence &&
        !({source with lower := a, upper := b}).check fieldSign 7 d.evidence &&
        d.checkReencoding r.target source.head a b r.evidence &&
        !r.evidence.check fieldSign 7 source.head source.lower source.upper
          (r.target.raw.queries ++ d.raw.constraints)
    | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard retained raw (.finite 1) (.finite 2)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard retained raw (.finite 0) .posInf
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard retained raw .negInf (.finite 2)

-- An empty partial word already selects the unique root in the old interval.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard retained {raw with lower := .finite 0, upper := .finite 2, indices := [], signs := []}
  (.finite 1) (.finite (3/2))

-- The root domain is contained even though the target interval extends farther right.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard retained {raw with lower := .finite 0, upper := .finite 2, indices := [], signs := []}
  (.finite 1) (.finite 5)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard retained {raw with signs := [-1]} (.finite (-2)) (.finite (-1)) false

/-- This specialization uses the actual selected real embedding of ℚ(∛2).
Its premises concern the input interval, not availability of an output. -/
theorem cubic_refinement (d : Descriptor CubicField Nat fieldSign 7)
    (a b : Endpoint CubicField)
    (hdom : HexSturmMathlib.Domain (Field.value rep) (Field.value_eq_zero rep binding real)
      d.raw.head a b)
    (hmem : d.root (Field.value rep) (Field.value_eq_zero rep binding real)
      (Field.value_one rep binding real) (Field.value_add rep binding real)
      (Field.value_sub rep binding real) (Field.value_mul rep binding real)
      (Field.value_natCast rep binding real) sign_spec ∈
      Tarski.rootsIn (interpret (Field.value rep) (Field.value_eq_zero rep binding real) d.raw.head)
        (a.map (Field.value rep)) (b.map (Field.value rep)))
    (hsubset : Tarski.rootsIn
      (interpret (Field.value rep) (Field.value_eq_zero rep binding real) d.raw.head)
        (a.map (Field.value rep)) (b.map (Field.value rep)) ⊆
      Tarski.rootsIn (interpret (Field.value rep) (Field.value_eq_zero rep binding real) d.raw.head)
        (d.raw.lower.map (Field.value rep)) (d.raw.upper.map (Field.value rep))) :
    ∃ r : Reencoding d d.raw.head a b,
      d.buildReencoding d.raw.head a b = .ok (some r) ∧
      r.target.root (Field.value rep) (Field.value_eq_zero rep binding real)
        (Field.value_one rep binding real) (Field.value_add rep binding real)
        (Field.value_sub rep binding real) (Field.value_mul rep binding real)
        (Field.value_natCast rep binding real) sign_spec =
      d.root (Field.value rep) (Field.value_eq_zero rep binding real)
        (Field.value_one rep binding real) (Field.value_add rep binding real)
        (Field.value_sub rep binding real) (Field.value_mul rep binding real)
        (Field.value_natCast rep binding real) sign_spec :=
  d.buildReencoding_refinement (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real) a b hdom hmem hsubset

/-- Equivalent nonzero endpoint representations retain their literal bindings.
The carrier has ordinary arithmetic and canonical zero, but no field instance. -/
def noncanonicalPasses : Bool :=
  let x := HexPoly.InterpretTests.x
  let one := HexPoly.InterpretTests.root
  let source : RawDescriptor HexPoly.InterpretTests.Rep Nat :=
    ⟨7, x*x - DensePoly.C one,
      .finite (HexPoly.InterpretTests.pack 0 (-2)),
      .finite (HexPoly.InterpretTests.pack 1 1), [1], [1]⟩
  let a : Endpoint HexPoly.InterpretTests.Rep := .finite 0
  let b : Endpoint HexPoly.InterpretTests.Rep := .finite (HexPoly.InterpretTests.pack 1 (1/2))
  match Descriptor.validate Hex.TarskiTests.Noncanonical.sign 7 source with
  | none => false
  | some d =>
    match d.buildReencoding source.head a b with
    | .ok (some r) =>
      r.target.raw.lower == a && r.target.raw.upper == b &&
        !r.evidence.check Hex.TarskiTests.Noncanonical.sign 7 source.head
          source.lower source.upper (r.target.raw.queries ++ d.raw.constraints) &&
        r.target.raw.signs == [1, 1] && r.target.signAt (x - DensePoly.C one) == 0 &&
        r.target.raw.check Hex.TarskiTests.Noncanonical.sign 7 r.target.evidence &&
        !r.target.raw.check Hex.TarskiTests.Noncanonical.sign 7 d.evidence &&
        !({r.target.raw with upper := .finite (3/2)}).check
          Hex.TarskiTests.Noncanonical.sign 7 r.target.evidence
    | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard noncanonicalPasses

/-- Refine an infinitesimal-width interval using two ordered coefficient levels.
There is no positive rational bound inside the interval; the supplied endpoints
are ordinary elements of the nested rational-function field. -/
def infinitesimalPasses : Bool :=
  let head := Hex.SignDet.Infinitesimal.nested
  let delta := Hex.SignDet.Infinitesimal.delta
  let sign := Hex.SignDet.Infinitesimal.secondSign
  let source : RawDescriptor Hex.SignDet.Infinitesimal.Second Nat :=
    ⟨7, head, .finite 0, .finite (2 * delta), [], []⟩
  match Descriptor.validate sign 7 source with
  | none => false
  | some d =>
    match d.buildReencoding head (.finite (delta / 2)) (.finite (3 * delta / 2)) with
    | .ok (some r) =>
      r.target.raw.head == head && r.target.raw.lower == .finite (delta / 2) &&
        r.target.raw.upper == .finite (3 * delta / 2) &&
        !({source with lower := .finite (delta / 2), upper := .finite (3 * delta / 2)}).check
          sign 7 d.evidence &&
        !r.evidence.check sign 7 head source.lower source.upper
          (r.target.raw.queries ++ d.raw.constraints) &&
        r.target.raw.signs == [1, -1, 1] &&
        r.target.signAt (Hex.SignDet.Infinitesimal.x - DensePoly.C delta) == 0 &&
        r.target.raw.check sign 7 r.target.evidence &&
        !r.target.raw.check sign 7 d.evidence
    | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard infinitesimalPasses

/-- Rebuild the same mathematical polynomial with different nonzero stored
coefficients. A zero difference permits re-encoding, while copied evidence
still fails the exact defining-polynomial binding, even on the same interval. -/
def changedHeadPasses : Bool :=
  let root := HexPoly.InterpretTests.root
  let source : RawDescriptor HexPoly.InterpretTests.Rep Nat :=
    ⟨7, DensePoly.ofCoeffs #[-root, 0, 1], .finite 0, .finite 2, [], []⟩
  let target : DensePoly HexPoly.InterpretTests.Rep := DensePoly.ofCoeffs #[-1, 0, root]
  let sign := Hex.TarskiTests.Noncanonical.sign
  match Descriptor.validate sign 7 source with
  | none => false
  | some d =>
    source.check sign 7 d.evidence &&
      decide (target ≠ source.head) && (target - source.head).isZero &&
      !({source with head := target}).check sign 7 d.evidence &&
      match d.buildReencoding target source.lower source.upper with
      | .ok (some r) =>
        r.target.raw.head == target && r.target.raw.lower == source.lower &&
          r.target.raw.upper == source.upper && r.target.raw.context == 7 &&
          r.target.raw.signs == [1, 1] &&
          r.target.signAt (HexPoly.InterpretTests.x - DensePoly.C 1) == 0 &&
          r.target.raw.check sign 7 r.target.evidence &&
          !r.target.evidence.check sign 7 source.head source.lower source.upper
            r.target.raw.queries &&
          d.checkReencoding r.target target source.lower source.upper r.evidence
      | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard changedHeadPasses

namespace Noncanonical

open HexPoly.InterpretTests Hex.SignDetMathlib.ReencodingConformance.Noncanonical

/-- A closed real interpretation of the noninjective coefficient carrier also
satisfies the refinement theorem; no field instance on the carrier is needed. -/
theorem refinement (d : Descriptor Rep Nat Hex.TarskiTests.Noncanonical.sign 7)
    (a b : Endpoint Rep) (hdom : HexSturmMathlib.Domain realValue zero d.raw.head a b)
    (hmem : d.root realValue zero one add sub mul natCast sign ∈
      Tarski.rootsIn (interpret realValue zero d.raw.head) (a.map realValue) (b.map realValue))
    (hsubset : Tarski.rootsIn (interpret realValue zero d.raw.head)
      (a.map realValue) (b.map realValue) ⊆
      Tarski.rootsIn (interpret realValue zero d.raw.head)
        (d.raw.lower.map realValue) (d.raw.upper.map realValue)) :
    ∃ r : Reencoding d d.raw.head a b,
      d.buildReencoding d.raw.head a b = .ok (some r) ∧
      r.target.root realValue zero one add sub mul natCast sign =
        d.root realValue zero one add sub mul natCast sign := by
  exact d.buildReencoding_refinement realValue zero one add sub mul natCast sign neg inv
    a b hdom hmem hsubset

/-- The changed-head producer theorem applies to the actual noninjective
carrier without a ring or field instance on its stored values. -/
theorem reencoding_congr (d : Descriptor Rep Nat Hex.TarskiTests.Noncanonical.sign 7)
    (target : DensePoly Rep) (a b : Endpoint Rep)
    (hzero : (target - d.raw.head).isZero = true)
    (hdom : HexSturmMathlib.Domain realValue zero target a b)
    (hmem : d.root realValue zero one add sub mul natCast sign ∈
      Tarski.rootsIn (interpret realValue zero target) (a.map realValue) (b.map realValue))
    (hsubset : Tarski.rootsIn (interpret realValue zero target)
      (a.map realValue) (b.map realValue) ⊆
      Tarski.rootsIn (interpret realValue zero d.raw.head)
        (d.raw.lower.map realValue) (d.raw.upper.map realValue)) :
    ∃ r : Reencoding d target a b,
      d.buildReencoding target a b = .ok (some r) ∧
      r.target.root realValue zero one add sub mul natCast sign =
        d.root realValue zero one add sub mul natCast sign := by
  exact d.buildReencoding_congr realValue zero one add sub mul natCast sign neg inv
    target a b hzero hdom hmem hsubset

end Noncanonical

/-- info: 'Hex.SignDet.Descriptor.buildReencoding_ofTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildReencoding_ofTable
/-- info: 'Hex.SignDet.Descriptor.reencoding_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.reencoding_rows
/-- info: 'Hex.SignDet.Descriptor.refinement_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.refinement_fiber
/-- info: 'Hex.SignDet.Descriptor.buildReencoding_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildReencoding_refinement

/-- info: 'Hex.SignDetMathlib.RefinementConformance.cubic_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_refinement
/-- info: 'Hex.SignDetMathlib.RefinementConformance.Noncanonical.refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Noncanonical.refinement

/-- info: 'Hex.SignDet.RawDescriptor.full_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.full_congr
/-- info: 'Hex.SignDet.Descriptor.reencoding_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.reencoding_fiber
/-- info: 'Hex.SignDet.Descriptor.buildReencoding_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildReencoding_congr
/-- info: 'Hex.SignDetMathlib.RefinementConformance.Noncanonical.reencoding_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Noncanonical.reencoding_congr

end Hex.SignDetMathlib.RefinementConformance
