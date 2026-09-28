/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.CompletionProducer
public import HexSignDetMathlib.SelectedProducerConformance
public meta import HexSignDetMathlib.SelectedProducerConformance
public meta import HexSignDet
public meta import HexNumberField
public meta import HexRCF.RealCoefficients.Coefficients

public section

/-! Completion checks over the actual cubic coefficient field, with empty
partial encodings, zero derivative signs and negative leading coefficients.
Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.CompletionConformance

open Hex Hex.SignDet Hex.SignDetMathlib.SelectedProducerConformance
open Hex.RCF.RealCoefficients HexPolyMathlib.Interpret

/-- Three roots over ℚ(∛2); the second derivative sign selects +∛2. -/
def cubicHead : DensePoly CubicField :=
  (xPoly - DensePoly.C alpha) * xPoly * (xPoly + DensePoly.C alpha)

def positive : RawDescriptor CubicField Nat :=
  ⟨7, cubicHead, .negInf, .posInf, [2], [1]⟩

/-- Compare every stored field, without quotienting coefficient representations. -/
def sameRaw (a b : RawDescriptor CubicField Nat) : Bool :=
  decide (a.context = b.context) && decide (a.head = b.head) &&
    decide (a.lower = b.lower) && decide (a.upper = b.upper) &&
    decide (a.indices = b.indices) && decide (a.signs = b.signs)

/-- The total accessor is checked against successful construction and the
complete literal descriptor. Copied results fail changed source bindings. -/
def completesAs (raw : RawDescriptor CubicField Nat) (word : List Int) : Bool :=
  match Descriptor.validate fieldSign 7 raw with
  | none => false
  | some d =>
    match d.buildCompletion with
    | .error _ => false
    | .ok c =>
      let out := d.complete
      sameRaw out.raw (raw.full word) &&
        sameRaw out.raw c.descriptor.raw &&
        raw.completes out.raw &&
        !({raw with context := 8}).completes out.raw &&
        !({raw with head := raw.head + 1}).completes out.raw &&
        !({raw with lower := .finite 0}).completes out.raw &&
        !({raw with upper := .finite 3}).completes out.raw &&
        (raw.signs.isEmpty ||
          !({raw with signs := raw.signs.map (fun s => if s = 0 then 1 else -s)}).completes out.raw) &&
        !({raw with indices := [0]}).completes out.raw

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard completesAs positive [1, 1, 1]

/-- Changing the leading sign changes every derivative sign, while the
selected root is still +∛2. An old full word cannot identify the new head. -/
def negative : RawDescriptor CubicField Nat :=
  {positive with head := -cubicHead, signs := [-1]}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard completesAs negative [-1, -1, -1]

/-- At zero the second derivative vanishes; the first derivative sign
selects it from the three roots of the cubic head. -/
def middle : RawDescriptor CubicField Nat :=
  {positive with indices := [1], signs := [-1]}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard completesAs middle [-1, 0, 1]

/-- Empty constraints are valid on a certified singleton interval. -/
def emptyPartial : RawDescriptor CubicField Nat :=
  ⟨7, head, .finite 1, .finite 2, [], []⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard completesAs emptyPartial [1, 1]

-- Completing an already full encoding retains its literal source word.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard completesAs (positive.full [1, 1, 1]) [1, 1, 1]

/-- Negation respects the actual selected real embedding, without a field
instance on a synthetic carrier. -/
theorem value_neg (a : CubicField) : Field.value rep (-a) = -Field.value rep a := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg, Field.value_complex rep binding real,
    Field.value_complex rep binding real, PolyQuot.map_neg]

/-- The public completion theorem applies to every validated descriptor over
this nonquadratic field, including empty partial encodings when uniquely realized. -/
theorem cubic_complete (d : Descriptor CubicField Nat fieldSign 7) :
    d.complete.root (Field.value rep) (Field.value_eq_zero rep binding real)
        (Field.value_one rep binding real) (Field.value_add rep binding real)
        (Field.value_sub rep binding real) (Field.value_mul rep binding real)
        (Field.value_natCast rep binding real) sign_spec =
      d.root (Field.value rep) (Field.value_eq_zero rep binding real)
        (Field.value_one rep binding real) (Field.value_add rep binding real)
        (Field.value_sub rep binding real) (Field.value_mul rep binding real)
        (Field.value_natCast rep binding real) sign_spec ∧
      d.raw.completes d.complete.raw = true ∧
      d.complete.raw.indices = (List.range d.raw.head.natDegree).map (· + 1) ∧
      d.complete.raw.signs = (List.range d.raw.head.natDegree).map (fun j =>
        (SignType.sign ((Polynomial.derivative^[j + 1]
          (interpret (Field.value rep) (Field.value_eq_zero rep binding real) d.raw.head)).eval
          (d.root (Field.value rep) (Field.value_eq_zero rep binding real)
            (Field.value_one rep binding real) (Field.value_add rep binding real)
            (Field.value_sub rep binding real) (Field.value_mul rep binding real)
            (Field.value_natCast rep binding real) sign_spec)) : Int)) := by
  exact d.complete_correct (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real)

/-- info: 'Hex.SignDet.Descriptor.buildCompletion_ofTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.buildCompletion_ofTable

/-- info: 'Hex.SignDet.Descriptor.complete_ofBuild' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.complete_ofBuild

/-- info: 'Hex.SignDet.Descriptor.buildCompletion_success' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.buildCompletion_success

/-- info: 'Hex.SignDet.Descriptor.complete_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.complete_correct

/-- info: 'Hex.SignDet.RawDescriptor.full_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.RawDescriptor.full_at

/-- info: 'Hex.SignDet.Descriptor.select_full_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.select_full_at

/-- info: 'Hex.SignDet.Descriptor.completion_rows' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.completion_rows

/-- info: 'Hex.SignDet.Descriptor.buildCompletion_roots' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.buildCompletion_roots

/-- info: 'Hex.SignDet.Descriptor.complete_success' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.complete_success

/--
info: 'Hex.SignDetMathlib.CompletionConformance.cubic_complete' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cubic_complete

end Hex.SignDetMathlib.CompletionConformance
