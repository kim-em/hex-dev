/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.QueryHandle
public import HexSignDetMathlib.SelectedProducerConformance
public import HexRealRootsMathlib.TarskiTests
public meta import HexSignDet
public meta import HexSignDetMathlib.SelectedProducerConformance
public meta import HexRealRoots.TarskiTests
public meta import HexNumberField
public meta import HexRCF.RealCoefficients.Coefficients

public section

/-! Successive selected-root queries and stale evidence rejection.
Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.QueryHandleConformance

open Hex Hex.SignDet Hex.SignDetMathlib.SelectedProducerConformance
open Hex.RCF.RealCoefficients HexPolyMathlib.Interpret

/-- Joint and singleton calls must succeed with the expected signs. Zero
answers separately require successful singleton construction. Fresh valid
descriptors must reject evidence copied from the original selection. -/
def preparedAs {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E]
    [Mul E] [NatCast E] [Neg E] [Inv E]
    (sign : E → Int) (raw : RawDescriptor E Nat) (qs : List (DensePoly E))
    (expected : List Int) (zeros : List (DensePoly E))
    (targets : List (RawDescriptor E Nat)) : Bool :=
  match Descriptor.validate sign raw.context raw with
  | none => false
  | some d =>
    match d.prepareQueries with
    | none => false
    | some h =>
      match h.buildSigns qs, h.buildSigns [] with
      | .ok s, .ok empty =>
        s.values.toList == expected && empty.values.toList == [] &&
          h.checkSigns qs s.values s.evidence &&
          (qs.zip expected).all (fun (q, value) => h.signAt q == value) &&
          zeros.all (fun q => match h.buildSigns [q] with
            | .ok single => single.value == 0 && h.signAt q == 0
            | .error _ => false) &&
          targets.all (fun target =>
            match Descriptor.validate sign target.context target with
            | none => false
            | some other => match other.prepareQueries with
              | none => false
              | some otherHandle => !otherHandle.checkSigns qs s.values s.evidence)
      | _, _ => false

def ratX : DensePoly Rat := DensePoly.ofList [0, 1]
def ratRaw : RawDescriptor Rat Nat :=
  ⟨7, ratX * ratX - 1, .negInf, .posInf, [1], [1]⟩

#guard preparedAs Sturm.orderSign ratRaw [ratX, ratX - 1, -ratX, ratX] [1, 0, -1, 1]
  [0, ratX - 1] [{ratRaw with context := 8}, {ratRaw with signs := [-1]},
    {ratRaw with lower := .finite 0, upper := .finite 2}]

-- An equivalent defining polynomial has different stored nonzero
-- coefficients. Reusing its old literal evidence must still be rejected.
def repRaw : RawDescriptor HexPoly.InterpretTests.Rep Nat :=
  ⟨7, Hex.TarskiTests.Noncanonical.head, .negInf, .posInf, [1], [1]⟩

#guard preparedAs Hex.TarskiTests.Noncanonical.sign repRaw
  [HexPoly.InterpretTests.x, HexPoly.InterpretTests.x - DensePoly.C HexPoly.InterpretTests.root]
  [1, 0] [HexPoly.InterpretTests.x - DensePoly.C HexPoly.InterpretTests.root]
  [{repRaw with head := HexPoly.InterpretTests.x * HexPoly.InterpretTests.x - 1}]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard preparedAs fieldSign raw queries [1, -1, 0, 1]
  [0, xPoly.natPow 3 - DensePoly.C 2]
  [{raw with context := 8}, {raw with signs := [-1]},
    {raw with lower := .finite 1, upper := .finite 2}]

/-- The prepared operations apply directly to arbitrary descriptors and
queries over the actual cubic field, preserving the original selected root. -/
theorem cubic_queries (d : Descriptor CubicField Nat fieldSign 7) (h : QueryHandle d)
    (qs : List (DensePoly CubicField)) :
    ∃ s : SelectedSigns d qs, h.buildSigns qs = .ok s ∧
      s.values.toList = signsAt (Field.value rep)
        (Field.value_eq_zero rep binding real) qs
        (d.root (Field.value rep) (Field.value_eq_zero rep binding real)
          (Field.value_one rep binding real) (Field.value_add rep binding real)
          (Field.value_sub rep binding real) (Field.value_mul rep binding real)
          (Field.value_natCast rep binding real) sign_spec) := by
  exact h.buildSigns_roots (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg (Field.value_inv rep binding real) qs

/-- info: 'Hex.SignDet.QueryHandle.buildSigns_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueryHandle.buildSigns_eq
/-- info: 'Hex.SignDet.QueryHandle.signAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueryHandle.signAt_eq
/-- info: 'Hex.SignDet.Descriptor.prepareQueries_success' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.prepareQueries_success
/-- info: 'Hex.SignDet.QueryHandle.buildSigns_roots' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueryHandle.buildSigns_roots
/-- info: 'Hex.SignDet.QueryHandle.signAt_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueryHandle.signAt_correct
/-- info: 'Hex.SignDetMathlib.QueryHandleConformance.cubic_queries' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cubic_queries

end Hex.SignDetMathlib.QueryHandleConformance
