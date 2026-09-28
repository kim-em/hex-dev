/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.TableProducer
public import HexSignDetMathlib.SelectedProducerConformance
public import HexRealRootsMathlib.TarskiTests
public meta import HexSignDetMathlib.SelectedProducerConformance
public meta import HexSignDet
public meta import HexRealRoots.TarskiTests
public meta import HexNumberField
public meta import HexRCF.RealCoefficients.Coefficients

public section

/-! Total table APIs retain the actual producer's rows and exact counts.
Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.TableConformance

open Hex Hex.SignDet Hex.SignDetMathlib.SelectedProducerConformance
open Hex.RCF.RealCoefficients HexPolyMathlib.Interpret

/-- All three public paths must agree with successful checked construction;
zero counts alone cannot pass by reaching the diagnostic fallback. -/
def countsAs {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E]
    [Mul E] [NatCast E] [Neg E] [Inv E]
    (sign : E → Int) (p : DensePoly E) (a b : Endpoint E)
    (qs : List (DensePoly E)) (reduced : Bool)
    (rows : List (List Int × Nat)) (zeros : List (List Int)) : Bool :=
  match Sturm.prepare sign p a b with
  | none => false
  | some domain =>
    match buildTablePrepared 7 domain qs reduced, determine sign 7 p a b qs reduced with
    | .ok checked, some actual =>
      let prepared := determinePrepared 7 domain qs reduced
      checked.rows.toList == rows && actual.rows.toList == rows &&
        prepared.rows.toList == rows &&
        zeros.all (fun word => checked.count word == 0 &&
          actual.count word == 0 && prepared.count word == 0)
    | _, _ => false

def ratX : DensePoly Rat := DensePoly.ofList [0, 1]
def ratHead : DensePoly Rat := ratX * ratX - 1

#guard countsAs Sturm.orderSign ratHead .negInf .posInf [ratX, ratX - 1] true
  [([-1, -1], 1), ([1, 0], 1)] [[0, 0], [1, 1], [], [1]]
#guard countsAs Sturm.orderSign ratHead .negInf .posInf [ratX, ratX - 1] false
  [([-1, -1], 1), ([1, 0], 1)] [[0, 0], [1, 1]]
#guard countsAs Sturm.orderSign ratHead (.finite 0) (.finite 2) [ratX, ratX - 1] true
  [([1, 0], 1)] [[-1, -1], [0, 0]]
#guard countsAs Sturm.orderSign ratHead .negInf .posInf [] true [([], 2)] [[0]]
#guard countsAs Sturm.orderSign ratHead .negInf .posInf [0] true [([0], 2)] [[-1], [1]]
#guard countsAs Sturm.orderSign ratHead .negInf .posInf [ratX, ratX] true
  [([-1, -1], 1), ([1, 1], 1)] [[-1, 1], [1, -1]]
#guard countsAs Sturm.orderSign (ratX * ratX + 1) .negInf .posInf [ratX] true [] [[-1], [0], [1]]
#guard countsAs Sturm.orderSign (DensePoly.C (2 : Rat)) .negInf .posInf [] true [] [[]]
#guard (determine Sturm.orderSign 7 (0 : DensePoly Rat) .negInf .posInf []).isNone
#guard (determine Sturm.orderSign 7 (ratHead * ratHead) .negInf .posInf [ratX]).isNone
#guard (determine Sturm.orderSign 7 ratHead (.finite 2) (.finite 0) []).isNone

-- This carrier has canonical zero and distinct representations of the same
-- nonzero value. It has ordinary operations and no field instance.
#guard countsAs Hex.TarskiTests.Noncanonical.sign Hex.TarskiTests.Noncanonical.head
  .negInf .posInf [HexPoly.InterpretTests.x] true
  [([-1], 1), ([1], 1)] [[0], []]
#guard decide (Hex.TarskiTests.Noncanonical.head ≠
  HexPoly.InterpretTests.x * HexPoly.InterpretTests.x - 1)

-- Real coefficients come from the selected embedding of the actual cubic
-- field. A nonzero query polynomial vanishes at one of the two head roots.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard countsAs fieldSign head .negInf .posInf
  [xPoly - DensePoly.C alpha, xPoly - 1, xPoly - DensePoly.C 2] true
  [([-1, -1, -1], 1), ([0, 1, -1], 1)] [[1, 1, -1], [0, 0, 0]]

/-- Negation respects the actual real embedding used by the coefficient sign. -/
theorem value_neg (a : CubicField) : Field.value rep (-a) = -Field.value rep a := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg, Field.value_complex rep binding real,
    Field.value_complex rep binding real, PolyQuot.map_neg]

/-- The generic correctness result applies directly to arbitrary successful
public tables over the nonquadratic coefficient field. -/
theorem cubic_table (p : DensePoly CubicField) (a b : Endpoint CubicField)
    (qs : List (DensePoly CubicField)) (reduced : Bool) (table : SignTable qs.length)
    (h : determine fieldSign 7 p a b qs reduced = some table) :
    HexSturmMathlib.Domain (Field.value rep) (Field.value_eq_zero rep binding real) p a b ∧
      ∀ word, table.count word =
        ((HexRealRootsMathlib.Tarski.rootsIn
          (interpret (Field.value rep) (Field.value_eq_zero rep binding real) p)
          (a.map (Field.value rep)) (b.map (Field.value rep))).filter
          (fun x => signsAt (Field.value rep) (Field.value_eq_zero rep binding real)
            qs x = word)).card := by
  exact determine_correct (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) value_neg (Field.value_inv rep binding real)
    fieldSign sign_spec 7 p a b qs reduced table h

/-- info: 'Hex.SignDet.SignTable.empty_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.SignTable.empty_count
/-- info: 'Hex.SignDet.buildTablePrepared_ofReplay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.buildTablePrepared_ofReplay
/-- info: 'Hex.SignDet.determinePrepared_ofBuild' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.determinePrepared_ofBuild
/-- info: 'Hex.SignDet.buildTablePrepared_success' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.buildTablePrepared_success
/-- info: 'Hex.SignDet.determinePrepared_success' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.determinePrepared_success
/-- info: 'Hex.SignDet.determinePrepared_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.determinePrepared_correct
/-- info: 'Hex.SignDet.determine_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.determine_isSome
/-- info: 'Hex.SignDet.determine_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.determine_correct
/-- info: 'Hex.SignDetMathlib.TableConformance.cubic_table' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_table

end Hex.SignDetMathlib.TableConformance
