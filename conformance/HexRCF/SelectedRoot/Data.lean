/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.RealCoefficients.SelectedFormula
public import HexRCF.SelectedRoot.Literals
public import HexRCF.RealCoefficients.NumberField
public import Std.Data.HashMap.Lemmas
public import HexSignDet.DagEncode
public import HexRealClosure.RootReplay

public import HexRealClosure.Algebraic
public import HexRealClosure.TowerContext
public import HexRealClosure.TowerSuffix
public import HexRealClosure.FrameFormat
public import HexSignDet.Descriptor
public import HexPoly.Euclid.DivGcd
public import HexRealClosure.SignRequests
public import HexSignDet.Codec
public import HexSignDet.Codec.Json
public import HexSignDet.Codec.Basic
public import HexSignDet.Codec.Node
public import HexSignDet.Codec.Evidence
public import HexSignDet.Codec.Value
public import HexSignDet.Dag
public import HexSignDet.DagReplay
public import HexRealRoots.TarskiShared
public import HexRealClosure.BaseContext
public import HexRealClosure.BaseJson

import all HexRCF.RealCoefficients.SelectedFormula
import all HexRCF.SelectedRoot.Literals
import all HexRCF.RealCoefficients.NumberField
import all HexSignDet.DagEncode
import all HexRealClosure.RootReplay
import all HexRealClosure.Algebraic
import all HexRealClosure.TowerContext
import all HexRealClosure.TowerSuffix
import all HexRealClosure.FrameFormat
import all HexSignDet.Descriptor
import all HexPoly.Euclid.DivGcd
import all HexRealClosure.SignRequests
import all HexSignDet.Codec
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Dag
import all HexSignDet.DagReplay
import all HexRealRoots.TarskiShared
import all HexRealClosure.BaseContext
import all HexRealClosure.BaseJson

@[expose] public section

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.SelectedRootTests.Data
open Hex.RCF.SelectedRootTests

theorem encodeLeaf {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
    [Hashable E] [Hashable Ctx] (node : Node E Ctx) :
    Dag.encode (.leaf node) = ⟨#[⟨node, none⟩], 0⟩ := by
  simp only [Dag.encode, Dag.encodeFrom, Dag.Encoder.insert,
    Std.HashMap.getElem?_empty]
  rfl

def registry : BaseContext.Registry := fun _ => none
abbrev base := NumberField.base registry
def lowerRead := Algebraic.RootReplay.readDescriptor base.codec Tower.Signature.codec
  base.sign base.signature Literals.lowerSubject Literals.lowerGraph
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem lowerAccepted : lowerRead.toOption.isSome = true := by
  decide +kernel
def lower := lowerRead.toOption.get lowerAccepted
set_option maxRecDepth 32768 in
theorem lowerLeaf : lower.evidence = .leaf lower.evidence.node := by
  have shape : (match lower.evidence with
      | .leaf _ => true | .split _ _ _ => false) = true := by decide +kernel
  cases he : lower.evidence with
  | leaf node => rfl
  | split node left right => simp only [he, Bool.false_eq_true] at shape
def extension := base.adjoin lower
def upperFieldsRead := Codec.tuple 6 Literals.upperSubject
set_option maxRecDepth 32768 in
theorem upperFieldsAccepted : upperFieldsRead.toOption.isSome = true := by decide +kernel
def upperFields := upperFieldsRead.toOption.get upperFieldsAccepted
def signatureRead := Tower.Signature.codec.decode upperFields[0]
set_option maxRecDepth 32768 in
theorem signatureAccepted : signatureRead.toOption.isSome = true := by decide +kernel
def frozenSignature := signatureRead.toOption.get signatureAccepted
set_option maxRecDepth 32768 in
theorem frameIndex : 0 < frozenSignature.roots.length := by decide +kernel
def frozenFrame := frozenSignature.roots[0]'frameIndex
set_option maxRecDepth 32768 in
theorem frozenRootData : Tower.rootData base.codec lower = frozenFrame.toJson := by
  let : Hashable base.Value := ⟨fun a => hash (base.codec.encode a)⟩
  let : Hashable Tower.Signature := ⟨fun _ => 0⟩
  unfold Tower.rootData
  dsimp only
  rw [lowerLeaf, encodeLeaf]
  decide +kernel

theorem frame_eq : extension.frame = frozenFrame := by
  have encoded := extension.encoded
  rw [frozenRootData, Tower.Literal.ofJson_toJson] at encoded
  exact (Option.some.inj encoded).symm
theorem frameEncoded : Tower.Literal.ofJson (Tower.rootData base.codec lower) = some frozenFrame := by
  rw [frozenRootData, Tower.Literal.ofJson_toJson]

abbrev parent : Tower.Context registry :=
  .pack (.root (.base (BaseContext.rational registry)) lower frozenFrame frameEncoded)

theorem parent_eq : extension.context = parent := by
  exact Tower.Context.adjoin_root_eq (.base (BaseContext.rational registry))
    lower frozenFrame frameEncoded

set_option maxRecDepth 32768 in
theorem signature_eq : parent.signature = frozenSignature := by decide +kernel
/-- info: 'Hex.RCF.SelectedRootTests.Data.frozenRootData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frozenRootData
/-- info: 'Hex.RCF.SelectedRootTests.Data.signature_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signature_eq

abbrev native := Algebraic.Context.adjoin lower base.isClean
noncomputable def original : Tower.Model parent ℝ :=
  (NumberField.rationalModel registry).root (.base (BaseContext.rational registry))
    lower frozenFrame frameEncoded
noncomputable abbrev rational := NumberField.rationalModel registry
@[simp] theorem rationalZero : rational.value (0 : base.Value) = 0 := (rational.zero_iff 0).mpr rfl
@[simp] theorem rationalOne : rational.value (1 : base.Value) = 1 := rational.one
@[simp] theorem rationalNat (n : Nat) : rational.value (n : base.Value) = (n : ℝ) := rational.nat n
@[simp] theorem rationalNeg (a : base.Value) : rational.value (-a) = -rational.value a := rational.neg a
@[simp] theorem rationalTwo : rational.value (2 : base.Value) = 2 := rational.nat 2
@[simp] theorem rationalNegativeTwo : rational.value (-2 : base.Value) = -2 := by
  rw [rational.neg, rationalTwo]
noncomputable def selectedReal : ℝ := lower.root rational.value rational.zero_iff rational.one
  rational.add rational.sub rational.mul rational.nat rational.sign
set_option maxRecDepth 32768 in
theorem lowerData : lower.raw.head = DensePoly.ofList [-2,0,1] ∧
    lower.raw.lower = .finite 1 ∧ lower.raw.upper = .finite 2 := by decide +kernel

open HexPolyMathlib.Interpret in
theorem variablePoly : interpret rational.value rational.zero_iff
    (DensePoly.ofList [0,1] : base.Poly) = Polynomial.X := by
  ext i
  cases i with
  | zero => simp [coeff_interpret, DensePoly.ofList, DensePoly.coeff_ofCoeffs, rationalZero]
  | succ i => cases i with
    | zero => simp [coeff_interpret, DensePoly.ofList, DensePoly.coeff_ofCoeffs, rationalOne]
    | succ i =>
      simp [coeff_interpret, DensePoly.ofList, DensePoly.coeff_ofCoeffs, Polynomial.coeff_X]
      exact rationalZero

open HexPolyMathlib.Interpret in
theorem definingPoly : interpret rational.value rational.zero_iff lower.raw.head =
    (Polynomial.X ^ 2 - 2 : Polynomial ℝ) := by
  rw [lowerData.1]
  ext i
  rcases i with _ | _ | _ | i
  all_goals simp [coeff_interpret, DensePoly.ofList, DensePoly.coeff_ofCoeffs,
    rationalZero, rationalOne, Polynomial.coeff_X_pow]
  all_goals first | exact rationalZero | exact rationalNegativeTwo

theorem selectedFacts : selectedReal ^ 2 = 2 ∧ 1 < selectedReal ∧ selectedReal < 2 := by
  have member := (lower.root_spec rational.value rational.zero_iff rational.one rational.add
    rational.sub rational.mul rational.nat rational.sign).1
  have data := (HexRealRootsMathlib.Tarski.mem_rootsIn_iff _
    (lower.head_ne_zero rational.value rational.zero_iff) _ _ _).mp member
  rw [definingPoly] at data
  simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero,
    lowerData.2.1, lowerData.2.2, Endpoint.map, selectedReal, rationalTwo] using data

theorem selectedSqrt : selectedReal = Real.sqrt 2 := by
  have facts := selectedFacts
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
def coordinate : base.Poly := DensePoly.ofList [0,1]
theorem variableSign : native.signPoly coordinate = 1 := by
  rw [native.signPoly_spec rational.value rational.zero_iff rational.one rational.add rational.sub
    rational.mul rational.nat rational.sign rational.neg rational.inv]
  simp only [Algebraic.Context.evalPoly, coordinate]
  erw [variablePoly, Polynomial.eval_X]
  change (SignType.sign selectedReal : Int) = 1
  simp [_root_.sign_pos (show 0 < selectedReal from lt_trans (by norm_num) selectedFacts.2.1)]
def alpha : Algebraic.Element native := Algebraic.Element.restore coordinate 1 variableSign (by decide +kernel)
set_option maxRecDepth 32768 in
theorem clean : native.canReduce = true := by
  rw [native.reduce_checked]
  decide +kernel
set_option maxRecDepth 32768 in
theorem monic : lower.raw.head.leadingCoeff = 1 := by decide +kernel
def reduction (p : base.Poly) : base.Poly := (DensePoly.divModMonic p lower.raw.head monic).2
theorem reduction_eq : reduction = native.reduce := by
  funext p
  rw [Algebraic.Context.reduce, dite_eq_left clean]
  rfl
set_option maxRecDepth 32768 in
theorem variableReduced : native.reduce coordinate = coordinate := by
  rw [← reduction_eq]
  decide +kernel

theorem generator_eq : extension.generator = alpha := by
  change Algebraic.Element.ofPoly coordinate = alpha
  have equality := Algebraic.Element.ofPoly_restore (context := native) coordinate 1
    (show native.signPoly (native.reduce coordinate) = 1 by rw [variableReduced]; exact variableSign)
    (by decide +kernel)
  have same : native.reduce coordinate = coordinate := variableReduced
  simpa only [same, alpha] using equality

theorem alpha_value : original.value alpha = Real.sqrt 2 := by
  rw [← generator_eq]
  have selected := (NumberField.rationalModel registry).root_generator
    (.base (BaseContext.rational registry)) lower frozenFrame frameEncoded
  exact selected.trans selectedSqrt
/-- info: 'Hex.RCF.SelectedRootTests.Data.parent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parent_eq
/-- info: 'Hex.RCF.SelectedRootTests.Data.lowerAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerAccepted
/-- info: 'Hex.RCF.SelectedRootTests.Data.selectedSqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selectedSqrt
/-- info: 'Hex.RCF.SelectedRootTests.Data.alpha_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alpha_value
end Hex.RCF.SelectedRootTests.Data
