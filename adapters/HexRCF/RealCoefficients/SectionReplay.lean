/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.SelectedFormula
public import HexRealClosure.RootReplay

public section
namespace Hex.RCF.RealCoefficients.SectionReplay
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Keep canonical predecessor instances when projecting a reconstructed root. -/
@[expose] def rowCodec (value : ValueCodec parent.Value)
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature) :=
  Algebraic.SignEvidence.codec value Signature.codec context.root.raw

/-- Check one frozen section and its entire Boolean row. The codec must restore
the predecessor's exact values using checked evidence. Original guards are
tested before parsing any descriptor or row; this checker never produces roots.
A false result describes this section only, not a false existential sentence. -/
@[expose, macro_inline] def check (original : Model parent ℝ)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (subject graph row : Codec.Json) : Except Replay.Error Bool :=
  if !guards.all (fun d => Decidable.decide (d ≠ 0)) then .error .divisor
  else match Algebraic.RootReplay.readDescriptor value Signature.codec
      parent.sign parent.signature subject graph with
    | .error _ => .error .evidence
    | .ok root =>
      match (Algebraic.SignEvidence.codec value Signature.codec root.raw).decode row with
      | .error _ => .error .evidence
      | .ok evidence => SelectedFormula.checkRow original values guards formula
          (Algebraic.Context.adjoin root parent.isClean) evidence

/-- Eight equal supplied operations are used both to reconstruct the section
and to check its row. Missing stored literal facts reject decoding; missing
intermediate arithmetic facts remain visible to kernel replay. -/
@[expose, macro_inline] def checkWith (original : Model parent ℝ)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (pOne : One parent.Value) (pAdd : Add parent.Value) (pNeg : Neg parent.Value)
    (pSub : Sub parent.Value) (pMul : Mul parent.Value) (pInv : Inv parent.Value)
    (pDiv : Div parent.Value) (pNat : NatCast parent.Value)
    (ho : pOne = (Tower.instOneValue parent)) (ha : pAdd = (Tower.instAddValue parent))
    (hn : pNeg = (Tower.instNegValue parent)) (hs : pSub = (Tower.instSubValue parent))
    (hm : pMul = (Tower.instMulValue parent)) (hi : pInv = (Tower.instInvValue parent))
    (hd : pDiv = (Tower.instDivValue parent)) (hc : pNat = (Tower.instNatCastValue parent))
    (subject graph row : Codec.Json) : Except Replay.Error Bool :=
  if !guards.all (fun d => Decidable.decide (d ≠ 0)) then .error .divisor
  else match @Algebraic.RootReplay.readContext parent.Value Signature
      (Tower.instZeroValue parent) (Tower.instDecidableEqValue parent) inferInstance
      (Tower.instOneValue parent) (Tower.instAddValue parent) (Tower.instNegValue parent)
      (Tower.instSubValue parent) (Tower.instMulValue parent) (Tower.instInvValue parent)
      (Tower.instDivValue parent) (Tower.instNatCastValue parent)
      value Signature.codec parent.sign parent.signature parent.isClean
      pOne pAdd pNeg pSub pMul pInv pDiv pNat ho ha hn hs hm hi hd hc subject graph with
    | .error _ => .error .evidence
    | .ok context =>
      match (rowCodec value context).decode row with
      | .error _ => .error .evidence
      | .ok evidence => SelectedFormula.checkRowWith original values guards formula context
          pOne pAdd pNeg pSub pMul pInv pDiv pNat ho ha hn hs hm hi hd hc evidence

theorem checkWith_eq (original : Model parent ℝ)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (pOne : One parent.Value) (pAdd : Add parent.Value) (pNeg : Neg parent.Value)
    (pSub : Sub parent.Value) (pMul : Mul parent.Value) (pInv : Inv parent.Value)
    (pDiv : Div parent.Value) (pNat : NatCast parent.Value)
    (ho : pOne = (Tower.instOneValue parent)) (ha : pAdd = (Tower.instAddValue parent))
    (hn : pNeg = (Tower.instNegValue parent)) (hs : pSub = (Tower.instSubValue parent))
    (hm : pMul = (Tower.instMulValue parent)) (hi : pInv = (Tower.instInvValue parent))
    (hd : pDiv = (Tower.instDivValue parent)) (hc : pNat = (Tower.instNatCastValue parent))
    (subject graph row : Codec.Json) :
    checkWith original value values guards formula pOne pAdd pNeg pSub pMul pInv pDiv pNat
      ho ha hn hs hm hi hd hc subject graph row =
      check original value values guards formula subject graph row := by
  cases ho
  cases ha
  cases hn
  cases hs
  cases hm
  cases hi
  cases hd
  cases hc
  unfold checkWith check
  rw [Algebraic.RootReplay.readContext_eq]
  split
  · rfl
  · cases Algebraic.RootReplay.readDescriptor value Signature.codec parent.sign
        parent.signature subject graph with
    | error message => rfl
    | ok root =>
      simp only [Except.map, rowCodec, Algebraic.Context.root_adjoin]
      cases (Algebraic.SignEvidence.codec value Signature.codec root.raw).decode row with
      | error message => rfl
      | ok evidence =>
        exact SelectedFormula.checkRowWith_eq original values guards formula
          (Algebraic.Context.adjoin root parent.isClean)
          _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl evidence

/-- Acceptance retains the complete checked section identity and literal row. -/
theorem check_fields (original : Model parent ℝ)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (subject graph row : Codec.Json) (result : Bool)
    (accepted : check original value values guards formula subject graph row = .ok result) :
    ∃ root : Descriptor parent.Value Signature parent.sign parent.signature,
      Algebraic.SignRequests.readRoot value Signature.codec subject = .ok root.raw ∧
      ∃ evidence, (Algebraic.SignEvidence.codec value Signature.codec root.raw).decode row =
        .ok evidence ∧ SelectedFormula.checkRow original values guards formula
          (Algebraic.Context.adjoin root parent.isClean) evidence = .ok result := by
  unfold check at accepted
  split at accepted
  · contradiction
  · cases hr : Algebraic.RootReplay.readDescriptor value Signature.codec parent.sign
        parent.signature subject graph with
    | error message => simp only [hr] at accepted; contradiction
    | ok root =>
      simp only [hr] at accepted
      cases he : (Algebraic.SignEvidence.codec value Signature.codec root.raw).decode row with
      | error message => simp only [he] at accepted; contradiction
      | ok evidence =>
        simp only [he] at accepted
        exact ⟨root, Algebraic.RootReplay.readDescriptor_subject _ _ _ _ _ _ root hr,
          evidence, he, accepted⟩

theorem check_domains (original : Model parent ℝ)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (subject graph row : Codec.Json) (result : Bool)
    (accepted : check original value values guards formula subject graph row = .ok result) :
    ∀ d ∈ guards, original.value d ≠ 0 := by
  obtain ⟨root, _, evidence, _, checked⟩ :=
    check_fields original value values guards formula subject graph row result accepted
  exact SelectedFormula.row_domains original values guards formula _ evidence result checked

/-- One accepted true section yields one ordinary real witness. Domain atoms
remain in the shared matrix. No coverage or false-existential claim is made. -/
theorem check_sound (original : Model parent ℝ)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (subject graph row : Codec.Json)
    (accepted : check original value values guards formula subject graph row = .ok true) :
    ∃ x : ℝ, formula.toProp (Samples.valuation original values x) := by
  obtain ⟨root, _, evidence, _, checked⟩ :=
    check_fields original value values guards formula subject graph row true accepted
  exact SelectedFormula.row_sound original values guards formula _ evidence checked

/-- False at this section supplies only a universal counterexample. -/
theorem check_false (original : Model parent ℝ)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (subject graph row : Codec.Json)
    (accepted : check original value values guards formula subject graph row = .ok false) :
    ∃ x : ℝ, ¬ formula.toProp (Samples.valuation original values x) := by
  obtain ⟨root, _, evidence, _, checked⟩ :=
    check_fields original value values guards formula subject graph row false accepted
  exact SelectedFormula.row_false original values guards formula _ evidence checked

/-- All supplied original guards are checked even when every packet is malformed. -/
theorem check_zero (original : Model parent ℝ)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (subject graph row : Codec.Json) (d : parent.Value)
    (member : d ∈ guards) (zero : d = 0) :
    check original value values guards formula subject graph row = .error .divisor := by
  have bad : guards.all (fun d => Decidable.decide (d ≠ 0)) = false := by
    apply Bool.eq_false_iff.mpr
    intro valid
    exact (of_decide_eq_true ((List.all_eq_true.mp valid) d member)) zero
  simp only [check, bad, Bool.not_false, ite_true]

end Hex.RCF.RealCoefficients.SectionReplay
