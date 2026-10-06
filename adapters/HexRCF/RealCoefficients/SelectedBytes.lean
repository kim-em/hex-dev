/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.RealCoefficients.SelectedFormula
public import HexRealClosure.SignEvidence

public section

namespace Hex.RCF.RealCoefficients.SelectedFormula
open Hex Hex.RealClosure Hex.SignDet
open Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Pin the packet codec to the context's canonical `Zero` and `DecidableEq`. -/
@[expose] def packetCodec
    (context : Algebraic.Context parent.Value Tower.Signature parent.sign parent.signature)
    (value : ValueCodec parent.Value) (ctx : ValueCodec Tower.Signature) :=
  Algebraic.SignEvidence.codec value ctx context.root.raw

/-- Preflight supplied original divisors before byte parsing. The outer result
retains the owner's decoding and authentication errors without classifying diagnostic strings; the
inner result retains typed mathematical replay errors and diagnostic false.
Source identities and the real parent model remain caller obligations.
`Codec.Limits` bound lexical decoding only. Compiled canonical arithmetic may
run native production; decoding also depends on the supplied value codec. -/
@[expose, macro_inline] def checkBytes (original : Tower.Model parent ℝ)
    (values : Fin n → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF (n+1))
    (context : Algebraic.Context parent.Value Tower.Signature parent.sign parent.signature)
    (value : ValueCodec parent.Value) (ctx : ValueCodec Tower.Signature)
    (input : ByteArray) (limits : Codec.Limits := {}) :
    Except String (Except Replay.Error Bool) :=
  if !guards.all (fun d => Decidable.decide (d ≠ 0)) then .ok (.error .divisor)
  else ((packetCodec context value ctx).decodeBytes input limits).map
    (checkRow original values guards formula context)

/-- Use the same eight equal supplied operations as checked literal row replay.
`Codec.Limits` bound lexical decoding only. Operation agreement does not exclude
native production: compiled cached arithmetic can produce on a fact miss, and
decoding depends on the supplied value codec. -/
@[expose, macro_inline] def checkBytesWith (original : Model parent ℝ) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (pOne : One parent.Value) (pAdd : Add parent.Value) (pNeg : Neg parent.Value)
    (pSub : Sub parent.Value) (pMul : Mul parent.Value) (pInv : Inv parent.Value)
    (pDiv : Div parent.Value) (pNat : NatCast parent.Value)
    (ho : pOne = (Tower.instOneValue parent)) (ha : pAdd = (Tower.instAddValue parent)) (hn : pNeg = (Tower.instNegValue parent))
    (hs : pSub = (Tower.instSubValue parent)) (hm : pMul = (Tower.instMulValue parent)) (hi : pInv = (Tower.instInvValue parent))
    (hd : pDiv = (Tower.instDivValue parent)) (hc : pNat = (Tower.instNatCastValue parent))
    (value : ValueCodec parent.Value) (ctx : ValueCodec Signature)
    (input : ByteArray) (limits : Codec.Limits := {}) : Except String (Except Replay.Error Bool) :=
  if !guards.all (fun d => Decidable.decide (d ≠ 0)) then .ok (.error .divisor)
  else ((packetCodec context value ctx).decodeBytes input limits).map
    (fun evidence => checkRowWith original values guards formula context pOne pAdd pNeg pSub pMul pInv pDiv pNat
        ho ha hn hs hm hi hd hc evidence)


/-- Every byte success, false row and refusal agrees with canonical operations. -/
theorem checkBytesWith_eq (original : Model parent ℝ) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (pOne : One parent.Value) (pAdd : Add parent.Value) (pNeg : Neg parent.Value)
    (pSub : Sub parent.Value) (pMul : Mul parent.Value) (pInv : Inv parent.Value)
    (pDiv : Div parent.Value) (pNat : NatCast parent.Value)
    (ho : pOne = (Tower.instOneValue parent)) (ha : pAdd = (Tower.instAddValue parent)) (hn : pNeg = (Tower.instNegValue parent))
    (hs : pSub = (Tower.instSubValue parent)) (hm : pMul = (Tower.instMulValue parent)) (hi : pInv = (Tower.instInvValue parent))
    (hd : pDiv = (Tower.instDivValue parent)) (hc : pNat = (Tower.instNatCastValue parent))
    (value : ValueCodec parent.Value) (ctx : ValueCodec Signature)
    (input : ByteArray) (limits : Codec.Limits) :
    checkBytesWith original values guards formula context pOne pAdd pNeg pSub pMul pInv pDiv pNat
      ho ha hn hs hm hi hd hc value ctx input limits =
      checkBytes original values guards formula context value ctx input limits := by
  unfold checkBytesWith checkBytes
  split
  · rfl
  · apply congrArg (fun f => ((packetCodec context value ctx).decodeBytes
      input limits).map f)
    funext evidence
    exact checkRowWith_eq original values guards formula context pOne pAdd pNeg pSub pMul pInv pDiv pNat
      ho ha hn hs hm hi hd hc evidence


section
variable (original : Tower.Model parent ℝ) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (context : Algebraic.Context parent.Value Tower.Signature parent.sign parent.signature)
    (value : ValueCodec parent.Value) (ctx : ValueCodec Tower.Signature)
    (input : ByteArray) (limits : Codec.Limits)

/-- Accepted bytes provide the actual decoded packet and checked row. -/
theorem bytes_evidence (result : Bool)
    (accepted : checkBytes original values guards formula context value ctx input limits =
      .ok (.ok result)) :
    ∃ evidence, (packetCodec context value ctx).decodeBytes input limits =
      .ok evidence ∧ checkRow original values guards formula context evidence = .ok result := by
  unfold checkBytes at accepted
  split at accepted
  · cases Except.ok.inj accepted
  · cases parsed : (packetCodec context value ctx).decodeBytes input limits with
    | error message => simp [parsed, Except.map] at accepted
    | ok evidence =>
      exact ⟨evidence, rfl, by simpa [parsed, Except.map] using accepted⟩

theorem bytes_domains (result : Bool)
    (accepted : checkBytes original values guards formula context value ctx input limits =
      .ok (.ok result)) : ∀ d ∈ guards, original.value d ≠ 0 := by
  obtain ⟨evidence, _, checked⟩ := bytes_evidence original values guards formula context value ctx
    input limits result accepted
  exact row_domains original values guards formula context evidence result checked

theorem bytes_sound
    (accepted : checkBytes original values guards formula context value ctx input limits =
      .ok (.ok true)) : ∃ x : ℝ, formula.toProp (Samples.valuation original values x) := by
  obtain ⟨evidence, _, checked⟩ := bytes_evidence original values guards formula context value ctx
    input limits true accepted
  exact row_sound original values guards formula context evidence checked

theorem bytes_false
    (accepted : checkBytes original values guards formula context value ctx input limits =
      .ok (.ok false)) : ∃ x : ℝ, ¬ formula.toProp (Samples.valuation original values x) := by
  obtain ⟨evidence, _, checked⟩ := bytes_evidence original values guards formula context value ctx
    input limits false accepted
  exact row_false original values guards formula context evidence checked

/-- A byte result has the source truth at exactly the same selected real point. -/
theorem bytes_spec (result : Bool)
    (accepted : checkBytes original values guards formula context value ctx input limits =
      .ok (.ok result)) :
    result = true ↔ formula.toProp (Samples.valuation original values
      (context.rootValue original.value original.zero_iff original.one original.add
        original.sub original.mul original.nat original.sign)) := by
  obtain ⟨evidence, _, checked⟩ := bytes_evidence original values guards formula context value ctx
    input limits result accepted
  exact row_spec original values guards formula context evidence result checked

/-- Successful byte decoding retains the exact row result, including rejection. -/
theorem bytes_decoded (evidence : Algebraic.SignEvidence parent.Value Tower.Signature)
    (decoded : (packetCodec context value ctx).decodeBytes input limits = .ok evidence) :
    checkBytes original values guards formula context value ctx input limits =
      .ok (checkRow original values guards formula context evidence) := by
  unfold checkBytes
  split
  · unfold checkRow
    rename_i bad
    rw [ite_eq_left bad]
  · rw [decoded]
    rfl

/-- A decoder refusal propagates unchanged when all original guards pass.
No error string determines a solver choice or a mathematical verdict. -/
theorem bytes_rejected (message : String)
    (valid : guards.all (fun d => Decidable.decide (d ≠ 0)) = true)
    (rejected : (packetCodec context value ctx).decodeBytes input limits = .error message) :
    checkBytes original values guards formula context value ctx input limits = .error message := by
  simp only [checkBytes, valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    rejected, Except.map]

/-- A zero original guard precedes every malformed-byte or lexical refusal. -/
theorem bytes_zero (zero : (0 : parent.Value) ∈ guards) :
    checkBytes original values guards formula context value ctx input limits = .ok (.error .divisor) := by
  unfold checkBytes
  have rejected : guards.all (fun d => Decidable.decide (d ≠ 0)) = false := by
    simpa using zero
  exact ite_eq_left (show (!guards.all (fun d => Decidable.decide (d ≠ 0))) = true by
    rw [rejected]; rfl)
end
end Hex.RCF.RealCoefficients.SelectedFormula
