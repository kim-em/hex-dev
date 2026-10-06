/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Samples
public import HexRCF.RealCoefficients.Replay
public import HexRealClosureTheory.FactReplay

public section

/-! A checked joint row at one ordinary selected real root. The supplied real
model is a faithful interpretation of the parent field. This interface supplies
neither that model nor complete root coverage. A true row gives one witness;
a false row gives one counterexample, not a false existential decision.

Frozen replay must supply checked coefficient operations and construct the
parent, coefficients and root from checked data. Operation agreement alone
does not establish that their construction avoids native sign production. -/

namespace Hex.RCF.RealCoefficients.SelectedFormula
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Keep the restored fact's canonical operations fixed when projecting its
sign under locally supplied equal operation instances. -/
@[expose] def factSign (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (fact : Algebraic.SignFact context) : Int := fact.sign

/-- A row result concerns this selected point, never an existential decision.
The supplied divisor values are checked before inspecting the packet. The
frontend must authenticate their identities and collect every original divisor.
Inlining keeps the noncomputable real model out of compiled checking. -/
@[expose, macro_inline] def checkRow (original : Model parent ℝ) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (evidence : Algebraic.SignEvidence parent.Value Signature) : Except Replay.Error Bool :=
  if !guards.all (fun d => Decidable.decide (d ≠ 0)) then .error .divisor
  else match context.readEvidence? original.value original.zero_iff original.one original.add
      original.sub original.mul original.nat original.sign original.neg original.inv
      (RepresentationSpecialize.prepare values formula) evidence with
    | none => .error .evidence
    | some facts => match Samples.Row.eval formula (facts.toList.map (factSign context)) with
      | none => .error .unresolved
      | some value => .ok value

/-- Supply exactly the owner's eight checked predecessor operations for both
specialization and packet checking. No native alternative is tried on failure.
Inlining keeps the noncomputable real model out of compiled checking. -/
@[expose, macro_inline] def checkRowWith (original : Model parent ℝ) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (pOne : One parent.Value) (pAdd : Add parent.Value) (pNeg : Neg parent.Value)
    (pSub : Sub parent.Value) (pMul : Mul parent.Value) (pInv : Inv parent.Value)
    (pDiv : Div parent.Value) (pNat : NatCast parent.Value)
    (ho : pOne = (Tower.instOneValue parent)) (ha : pAdd = (Tower.instAddValue parent)) (hn : pNeg = (Tower.instNegValue parent))
    (hs : pSub = (Tower.instSubValue parent)) (hm : pMul = (Tower.instMulValue parent)) (hi : pInv = (Tower.instInvValue parent))
    (hd : pDiv = (Tower.instDivValue parent)) (hc : pNat = (Tower.instNatCastValue parent))
    (evidence : Algebraic.SignEvidence parent.Value Signature) : Except Replay.Error Bool :=
  if !guards.all (fun d => Decidable.decide (d ≠ 0)) then .error .divisor
  else
    let required := @RepresentationSpecialize.prepare parent.Value _ _ pOne pAdd pMul pNeg pNat
      n values formula
    match @Algebraic.Context.readEvidenceWith? parent.Value Signature ℝ
        (Tower.instZeroValue parent) (Tower.instDecidableEqValue parent)
        (Tower.instOneValue parent) (Tower.instAddValue parent) (Tower.instNegValue parent)
        (Tower.instSubValue parent) (Tower.instMulValue parent) (Tower.instInvValue parent)
        (Tower.instDivValue parent) (Tower.instNatCastValue parent)
        _ parent.sign parent.signature _ _ _ _ _
        original.value original.zero_iff original.one original.add
        original.sub original.mul original.nat original.sign original.neg original.inv context
        pOne pAdd pNeg pSub pMul pInv pDiv pNat ho ha hn hs hm hi hd hc required evidence with
      | none => .error .evidence
      | some facts => match Samples.Row.eval formula (facts.toList.map (factSign context)) with
        | none => .error .unresolved
        | some value => .ok value

/-- Equal checked operations preserve every success, false row and failure. -/
theorem checkRowWith_eq (original : Model parent ℝ) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (pOne : One parent.Value) (pAdd : Add parent.Value) (pNeg : Neg parent.Value)
    (pSub : Sub parent.Value) (pMul : Mul parent.Value) (pInv : Inv parent.Value)
    (pDiv : Div parent.Value) (pNat : NatCast parent.Value)
    (ho : pOne = (Tower.instOneValue parent)) (ha : pAdd = (Tower.instAddValue parent)) (hn : pNeg = (Tower.instNegValue parent))
    (hs : pSub = (Tower.instSubValue parent)) (hm : pMul = (Tower.instMulValue parent)) (hi : pInv = (Tower.instInvValue parent))
    (hd : pDiv = (Tower.instDivValue parent)) (hc : pNat = (Tower.instNatCastValue parent))
    (evidence : Algebraic.SignEvidence parent.Value Signature) :
    checkRowWith original values guards formula context pOne pAdd pNeg pSub pMul pInv pDiv pNat
      ho ha hn hs hm hi hd hc evidence = checkRow original values guards formula context evidence := by
  cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
  unfold checkRowWith checkRow
  dsimp only
  rw [Algebraic.Context.readEvidenceWith_eq]
  split
  · rfl
  · cases context.readEvidence? original.value original.zero_iff original.one original.add
        original.sub original.mul original.nat original.sign original.neg original.inv
        (RepresentationSpecialize.prepare values formula) evidence <;> rfl

/-- All source signs refer to the same ordinary selected real root. -/
theorem source_signs (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1))
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (signs : SelectedSigns context.root (RepresentationSpecialize.prepare values formula)) :
    signs.values.toList = formula.polys.map (fun q =>
      (SignType.sign (q.eval (Samples.valuation original values
        (context.rootValue original.value original.zero_iff original.one original.add
          original.sub original.mul original.nat original.sign))) : Int)) := by
  have exactRow := signs.values_at_root original.value original.zero_iff original.one
    original.add original.sub original.mul original.nat original.sign
  have evaluations := Samples.prepare_real original values formula
    (context.rootValue original.value original.zero_iff original.one original.add
      original.sub original.mul original.nat original.sign)
  rw [exactRow]
  simpa only [signsAt, List.map_map, Function.comp_def,
    RepresentationSpecialize.evaluate, Algebraic.Context.rootValue] using
    congrArg (List.map (fun a : ℝ => (SignType.sign a : Int))) evaluations

theorem fact_signs (original : Model parent ℝ)
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    {queries : List (DensePoly parent.Value)} (signs : SelectedSigns context.root queries) :
    (context.signFacts original.value original.zero_iff original.one original.add original.sub
      original.mul original.nat original.sign original.neg original.inv signs).toList.map
      Algebraic.SignFact.sign = signs.values.toList := by
  rw [← Vector.toList_map]
  apply congrArg Vector.toList
  apply Vector.ext
  intro i hi
  simpa only [Vector.getElem_map] using
    (context.signFacts_fields original.value original.zero_iff original.one original.add original.sub
      original.mul original.nat original.sign original.neg original.inv signs ⟨i, hi⟩).2

section Row
variable (original : Model parent ℝ) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (evidence : Algebraic.SignEvidence parent.Value Signature)

/-- A result requires every original divisor to be nonzero in the real model. -/
theorem row_domains (result : Bool)
    (accepted : checkRow original values guards formula context evidence = .ok result) :
    ∀ d ∈ guards, original.value d ≠ 0 := by
  unfold checkRow at accepted
  split at accepted
  · contradiction
  · rename_i valid
    have nozero : (0 : parent.Value) ∉ guards := by simpa using valid
    intro d member zero
    have same := (original.zero_iff d).mp zero
    exact nozero (same ▸ member)

/-- A checked result is exactly the formula's truth at this selected real point. -/
theorem row_spec (result : Bool)
    (accepted : checkRow original values guards formula context evidence = .ok result) :
    result = true ↔ formula.toProp (Samples.valuation original values
      (context.rootValue original.value original.zero_iff original.one original.add
        original.sub original.mul original.nat original.sign)) := by
  unfold checkRow at accepted
  split at accepted
  · contradiction
  · cases packet : context.readEvidence? original.value original.zero_iff original.one
        original.add original.sub original.mul original.nat original.sign original.neg
        original.inv (RepresentationSpecialize.prepare values formula) evidence with
    | none => simp only [packet] at accepted; contradiction
    | some facts =>
      obtain ⟨signs, _, equal⟩ := context.readEvidence_evidence original.value original.zero_iff
        original.one original.add original.sub original.mul original.nat original.sign
        original.neg original.inv _ evidence facts packet
      subst facts
      simp only [packet] at accepted
      have row := fact_signs original context signs
      change (context.signFacts original.value original.zero_iff original.one original.add
        original.sub original.mul original.nat original.sign original.neg original.inv signs).toList.map
        (factSign context) = signs.values.toList at row
      rw [row] at accepted
      obtain ⟨value, evaluated, semantic⟩ := Samples.Row.eval_spec formula signs.values.toList
        _ (source_signs original values formula context signs)
      rw [evaluated] at accepted
      have same : value = result := Except.ok.inj accepted
      exact same ▸ semantic

/-- A true row supplies one real witness, including the shared domain atoms. -/
theorem row_sound
    (accepted : checkRow original values guards formula context evidence = .ok true) :
    ∃ x : ℝ, formula.toProp (Samples.valuation original values x) := by
  exact ⟨_, (row_spec original values guards formula context evidence true accepted).mp rfl⟩

/-- A false row is a counterexample at one point, never a false existential verdict. -/
theorem row_false
    (accepted : checkRow original values guards formula context evidence = .ok false) :
    ∃ x : ℝ, ¬ formula.toProp (Samples.valuation original values x) := by
  refine ⟨context.rootValue original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign, ?_⟩
  intro truth
  have impossible := (row_spec original values guards formula context evidence false accepted).mpr truth
  contradiction
/-- Authentic complete packet rows cannot leave the Boolean fold unresolved. -/
theorem row_total (valid : guards.all (fun d => Decidable.decide (d ≠ 0)) = true)
    (signs : SelectedSigns context.root (RepresentationSpecialize.prepare values formula))
    (packet : evidence.check? context (RepresentationSpecialize.prepare values formula) = some signs) :
    ∃ result, checkRow original values guards formula context evidence = .ok result := by
  unfold checkRow Algebraic.Context.readEvidence?
  simp only [valid, Bool.not_true, Bool.false_eq_true, ite_false, packet]
  have row := fact_signs original context signs
  change (context.signFacts original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign original.neg original.inv signs).toList.map
    (factSign context) = signs.values.toList at row
  rw [row]
  obtain ⟨result, evaluated⟩ := Samples.Row.eval_total formula signs.values.toList _
    (source_signs original values formula context signs)
  exact ⟨result, by rw [evaluated]⟩

/-- A zero original divisor rejects independently of every certificate field. -/
theorem row_zero (d : parent.Value) (member : d ∈ guards) (zero : d = 0) :
    checkRow original values guards formula context evidence = .error .divisor := by
  have bad : guards.all (fun d => Decidable.decide (d ≠ 0)) = false := by
    apply Bool.eq_false_iff.mpr
    intro valid
    have nonzero := of_decide_eq_true ((List.all_eq_true.mp valid) d member)
    exact nonzero zero
  simp only [checkRow, bad, Bool.not_false, ite_true]
end Row

end Hex.RCF.RealCoefficients.SelectedFormula
