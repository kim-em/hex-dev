/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.Samples
public import HexRCF.RealCoefficients.Replay
public import HexRealClosure.SignCodec
public section
namespace Hex.RCF.RealCoefficients.PointReplay
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

@[expose] def signs {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E]
    [Mul E] [Neg E] [NatCast E] (sign : E → Int) {n : Nat} (values : Fin n → E)
    (formula : RealFormula.QF (n+1)) (sample : E) : List Int :=
  (RepresentationSpecialize.prepare values formula).map (fun p => sign (p.eval sample))

@[expose] def row (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (sample : parent.Value) : List Int := signs parent.sign values formula sample

@[expose] def rowWith (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (sample : parent.Value) (one : One parent.Value) (add : Add parent.Value)
    (mul : Mul parent.Value) (neg : Neg parent.Value) (nat : NatCast parent.Value) : List Int :=
  @signs parent.Value (Tower.instZeroValue parent) (Tower.instDecidableEqValue parent)
    one add mul neg nat parent.sign n values formula sample

theorem rowWith_eq (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (sample : parent.Value) (one : One parent.Value) (add : Add parent.Value)
    (mul : Mul parent.Value) (neg : Neg parent.Value) (nat : NatCast parent.Value)
    (ho : one = Tower.instOneValue parent) (ha : add = Tower.instAddValue parent)
    (hm : mul = Tower.instMulValue parent) (hn : neg = Tower.instNegValue parent)
    (hc : nat = Tower.instNatCastValue parent) :
    rowWith values formula sample one add mul neg nat = row values formula sample := by
  cases ho; cases ha; cases hm; cases hn; cases hc
  rfl

@[expose] def check (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (subject : Codec.Json) : Except Replay.Error Bool :=
  if !guards.all (fun d => Decidable.decide (d ≠ 0)) then .error .divisor
  else match value.decode subject with
    | .error _ => .error .evidence
    | .ok sample => match Samples.Row.eval formula (row values formula sample) with
      | none => .error .unresolved
      | some result => .ok result

@[expose] def checkWith (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (one : One parent.Value) (add : Add parent.Value) (mul : Mul parent.Value)
    (neg : Neg parent.Value) (nat : NatCast parent.Value)
    (_ho : one = Tower.instOneValue parent) (_ha : add = Tower.instAddValue parent)
    (_hm : mul = Tower.instMulValue parent) (_hn : neg = Tower.instNegValue parent)
    (_hc : nat = Tower.instNatCastValue parent) (subject : Codec.Json) : Except Replay.Error Bool :=
  if !guards.all (fun d => Decidable.decide (d ≠ 0)) then .error .divisor
  else match value.decode subject with
    | .error _ => .error .evidence
    | .ok sample => match Samples.Row.eval formula (rowWith values formula sample one add mul neg nat) with
      | none => .error .unresolved
      | some result => .ok result

theorem checkWith_eq (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (one : One parent.Value) (add : Add parent.Value) (mul : Mul parent.Value)
    (neg : Neg parent.Value) (nat : NatCast parent.Value)
    (ho : one = Tower.instOneValue parent) (ha : add = Tower.instAddValue parent)
    (hm : mul = Tower.instMulValue parent) (hn : neg = Tower.instNegValue parent)
    (hc : nat = Tower.instNatCastValue parent) (subject : Codec.Json) :
    checkWith value values guards formula one add mul neg nat ho ha hm hn hc subject =
      check value values guards formula subject := by
  cases ho; cases ha; cases hm; cases hn; cases hc
  rfl

theorem row_signs (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (sample : parent.Value) :
    row values formula sample = formula.polys.map (fun p =>
      (SignType.sign (p.eval (Samples.valuation original values (original.value sample))) : Int)) := by
  have evaluations := Samples.prepare_real original values formula (original.value sample)
  have signedEvaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int))) evaluations
  unfold row signs
  simp only [List.map_map, Function.comp_def] at signedEvaluations ⊢
  have equal (p : DensePoly parent.Value) :
      parent.sign (p.eval sample) =
        (SignType.sign (RepresentationSpecialize.evaluate original.value original.zero_iff
          (original.value sample) p) : Int) := by
    rw [original.sign]
    unfold RepresentationSpecialize.evaluate
    rw [HexPolyTheory.Interpret.eval_interpret original.value original.zero_iff
      original.add original.mul]
  simpa only [equal] using signedEvaluations

theorem check_fields (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (subject : Codec.Json) (result : Bool)
    (accepted : check value values guards formula subject = .ok result) :
    ∃ sample, value.decode subject = .ok sample ∧
      guards.all (fun d => Decidable.decide (d ≠ 0)) = true ∧
      Samples.Row.eval formula (row values formula sample) = some result := by
  unfold check at accepted
  cases domains : guards.all (fun d => Decidable.decide (d ≠ 0)) <;>
    simp only [domains, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte] at accepted
  · cases accepted
  · cases parsed : value.decode subject <;> simp only [parsed] at accepted
    · cases accepted
    · rename_i sample
      cases evaluated : Samples.Row.eval formula (row values formula sample) <;>
        simp only [evaluated] at accepted
      · cases accepted
      · rename_i observed
        have same : observed = result := Except.ok.inj accepted
        subst observed
        exact ⟨sample, rfl, rfl, evaluated⟩

theorem check_domains (original : Model parent ℝ) (value : ValueCodec parent.Value)
    (values : Fin n → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF (n+1)) (subject : Codec.Json) (result : Bool)
    (accepted : check value values guards formula subject = .ok result) :
    ∀ d ∈ guards, original.value d ≠ 0 := by
  obtain ⟨_, _, nonzero, _⟩ := check_fields value values guards formula subject result accepted
  intro d member zero
  have checked := List.all_eq_true.mp nonzero d member
  have same := (original.zero_iff d).mp zero
  simp [same] at checked

theorem check_sound (original : Model parent ℝ) (value : ValueCodec parent.Value)
    (values : Fin n → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF (n+1)) (subject : Codec.Json)
    (accepted : check value values guards formula subject = .ok true) :
    ∃ x : ℝ, formula.toProp (Samples.valuation original values x) := by
  obtain ⟨sample, _, _, truth⟩ := check_fields value values guards formula subject true accepted
  exact ⟨original.value sample, (Samples.Row.eval_true _ _ _
    (row_signs original values formula sample)).mp truth⟩

theorem check_false (original : Model parent ℝ) (value : ValueCodec parent.Value)
    (values : Fin n → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF (n+1)) (subject : Codec.Json)
    (accepted : check value values guards formula subject = .ok false) :
    ¬ ∀ x : ℝ, formula.toProp (Samples.valuation original values x) := by
  obtain ⟨sample, _, _, rejected⟩ := check_fields value values guards formula subject false accepted
  intro all
  have truth := (Samples.Row.eval_true _ _ _
    (row_signs original values formula sample)).mpr (all (original.value sample))
  rw [rejected] at truth
  cases truth


theorem check_zero (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1)) (subject : Codec.Json)
    (present : 0 ∈ guards) : check value values guards formula subject = .error .divisor := by
  have rejected : guards.all (fun d => Decidable.decide (d ≠ 0)) = false := by
    cases result : guards.all (fun d => Decidable.decide (d ≠ 0)) with
    | false => rfl
    | true =>
      have nonzero := List.all_eq_true.mp result 0 present
      simp at nonzero
  simp only [check, rejected, Bool.not_false, ↓reduceIte]
end Hex.RCF.RealCoefficients.PointReplay
