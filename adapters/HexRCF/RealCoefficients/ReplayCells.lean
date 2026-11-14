/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Replay
public import HexRCF.RealCoefficients.FieldCells
public section

/-! Frozen sentence replay using finite real-cell evidence. The input and
certificate records are shared with the fixed-field producer. Acceptance
requires no irreducibility theorem for their common presentation. -/
namespace Hex.RCF.RealCoefficients.Replay

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable {Ctx : Type u} [DecidableEq Ctx]

/-- Read the strict fold using the automatic frontend's grouped source
specialization. The envelope checker establishes coverage before this fold;
the fold alone does not authenticate its sign-table reads. -/
@[expose] def Input.cellValue (input : Input p s hw hp Ctx n)
    (data : FieldBuild.Result p s hw hp Ctx (n + 1)) : Option Bool :=
  let row := fun cell => input.formula.evalSigns
    (Decision.cellSign (FieldQuery.cached data.signs) FieldDecision.point
      (RepresentationSpecialize.polynomial input.values) data.isolation
      (data.rootSigns.value data.isolation.total) cell)
  match input.quantifier with
  | .forallReal => OptionFold.allArray (Cell.all data.isolation.isolations.intervals.size) row
  | .existsReal => OptionFold.anyArray (Cell.all data.isolation.isolations.intervals.size) row

/-- Check the exact input binding, every original divisor, the complete finite
envelope and then the strict fold. Every retained sign certificate is checked.
No root, gcd, sign or approximation search is invoked. -/
@[expose] def checkCells (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) : Except Error Bool :=
  if !cert.input.matches input then .error .binding
  else if !input.divisors.all (fun divisor =>
      (cert.data.signs.lookup? divisor).any (fun value => Decidable.decide (value ≠ 0))) then .error .divisor
  else if !FieldCells.check cert.data.signs input.context
      (RepresentationSpecialize.polynomial input.values) input.formula
      cert.data.radical cert.data.isolation cert.data.rootSigns then .error .evidence
  else match input.cellValue cert.data with
    | none => .error .unresolved
    | some value => .ok value

theorem checkCells_parts (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) (value : Bool)
    (accepted : checkCells input cert = .ok value) :
    cert.input.matches input = true ∧
    input.divisors.all (fun divisor =>
      (cert.data.signs.lookup? divisor).any (fun value => Decidable.decide (value ≠ 0))) = true ∧
    FieldCells.check cert.data.signs input.context
      (RepresentationSpecialize.polynomial input.values) input.formula
      cert.data.radical cert.data.isolation cert.data.rootSigns = true ∧
    input.cellValue cert.data = some value := by
  unfold checkCells at accepted
  split at accepted
  · cases accepted
  · rename_i binding
    split at accepted
    · cases accepted
    · rename_i domains
      split at accepted
      · cases accepted
      · rename_i evidence
        cases folded : input.cellValue cert.data with
        | none => simp only [folded] at accepted; cases accepted
        | some observed =>
          simp only [folded] at accepted
          cases accepted
          exact ⟨by simpa using binding, by simpa using domains,
            by simpa using evidence, rfl⟩

/-- Original divisor nonvanishing is a conclusion of authenticated finite
sign evidence, even for constant, zero or empty-domain sentences. -/
theorem checkCells_domains (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) (value : Bool)
    (accepted : checkCells input cert = .ok value) :
    ∀ divisor ∈ input.divisors,
      Field.value (Field.literalRep p s hw hp) divisor ≠ 0 := by
  obtain ⟨_, domains, evidence, _⟩ := checkCells_parts input cert value accepted
  have header := FieldCells.signs_checked cert.data.signs input.context
    (RepresentationSpecialize.polynomial input.values) input.formula
    cert.data.radical cert.data.isolation cert.data.rootSigns evidence
  intro divisor member zero
  have guard := List.all_eq_true.mp domains divisor member
  cases found : cert.data.signs.lookup? divisor with
  | none => simp [found] at guard
  | some observed =>
    have nonzero : observed ≠ 0 := by simpa [found] using guard
    have exactSign := Field.checkSignTable_lookup p s hw hp cert.data.signs
      header divisor observed found
    rw [exactSign, zero] at nonzero
    exact nonzero (by simp)

/-- Every accepted verdict has the exact fixed-source meaning. Complete roots,
semantic degrees, signs and ordinary real samples follow from checked data. -/
theorem checkCells_spec (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) (value : Bool)
    (accepted : checkCells input cert = .ok value) : value = true ↔ input.toProp := by
  obtain ⟨_, _, evidence, folded⟩ := checkCells_parts input cert value accepted
  have header := FieldCells.signs_checked cert.data.signs input.context
    (RepresentationSpecialize.polynomial input.values) input.formula
    cert.data.radical cert.data.isolation cert.data.rootSigns evidence
  let valuation := fun x : ℝ => RealFormula.append
    (fun j => Field.value (Field.literalRep p s hw hp) (input.values j)) x
  have specialization := FieldCells.specialize cert.data.signs header input.values
  cases quantifier : input.quantifier with
  | forallReal =>
    have meaning := FieldCells.forall_formula cert.data.signs input.context
      (RepresentationSpecialize.polynomial input.values) input.formula
      cert.data.radical cert.data.isolation cert.data.rootSigns valuation specialization evidence
    simp only [Input.cellValue, quantifier] at folded
    rw [folded] at meaning
    simpa only [Option.some.injEq, Input.toProp, quantifier, valuation] using meaning
  | existsReal =>
    have meaning := FieldCells.exists_formula cert.data.signs input.context
      (RepresentationSpecialize.polynomial input.values) input.formula
      cert.data.radical cert.data.isolation cert.data.rootSigns valuation specialization evidence
    simp only [Input.cellValue, quantifier] at folded
    rw [folded] at meaning
    simpa only [Option.some.injEq, Input.toProp, quantifier, valuation] using meaning

theorem checkCells_sound (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n)
    (accepted : checkCells input cert = .ok true) : input.toProp :=
  (checkCells_spec input cert true accepted).mp rfl

/-- Compose finite replay with the independently authenticated source goal. -/
theorem checkCells_original (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) (original : Prop)
    (equivalence : input.toProp ↔ original)
    (accepted : checkCells input cert = .ok true) : original :=
  equivalence.mp (checkCells_sound input cert accepted)

end Hex.RCF.RealCoefficients.Replay
