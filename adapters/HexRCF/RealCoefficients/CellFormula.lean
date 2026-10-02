/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Formula
public import HexRCF.Soundness

public section

/-! Quantifier folds over real cells whose polynomial signs have been checked. -/

namespace Hex.RCF.RealCoefficients

private theorem cell_eval {m n : Nat} (root : Fin m → ℝ)
    (hmono : StrictMono root) (formula : Hex.RealFormula.QF n)
    (valuation : ℝ → Fin n → ℝ)
    (signOf : Cell m → Hex.RealFormula.Poly n → Option Sign)
    (hlookup : ∀ c x, Cell.Region root c x →
      ∀ p ∈ formula.polys, ∃ sign,
        signOf c p = some sign ∧
        SignType.sign (((sign.toInt : Int) : ℝ)) =
          SignType.sign (p.eval (valuation x))) (c : Cell m) :
    ∃ value, formula.evalSigns (signOf c) = some value ∧
      ∀ x, Cell.Region root c x →
        (value = true ↔ formula.toProp (valuation x)) := by
  obtain ⟨sample, hsample⟩ := Cell.Region.exists_point root hmono c
  obtain ⟨value, hvalue, _⟩ := Hex.RealFormula.QF.evalSigns_spec
    (hlookup c sample hsample)
  refine ⟨value, hvalue, ?_⟩
  intro x hx
  have hiff := Hex.RealFormula.QF.evalSigns_eq_true_iff (hlookup c x hx)
  rw [hvalue] at hiff
  simpa only [Option.some.injEq] using hiff

/-- A strict fold of checked cell formulas proves a universal real statement. -/
theorem forall_formula {m n : Nat} (root : Fin m → ℝ)
    (hmono : StrictMono root) (formula : Hex.RealFormula.QF n)
    (valuation : ℝ → Fin n → ℝ)
    (signOf : Cell m → Hex.RealFormula.Poly n → Option Sign)
    (hlookup : ∀ c x, Cell.Region root c x →
      ∀ p ∈ formula.polys, ∃ sign,
        signOf c p = some sign ∧
        SignType.sign (((sign.toInt : Int) : ℝ)) =
          SignType.sign (p.eval (valuation x))) :
    OptionFold.allArray (Cell.all m) (fun c => formula.evalSigns (signOf c)) = some true ↔
      ∀ x, formula.toProp (valuation x) := by
  obtain ⟨value, hvalue, hsemantic⟩ := CellFold.Region.forall_spec root hmono
    (fun c => formula.evalSigns (signOf c))
    (fun x => formula.toProp (valuation x))
    (cell_eval root hmono formula valuation signOf hlookup)
  constructor
  · intro h
    exact hsemantic.mp (Option.some.inj (hvalue.symm.trans h))
  · intro h
    have hv : value = true := hsemantic.mpr h
    simpa [hv] using hvalue

/-- A strict fold of checked cell formulas proves an existential real statement. -/
theorem exists_formula {m n : Nat} (root : Fin m → ℝ)
    (hmono : StrictMono root) (formula : Hex.RealFormula.QF n)
    (valuation : ℝ → Fin n → ℝ)
    (signOf : Cell m → Hex.RealFormula.Poly n → Option Sign)
    (hlookup : ∀ c x, Cell.Region root c x →
      ∀ p ∈ formula.polys, ∃ sign,
        signOf c p = some sign ∧
        SignType.sign (((sign.toInt : Int) : ℝ)) =
          SignType.sign (p.eval (valuation x))) :
    OptionFold.anyArray (Cell.all m) (fun c => formula.evalSigns (signOf c)) = some true ↔
      ∃ x, formula.toProp (valuation x) := by
  obtain ⟨value, hvalue, hsemantic⟩ := CellFold.Region.exists_spec root hmono
    (fun c => formula.evalSigns (signOf c))
    (fun x => formula.toProp (valuation x))
    (cell_eval root hmono formula valuation signOf hlookup)
  constructor
  · intro h
    exact hsemantic.mp (Option.some.inj (hvalue.symm.trans h))
  · intro h
    have hv : value = true := hsemantic.mpr h
    simpa [hv] using hvalue

end Hex.RCF.RealCoefficients
