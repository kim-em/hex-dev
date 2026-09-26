/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.SignMatrix
public import HexRCF.RealFormula

public section

/-! Evaluate shared real formulas from signs supplied by checked cells. -/

namespace Hex.RealFormula.QF

open Hex.RCF

/-- Every Boolean branch is evaluated, including one whose other branch has
already decided the truth value. Thus a missing sign always fails closed. -/
@[expose] def evalSigns (signOf : Hex.RealFormula.Poly n → Option Sign) : Hex.RealFormula.QF n → Option Bool
  | .atom a => do
      let sign ← signOf a.p
      pure ((Hex.RCF.RealFormula.toCmp a.cmp).evalSign sign)
  | .tt => some true
  | .ff => some false
  | .not p => do
      let value ← evalSigns signOf p
      pure (!value)
  | .and p q => do
      let left ← evalSigns signOf p
      let right ← evalSigns signOf q
      pure (left && right)
  | .or p q => do
      let left ← evalSigns signOf p
      let right ← evalSigns signOf q
      pure (left || right)

/-- The executable Boolean result agrees with the original formula whenever
each referenced polynomial has an exact sign at the given real valuation. -/
theorem evalSigns_spec {formula : Hex.RealFormula.QF n}
    {signOf : Hex.RealFormula.Poly n → Option Sign} {ρ : Fin n → ℝ}
    (hlookup : ∀ p ∈ formula.polys, ∃ sign,
      signOf p = some sign ∧
      SignType.sign (((sign.toInt : Int) : ℝ)) = SignType.sign (p.eval ρ)) :
    ∃ value, evalSigns signOf formula = some value ∧
      (value = true ↔ formula.toProp ρ) := by
  induction formula with
  | atom a =>
      obtain ⟨sign, hs, hsign⟩ := hlookup a.p (by simp)
      refine ⟨(Hex.RCF.RealFormula.toCmp a.cmp).evalSign sign,
        by simp [evalSigns, hs], ?_⟩
      rw [Hex.RealFormula.QF.toProp, Hex.RealFormula.Atom.toProp]
      exact (Hex.RCF.Cmp.evalSign_iff hsign).trans
        (Hex.RCF.RealFormula.toCmp_correct a.cmp (a.p.eval ρ))
  | tt => exact ⟨true, rfl, by simp [Hex.RealFormula.QF.toProp]⟩
  | ff => exact ⟨false, rfl, by simp [Hex.RealFormula.QF.toProp]⟩
  | not p ih =>
      obtain ⟨v, hv, hp⟩ := ih (by
        intro q hq
        exact hlookup q (by simpa using hq))
      refine ⟨!v, by simp [evalSigns, hv], ?_⟩
      cases v <;> simp_all [Hex.RealFormula.QF.toProp]
  | and p q ihp ihq =>
      obtain ⟨v, hv, hp⟩ := ihp (by
        intro r hr
        exact hlookup r (by simp [hr]))
      obtain ⟨w, hw, hq⟩ := ihq (by
        intro r hr
        exact hlookup r (by simp [hr]))
      refine ⟨v && w, by simp [evalSigns, hv, hw], ?_⟩
      cases v <;> cases w <;> simp_all [Hex.RealFormula.QF.toProp]
  | or p q ihp ihq =>
      obtain ⟨v, hv, hp⟩ := ihp (by
        intro r hr
        exact hlookup r (by simp [hr]))
      obtain ⟨w, hw, hq⟩ := ihq (by
        intro r hr
        exact hlookup r (by simp [hr]))
      refine ⟨v || w, by simp [evalSigns, hv, hw], ?_⟩
      cases v <;> cases w <;> simp_all [Hex.RealFormula.QF.toProp]

/-- A successful true evaluation is equivalent to the original formula. -/
theorem evalSigns_eq_true_iff {formula : Hex.RealFormula.QF n}
    {signOf : Hex.RealFormula.Poly n → Option Sign} {ρ : Fin n → ℝ}
    (hlookup : ∀ p ∈ formula.polys, ∃ sign,
      signOf p = some sign ∧
      SignType.sign (((sign.toInt : Int) : ℝ)) = SignType.sign (p.eval ρ)) :
    formula.evalSigns signOf = some true ↔ formula.toProp ρ := by
  obtain ⟨value, hvalue, hsemantic⟩ := evalSigns_spec hlookup
  constructor
  · intro htrue
    exact hsemantic.mp (Option.some.inj (hvalue.symm.trans htrue))
  · intro hprop
    have htrue : value = true := hsemantic.mpr hprop
    simpa [htrue] using hvalue

end Hex.RealFormula.QF
